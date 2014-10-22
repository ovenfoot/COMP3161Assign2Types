module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)

unify :: Type -> Type -> TC Subst
unify (TypeVar v1) (TypeVar v2) = if v1 == v2 then
                                    return emptySubst
                                  else
                                    return (v1 =: (TypeVar v2))
unify (Base t1) (Base t2) = if t1 == t2 then
                              return emptySubst
                            else
                             typeError (TypeMismatch (Base t1) (Base t2))-- 
unify (Prod x1 x2) (Prod y1 y2) = do
                  s1 <- unify x1 y1
                  s2 <- unify (substitute s1 x2) (substitute s1 y2)
                  return (s1 <> s2)
unify (Sum x1 x2) (Sum y1 y2) = do
                  s1 <- unify x1 y1
                  s2 <- unify (substitute s1 x2) (substitute s1 y2)
                  return (s1 <> s2)
unify (Arrow x1 x2) (Arrow y1 y2) = do
                  s1 <- unify x1 y1
                  s2 <- unify (substitute s1 x2) (substitute s1 y2)
                  return (s1 <> s2)
unify (TypeVar v) (t) =  if (elem v (tv t)) then
                          typeError (OccursCheckFailed v t)
                        else
                          return (v =: t) 
unify (t) (TypeVar v) =  if (elem v (tv t)) then
                          typeError (OccursCheckFailed v t)
                        else
                          return (v =: t)
--unify _ _ = typeError (MalformedAlternatives)
unify t1 t2 = error ("implement unify! t1 is -->" ++ (show t1) ++"<---->" ++ (show t2))

generaliseList :: [Id] -> Type -> QType
generaliseList [] t = Ty t
generaliseList (x:xs) t  = Forall x (generaliseList xs t)
removeID:: [Id] -> [Id] -> [Id]
removeID gamma [] = gamma
removeID gamma (x:xs) = filter (/=x) (removeID gamma xs)

generalise :: Gamma -> Type -> QType
generalise g t = generaliseList (removeID (tv t) (tvGamma g) ) t

generaliseTC::Gamma -> Type -> TC QType
generaliseTC g t = return $ generalise g t

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram gamma [Bind id Nothing [] expr] = 
    do  (expr', t , s) <-inferExp gamma expr
        return ( ([Bind id (Just (generalise gamma t)) [] (allTypes (substQType s) expr') ]), t, s)


inferProgram env bs = error ("implement inferProgram! Gamma is -->" ++ (show env) ++ "<--- program is --->" ++ (show bs)) 
--don't forget to run the result substitution on the entire expression using allTypes from Syntax.hs"


inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp g (Num n) = do   
            return (Num n, Base Int, emptySubst)

inferExp g (Con c) = do   
            t  <- unquantify (qtau)
            --beta  <- fresh
            return (Con c, t, emptySubst)
              where Just qtau = constType c

inferExp g (Prim p) = do
            t     <- unquantify (qtau)
           -- beta  <- fresh
            return (Prim p, t, emptySubst)
              where qtau = primOpType p

inferExp g (Var id) = case E.lookup g id of 
            Just qt -> do
              t1    <- unquantify qt
              --beta  <- fresh
              return (Var id, t1, emptySubst)
            Nothing -> error "Variable not in environment"

inferExp g (App e1 e2) = do
            (e1', t1, s1) <- inferExp g e1
            (e2', t2, s2) <- inferExp g e2
            alpha         <- fresh
            u             <- unify (substitute s2 t1) (Arrow t2 alpha)
            return ( 
              (App e1' e2'), 
              (substitute u alpha), 
              s1<>s2<>u
              )

inferExp g (If e e1 e2) = do
            (e', t, s)    <- inferExp g e
            u             <- unify t (Base Bool)
            (e1', t1, s1) <- inferExp g e1
            (e2', t2, s2) <- inferExp g e2
            u'            <- unify (substitute s2 t1) (t2)
            return (
                      (If e' e1' e2'), 
                      (substitute u' t2), 
                      u'<>s2<>s1<>u<>s
                      )

inferExp g (Let [Bind id Nothing [] e1] e2) = do
            (e1', t1, s1)   <- inferExp g e1
            (e2', t2, s2)   <- inferExp (E.add g (id, (generalise g t1))) e2
            t1Final         <- generaliseTC (E.add g (id, (generalise g t1))) t1
            return (
              (Let [Bind id (Just (t1Final)) [] e1'] e2'), 
              t2, 
              s2<>s1
              )

inferExp g (Letfun (Bind funId Nothing [varId] e)) = do
            alpha1        <- fresh
            alpha2        <- fresh
            (e', t, s)    <- inferExp (E.addAll g [
                                        (varId, (Ty alpha1)), 
                                        (funId, (Ty alpha2))
                                        ]) 
                                        e
            u             <- unify (substitute s alpha2) (Arrow (substitute s alpha1) t)
            tfinal        <- generaliseTC (E.addAll g [
                                        (varId, (Ty alpha1)), 
                                        (funId, (Ty alpha2))
                                        ]) 
                                  (substitute u (Arrow (substitute s alpha1) t))
            return (
              (Letfun (Bind funId (Just tfinal) [varId] e')) , 
              (substitute u (Arrow (substitute s alpha1) t)), 
              s<>u
              )

inferExp g (Case e [Alt id1 [x1] e1, Alt id2 [y1] e2]) = do
            alpha1          <- fresh
            alpha2          <- fresh
            (e', t, s)      <- inferExp g e
            (e1', tl, s1)   <- inferExp (E.add g (x1, (Ty alpha1))) e1
            (e2', tr, s2)   <- inferExp (E.add g (y1, (Ty alpha2))) e2
            u               <- unify (substitute (s<>s1<>s2) (Sum alpha1 alpha2)) 
                                      (substitute (s1<>s2) t)
            u'              <- unify (substitute (s2<>u) tl) (substitute u tr)
            return (
                (Case e' [Alt id1 [x1] e1', Alt id2 [y1] e2'] ),
                substitute (u<>u') tr,
                u<>u'
                )

inferExp g exp = error ("Implement inferExp! Gamma is -->" ++ (show g) ++ "<--- exp is --->" ++ (show exp))                        
