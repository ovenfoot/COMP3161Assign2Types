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
primOpType Fst  = Forall "t" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "t" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
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

generalise :: Gamma -> Type -> QType
generalise g t = Ty t 
generalise g t = error "implement generalse!"


inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram gamma [Bind id Nothing [] expr] = 
    do  (expr', t , s) <-inferExp gamma expr 
        return ([Bind id (Just (Ty t)) [] expr' ], t, s)


--inferProgram env [Bind "main" Nothing [] (Num n)] = return $ (([Bind "main" (Just (Ty (Base Int))) [] (Num n)]), (Base Int), ([("main", Num)]))  



--error("Spotted!")
inferProgram env bs = error ("implement inferProgram! Gamma is -->" ++ (show env) ++ "<--- program is --->" ++ (show bs)) 
--don't forget to run the result substitution on the entire expression using allTypes from Syntax.hs"

arrowTail:: Type -> TC Type
arrowTail (Arrow e1 t1) = return t1
arrowTail (t1) = return t1

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp g (Num n) = do   
            return (Num n, Base Int, emptySubst)
inferExp g (Con c) = do   
            t  <- unquantify (qtau)
            return (Con c, t, emptySubst)
              where Just qtau = constType c
inferExp g (Prim p) = do
            t   <- unquantify (qtau)
            beta <- fresh
            return (Prim p, t, emptySubst)
              where qtau = primOpType p
inferExp g (Var id) = case E.lookup g id of 
            Just qt -> do
              t1 <- unquantify qt
              return (Var id, t1, emptySubst)
            Nothing -> error "FUCK"

  {-do
            beta <- fresh
            return (Var id, t1, emptySubst)
              where t1 = TypeVar id -}
inferExp g (App e1 e2) = do
            (e1', t1, s1) <- inferExp g e1
            (e2', t2, s2) <- inferExp g e2
            alpha         <- fresh
            u             <- unify (substitute (s2<>s1) (t1)) (Arrow (substitute (s2<>s1) (t2)) alpha)
            return (App e1' e2', (substitute u alpha), s1 <> s2 <> u)

inferExp g (If e e1 e2) = do
            (e', t, s)    <- inferExp g e
            u             <- unify t (Base Bool)
            (e1', t1, s1) <- inferExp g e1
            (e2', t2, s2) <- inferExp g e2
            u'            <- unify (substitute s2 t1) (t2)
            return (If e' e1' e2', (substitute u' t2), u'<>s2<>s1<>u<>s)

inferExp g (Let [Bind id Nothing [] e1] e2) = do
            (e1', t1, s1)   <- inferExp g e1
            (e2', t2, s2)   <- inferExp (E.add g (id, (generalise g t1))) e2         
            return ((Let [Bind id (Just (Ty t1)) [] e1'] e2'), t2, s2<>s1) 


inferExp g (Letfun (Bind funId Nothing [varId] e)) = do
            alpha1        <- fresh
            alpha2        <- fresh
            (e', t, s)    <- inferExp (
              E.addAll g [(varId, (generalise g alpha1)), 
                          (funId, (generalise g alpha2)) ]) e
            u             <- unify (substitute (s) alpha2) (Arrow (substitute s alpha1) t)
            typ           <- unquantify' 0 u (Ty (Arrow (substitute s alpha1) (t) ))
            return (Letfun (Bind funId (Just (Ty typ)) [varId] e'), typ, u<>s)
            --return (Letfun (Bind funId (Just (Ty (substitute u (Arrow (substitute (s<>s1<>s2) alpha1) t)))) [varId] e'),   (substitute u (Arrow (substitute (s<>s1<>s2) alpha1) t)), u<>s<>s1<>s2)
inferExp g exp = error ("Implement inferExp! Gamma is -->" ++ (show g) ++ "<--- exp is --->" ++ (show exp))                        

{-
inferExp g (App (App (Prim Eq) (Num n)) (Num m)) = do    
              s <- unify (Base Bool) (Base Bool)
              return (exp, Base Bool, s) where
                exp = (App (App (Prim Eq) (Num n)) (Num m))
inferExp g (App (App (Prim Ne) (Num n)) (Num m)) = do    
              s <- unify (Base Bool) (Base Bool)
              return (exp, Base Bool, s) where
                exp = (App (App (Prim Ne) (Num n)) (Num m))
inferExp g (App (App (Prim Lt) (Num n)) (Num m)) = do    
              s <- unify (Base Bool) (Base Bool)
              return (exp, Base Bool, s) where
                exp = (App (App (Prim Lt) (Num n)) (Num m))
inferExp g (App (App (Prim Le) (Num n)) (Num m)) = do    
              s <- unify (Base Bool) (Base Bool)
              return (exp, Base Bool, s) where
                exp = (App (App (Prim Le) (Num n)) (Num m))
inferExp g (App (App (Prim Gt) (Num n)) (Num m)) = do    
              s <- unify (Base Bool) (Base Bool)
              return (exp, Base Bool, s) where
                exp = (App (App (Prim Gt) (Num n)) (Num m))
inferExp g (App (App (Prim Ge) (Num n)) (Num m)) = do    
              s <- unify (Base Bool) (Base Bool)
              return (exp, Base Bool, s) where
                exp = (App (App (Prim Ge) (Num n)) (Num m))
inferExp g (App (App (Prim p) (Num n)) (Num m)) = do    
              s <- unify (Base Int) (Base Int)
              return (exp, Base Int, s) where
                exp = (App (App (Prim p) (Num n)) (Num m))
-} 