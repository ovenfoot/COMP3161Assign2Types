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
unify (Base Int) (Base Int) = return emptySubst
unify (Base Unit) (Base Unit) = return emptySubst
unify (Base Bool) (Base Bool) = return emptySubst

unify _ _ = error "implement unify!"

generalise :: Gamma -> Type -> QType
generalise g t = error "implement generalse!"

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram gamma [Bind id Nothing [] expr] = 
    do  (expr', t , s) <-inferExp gamma expr 
        return ([Bind id (Just (Ty t)) [] expr' ], t, s)


--inferProgram env [Bind "main" Nothing [] (Num n)] = return $ (([Bind "main" (Just (Ty (Base Int))) [] (Num n)]), (Base Int), ([("main", Num)]))  



--error("Spotted!")
inferProgram env bs = error ("implement inferProgram! Gamma is -->" ++ (show env) ++ "<--- program is --->" ++ (show bs)) 
--don't forget to run the result substitution on the entire expression using allTypes from Syntax.hs"

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)

inferExp g (Num n) = do   s <- unify (Base Int) (Base Int)
                          return (Num n, Base Int, s)
inferExp g (Con "False") = do   s <- unify (Base Bool) (Base Bool)
                                return (Con "False", Base Bool, s) 
inferExp g (Con "True") = do    s <- unify (Base Bool) (Base Bool)
                                return (Con "True", Base Bool, s)
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

inferExp g exp = error ("Implement inferExp! Gamma is -->" ++ (show g) ++ "<--- exp is --->" ++ (show exp))                        
--inferExp g _ = error "Implement inferExp!"
-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives


 