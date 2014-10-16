--Hints from Gabi

data Type = Arrow Type Type
			| Prod Type Type
			| Sum Type Type
			| Base Basteype
			


--etc

freshname:: TC Id

typeError -whenever you can't unify the type properly

substGamma subtitute into the envrionment

Get unificaiton done as quckly as possible


--Code from liam's tute week 11


module Unification where

type VarName = String

data Type = Id String
			| Pair Type Type
			| Sum Type Type
			| Fun Type Type
			| PInt |PBool
			deriving (Show)

			


--Substitution 
data Subst = [(VarName, Type)] --in the assignment there is an abstract type

class Monad 'm where
	return' :: a-> m a
	(>>=') ::  m a -> (a->m b) -> m b


substOne :: (Varname, Type) -> Type -> Type
substOne (v,t) (Id x) 	| x==v = t
						| otherwise Id x
substOne (v,t) (Pair x y)  = Pair (substOne s x) (substOne s y)
substOne (v,t) (Sum x y)  = Sum (substOne s x) (substOne s y)
substOne (v,t) (Fun x y)  = Fun (substOne s x) (substOne s y)
substOne _ t = t


subst :: Subst -> Type -> Type
subst s t = foldr substOne t s
subst = subst

occursIn v t = v 'elem' tv t

tv :: Type-> [VarName]
tv (Id v) = [v]
tv (Pair x y) = tv x ++ tv y
tv (Sum x y) = tv x ++ tv y
tv (Fun x y) = tv x ++ tv y
tv _ = []

Bind :: Maybe a -> (a-> Maybe b) -> Maybe b
Bind Nothing = Nothing
Bind (Just x) f = f x

--Introduce Maybe to say that it might not return a value
--The use of maybe means we have to include "Just" in everything we return
unify :: Type -> Type -> Maybe Subst
{-let thet = unify t1 t2
	in theta(t1) == theta(t2) --Unifying two types makes the substitution the same
	and theta is the most general substitution possible
	
-}
unify (Id x) (Id y) | Just x==y = [] --same type means empty substitution
					| otherwise = [(x, Id y)]
--This implements proper error handling
unify (Pair x1 x2) (Pair y1 y2)  = do
			u1 <- x1 'unify' y1
			u2 <- subst u1 x2 'unify' subst u1 y2
			return (u1 ++ u2)

unify (Fun x1 x2) (Fun y1 y2)  = do
			u1 <- x1 'unify' y1
			u2 <- subst u1 x2 'unify' subst u1 y2
			return (u1 ++ u2)
unify (Sum x1 x2) (Sum y1 y2)  = do
			u1 <- x1 'unify' y1
			u2 <- subst u1 x2 'unify' subst u1 y2
			return (u1 ++ u2)

--Below is the stock standard stupid way of implementing withot proper error handling			
{-unify (Pair x1 x2) (Pair y1 y2)  = --pair is a product type
			let 	u1 = x1 'unify' y1
					u2 = subst u1 x2 'unify' subst u1 u2
					in u1 ++ u2
unify (Sum x1 x2) (Sum y1 y2)  = --pair is a product type
			let 	u1 = x1 'unify' y1
					u2 = subst u1 x2 'unify' subst u1 u2
					in u1 ++ u2
unify (Fun x1 x2) (Fun y1 y2)  = --pair is a product type
			let 	u1 = x1 'unify' y1
					u2 = subst u1 x2 'unify' subst u1 u2
					in u1 ++ u2
-}
{-
--below implements halfway correct error handling using monads
unify (Pair x1 x2) (Pair y1 y2)  = --pair is a product type
			(x1 'unify' y1) 'bind' \u1 ->
				(subst u1 x2 'unify' subst u1 y2) 'bind' \u2 ->
					Just (u1 ++ u2)
-}
--note that in the assignment, Pair, Sum and Fun are encompassed in an applcation. so we need only take care of the application case
unify (PInt) (PInt) = Just []
unify (PBool)(PBool) = Just []
unify (Id x) t 	| x 'occursIn' t 	= Nothing
				| otherwise			= [(x,t)]
unify _ _ = Nothing
--in the assignment dont use error to trash the entire program


{-
The assignment uses a monad called TC a
typeError: TypeError: TC a
fresh::TC Type
returns a fresh type variable which has never been heard of before
-}

{-
'you could have invented monads' is a good monad tutorial
-}

{-
given App (App (Con Pair) x1) x2) - first unify (App (Con Pair) x1) then unify x2
-}

{-
Hints from lec week 13
-}

--program syntax 
Bind id Nothing [] expr 

--inferExpression infers the type of expr and puts the type in Nothing.
--So the bind becomes
Bind id (Just t) [] expr

inferProgram calls inferBind calls inferExpression
{-
Generally, just do simple expressions and work from there
Simple expressions should not need too much unification
e.g main = 1+3 infers what the type "plus" is through unification.
-}

App e1 e2 -- see the assignemnt spec for implementation notes

unify:: Type -> Type -> TC Subst
--TCMonad hides global state (not entirely sure what that means

--during inference 
s<-unify ...
Debug.trace(show s)

inferProgram [Bind ... expr] = do (expr', t ,s) <- inferExpression(...) -- t is type 
--or
return ([Bind id (Just t)  expr', t, s)

--if you want to print something in TCMonad
Debug.traceM(show subst)
