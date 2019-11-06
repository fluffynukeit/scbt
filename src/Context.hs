module Context where

import Syntax
import Data.Sequence
import Data.Foldable

pattern Comma a b = (:|>) a b
pattern Empty = Data.Sequence.Empty

-- | Implements Figure 12, applying a context to a Type
class Subst a where
    subst :: Gamma -> a -> a

instance Subst Tau where
    subst gamma alpha@(Alpha sym) = 
        let result = find matchingSymbol gamma
            matchingSymbol = \case
                Equals (sym' :=: _) | sym == sym' -> True
                _ -> False
        in case result of
            Just (Equals (_ :=: tau)) -> subst gamma tau
            Nothing -> alpha
    subst gamma alphaHat@(AlphaHat sym) = 
        let result = find matchingSymbol gamma
            matchingSymbol = \case
                HatEquals (sym' ::: kappa :=: tau) | sym == sym' -> True
                _ -> False
        in case result of
            Just (HatEquals (sym ::: kappa :=: tau)) -> subst gamma tau
            Nothing -> alphaHat


instance Subst A where
    subst gamma ((t1 :=: t2) :>: a) = (subst gamma t1 :=: subst gamma t2) :>: subst gamma a
    subst gamma (a :/\: (t1 :=: t2)) = subst gamma a :/\: (subst gamma t1 :=: subst gamma t2)
    subst gamma (a :->: b) = subst gamma a :->: subst gamma b
    subst gamma (a :+: b) = subst gamma a :+: subst gamma b
    subst gamma (a :*: b) = subst gamma a :*: subst gamma b
    subst gamma (Vec t a) = Vec (subst gamma t) (subst gamma a)
    subst gamma (V anno a) = V anno (subst gamma a)
    subst gamma (E anno a) = E anno (subst gamma a)

