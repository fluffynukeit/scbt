module Context where

import Syntax
import qualified Data.Sequence as S
import Data.Foldable

-- | Patterns for Gamma,Info commonly used in paper
pattern Comma a b = (S.:|>) a b
pattern Empty = S.Empty

-- | Implementation of hole notation in section 5.2.
--
-- Hole notation splits a context into left and right segments at the hole boundary.
-- Different utility functions provide the search criteria for the hole.
-- A hole is found when the list of criteria is satisfied.

-- | True iff Info has a universal variable (one without hat)
noHat :: Info -> Bool
noHat (Kappa _) = True
noHat (Equals _) = True
noHat _ = False

-- | True iff Info has a universal variable of matching symbol
noHatOf :: Sym -> Info -> Bool
noHatOf s = \case
    Kappa (s' ::: _) -> s == s'
    Equals (s' :=: _) -> s == s'
    _ -> False

-- | True iff Info has an existential variable
hat :: Info -> Bool
hat (HatKappa _) = True
hat (HatEquals _) = True
hat _ = False

-- | True iff Info has an existential variable of matching symbol
hatOf :: Sym -> Info -> Bool
hatOf s = \case
    HatKappa (s' ::: _) -> s == s'
    HatEquals (s' ::: _ :=: _ ) -> s == s'
    _ -> False

-- | True iff Info has a sort annotation kappa
kappa :: Info -> Bool
kappa (Kappa _) = True
kappa (HatKappa _) = True
kappa (HatEquals _) = True
kappa _ = False

-- | True iff Info has a sort annotation of matching sort
kappaOf :: Kappa -> Info -> Bool
kappaOf k = \case
    Kappa (_ ::: k') -> k == k'
    HatKappa (_ ::: k') -> k == k'
    HatEquals (_ ::: k' :=: _) -> k == k'
    _ -> False

-- | True iff Info has a solved tau
tau :: Info -> Bool
tau (Equals _) = True
tau (HatEquals _) = True
tau _ = False

-- | True iff Info has a solved tau of matching term/monoterm
tauOf :: Tau -> Info -> Bool
tauOf t = \case
    HatEquals (_ ::: _ :=: t') -> t == t'
    Equals (_ :=: t') -> t == t'
    _ -> False


-- | Split a context based on predicate condition list, if possible.
-- Implements the Gamma [stuff] hole notation.
hole :: [Info -> Bool] -> Gamma -> Maybe (Gamma, Info, Gamma)
hole preds gamma = 
    -- Pipe the context info element into the list of predicates
    -- and ensure they are all True
    let satisfied k = foldl' (&&) True (map ($ k) preds)
    in case S.breakl satisfied gamma of
        (_, S.Empty) -> Nothing -- no matching info
        (gamL, theta S.:<| gamR) -> Just (gamL, theta, gamR)


-- | Implements Figure 12, applying a context to a Type
class Subst a where
    subst :: Gamma -> a -> a

-- | Substitution into terms/monoterms
instance Subst Tau where
    subst gamma alpha@(Alpha sym) = 
        -- use hole notation for the search for convenience
        case hole [noHatOf sym, tauOf alpha] gamma of 
            Just (_, Equals (_ :=: tau), _) -> subst gamma tau
            _ -> alpha

    subst gamma alphaHat@(AlphaHat sym) = 
        case hole [hatOf sym, kappa, tau] gamma of
            Just (l, HatEquals (_ ::: _ :=: tau), r) -> subst gamma tau
            _ -> alphaHat 
            -- ^ does this also cover the [alphaHat : kappa] case in the figure?

-- | Substitution into predicates
instance Subst P where
    subst gamma (t1 :=: t2) = subst gamma t1 :=: subst gamma t2

instance Subst A where
    subst gamma (p :>: a) = subst gamma p :>: subst gamma a
    subst gamma (a :/\: p) = subst gamma a :/\: subst gamma p
    subst gamma (a :->: b) = subst gamma a :->: subst gamma b
    subst gamma (a :+: b) = subst gamma a :+: subst gamma b
    subst gamma (a :*: b) = subst gamma a :*: subst gamma b
    subst gamma (Vec t a) = Vec (subst gamma t) (subst gamma a)
    subst gamma (V anno a) = V anno (subst gamma a)
    subst gamma (E anno a) = E anno (subst gamma a)

