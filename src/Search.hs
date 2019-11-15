module Search 
  ( module Search
  , module Data.Foldable
  ) where

import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf, filtered)
import Unbound.Generics.LocallyNameless
import qualified Data.Set as S
import Data.Typeable
import Data.Maybe
import Data.Foldable
import GHC.Generics hiding ((:+:), (:*:), (:.:), S)
import qualified GHC.Generics as G ((:+:)(..), (:*:)(..), (:.:)(..))
import qualified Data.Sequence ()

import Syntax hiding (Alpha)
import qualified Syntax as X (Alpha)

-- | Determine if name is used in a term or type.
elemFV :: Alpha (Syn a) => X.Alpha Tm -> (Syn a) -> Bool
elemFV a tree = a `elem` (S.fromList . toListOf fv $ tree)

-- | Determine if name is used as an existential term or type.
elemFEV :: Alpha (Syn a) => X.Alpha Tm -> (Syn a) -> Bool
elemFEV a tree = a `elem` (S.fromList . toListOf (filtered isHat . fv) $ tree)
  where 
    isHat = \case
      Hat _ -> True
      _ -> False
    

-- | Determine whether an Info is a solution fact.
-- Works for Univ and Exis variables.
solution :: X.Alpha Tm -> Info -> Bool
solution a (Equals (a' :=: _)) = a == a'
solution a (HatEquals (a' ::: _ :=: _)) = a == a'
solution a _ = False

-- | Determine whether a context contains a solution for the variable.
solved :: X.Alpha Tm -> Gamma -> Bool
solved a = isJust . find (solution a)

-- | Determine whether an Info is an unsolved variable.
problem :: X.Alpha Tm -> Info -> Bool
problem a (Kappa (a' ::: _)) = AnyName a == AnyName a'
problem a (HatKappa (a' ::: _)) = AnyName a == AnyName a'
problem a _ = False

-- | Determine whether a context contains the unsolved variable.
unsolved :: X.Alpha Tm -> Gamma -> Bool
unsolved a = isJust . find (problem a)

-- A GADT cannot derive Generic, and we need a Generic instance
-- for unbounded-generic to work. Note that I tried just unbounded,
-- which uses template Haskell instead, but it gave kind errors on 
-- Syn (Kind is not star).
-- 
-- Given the needs, we'll do it manually. (ugh)
instance Generic T where
    type Rep T =
        U1 -- Unit
        G.:+:
        (Rec0 T G.:*: Rec0 T) -- :->:
        G.:+:
        (Rec0 T G.:*: Rec0 T) -- :+:
        G.:+:
        (Rec0 T G.:*: Rec0 T) -- :*:
        G.:+:
        (Rec0 (X.Alpha Tm)) -- NoHat
        G.:+:
        (Rec0 (X.Alpha Tm)) -- Hat
        G.:+:
        U1 -- Zero
        G.:+:
        (Rec0 T) -- Succ

    from Unit       = L1 U1
    from (a :->: b) = R1 (L1 (K1 a G.:*: K1 b))
    from (a :+: b)  = R1 (R1 (L1 (K1 a G.:*: K1 b)))
    from (a :*: b)  = R1 (R1 (R1 (L1 (K1 a G.:*: K1 b))))
    from (NoHat a)  = R1 (R1 (R1 (R1 (L1 (K1 a)))))
    from (Hat a)    = R1 (R1 (R1 (R1 (R1 (L1 (K1 a))))))
    from Zero       = R1 (R1 (R1 (R1 (R1 (R1 (L1 U1))))))
    from (Succ a)   = R1 (R1 (R1 (R1 (R1 (R1 (R1 (K1 a)))))))

    to (L1 U1) = Unit
    to (R1 (L1 (K1 a G.:*: K1 b))) = a :->: b
    to (R1 (R1 (L1 (K1 a G.:*: K1 b)))) = a :+: b
    to (R1 (R1 (R1 (L1 (K1 a G.:*: K1 b))))) = a :*: b
    to (R1 (R1 (R1 (R1 (L1 (K1 a)))))) = NoHat a
    to (R1 (R1 (R1 (R1 (R1 (L1 (K1 a))))))) = Hat a
    to (R1 (R1 (R1 (R1 (R1 (R1 (L1 U1))))))) = Zero
    to (R1 (R1 (R1 (R1 (R1 (R1 (R1 (K1 a)))))))) = Succ a

instance Generic A where
    type Rep A =
        U1 -- Unit
        G.:+:
        (Rec0 A G.:*: Rec0 A) -- :->:
        G.:+:
        (Rec0 A G.:*: Rec0 A) -- :+:
        G.:+:
        (Rec0 A G.:*: Rec0 A) -- :*:
        G.:+:
        (Rec0 (X.Alpha Ty)) -- NoHat
        G.:+:
        (Rec0 (X.Alpha Ty)) -- Hat
        G.:+:
        (Rec0 (X.Alpha Tm ::: Kappa) G.:*: Rec0 A) -- V
        G.:+:
        (Rec0 (X.Alpha Tm ::: Kappa) G.:*: Rec0 A) -- E
        G.:+:
        (Rec0 P G.:*: Rec0 A) -- :>:
        G.:+:
        (Rec0 A G.:*: Rec0 P) -- :/\:
        G.:+:
        (Rec0 T G.:*: Rec0 A) -- Vec


    from Unit       = L1 U1
    from (a :->: b) = R1 (L1 (K1 a G.:*: K1 b))
    from (a :+: b)  = R1 (R1 (L1 (K1 a G.:*: K1 b)))
    from (a :*: b)  = R1 (R1 (R1 (L1 (K1 a G.:*: K1 b))))
    from (NoHat a)  = R1 (R1 (R1 (R1 (L1 (K1 a)))))
    from (Hat a)    = R1 (R1 (R1 (R1 (R1 (L1 (K1 a))))))
    from (V a b)    = R1 (R1 (R1 (R1 (R1 (R1 (L1 (K1 a G.:*: K1 b)))))))
    from (E a b)    = R1 (R1 (R1 (R1 (R1 (R1 (R1 (L1 (K1 a G.:*: K1 b))))))))
    from (a :>: b)  = R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (L1 (K1 a G.:*: K1 b)))))))))
    from (a :/\: b) = R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (L1 (K1 a G.:*: K1 b))))))))))
    from (Vec a b)  = R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (K1 a G.:*: K1 b))))))))))

    to (L1 U1) = Unit
    to (R1 (L1 (K1 a G.:*: K1 b))) = a :->: b
    to (R1 (R1 (L1 (K1 a G.:*: K1 b)))) = a :+: b
    to (R1 (R1 (R1 (L1 (K1 a G.:*: K1 b))))) = a :*: b
    to (R1 (R1 (R1 (R1 (L1 (K1 a)))))) = NoHat a
    to (R1 (R1 (R1 (R1 (R1 (L1 (K1 a))))))) = Hat a
    to (R1 (R1 (R1 (R1 (R1 (R1 (L1 (K1 a G.:*: K1 b)))))))) = V a b
    to (R1 (R1 (R1 (R1 (R1 (R1 (R1 (L1 (K1 a G.:*: K1 b))))))))) = E a b
    to (R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (L1 (K1 a G.:*: K1 b)))))))))) = a :>: b
    to (R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (L1 (K1 a G.:*: K1 b))))))))))) = a :/\: b
    to (R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (K1 a G.:*: K1 b))))))))))) = Vec a b

instance Alpha T

instance Subst A A where
  isvar (Hat a) = Just (SubstName a)
  isvar (NoHat a) = Just (SubstName a)
  isvar _ = Nothing

instance Subst A (X.Alpha Tm ::: Kappa)
instance Subst A Kappa
instance Subst A P
instance Subst A T
instance Subst T (X.Alpha Tm ::: Kappa)
instance Subst T Kappa
instance Subst T A
instance Subst T P

instance Subst T T where
  isvar (Hat a) = Just (SubstName a)
  isvar (NoHat a) = Just (SubstName a)
  isvar _ = Nothing

-- | Variable substitution. J // K means replace variable K with J.
(//) e nm = subst nm e
