module Search 
  ( module Search
  , module Data.Foldable
  ) where

import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import Unbound.Generics.LocallyNameless
import Data.Set as S
import Data.Typeable
import Data.Maybe
import Data.Foldable

import Syntax hiding (Alpha)
import qualified Syntax as X (Alpha)
import GHC.Generics hiding ((:+:), (:*:), (:.:), S)
import qualified GHC.Generics as G ((:+:)(..), (:*:)(..), (:.:)(..))

-- | Get the set of all free universals and existentials.
elemFV :: (Alpha a, Typeable b) => Name b -> a -> Bool
elemFV n t = AnyName n `elem` (S.fromList . toListOf fvAny $ t)

-- | Get the set of only existentials
elemFEV :: Alpha a => Name Exis -> a -> Bool
elemFEV a t = a `elem` (S.fromList . toListOf fv $ t)

-- | Determine whether an Info is a solution fact.
-- Works for Univ and Exis variables.
solution :: Typeable a => Name a -> Info -> Bool
solution a (Equals (a' :=: _)) = AnyName a == AnyName a'
solution a (HatEquals (a' ::: _ :=: _)) = AnyName a == AnyName a'
solution a _ = False

-- | Determine whether a context contains a solution for the variable.
solved :: Typeable a => Name a -> Gamma -> Bool
solved a = isJust . find (solution a)

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
        (Rec0 X.Alpha) -- NoHat
        G.:+:
        (Rec0 AlphaHat) -- Hat
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
        (Rec0 X.Alpha) -- NoHat
        G.:+:
        (Rec0 AlphaHat) -- Hat
        G.:+:
        (Rec0 (X.Alpha ::: Kappa) G.:*: Rec0 A) -- V
        G.:+:
        (Rec0 (X.Alpha ::: Kappa) G.:*: Rec0 A) -- E
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
instance Alpha A
instance Alpha Kappa
instance Alpha (X.Alpha ::: Kappa)
instance Alpha (T :=: T)



