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

-- | Variable substitution. J / K means replace variable K with J.
(/) e nm = subst nm e

-- | Determine if name is used in a term or type.
setFV :: Alpha Syn => Syn -> S.Set (X.Alpha)
setFV = S.fromList . toListOf fv 

-- | Determine if name is used as an existential term or type.
setFEV :: Alpha Syn => Syn -> S.Set (X.Alpha)
setFEV = S.fromList . toListOf (filtered (not . isUniv) . fv) 
  where 
    isUniv = \case 
      NoHat _ -> True
      _ -> False
    

-- | Determine whether an Info is a solution fact.
solution :: X.Alpha -> Info -> Bool
solution a (Equals (a' :=: _)) = a == a'
solution a (HatEquals (a' ::: _ :=: _)) = a == a'
solution a _ = False

-- | Determine whether an Info is a solution fact with matching sort.
solutionHat :: X.Alpha -> Kappa -> Info -> Bool
solutionHat a k (HatEquals (a' ::: k' :=: _)) = a == a' && k == k'
solutionHat a k _ = False

-- | Determine whether a context contains a solution for the variable.
solved :: X.Alpha -> Gamma -> Bool
solved a = isJust . find (solution a)

-- | Determine whether an existential is solved in the context.
solvedHat a k = isJust . find (solutionHat a k)

-- | Determine whether an Info is an unsolved variable.
problem :: X.Alpha -> Info -> Bool
problem a (Kappa (a' ::: _)) = a == a'
problem a (HatKappa (a' ::: _)) = a == a'
problem a _ = False

-- | Determine whether a context contains the unsolved variable.
unsolved :: X.Alpha -> Gamma -> Bool
unsolved a = isJust . find (problem a)

-- | Predicate for finding an expression solution
solutionX :: X -> Info -> Bool
solutionX x (XAp (x' ::: _ ) _) = x == x'
solutionX _ _ = False

-- | Determine if info contains a matching variable entry.
var :: X.Alpha -> Info -> Bool
var a (Mark a') = a == a'
var a b = problem a b || solution a b

-- From Practical Foundations for Programming Languages SECOND EDITION:
-- "We write x notelem dom(Γ) to say that there is no assumption in Γ of the form x:τ for any type τ"
dom :: X.Alpha -> Gamma -> Bool
dom a = isJust . find (var a)

domX :: X -> Gamma -> Bool
domX x = isJust . find (solutionX x)

-- Not at all sure I did these instances correctly...
instance Alpha Syn
instance Alpha (X.Alpha ::: Kappa :.: A)
instance Alpha Kappa
instance Alpha P

instance Subst Syn Syn where
  isvar (NoHat a) = Just (SubstName a)
  isvar (Hat a) = Just (SubstName a)
  isvar _ = Nothing

instance Subst Syn (X.Alpha ::: Kappa :.: A)
instance Subst Syn Kappa
instance Subst Syn P

