module Search 
  ( module Search
  , module Data.Foldable
  ) where

import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import Unbound.Generics.LocallyNameless
import qualified Data.Set as S
import Data.Maybe
import Data.Foldable
import qualified Data.Sequence ()

import Syntax hiding (Alpha, var)
import qualified Syntax as X (Alpha)

-- | Variable substitution. J / K means replace variable K with J.
(/) :: Subst b a => b -> Name b -> a -> a
(/) e nm = subst nm e

-- | Get set of names used in a term or type.
setFV :: Alpha Syn => Syn -> S.Set (X.Alpha)
setFV = S.fromList . toListOf fv 

-- | Get set of names used as an existential term or type. 
setFEV :: Alpha Syn => Syn -> S.Set (X.Alpha)
setFEV = setFV . killUnivs
  where 
    -- This is annoying transformation that I'm not sure how to get around cleanly.
    -- It removes all the universal variable Alphas from the syntax tree so that
    -- setFV only finds the existential ones.  The resulting tree could be invalid
    -- but it is only used for finding the names anyway.
    killUnivs (V (_al ::: _k :.: a)) = killUnivs a -- remove forall universal name
    killUnivs (E (_al ::: _k :.: a)) = killUnivs a -- remove exists universal name
    killUnivs (NoHat _) = Unit -- remove universal variable usages

    killUnivs bin@(Bin a b) = let (Op op) = bin in killUnivs a `op` killUnivs b
    killUnivs (p :>: a) = p :>: killUnivs a
    killUnivs (a :/\: p) = killUnivs a :/\: p
    killUnivs (Vec t a) = Vec (killUnivs t) (killUnivs a)
    killUnivs (Hat a) = Hat a
    killUnivs Unit = Unit 
    killUnivs Zero = Zero
    killUnivs (Succ t) = Succ (killUnivs t)

    

-- | Determine whether an Info is a solution fact.
solution :: X.Alpha -> Info -> Bool
solution a (Equals (a' :=: _)) = a == a'
solution a (HatEquals (a' ::: _ :=: _)) = a == a'
solution _ _ = False

-- | Determine whether an Info is a solution fact with matching sort.
solutionHat :: X.Alpha -> Kappa -> Info -> Bool
solutionHat a k (HatEquals (a' ::: k' :=: _)) = a == a' && k == k'
solutionHat _ _ _ = False

-- | Determine whether a context contains a solution for the variable.
solved :: X.Alpha -> Gamma -> Bool
solved a = isJust . find (solution a)

-- | Determine whether an existential is solved in the context.
solvedHat :: X.Alpha -> Kappa -> Gamma -> Bool
solvedHat a k = isJust . find (solutionHat a k)

-- | Determine whether an Info is an unsolved variable.
problem :: X.Alpha -> Info -> Bool
problem a (Kappa (a' ::: _)) = a == a'
problem a (HatKappa (a' ::: _)) = a == a'
problem _ _ = False

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

