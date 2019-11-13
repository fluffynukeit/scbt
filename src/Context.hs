module Context 
    ( module Context
    , module Unbound.Generics.LocallyNameless.Fresh
    ) where

import Syntax
import Search
import qualified Data.Sequence as S
import Data.List.Split
import Unbound.Generics.LocallyNameless.Fresh
import Control.Monad

-- | Patterns for Gamma,Info commonly used in paper
pattern Comma a b = (S.:|>) a b
pattern Empty = S.Empty

-- | Implementation of hole notation in section 5.2.
--
-- Hole notation splits a context into some number of segments at the hole boundary.

-- | Given a list of hole specifications, splits a context into segments between
-- each hole specification.
holes :: [[Info]] -> Gamma -> [Gamma]
holes [] gamma = [gamma] -- split on empty is just the remainder of the context
holes ([]:_) gamma = error "Encountered empty hole specification."
holes (is:iss) gamma = 
    let (seg:segs) = splitOn is (toList gamma) -- segs is list of list of infos
    in (S.fromList seg) : holes iss (mconcat $ map S.fromList segs)

-- | Insert information elements into the holes made by hole function.
-- Inverse of holes.
unholes :: [[Info]] -> [Gamma] -> Gamma
unholes _ [] = Empty
unholes [] g = mconcat g -- nothing to change, just concat everything remaining
unholes (is:iss) (g:gs) = g S.>< S.fromList is S.>< unholes iss gs

-- | Infix forms of holes and unholes, respectively, but with arguments flipped.
(<@>) = flip holes
(>@<) = flip unholes

-- | Result for inconsistent context
bottom :: DeltaBot
bottom = mzero 

-- | Implements Figure 12, applying a context to a Type
class Subst a where
    subst :: Gamma -> a -> a

-- | Substitution into terms/monoterms
instance Subst Tau where

    subst gamma alpha@(NoHat sym) = 
        let result = find (solution sym) gamma
        in case result of
            Just (Equals (_ :=: tau)) -> subst gamma tau
            Nothing -> alpha

    subst gamma alphaHat@(Hat sym) = 
        let result = find (solution sym) gamma
        in case result of
            Just (HatEquals (sym ::: kappa :=: tau)) -> subst gamma tau
            Nothing -> alphaHat

    -- Are these terms necessary or covered by Subst A?
    subst gamma (a :->: b) = subst gamma a :->: subst gamma b
    subst gamma (a :+: b) = subst gamma a :+: subst gamma b
    subst gamma (a :*: b) = subst gamma a :*: subst gamma b

-- | Substitution into predicates
instance Subst P where
    subst gamma (t1 :=: t2) = subst gamma t1 :=: subst gamma t2

-- | Substituion into types
instance Subst A where
    subst gamma (p :>: a) = subst gamma p :>: subst gamma a
    subst gamma (a :/\: p) = subst gamma a :/\: subst gamma p
    subst gamma (a :->: b) = subst gamma a :->: subst gamma b
    subst gamma (a :+: b) = subst gamma a :+: subst gamma b
    subst gamma (a :*: b) = subst gamma a :*: subst gamma b
    subst gamma (Vec t a) = Vec (subst gamma t) (subst gamma a)
    subst gamma (V anno a) = V anno (subst gamma a)
    subst gamma (E anno a) = E anno (subst gamma a)

