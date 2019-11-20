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
class GamSub a where
    gamsub :: Gamma -> a -> a

-- | Substitution into terms/monoterms
instance GamSub Tau where

    gamsub gamma alpha@(NoHat sym) = 
        let result = find (solution sym) gamma
        in case result of
            Just (Equals (_ :=: tau)) -> gamsub gamma tau
            Nothing -> alpha

    gamsub gamma alphaHat@(Hat sym) = 
        let result = find (solution sym) gamma
        in case result of
            Just (HatEquals (sym ::: kappa :=: tau)) -> gamsub gamma tau
            Nothing -> alphaHat

    -- Are these terms necessary or covered by GamSub A?
    gamsub gamma (a :->: b) = gamsub gamma a :->: gamsub gamma b
    gamsub gamma (a :+: b) = gamsub gamma a :+: gamsub gamma b
    gamsub gamma (a :*: b) = gamsub gamma a :*: gamsub gamma b

-- | Substitution into predicates
instance GamSub P where
    gamsub gamma (t1 :=: t2) = gamsub gamma t1 :=: gamsub gamma t2

-- | Substituion into types
instance GamSub A where
    gamsub gamma (p :>: a) = gamsub gamma p :>: gamsub gamma a
    gamsub gamma (a :/\: p) = gamsub gamma a :/\: gamsub gamma p
    gamsub gamma (a :->: b) = gamsub gamma a :->: gamsub gamma b
    gamsub gamma (a :+: b) = gamsub gamma a :+: gamsub gamma b
    gamsub gamma (a :*: b) = gamsub gamma a :*: gamsub gamma b
    gamsub gamma (Vec t a) = Vec (gamsub gamma t) (gamsub gamma a)
    gamsub gamma (V (a ::: b :.: c)) = V $ a ::: b :.: (gamsub gamma c)
    gamsub gamma (E (a ::: b :.: c)) = E $ a ::: b :.: (gamsub gamma c)

