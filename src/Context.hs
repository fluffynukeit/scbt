module Context 
    ( module Context
    , module Unbound.Generics.LocallyNameless.Fresh
    ) where

import Syntax
import Search
import qualified Data.Sequence as S
import Data.List.Split
import Unbound.Generics.LocallyNameless.Fresh


-- | Implementation of hole notation in section 5.2.
--
-- Hole notation splits a context into some number of segments at the hole boundary.

-- | Given a list of hole specifications, splits a context into segments between
-- each hole specification.
holes :: [[Info]] -> Gamma -> [Gamma]
holes [] gamma = [gamma] -- split on empty is just the remainder of the context
holes ([]:_) _gamma = error "Encountered empty hole specification."
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
(<@>) :: Gamma -> [[Info]] -> [Gamma]
(<@>) = flip holes
(>@<) :: [Gamma] -> [[Info]] -> Gamma
(>@<) = flip unholes

-- | Implements Figure 12, applying a context to a Type
class GamSub a where
    gamsub :: Gamma -> a -> a

-- | Substitution into propositions
instance GamSub P where
    gamsub gamma (t1 :=: t2) = gamsub gamma t1 :=: gamsub gamma t2

-- | Substituion into types, terms, monotypes (algorithmic syntax)
instance GamSub Syn where
    gamsub gamma (p :>: a) = gamsub gamma p :>: gamsub gamma a
    gamsub gamma (a :/\: p) = gamsub gamma a :/\: gamsub gamma p
    gamsub gamma (a :->: b) = gamsub gamma a :->: gamsub gamma b
    gamsub gamma (a :+: b) = gamsub gamma a :+: gamsub gamma b
    gamsub gamma (a :*: b) = gamsub gamma a :*: gamsub gamma b
    gamsub gamma (Vec t a) = Vec (gamsub gamma t) (gamsub gamma a)
    gamsub gamma (V (a ::: b :.: c)) = V $ a ::: b :.: (gamsub gamma c)
    gamsub gamma (E (a ::: b :.: c)) = E $ a ::: b :.: (gamsub gamma c)
    gamsub _gamma Unit = Unit

    gamsub gamma alpha@(NoHat sym) = 
        let result = find (solution sym) gamma
        in case result of
            Just (Equals (_sym :=: tau)) -> gamsub gamma tau
            _ -> alpha

    gamsub gamma alphaHat@(Hat sym) = 
        let result = find (solution sym) gamma
        in case result of
            Just (HatEquals (_sym ::: _kappa :=: tau)) -> gamsub gamma tau
            _ -> alphaHat

    gamsub _gamma Zero = error "Gamma substitution into Zero term not defined."
    gamsub _gamma (Succ _) = error "Gamma substitution into Succ term not defined."

