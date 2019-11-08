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

-- | Split a context based on a piece of context information.
-- Implements the Gamma [stuff] hole notation.
hole1 :: Info -> Gamma -> Maybe (Gamma, Gamma)
hole1 info gamma = case S.breakl ((==) info) gamma of
        (_, S.Empty) -> Nothing -- no matching info
        (gamL, match S.:<| gamR) -> Just (gamL, gamR)

-- | Like hole but with 2 holes
hole2 :: Info -> Info -> Gamma -> Maybe (Gamma, Gamma, Gamma)
hole2 p1 p2 gamma
    | Just (gamL, gamL') <- hole1 p1 gamma
    , Just (gamM, gamR) <- hole1 p2 gamL'
    = Just (gamL, gamM, gamR)
hole2 _ _ _ = Nothing

-- | Split a context into a list of gammas, returning a list length
-- 1 greater than the number of search items for a pattern match and
-- some different length for a match failure.
-- 
--  hole [A,B] Gamma yields (GamL, GamM, GamR) on success
--  where Gamma = (GamL, A, GamM, B, GamR) 
--
-- This is more convenient for pattern matching than hole1 and hole2
-- because we usually (always?) know how many segments are required
-- and can pattern match on the list elements themselves.
hole :: [Info] -> Gamma -> [Gamma]
hole [] gamma = [gamma] -- remaining context (possibly empty) becomes the final segment
hole _ Empty = [] -- can't split an empty context into any more segments.  Failure.
hole (i:is) gamma = case hole1 i gamma of
    Nothing -> [gamma] -- can't find this info item, so stop processing
    Just (gamL, gamR) -> gamL : hole is gamR

-- | Reassemble a gamma from hole representation
unhole1 gl t gr = gl `Comma` t S.>< gr

-- | Same as unhole but with 2 holes
unhole2 gl t1 gm t2 gr = gl `Comma` t1 S.>< gm `Comma` t2 S.>< gr

-- | Insert information elements into the holes made by hole function.
unhole :: [Gamma] -> [[Info]] -> Gamma
unhole [] _ = Empty
unhole g [] = mconcat g -- nothing to change, just concat everything remaining
unhole (g:gs) (is:iis) = g S.>< S.fromList is S.>< unhole gs iis


-- | Implements Figure 12, applying a context to a Type
class Subst a where
    subst :: Gamma -> a -> a

-- | Substitution into terms/monoterms
instance Subst Tau where
    subst gamma alpha@(Alpha sym) = 
        -- we can't use hole notation here because we don't yet know tau.
        -- Instead, we just have to search for a matching alpha
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

