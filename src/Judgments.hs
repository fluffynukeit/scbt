module Judgments where

import Syntax

-- | A Turnstile is a type evaluating to a result, either bool
-- or updated context typicall.  It implements the |- turnstile
-- notation.
class Turnstile a b where
    (|-) :: Gamma -> a -> b
infix 6 |-

-- | Algorithmic judgments from Appendix 2
-- Tau ::: Kappa -- Index term/monotype is well-formed (Fig 17), no additional type declaration needed
newtype Prop = Prop P  -- Proposition is well-formed (Fig 17)
newtype Type = Type A -- Polytype is well-formed (Fig 17)
-- Note: [Gamma]A applying a context, as substitution, to a type is implemented in Context.hs

-- Variants of Polytype is well-formed (Fig 17)
data Ptype = Ptype A SmallP
newtype Types = Types [Type]
data Ptypes = Ptypes SmallP [Type]


data AlgoChecking = E :<=: A
