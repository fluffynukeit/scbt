module Judgments where

import Syntax

-- | A Turnstile is a type evaluating to a result, either bool
-- or updated context typicall.  It implements the |- turnstile
-- notation.
class Turnstile a b where
    (|-) :: Gamma -> a -> b
infix 6 |-

-- | Algorithmic judgments from Appendix 2
type TauKappa = Anno Tau Kappa
newtype Prop = Prop P  -- Proposition is well-formed
newtype Type = Type A -- Polytype is well-formed

-- Variants of Polytype is well-formed
data Ptype = Ptype A SmallP
newtype Types = Types [Type]
data Ptypes = Ptypes SmallP [Type]

