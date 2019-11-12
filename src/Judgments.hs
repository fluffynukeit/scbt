module Judgments where

import Syntax

-- | A Turnstile is a type evaluating to a result, either bool
-- or updated context typically.  It implements the |- turnstile
-- notation.
class Turnstile a b where
    (|-) :: Gamma -> a -> b
infix 5 |-

-- | Algorithmic judgments from Appendix 2
-- Tau ::: Kappa -- Index term/monotype is well-formed (Fig 17), no additional type declaration needed
newtype Prop = Prop P  -- Proposition is well-formed (Fig 17)
newtype Type = Type A -- Polytype is well-formed (Fig 17)

-- Variants of Polytype is well-formed (Fig 17)
data Ptype = Ptype A SmallP
newtype Types = Types [Type]
data Ptypes = Ptypes SmallP [Type]

-- Note: [Gamma]A applying a context, as substitution, to a type is implemented in Context.hs.

newtype Ptrue = Ptrue P
data (:=*=:) = T :=*=: (T ::: Kappa)
infix 6 :=*=:

data (:=) = Sym := (T ::: Kappa) -- Instantiate, Figure 23
infix 6 :=

data (:<=:) = E :<=: (A, SmallP) -- Algorithmic checking, Figure 14
