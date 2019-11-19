module Judgments where

import Syntax

-- | A Turnstile is a type evaluating to a result, either bool
-- or updated context typically.  It implements the |- turnstile
-- notation.
class Turnstile a b where
    (|-) :: Gamma -> a -> b
infix 4 |-

-- | An Assumption implements the / notation.
class Assume a b where
    (/) :: Gamma -> a -> b
infix 5 /


-- | Algorithmic judgments from Appendix 2
-- Tau ::: Kappa -- Index term/monotype is well-formed (Fig 17), no additional type declaration needed
newtype Prop = Prop P  -- Proposition is well-formed (Fig 17)
newtype Type = Type A -- Polytype is well-formed (Fig 17)

-- Variants of Polytype is well-formed (Fig 17)
data Ptype = Ptype A SmallP
newtype Types = Types [Type]
data Ptypes = Ptypes SmallP [Type]

-- Note: [Gamma]A applying a context, as substitution, to a type is implemented in Context.hs.

newtype Ptrue = Ptrue P -- Check proposition, (Fig 18)

data (:=*=:) = T :=*=: (T ::: Kappa) -- Check equation, (Fig 19). Also assume/eliminate equation (Fig 21)
infix 6 :=*=:

data (:<:?:) = A :<:+: B | A :<:-: B -- Algorithmic subtyping, Figure 22
data (:===:) a b = a :===: b -- Propositional and Type equivalance, Figure 22
infix 6 :===:

data (:=) = Alpha Tm := (T ::: Kappa) -- Instantiate, Figure 23
infix 6 :=

data (:<=:) k = k :<=: (A, SmallP) -- Algorithmic checking, Figure 14a. Also pattern branch checking, Figure 24.
infix 6 :<=:
data (:=>:) k = (:=>:) (DecSyn k) -- Algorithmic synthesis, Figure 14a
data (:>>:) k = (:>>:) (S k ::: A, SmallP) -- Algorithmic spine typing, Figure 14a
data (:>>?:) k = (:>>?:) (S k ::: A, SmallP) -- Algorithmic spine typing with principality recovery, Figure 14a



