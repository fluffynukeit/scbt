{-# LANGUAGE MultiParamTypeClasses #-}
module Judgments where

import Syntax

-- | A Turnstile is a type evaluating to a result, either bool
-- or updated context typicall.  It implements the |- turnstile
-- notation.
class Turnstile a b where
    (|-) :: BigGamma -> a -> b
infix 6 |-

-- | Algorithmic judgments from Appendix 2
data TauKappa = Tau ::: Kappa -- Index term/monotype is well-formed
infix 7 :::
newtype Prop = Prop P -- Proposition is well-formed
newtype Type = Type A -- Polytype is well-formed

-- Variants of Polytype is well-formed
data Ptype = Ptype A SmallP
newtype Types = Types [Type]
data Ptypes = Ptypes SmallP [Type]

data AlgoCheck = E :<=: Ptype
infix 7 :<=:
data AlgoSynth = E :=>: Ptype
infix 7 :=>:
