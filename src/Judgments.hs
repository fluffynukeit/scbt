{-# LANGUAGE MultiParamTypeClasses #-}
module Judgments where

import Syntax

-- | A judgment is a type evaluating to a result, either bool
-- or updated context
class Judgment a b where
    (|-) :: BigGamma -> a -> b
infix 6 |-

-- | Algorithmic judgments from Appendix 2
data TauKappa = Tau ::: Kappa
infix 7 :::
newtype Prop = Prop P
newtype Type = Type A
data Ptype = Ptype A SmallP
newtype Types = Types [Type]
data Ptypes = Ptypes SmallP [Type]

