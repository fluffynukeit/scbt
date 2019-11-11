-- | Implements judgments in Figure 23: Instantiation
module Instantiate where

import Syntax
import Context
import Judgments
import WellFormed

import Data.Text

instance Turnstile Instantiate Delta where 

  -- In some of these definitions, a pattern guard is needed instead of a view
  -- pattern so that bound variables can be in scope for the hole function call.

  -- InstZero
  gamma |- a := Zero ::: N | h@[_,_] <- gamma <@> [[HatKappa $ a ::: N]] = 
    h >@< [[HatEquals $ a ::: N :=: Zero]]

  -- InstSucc
  gamma |- a := Succ t1 ::: N | h@[_,_] <- gamma <@> [[HatKappa $ a ::: N]] =
    h >@< [[HatKappa $ a1 ::: N, HatEquals $ a ::: N :=: Succ (Hat a1)]] |- a1 := t1 ::: N 
      where a1 = Data.Text.pack "blah"

  -- InstBin
  gamma |- a := b@(Conn t1 t2) ::: Star | h@[_,_] <- gamma <@> [[HatKappa $ a ::: Star]]= 
    let Op op = b
        a1 = Data.Text.pack "blah"
        a2 = Data.Text.pack "blah"

        theta = h >@< 
          [
            [ HatKappa $ a2 ::: Star
            , HatKappa $ a1 ::: Star
            , HatEquals $ a ::: Star :=: (Hat a1 `op` Hat a2)
            ]
          ] |- a1 := t1 ::: Star
    in theta |- a2 := (subst theta t2) ::: Star

  -- TODO: InstReach (what is "unsolved"?)
  {-gamma |- a := b ::: k | h@[_,_,gamR] <- gamma <@> [[HatKappa $ a ::: k], [HatKappa $ b ::: k]] =
    let unsolved = filter gamR 
    if b `elem` unsolved gamma
      then h >@< [[HatKappa $ a ::: k], [HatEquals $ b ::: k :=: a]]
      else gamma
        where unsolved gamma = 
        -}

  -- InstSolve
  gamma |- a := t ::: k | h@[gam0, gam1] <- gamma <@> [[HatKappa $ a ::: k]] =
    if gam0 |- t ::: k
      then h >@< [[HatEquals $ a ::: k :=: t]]
      else gamma

