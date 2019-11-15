-- | Implements judgments in Figure 23: Instantiation
module Instantiate where

import Syntax
import Context
import Judgments
import WellFormed
import Search

import Data.Text

instance Turnstile (:=) Delta where 

  -- InstZero
  gamma |- a := Zero ::: N | h@[_,_] <- gamma <@> [[HatKappa $ a ::: N]] = 
    return $ h >@< [[HatEquals $ a ::: N :=: Zero]]

  -- InstSucc
  gamma |- a := Succ t1 ::: N | h@[_,_] <- gamma <@> [[HatKappa $ a ::: N]] = do
    a1 <- fresh a
    delta <- h >@< [[HatKappa $ a1 ::: N, HatEquals $ a ::: N :=: Succ (Hat a1)]] |- a1 := t1 ::: N 
    return delta

  -- InstBin
  gamma |- a := b@(Bin tau1 tau2) ::: Star | h@[_,_] <- gamma <@> [[HatKappa $ a ::: Star]]= do
    let Op op = b
    a1 <- fresh a
    a2 <- fresh a
    theta <- h >@< 
      [
        [ HatKappa $ a2 ::: Star
        , HatKappa $ a1 ::: Star
        , HatEquals $ a ::: Star :=: (Hat a1 `op` Hat a2)
        ]
      ] |- a1 := tau1 ::: Star
    delta <- theta |- a2 := (gamsub theta tau2) ::: Star
    return delta

  -- InstReach
  gamma |- a := (Hat b) ::: k 
    | h@[_,_,_] <- gamma <@> [[HatKappa $ a ::: k], [HatKappa $ b ::: k]] 
    , unsolved b gamma 
    = return $ h >@< [[HatKappa $ a ::: k], [HatEquals $ b ::: k :=: (Hat a)]]

  -- InstSolve
  gamma |- a := tau ::: k 
    | h@[gam0, gam1] <- gamma <@> [[HatKappa $ a ::: k]] 
    , gam0 |- tau ::: k 
    = return $ h >@< [[HatEquals $ a ::: k :=: tau]]

