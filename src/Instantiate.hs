-- | Implements judgments in Figure 23: Instantiation
module Instantiate where

import Syntax
import Context
import Judgments

import Data.Text

instance Turnstile Instantiate Delta where 

  -- In some of these definitions, a pattern guard is needed instead of a view
  -- pattern so that bound variables can be in scope for the hole function call.

  -- InstZero
  gamma |- a := Zero ::: N | h@[_,_] <- hole [HatKappa (a ::: N)] gamma = 
    unhole h [[HatEquals $ a ::: N :=: Zero]]

  -- InstSucc
  gamma |- a := Succ t1 ::: N | h@[_,_] <- hole [HatKappa (a ::: N)] gamma =
    unhole h [[HatKappa (a1 ::: N), HatEquals (a ::: N :=: Succ (AlphaHat a1))]] |- a1 := t1 ::: N 
      where a1 = Data.Text.pack "blah"
