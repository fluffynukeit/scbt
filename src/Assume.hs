-- | Implements assumption judgments in Figures 18, 21, and 22.
module Assume where

import Control.Monad

import Judgments
import Syntax
import Context
import Search
import Head

import Prelude hiding ((/))

-- Assume proposition, Figure 18
instance Assume P DeltaBot where

  -- ElimpropEq
  gamma / t1 :=: t2 = gamma / t1 :=*=: t2 ::: N


-- Assume/eliminate equation, Figure 21
instance Assume (:=*=:) DeltaBot where

  -- ElimeqUvarRefl
  gamma / NoHat a :=*=: NoHat a' ::: k | a == a' = return gamma

  -- ElimeqZero
  gamma / Zero :=*=: Zero ::: N = return gamma

  -- ElimeqSucc 
  gamma / Succ sigma :=*=: Succ tau ::: N = gamma / sigma :=*=: tau ::: N

  -- UvarLs
  gamma / NoHat a :=*=: tau ::: k 
    -- ElimeqUvarL
    | not (a `elemFV` tau) && not (a `solved` gamma) = return $ gamma `Comma` (Equals $ a :=: tau)
    -- ElimeqUvarLBot
    | tau /= NoHat a && a `elemFV` tau = bottom

  -- UvarRs
  gamma / tau :=*=: NoHat a ::: k
    -- ElimeqUvarR
    | not (a `elemFV` tau) && not (a `solved` gamma) = return $ gamma `Comma` (Equals $ a :=: tau)
    -- ElimeqUvarRBot
    | tau /= NoHat a && a `elemFV` tau = bottom

  -- ElimeqUnit
  gamma / Unit :=*=: Unit ::: Star = return gamma

  -- ElimeqBin and ElimeqBinBot.  BinBot rule is to return Bottom (Nothing) if theta is Nothing
  gamma / Bin t1 t2 :=*=: Bin t1' t2' ::: Star = do
    theta <- gamma / t1 :=*=: t1' ::: Star
    theta / subst theta t2 :=*=: subst theta t2' ::: Star

  -- ElimeqClash
  gamma / sigma :=*=: tau ::: k = 
    if sigma # tau 
      then bottom 
      else error "ElimeqClash else case" -- what to do here?

