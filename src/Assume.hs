-- | Implements assumption judgments in Figures 18, 21, and 22.
module Assume where

import Control.Monad

import Judgments
import Syntax
import Context
import Search
import Head


-- Assume proposition, Figure 18
instance Assume P DeltaBot where

  -- ElimpropEq
  gamma // t1 :=: t2 = gamma // t1 :=*=: t2 ::: N


-- Assume/eliminate equation, Figure 21
instance Assume (:=*=:) DeltaBot where

  -- ElimeqUvarRefl
  gamma // NoHat a :=*=: NoHat a' ::: k | a == a' = return gamma

  -- ElimeqZero
  gamma // Zero :=*=: Zero ::: N = return gamma

  -- ElimeqSucc 
  gamma // Succ sigma :=*=: Succ tau ::: N = gamma // sigma :=*=: tau ::: N

  -- ElimeqUvarLs
  gamma // NoHat a :=*=: tau ::: k 
    -- ElimeqUvarL
    | a `notElem` setFV tau && not (a `solved` gamma) = return $ gamma `Comma` (Equals $ a :=: tau)
    -- ElimeqUvarLBot
    | tau /= NoHat a && a `elem` setFV tau = bottom

  -- ElimeqUvarRs
  gamma // tau :=*=: NoHat a ::: k
    -- ElimeqUvarR
    | a `notElem` setFV tau && not (a `solved` gamma) = return $ gamma `Comma` (Equals $ a :=: tau)
    -- ElimeqUvarRBot
    | tau /= NoHat a && a `elem` setFV tau = bottom

  -- ElimeqUnit
  gamma // Unit :=*=: Unit ::: Star = return gamma

  -- ElimeqBin and ElimeqBinBot.  BinBot rule is to return Bottom (Nothing) if theta is Nothing
  gamma // Bin t1 t2 :=*=: Bin t1' t2' ::: Star = do
    theta <- gamma // t1 :=*=: t1' ::: Star
    theta // gamsub theta t2 :=*=: gamsub theta t2' ::: Star

  -- ElimeqClash
  gamma // sigma :=*=: tau ::: k = 
    if sigma # tau 
      then bottom 
      else error "ElimeqClash else case" -- what to do here?

