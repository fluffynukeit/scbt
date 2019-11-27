-- | Implements assumption judgments in Figures 18, 21, and 22.
module Assume where

import Judgments
import Syntax
import Context
import Search
import Head


-- Assume proposition, Figure 18
instance Assume P (Judgment DeltaBot) where

  -- ElimpropEq
  gamma // t1 :=: t2 = gamma // t1 :=*=: t2 ::: N


-- Assume/eliminate equation, Figure 21
instance Assume (:=*=:) (Judgment DeltaBot) where

  -- ElimeqUvarRefl
  gamma // NoHat a :=*=: NoHat a' ::: _k | a == a' = return $ Delta gamma

  -- ElimeqZero
  gamma // Zero :=*=: Zero ::: N = return $ Delta gamma

  -- ElimeqSucc 
  gamma // Succ sigma :=*=: Succ tau ::: N = gamma // sigma :=*=: tau ::: N

  -- ElimeqUvarLs
  gamma // NoHat a :=*=: tau ::: _k 
    -- ElimeqUvarL
    | a `notElem` setFV tau && not (a `solved` gamma) = return . Delta $ gamma `Comma` (Equals $ a :=: tau)
    -- ElimeqUvarLBot
    | tau /= NoHat a && a `elem` setFV tau = return Bottom

  -- ElimeqUvarRs
  gamma // tau :=*=: NoHat a ::: _k
    -- ElimeqUvarR
    | a `notElem` setFV tau && not (a `solved` gamma) = return . Delta $ gamma `Comma` (Equals $ a :=: tau)
    -- ElimeqUvarRBot
    | tau /= NoHat a && a `elem` setFV tau = return Bottom

  -- ElimeqUnit
  gamma // Unit :=*=: Unit ::: Star = return $ Delta gamma

  -- ElimeqBin and ElimeqBinBot.
  gamma // Bin t1 t2 :=*=: Bin t1' t2' ::: Star = do
    result <- gamma // t1 :=*=: t1' ::: Star
    case result of
      Delta theta -> theta // gamsub theta t2 :=*=: gamsub theta t2' ::: Star -- ElimeqBin
      Bottom -> return Bottom -- ElimeqBinBot

  -- ElimeqClash
  _gamma // sigma :=*=: tau ::: _k | sigma # tau = return Bottom

