-- | Implements assumption judgments in Figures 18, 21, and 22.
module Assume where

import Judgments
import Syntax
import Context

import Prelude hiding ((/))

-- Check proposition, Figure 18
instance Assume P DeltaBot where

  -- ElimpropEq
  gamma / t1 :=: t2 = gamma / t1 :=*=: t2 ::: N


-- Assume/eliminate equation, Figure 21
instance Assume (:=*=:) DeltaBot where

  -- ElimeqUvarRefl
  gamma / NoHat a :=*=: NoHat a' ::: k = pure gamma

  -- ElimeqZero
  gamma / Zero :=*=: Zero ::: N = pure gamma

  -- ElimeqSucc 
  gamma / Succ sigma :=*=: Succ tau ::: N = gamma / sigma :=*=: tau ::: N

  -- TODO: UvarL, UvarR, UvarLBottom

  -- ElimeqUnit
  gamma / Unit :=*=: Unit ::: Star = pure gamma

  -- ElimeqBin and ElimeqBinBot.  BinBot rule is to return Bottom (Nothing) if theta is Nothing
  gamma / Bin t1 t2 :=*=: Bin t1' t2' ::: Star = do
    theta <- gamma / t1 :=*=: t1' ::: Star
    theta / subst theta t2 :=*=: subst theta t2' ::: Star

