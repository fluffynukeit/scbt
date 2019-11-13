-- | This module implements Check proposition and CHeck equation judgements
-- in Figures 18 and 19
module Check where

import Judgments
import Syntax
import Context

instance Turnstile Ptrue Delta where

  -- CheckpropEq
  gamma |- Ptrue (t1 :=: t2) = gamma |- t1 :=*=: t2 ::: N

instance Turnstile (:=*=:) Delta where

  -- CheckeqVar
  gamma |- U u :=*=: U u' ::: k | u == u' = return gamma

  -- CheckeqUnit
  gamma |- Unit :=*=: Unit ::: Star = return gamma

  -- CheckeqZero
  gamma |- Zero :=*=: Zero ::: N = return gamma

  -- CheckeqSucc
  gamma |- Succ t1 :=*=: Succ t2 ::: N = gamma |- t1 :=*=: t1 ::: N

  -- CheckeqBin
  gamma |- Bin t1 t2 :=*=: Bin t1' t2' ::: Star = do
    theta <- gamma |- t1 :=*=: t1' ::: Star
    theta |- subst theta t2 :=*=: subst theta t2' ::: Star

  -- TODO: CheckeqInstL, CheckeqInstR
