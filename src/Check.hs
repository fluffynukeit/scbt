-- | This module implements Check proposition and Check equation judgements
-- in Figures 18 and 19.
-- Also checked introduction form for expressions in Figure 5
module Check where

import Judgments
import Syntax
import Context
import Search
import Instantiate

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
  gamma |- Bin tau1 tau2 :=*=: Bin tau1' tau2' ::: Star = do
    theta <- gamma |- tau1 :=*=: tau1' ::: Star
    theta |- gamsub theta tau2 :=*=: gamsub theta tau2' ::: Star

  -- CheckeqInstL
  gamma |- Hat a :=*=: t ::: k 
    | [_,_] <- gamma <@> [[HatKappa $ a ::: k]]
    , a `notElem` setFV t
    = gamma |- a := t ::: k

  -- CheckeqInstR
  gamma |- t :=*=: Hat a ::: k 
      | [_,_] <- gamma <@> [[HatKappa $ a ::: k]]
      , a `notElem` setFV t
      = gamma |- a := t ::: k

chkI :: DecSyn k -> Bool
chkI (Lam _) = True
chkI Un = True
chkI (Pair _ _) = True
chkI (Inj1 _) = True
chkI (Inj2 _) = True
chkI (_ :::: _) = True
chkI _ = error "chkI"
