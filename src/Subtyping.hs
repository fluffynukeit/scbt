-- | Implements rules in Figure 22, Algo subtyping and equivalence
module Subtyping where

import Syntax
import Judgments
import Context
import Search
import Check ()
import Instantiate ()

import Prelude hiding ((/))

-- | Return the appropriate subtyping constructor based on input polarities.
-- See Figure 4.
join :: Pol -> Pol -> A -> B -> (:<:?:)
join Pos _ = (:<:+:)
join Neg _ = (:<:-:)
join None Pos = (:<:+:)
join None Neg = (:<:-:)
join None None = (:<:-:)

instance Turnstile (:<:?:) (Judgment Delta) where

  -- <:VL
  gamma |- V (al ::: k :.: a) :<:-: b | not (headV b) = do
    alHat <- fresh al
    new <- gamma `Comma` Mark alHat `Comma` Kappa (alHat ::: k) |- (Hat alHat / al) a :<:-: b
    let [delta, _theta] = new <@> [[Mark alHat]]
    return delta

  -- <:VR
  gamma |- a :<:-: V (be ::: k :.: b) = do
    new <- gamma `Comma` Kappa (be ::: k) |- a :<:-: b
    let [delta, _theta] = new <@> [[Kappa (be ::: k)]]
    return delta

  -- <:EL
  gamma |- E (al ::: k :.: a) :<:+: b = do
    new <- gamma `Comma` Kappa (al ::: k) |- a :<:+: b
    let [delta, _theta] = new <@> [[Kappa (al ::: k)]]
    return delta

  -- <:ER
  gamma |- a :<:+: E (be ::: k :.: b) | not (headE a) = do
    beHat <- fresh be
    new <- gamma `Comma` Mark beHat `Comma` Kappa (beHat ::: k) |- a :<:+: (Hat beHat / be) b
    let [delta, _theta] = new <@> [[Mark beHat]]
    return delta

  gamma |- a :<:+: b 
    | neg a && nonpos b = gamma |- a :<:-: b -- <:-+L
    | nonpos a && neg b = gamma |- a :<:-: b -- <:-+R

  gamma |- a :<:-: b
    | pos a && nonneg b = gamma |- a :<:+: b -- <:+-L
    | nonneg a && pos b = gamma |- a :<:+: b -- <:+-R

  -- <:Equiv, positive and negative cases
  gamma |- a :<:+: b | not (headV a || headE a || headV b || headE b) = gamma |- a :===: b
  gamma |- a :<:-: b | not (headV a || headE a || headV b || headE b) = gamma |- a :===: b

instance Turnstile (P :===: Q) (Judgment Delta) where

  -- PropEq
  gamma |- (t1 :=: t1') :===: (t2 :=: t2') = do
    theta <- gamma |- t1 :=*=: t2 ::: N
    theta |- gamsub theta t1' :=*=: gamsub theta t2' ::: N


instance Turnstile (A :===: B) (Judgment Delta) where
  
  -- =Var
  gamma |- NoHat a :===: NoHat a' | a == a' = return gamma

  -- =Exvar
  gamma |- Hat a :===: Hat a' | a == a' = return gamma

  -- =Unit
  gamma |- Unit :===: Unit = return gamma

  -- =Bin
  gamma |- Bin a1 a2 :===: Bin b1 b2 = do
    theta <- gamma |- a1 :===: b1
    theta |- gamsub theta a2 :===: gamsub theta b2

  -- =Vec
  gamma |- Vec t1 a1 :===: Vec t2 a2 = do
    theta <- gamma |- t1 :===: t2
    theta |- gamsub theta a1 :===: gamsub theta a2

  -- =V
  gamma |- V (al ::: k :.: a) :===: V (al' ::: k' :.: b) | al == al' && k == k' = do
    new <- gamma `Comma` Kappa (al ::: k) |- a :===: b
    let [delta, _delta'] = new <@> [[Kappa (al ::: k)]]
    return delta

  -- =E
  gamma |- E (al ::: k :.: a) :===: E (al' ::: k' :.: b) | al == al' && k == k' = do
    new <- gamma `Comma` Kappa (al ::: k) |- a :===: b
    let [delta, _delta'] = new <@> [[Kappa (al ::: k)]]
    return delta

  -- =Implies
  gamma |- p :>: a :===: q :>: b = do
    theta <- gamma |- p :===: q
    theta |- gamsub theta a :===: gamsub theta b

  -- =With
  gamma |- a :/\: p :===: b :/\: q = do
    theta <- gamma |- p :===: q
    theta |- gamsub theta a :===: gamsub theta b

-- NOTE: gamma[alphaHat] is not a well-formed expression because there is no
-- possible context element that is just a variable without an accompanying
-- sort, kappa.  Is there an implied sort then?  Or just ignore sort?  I proceed
-- assuming the sort is ignored, which is the same as an "unsolved" query.
--
  -- =InstantiateL
  gamma |- Hat a :===: tau | unsolved a gamma && a `notElem` setFV tau =
    gamma |- a := tau ::: Star

  -- =InstantiateR
  gamma |- tau :===: Hat a | unsolved a gamma && a `notElem` setFV tau =
    gamma |- a := tau ::: Star
  

