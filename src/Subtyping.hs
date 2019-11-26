-- | Implements rules in Figure 22, Algo subtyping and equivalence
module Subtyping where

import Syntax
import Judgments
import Context
import Check
import Search
import Instantiate
import Unbound.Generics.LocallyNameless hiding (Alpha)

import Prelude hiding ((/))

-- | Return the appropriate subtyping constructor based on input polarities.
-- See Figure 4.
join Pos _ = (:<:+:)
join Neg _ = (:<:-:)
join None Pos = (:<:+:)
join None Neg = (:<:-:)
join None None = (:<:-:)

instance Turnstile (:<:?:) Delta where

  -- <:VL
  gamma |- V (al ::: k :.: a) :<:-: b | not (headV b) = do
    alHat <- fresh al
    new <- gamma `Comma` Mark alHat `Comma` Kappa (alHat ::: k) |- (Hat alHat / al) a :<:-: b
    let [delta, theta] = new <@> [[Mark alHat]]
    return delta

  -- <:VR
  gamma |- a :<:-: V (be ::: k :.: b) = do
    new <- gamma `Comma` Kappa (be ::: k) |- a :<:-: b
    let [delta, theta] = new <@> [[Kappa (be ::: k)]]
    return delta

  -- <:EL
  gamma |- E (al ::: k :.: a) :<:+: b = do
    new <- gamma `Comma` Kappa (al ::: k) |- a :<:+: b
    let [delta, theta] = new <@> [[Kappa (al ::: k)]]
    return delta

  -- <:ER
  gamma |- a :<:+: E (be ::: k :.: b) | not (headE a) = do
    beHat <- fresh be
    new <- gamma `Comma` Mark beHat `Comma` Kappa (beHat ::: k) |- a :<:+: (Hat beHat / be) b
    let [delta, theta] = new <@> [[Mark beHat]]
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

instance Turnstile (P :===: Q) Delta where

  -- PropEq
  gamma |- (t1 :=: t1') :===: (t2 :=: t2') = do
    theta <- gamma |- t1 :=*=: t2 ::: N
    theta |- gamsub theta t1' :=*=: gamsub theta t2' ::: N


instance Turnstile (A :===: B) Delta where
  
  -- =Var
  gamma |- NoHat a :===: NoHat a' | a == a' = return gamma

  -- =Exvar
  gamma |- Hat a :===: Hat a' | a == a' = return gamma

  -- =Unit
  gamma |- Unit :===: Unit = return gamma

  -- =Bin
  gamma |- Bin a1 a2 :===: Bin b1 b2 = do
    theta <- gamma |- a1 :===: b1
    theta |- gamsub theta a1 :===: gamsub theta b2

  -- =Vec
  gamma |- Vec t1 a1 :===: Vec t2 a2 = do
    -- I think the paper has a typo in that t1 === t2 should be a checking equation in Figure 19.
    -- There's no === judgment defined for terms, only types.
    theta <- gamma |- t1 :=*=: t2 ::: N
    theta |- gamsub theta a1 :===: gamsub theta a2

  -- =V
  gamma |- V (al ::: k :.: a) :===: V (al' ::: k' :.: b) | al == al' && k == k' = do
    new <- gamma `Comma` Kappa (al ::: k) |- a :===: b
    let [delta, delta'] = new <@> [[Kappa (al ::: k)]]
    return delta

  -- =E
  gamma |- E (al ::: k :.: a) :===: E (al' ::: k' :.: b) | al == al' && k == k' = do
    new <- gamma `Comma` Kappa (al ::: k) |- a :===: b
    let [delta, delta'] = new <@> [[Kappa (al ::: k)]]
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
  

