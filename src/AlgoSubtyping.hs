-- | Implements rules in Figure 22, Algo subtyping and equivalence
module AlgoSubtyping where

import Syntax
import Judgments
import Context
import Check
import Search
import Instantiate

isV (V _ _) = True
isV _ = False

isE (E _ _) = True
isE _ = False

pol (V _ _) = Neg
pol (E _ _) = Pos
pol _ = None

nonpos a = pol a /= Pos
nonneg a = pol a /= Neg

instance Turnstile (:<:+:) Delta where

  -- <:EL
  gamma |- E (al ::: k) a :<:+: b = do
    new <- gamma `Comma` Kappa (al ::: k) |- a :<:+: b
    let [delta, theta] = new <@> [[Kappa (al ::: k)]]
    return delta

  -- <:ER
  -- gamma |- a :<:+: V (be ::: k) b = 
    -- let new = gamma `Comma` Mark b `Comma` Kappa b ::: k

  -- <:Equiv, positive case
  gamma |- a :<:+: b | not (isV a || isE a || isV b || isE b) = gamma |- a :===: b

instance Turnstile (P :===: Q) Delta where

  -- PropEq
  gamma |- (t1 :=: t1') :===: (t2 :=: t2') = do
    theta <- gamma |- t1 :=*=: t2 ::: N
    delta <- theta |- subst theta t1' :=*=: subst theta t2' ::: N
    return delta


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
    delta <- theta |- subst theta a1 :===: subst theta b2
    return delta

  -- =Vec
  gamma |- Vec t1 a1 :===: Vec t2 a2 = do
    -- I think the paper has a typo in that t1 === t2 should be a checking equation in Figure 19.
    -- There's no === judgment defined for terms, only types.
    theta <- gamma |- t1 :=*=: t2 ::: N
    delta <- theta |- subst theta a1 :===: subst theta a2
    return delta

  -- =V
  gamma |- V (al ::: k) a :===: V (al' ::: k') b | al == al' && k == k' = do
    new <- gamma `Comma` Kappa (al ::: k) |- a :===: b
    let [delta, delta'] = new <@> [[Kappa (al ::: k)]]
    return delta

  -- =E
  gamma |- E (al ::: k) a :===: E (al' ::: k') b | al == al' && k == k' = do
    new <- gamma `Comma` Kappa (al ::: k) |- a :===: b
    let [delta, delta'] = new <@> [[Kappa (al ::: k)]]
    return delta

  -- =Implies
  gamma |- p :>: a :===: q :>: b = do
    theta <- gamma |- p :===: q
    delta <- theta |- subst theta a :===: subst theta b
    return delta

  -- =With
  gamma |- a :/\: p :===: b :/\: q = do
    theta <- gamma |- p :===: q
    delta <- theta |- subst theta a :===: subst theta b
    return delta

instance Turnstile (T :===: Tau) Delta where
  
  -- =InstantiateL
  gamma |- Hat a :===: tau | unsolved a gamma && not (a `elemFV` tau) =
    gamma |- a := tau ::: Star

  -- =InstantiateR
  gamma |- tau :===: Hat a | unsolved a gamma && not (a `elemFV` tau) =
    gamma |- a := tau ::: Star
