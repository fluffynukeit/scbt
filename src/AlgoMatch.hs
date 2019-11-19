-- | Algorithmic pattern matching, Figure 24.
module AlgoMatch where

import Judgments
import Syntax
import Context
import AlgoTyping
import Unbound.Generics.LocallyNameless.Name

instance Turnstile ((:<=:) (BigPi ::: ([A], SmallQ))) Delta where

  -- MatchEmpty
  gamma |- [] ::: (as, q) :<=: (c, p) = return gamma

  -- MatchSeq
  gamma |- (pi :|: pi') ::: (as, q) :<=: (c, p) = do
    theta <- gamma |- pi ::: (as, q) :<=: (c, p)
    theta |- pi' ::: (map (gamsub theta) as, q) :<=: (c, p)

instance Turnstile ((:<=:) (SmallPi ::: ([A], SmallQ))) Delta where

  -- MatchBase
  gamma |- [] :=> e ::: ([], q) :<=: (c, p) = gamma |- e :<=: (c, p)

  -- MatchUnit
  gamma |- (Un:rho) :=> e ::: (Unit:as, q) :<=: (c, p) = 
    gamma |- rho :=> e ::: (as, q) :<=: (c, p)

  -- MatchE
  gamma |- rho :=> e ::: (E (al ::: k :.: a):as, q) :<=: (c, p) = do
    new <- gamma `Comma` Kappa (al ::: k) |- rho :=> e ::: (a:as, q) :<=: (c, p)
    let [delta, theta] = new <@> [[Kappa $ al ::: k]]
    return delta

  -- MatchWith
  gamma |- rho :=> e ::: ((a :/\: p):as, Bang) :<=: (c, smallp) = 
    gamma |- (p, rho :=> e ::: (a:as), Bang) :<=: (c, smallp)

  -- MatchWithSlash
  gamma |- rho :=> e ::: ((a :/\: p):as, Slash) :<=: (c, smallp) = 
    gamma |- rho :=> e ::: ((a:as), Slash) :<=: (c, smallp)
  
  -- MatchX
  gamma |- (Pair rho1 rho2 : rho) :=> e ::: ((a1 :*: a2):as, q) :<=: (c, p) =
    gamma |- (rho1:rho2:rho) :=> e ::: (a1:a2:as, q) :<=: (c, p)

  -- Match+k
  gamma |- (i@(InjK rho) : rhos) :=> e ::: ((a1 :+: a2):as, q) :<=: (c, p) =
    gamma |- (rho:rhos) :=> e ::: ((ak i a1 a2):as, q) :<=: (c, p)

  -- MatchNeg
  gamma |- ((X z):rho) :=> e ::: (a:as, q) :<=: (c, p) | not (headV a || headE a) = do
    let e' = e -- FIXME TODO where does e' come from !??!
    new <- gamma `Comma` XAp (z ::: a) Bang |- rho :=> e' ::: (as, q) :<=: (c, p)
    let [delta, delta'] = new <@> [[XAp (z ::: a) Bang]]
    return delta

  -- MatchWild
  gamma |- (Wild:rho) :=> e ::: (a:as, q) :<=: (c, p) | not (headV a || headE a) = 
    gamma |- rho :=> e ::: (as, q) :<=: (c, p)

  -- MatchNil
  gamma |- (Nil:rho) :=> e ::: ((Vec t a):as, Bang) :<=: (c, p) =
    gamma |- (t :=: Zero, rho :=> e ::: as, Bang) :<=: (c, p)

  -- MatchCons
  gamma |- ((rho1 :::: rho2):rho) :=> e ::: ((Vec t a):as, Bang) :<=: (c, p) = do
    al <- fresh $ s2n "alpha"
    new <- gamma `Comma` Kappa (al ::: N) |- 
      ( t :=: (Succ $ NoHat al)
      , (rho1:rho2:rho) :=> e ::: (a:(Vec (NoHat al) a):as)
      , Bang
      ) :<=: (c, p)
    let [delta, theta] = new <@> [[Kappa $ al ::: N]]
    return delta

  -- MatchNilSlash
  gamma |- (Nil:rho) :=> e ::: ((Vec t a):as, Slash) :<=: (c, p) =
    gamma |- rho :=> e ::: (as, Slash) :<=: (c, p)

  -- MatchConsSlash
  gamma |- ((rho1 :::: rho2):rho) :=> e ::: ((Vec t a):as, Slash) :<=: (c, p) = do
    al <- fresh $ s2n "alpha"
    new <- gamma `Comma` Kappa (al ::: N) |- 
      (rho1:rho2:rho) :=> e ::: ((a:(Vec (NoHat al) a):as), Slash) :<=: (c, p)
    let [delta, theta] = new <@> [[Kappa $ al ::: N]]
    return delta

-- Incorporate proposition P while checking branches Big Pi.
-- In this case, I have changed the notation to move the proposition P
-- on the right hand side of the turnstile to avoid clashing with the 
-- Assume typeclass used for assumptions leading to possibly inconsistent
-- contexts.
instance Turnstile ((:<=:) (P, SmallPi ::: [A], SmallQ)) Delta where -- paper says big pi?

  -- MatchBottom and MatchUnify
  gamma |- (sigma :=: tau, rho :=> e ::: as, Bang) :<=: (c, smallp) = do
    p <- fresh $ s2n "Pmark"
    let k = Star -- FIXME TODO where does k come from?!?
    let mtheta = runDeltaBot $ gamma `Comma` Mark p // (sigma :=*=: tau ::: k)
    case mtheta of
      Nothing -> return gamma
      Just theta -> do
        new <- theta |- rho :=> e ::: (as, Bang) :<=: (c, smallp)
        let [delta, delta'] = new <@> [[Mark p]]
        return delta
