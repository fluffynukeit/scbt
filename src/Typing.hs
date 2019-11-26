-- | THE BIG ONE.  Implements rules in Figure 14a.
module Typing where

import Syntax
import Judgments
import Subtyping
import Search
import Context
import Check
import Assume
import Covers

import Unbound.Generics.LocallyNameless
import Prelude hiding ((/))

-- GENERAL NOTE
-- The paper states that omitting the principality p in the paper's expressions
-- implies that the principality is Slash.  In most cases, this is related to 
-- existential variables alpha hat.
-- I have tried to mark such cases with "implied Slash"


-- | Check if an expression is a case statement.
isCase (Case _ _) = True
isCase _ = False

-- | Checking against an expression against input type
instance Turnstile ((:<=:) (DecSyn k)) Delta where

    -- Rec
  gamma |- (Rec (x :.: v)) :<=: (a,p) = do
    new <- gamma `Comma` (XAp (x ::: a) p) |- v :<=: (a,p)
    let [delta, theta] = new <@> [[XAp (x ::: a) p]]
    return delta

  -- 1I
  gamma |- Un :<=: (Unit, p) = return gamma

  -- 1IAlphaHat
  gamma |- Un :<=: (Hat a, Slash) -- implied Slash?
    | h@[_,_] <- gamma <@> [[HatKappa $ a ::: Star]] 
    = return $ h >@< [[HatEquals $ a ::: Star :=: Unit]]

  -- VI
  gamma |- v :<=: (V (al ::: k :.: a), p) | chkI v = do
    new <- gamma `Comma` Kappa (al ::: k) |- v :<=: (a,p)
    let [delta, theta] = new <@> [[Kappa $ al ::: k]]
    return delta

  -- EI
  gamma |- e :<=: (E (al ::: k :.: a), p) | chkI e = do
    alHat <- fresh al
    gamma `Comma` HatKappa (alHat ::: k) |- e :<=: ((Hat alHat / al) a, Slash) -- implied Slash?

  -- ImpliesI and ImpliesIBot
  gamma |- v :<=: (p :>: a, Bang) | chkI v = do
    mark <- fresh $ s2n "Pmark"
    let maybetheta = runDeltaBot $ (gamma `Comma` Mark mark) // p
    case maybetheta of
      Just theta -> do
        new <- theta |- v :<=: (gamsub theta a, Bang)
        let [delta, delta'] = new <@> [[Mark mark]]
        return delta
      Nothing -> return gamma

  -- WithI
  gamma |- e :<=: (a :/\: p, smallp) | not (isCase e) = do
    theta <- gamma |- Ptrue p
    theta |- e :<=: (gamsub theta a, smallp)

  -- ArrowI
  gamma |- Lam (x :.: e) :<=: (a :->: b, p) = do
    new <- gamma `Comma` XAp (x ::: a) p |- e :<=: (b, p)
    let [delta, theta] = new <@> [[XAp (x ::: a) p]]
    return delta

  -- ArrowIAlphaHat
  gamma |- Lam (x :.: e) :<=: (NoHat a,Slash) | h@[_,_] <- gamma <@> [[HatKappa $ a ::: Star]] = do -- implied Slash?
    a1 <- fresh a
    a2 <- fresh a1
    let gamma' = h >@< [[HatKappa $ a1 ::: Star, HatKappa $ a2 ::: Star, HatEquals $ a ::: Star :=: (Hat a1 :->: Hat a2)]]
    new <- gamma' `Comma` XAp (x ::: Hat a1) Slash |- e :<=: (Hat a2,Slash) -- implied Slash? x2
    let [delta, delta'] = new <@> [[XAp (x ::: Hat a1) Slash]] -- implied Slash?
    return delta

  -- Case
  gamma |- Case e pi :<=: (c, p) = do
    (a, q, theta) <- gamma |- (e :=>:)
    delta <- theta |- (pi ::: ([gamsub theta a], q)) :<=: (gamsub theta c, p)
    result <- delta |- pi `Covers` ([gamsub delta a], q)
    if result 
      then return delta
      else error "Case rule failed pattern list coverage check." -- TODO what happens here?
  
  -- PlusIK
  gamma |- i@(InjK e) :<=: (a1 :+: a2, p) = gamma |- e :<=: (ak i a1 a2, p)

  -- PlusIAlphaHatK
  gamma |- i@(InjK e) :<=: (Hat a, Slash) | h@[_,_] <- gamma <@> [[HatKappa $ a ::: Star]] = do -- implied Slash?
    a1 <- fresh a
    a2 <- fresh a1
    let gamma' = h >@< [[HatKappa $ a1 ::: Star, HatKappa $ a2 ::: Star, HatEquals $ a ::: Star :=: (Hat a1 :+: Hat a2)]]
    gamma' |- e :<=: (ak i (Hat a1) (Hat a2), Slash) -- implied Slash?

  -- CrossI
  gamma |- Pair e1 e2 :<=: (a1 :*: a2, p) = do
    theta <- gamma |- e1 :<=: (a1, p)
    theta |- e2 :<=: (gamsub theta a2, p)

  -- CrossIAlphaHat
  gamma |- Pair e1 e2 :<=: (Hat a, Slash) | h@[_,_] <- gamma <@> [[HatKappa $ a ::: Star]] = do -- implied Slash?
      a1 <- fresh a
      a2 <- fresh a1
      let gamma' = h >@< [[HatKappa $ a2 ::: Star, HatKappa $ a1 ::: Star, HatEquals $ a ::: Star :=: (Hat a1 :*: Hat a2)]]
      theta <- gamma' |- e1 :<=: (Hat a1, Slash) -- implied Slash?
      theta |- e2 :<=: (gamsub theta $ Hat a2, Slash) -- implied Slash?

  -- Nil
  gamma |- Nil :<=: (Vec t a, p) = gamma |- Ptrue (t :=: Zero)

  -- Cons
  gamma |- (e1 :::: e2) :<=: (Vec t a, p) = do
    al <- fresh (s2n "alHatmark")
    gamma' <- gamma `Comma` Mark al `Comma` HatKappa (al ::: N) |- Ptrue (t :=: Succ (Hat al))
    theta <- gamma' |- e1 :<=: (gamsub gamma' a, p)
    new <- theta |- e2 :<=: (gamsub theta $ Vec (Hat al) a, Slash)
    let [delta, delta'] = new <@> [[Mark al]]
    return delta

  -- Sub (last due to overlapping/redundant pattern match)
  gamma |- e :<=: (b,p) = do
    (a, q, theta) <- (gamma |- (e :=>:)) :: ApDelta
    let op = join (pol b) (pol a)
    theta |- a `op` b

-- | Expression e synthesizes to output type A and new context Delta
instance Turnstile ((:=>:) k) ApDelta where

  -- Note: I can construct synthesis using postfix :=>: due to 
  -- PostfixOperators extension, but I apparently cannot pattern match
  -- on it, so the pattern match order is reversed.
  --
  -- Var
  gamma |- (:=>:) (X x) | Just (XAp (_ ::: a) p) <- find (solutionX x) gamma =
    return (gamsub gamma a, p, gamma)

  -- Anno
  gamma |- (:=>:) (Ann (e ::: a)) | gamma |- Ptype a Bang = do
    delta <- gamma |- e :<=: (gamsub gamma a, Bang)
    return (gamsub delta a, Bang, delta)

  -- ArrowE
  gamma |- (:=>:) (App e (SPlus s ss)) = do 
    (a, p, theta) <- gamma |- (e :=>:)
    theta |- (((s:ss) ::: a, p) :>>?:)

-- | Passing spine s to a function of type A synthesizes type C.
-- (Not recovering principality)
instance Turnstile ((:>>:) k) CqDelta where
  
  -- VSpine
  gamma |- (:>>:) ((e:s) ::: V (al ::: k :.: a), p) = do
    alHat <- fresh al
    gamma `Comma` HatKappa (alHat ::: k) |- (((e:s) ::: (Hat alHat / al) a, Slash) :>>:) -- implied Slash?

  -- ImpliesSpline
  gamma |- (:>>:) ((e:s) ::: p :>: a, smallp) = do
    theta <- gamma |- Ptrue p
    theta |- (((e:s) ::: gamsub theta a, smallp) :>>:)

  -- EmptySpine
  gamma |- (:>>:) ([] ::: a, p) = return (a, p, gamma)

  -- ArrowSpine
  gamma |- (:>>:) ((e:s) ::: a :->: b, p) = do
    theta <- gamma |- e :<=: (a, p)
    theta |- ((s ::: gamsub theta b, p) :>>:)
  
  -- AlphaSpine
  gamma |- (:>>:) ((e:s) ::: Hat a, Slash) | h@[_,_] <- gamma <@> [[HatKappa $ a ::: Star]] = do -- implied Slash?
    a1 <- fresh a
    a2 <- fresh a1
    let gamma' = h >@< 
          [
            [ HatKappa $ a2 ::: Star
            , HatKappa $ a1 ::: Star
            , HatEquals $ a ::: Star :=: (Hat a1 :->: Hat a2)
            ]
          ]
    gamma' |- (((e:s) ::: (Hat a1 :->: Hat a2), Slash) :>>:) -- implied Slash?

-- | Passing spine s to function of type A synthesizes type C.
-- (Recover principality if possible)
instance Turnstile ((:>>?:) k) CqDelta where

  -- SpinePass and SpineRecover
  gamma |- (:>>?:) (s ::: a, p) = do
    (c, q, delta) <- gamma |- ((s ::: a, p) :>>:)
    if p == Slash || q == Bang || not (null (setFEV c))
      then return (c, q, delta) -- SpinePass
      else return (c, Bang, delta) -- SpineRecover


-- | Algorithmic pattern matching in Figure 24.  Mutually dependent
-- with type synthesis and type checking (due to Case rule), so it's 
-- in the same module here.
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
