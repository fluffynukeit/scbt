-- | THE BIG ONE.  Implements fules in Figure 14a.
module AlgoTyping where

import Syntax
import Judgments
import AlgoSubtyping
import Search
import Context
import Check
import Assume

import Unbound.Generics.LocallyNameless
import Prelude hiding ((/))

-- | Check if an expression is a case statement.
isCase (Case _ _) = True
isCase _ = False

-- | Match on Inj1 or Inj2
pattern InjK k <- 
  (
  (\case
  Inj1 a -> Just a
  Inj2 a -> Just a
  _ -> Nothing
  )
  -> Just k
  )

-- | Map Inj1/Inj2 to arguments 1 and 2
ak (Inj1 _) a b = a
ak (Inj2 _) a b = b

-- | Checking against an expression against input type
instance Turnstile ((:<=:) k) Delta where

    -- Rec
  gamma |- (Rec (x :.: v)) :<=: (a,p) = do
    new <- gamma `Comma` (XAp (x ::: a) p) |- v :<=: (a,p)
    let [delta, theta] = new <@> [[XAp (x ::: a) p]]
    return delta

  -- 1|
  gamma |- Un :<=: (Unit, p) = return gamma

  -- 1|alpha
  gamma |- Un :<=: (Hat a, _) 
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
    delta <- gamma `Comma` HatKappa (alHat ::: k) |- e :<=: ((Hat alHat // al) a, p)
    -- Does principality p go along for the ride? Not shown in rule.
    return delta

  -- ImpliesI and ImpliesIBot
  gamma |- v :<=: (p :>: a, Bang) | chkI v = do
    mark <- fresh $ s2n "Pmark"
    let maybetheta = runDeltaBot $ (gamma `Comma` Mark mark) / p
    case maybetheta of
      Just theta -> do
        new <- theta |- v :<=: (gamsub theta a, Bang)
        let [delta, delta'] = new <@> [[Mark mark]]
        return delta
      Nothing -> return gamma

  -- WithI
  gamma |- e :<=: (a :/\: p, smallp) | not (isCase e) = do
    theta <- gamma |- Ptrue p
    delta <- theta |- e :<=: (gamsub theta a, smallp)
    return delta

  -- ArrowI
  gamma |- Lam (x :.: e) :<=: (a :->: b, p) = do
    new <- gamma `Comma` XAp (x ::: a) p |- e :<=: (b, p)
    let [delta, theta] = new <@> [[XAp (x ::: a) p]]
    return delta

  -- ArrowIAlphaHat
  gamma |- Lam (x :.: e) :<=: (NoHat a,p) | h@[_,_] <- gamma <@> [[HatKappa $ a ::: Star]] = do
    a1 <- fresh a
    a2 <- fresh a1
    let gamma' = h >@< [[HatKappa $ a1 ::: Star, HatKappa $ a2 ::: Star, HatEquals $ a ::: Star :=: (Hat a1 :->: Hat a2)]]
    new <- gamma' |- e :<=: (Hat a2,p)
    let Just solu = find (solutionXA x (Hat a1)) new -- paper suggests this cannot fail?
        [delta, delta'] = new <@> [[solu]] -- a little inefficient, oh well
    return delta

  -- TODO Case
  
  -- PlusIK
  gamma |- i@(InjK e) :<=: (a1 :+: a2, p) = gamma |- e :<=: (ak i a1 a2, p) -- passthrough principality?

  -- PlusIAlphaHatK
  gamma |- i@(InjK e) :<=: (Hat a, p) | h@[_,_] <- gamma <@> [[HatKappa $ a ::: Star]] = do
    a1 <- fresh a
    a2 <- fresh a1
    let gamma' = h >@< [[HatKappa $ a1 ::: Star, HatKappa $ a2 ::: Star, HatEquals $ a ::: Star :=: (Hat a1 :+: Hat a2)]]
    delta <- gamma' |- e :<=: (ak i (Hat a1) (Hat a2), p) -- passthrough principality?
    return delta

  -- CrossI
  gamma |- Pair e1 e2 :<=: (a1 :*: a2, p) = do
    theta <- gamma |- e1 :<=: (a1, p)
    delta <- theta |- e2 :<=: (gamsub theta a2, p)
    return delta

  -- CrossIAlphaHat
  gamma |- Pair e1 e2 :<=: (Hat a, p) | h@[_,_] <- gamma <@> [[HatKappa $ a ::: Star]] = do
      a1 <- fresh a
      a2 <- fresh a1
      let gamma' = h >@< [[HatKappa $ a2 ::: Star, HatKappa $ a1 ::: Star, HatEquals $ a ::: Star :=: (Hat a1 :*: Hat a2)]]
      theta <- gamma' |- e1 :<=: (Hat a1, p) -- passthrough principality?
      delta <- theta |- e2 :<=: (gamsub theta $ Hat a2, p) -- passthrough principality?
      return delta

  -- Nil
  gamma |- Nil :<=: (Vec t a, p) = do
    delta <- gamma |- Ptrue (t :=: Zero)
    return delta

  -- Cons
  gamma |- (e1 :::: e2) :<=: (Vec t a, p) = do
    al <- fresh (s2n "alHatmark")
    gamma' <- gamma `Comma` Mark al `Comma` HatKappa (al ::: N) |- Ptrue (t :=: Succ (Hat al))
    theta <- gamma' |- e1 :<=: (gamsub gamma' a, p)
    new <- theta |- e2 :<=: (gamsub theta (Vec (Hat al) a), Slash)
    let [delta, delta'] = new <@> [[Mark al]]
    return delta


  -- Sub (last due to overlapping/redundant pattern match)
  gamma |- e :<=: (b,p) = do
    (a, q :: SmallP, theta) <- gamma |- (e :=>:)
    let op = join (pol b) (pol a)
    delta <- theta |- a `op` b
    return delta


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
    (c, q, delta) <- theta |- (((s:ss) ::: a, p) :>>?:)
    return (c, q, delta)


-- | Passing spine s to a function of type A synthesizes type C.
-- (Not recovering principality)
instance Turnstile ((:>>:) k) CqDelta where
  
  -- VSpine
  gamma |- (:>>:) ((e:s) ::: V (al ::: k :.: a), p) = do
    alHat <- fresh al
    (c, q, delta) <- gamma `Comma` HatKappa (al ::: k) |- (((e:s) ::: (Hat alHat // al) a, p) :>>:)
    return (c, q, delta)

  -- ImpliesSpline
  gamma |- (:>>:) ((e:s) ::: p :>: a, smallp) = do
    theta <- gamma |- Ptrue p
    (c, q, delta) <- theta |- (((e:s) ::: gamsub theta a, smallp) :>>:)
    return (c, q, delta)

  -- EmptySpine
  gamma |- (:>>:) ([] ::: a, p) = return (a, p, gamma)

  -- ArrowSpine
  gamma |- (:>>:) ((e:s) ::: a :->: b, p) = do
    theta <- gamma |- e :<=: (a, p)
    (c, q, delta) <- theta |- ((s ::: gamsub theta b, p) :>>:)
    return (c, q, delta)
  
  -- AlphaSpine
  gamma |- (:>>:) ((e:s) ::: Hat a, p) | h@[_,_] <- gamma <@> [[HatKappa $ a ::: Star]] = do
    a1 <- fresh a
    a2 <- fresh a1
    let gamma' = h >@< 
          [
            [ HatKappa $ a2 ::: Star
            , HatKappa $ a1 ::: Star
            , HatEquals $ a ::: Star :=: (Hat a1 :->: Hat a2)
            ]
          ]
    (c, q, delta) <- gamma' |- (((e:s) ::: (Hat a1 :->: Hat a2), p) :>>:) -- passthrough principality?
    return (c, q, delta)

-- | Passing spine s to function of type A synthesizes type C.
-- (Recover principality if possible
instance Turnstile ((:>>?:) k) CqDelta where

  -- SpinePass and SpineRecover
  gamma |- (:>>?:) (s ::: a, p) = do
    (c, q, delta) <- gamma |- ((s ::: a, p) :>>:)
    if p == Slash || q == Bang || not (null (setFEV c))
      then return (c, q, delta) -- SpinePass
      else return (c, Bang, delta) -- SpineRecover
