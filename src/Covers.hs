-- | Implements the covers judgments of Figure 25 and pattern expansion in Figure 9.
module Covers where

import Syntax
import Judgments
import Context
import Assume()
import Unbound.Generics.LocallyNameless
import Prelude hiding (pi)

-- | Pattern expansion, Figure 9.
--
xWild :: Rho -> Bool
xWild (RhoX _) = True
xWild (Wild) = True
xWild _ = False

isUnit :: Rho -> Bool
isUnit (RhoUnit) = True
isUnit _ = False

-- | Vector expansion
(~>::) :: BigPi -> (BigPi, BigPi)
(~>::) [] = ([], [])
(~>::) ((rho:rhos) :=> e :|: pi) | xWild rho = 
  let (a, b) = (pi ~>::)
  in ( rhos :=> e :|: a, (Wild:Wild:rhos) :=> e :|: b )
(~>::) ((RhoNil:rhos) :=> e :|: pi) = 
  let (a, b) = (pi ~>::)
  in ( rhos :=> e :|: a, b)
(~>::) (((RhoConcat rho rho'):rhos) :=> e :|: pi) = 
  let (a,b) = (pi ~>::)
  in (a, (rho:rho':rhos) :=> e :|: b)

-- | Pair expansion
(~>*) :: BigPi -> BigPi
(~>*) [] = []
(~>*) (((RhoPair rho1 rho2):rhos) :=> e :|: pi) = 
  let pi' = (pi ~>*)
  in (rho1:rho2:rhos) :=> e :|: pi'
(~>*) ((rho:rhos) :=> e :|: pi) | xWild rho = 
  let pi' = (pi ~>*)
  in (Wild:Wild:rhos) :=> e :|: pi'

-- | Sum expansion
(~>+) :: BigPi -> (BigPi, BigPi)
(~>+) [] = ([], [])
(~>+) ((rho:rhos) :=> e :|: pi) | xWild rho =
  let (piL, piR) = (pi ~>+)
  in ( (Wild:rhos) :=> e :|: piL, (Wild:rhos) :=> e :|: piR )
(~>+) (((RhoInj1 rho):rhos) :=> e :|: pi) = 
  let (piL, piR) = (pi ~>+)
  in ( (rho:rhos) :=> e :|: piL, piR)
(~>+) (((RhoInj2 rho):rhos) :=> e :|: pi) = 
  let (piL, piR) = (pi ~>+)
  in ( piL, (rho:rhos) :=> e :|: piR )

-- | Var expansion
(~>~) :: BigPi -> BigPi
(~>~) [] = []
(~>~) ((rho:rhos) :=> e :|: pi) | xWild rho =
  let pi' = (pi ~>~)
  in rhos :=> e :|: pi'

-- | Unit expansion
(~>|) :: BigPi -> BigPi
(~>|) [] = []
(~>|) ((rho:rhos) :=> e :|: pi) | xWild rho || isUnit rho =
  let pi' = (pi ~>|)
  in rhos :=> e :|: pi'

-- | Guarded check, Pattern list pi contains a list pattern constructor at the head position
guarded :: BigPi -> Bool
guarded ((RhoNil:_rhos) :=> _e :|: _pi) = True
guarded (((RhoConcat _rho _rho'):_rhos) :=> _e :|: _pi) = True
guarded ((Wild:_rhos) :=> _e :|: pi) = guarded pi
guarded (((RhoX _x):_rhos) :=> _e :|: pi) = guarded pi


-- Under context gamma, patterns pi cover the types As
instance Turnstile (Covers BigPi) (Judgment Bool) where

  -- CoversEmpty
  _gamma |- ([] :=> _e :|: _pi) `Covers` ([], _q) = return True

  -- Covers1
  gamma |- pi `Covers` (Unit:as, q) = do
    let pi' = (pi ~>|)
    gamma |- pi' `Covers` (as, q)

  -- CoversX
  gamma |- pi `Covers` ((a1 :*: a2):as, q) = do
    let pi' = (pi ~>*)
    gamma |- pi' `Covers` (a1:a2:as, q)

  -- Covers+
  gamma |- pi `Covers` ((a1 :+: a2):as, q) = do
    let (piL, piR) = (pi ~>+)
    a <- gamma |- piL `Covers` (a1:as, q)
    b <- gamma |- piR `Covers` (a2:as, q)
    return $ a && b

  -- CoversE
  gamma |- pi `Covers` (E (al ::: k :.: _a):as, q) =
    gamma `Comma` Kappa (al ::: k) |- pi `Covers` (as, q)

  -- CoversWith
  gamma |- pi `Covers` ((a0 :/\: (t1 :=: t2)):as, Bang) =
    gamma |- (t1 :=: t2, pi) `Covers` (a0:as, Bang)

  -- CoversWithSlash (why is this rule's formatting so messed up in the paper?)
  gamma |- pi `Covers` ((a0 :/\: (_t1 :=: _t2)):as, Slash) =
    gamma |- pi `Covers` (a0:as, Slash) -- implied Slash?

  -- CoversVec
  gamma |- pi `Covers` ((Vec t a):as, Bang) = do
    let (piL, piR) = (pi ~>::)
    n <- fresh $ s2n "n" -- I *think* this rule introduces a variable for n
    g <- return $ guarded pi
    z <- gamma |- (t :=: Zero, piL) `Covers` (as, Bang)
    v <- gamma `Comma` Kappa (n ::: N) |- (t :=: Succ (NoHat n), piR) `Covers` (a:(Vec (NoHat n) a):as, Bang)
    return $ g && z && v

  -- CoversVecSlash
  gamma |- pi `Covers` ((Vec _t a):as, Slash) = do
    let (piL, piR) = (pi ~>::)
    n <- fresh $ s2n "n" -- I *think* this rule introduces a variable for n
    g <- return $ guarded pi
    z <- gamma |- piL `Covers` (as, Slash)
    v <- gamma `Comma` Kappa (n ::: N) |- piR `Covers` (a:(Vec (NoHat n) a):as, Slash)
    return $ g && z && v

  -- CoversVar (last for overlapping patterns fallthrough)
  gamma |- pi `Covers` (_a:as, q) =  do
    let pi' = (pi ~>~)
    gamma |- pi' `Covers` (as, q)


-- Under context gamma, pattern pi cover the types As assumping P
instance Turnstile (Covers (P, BigPi)) (Judgment Bool) where

  -- CoversEq and CoversEqBot
  gamma |- (t1 :=: t2, pi) `Covers` (as, Bang) = do
    let k = N -- TODO where does this kappa come from?
        q = Bang -- TODO where does this q come from?
    case runJudgment (gamma // (gamsub gamma t1 :=*=: gamsub gamma t2 ::: k)) of
      Bottom -> return True -- CoversEqBot. "Coverage succeeds since there are no possible values of that type."
      Delta delta -> delta |- pi `Covers` (map (gamsub delta) as, q) -- TODO gamma substitution into pi??
