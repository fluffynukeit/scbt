-- | THE BIG ONE.  Implements fules in Figure 14a.
module AlgoTyping where

import Syntax
import Judgments
import AlgoSubtyping
import Search
import Context

-- | Checking against an expression against input type
instance Turnstile (:<=:) Delta where

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

  -- Sub (last due to redundant pattern match)
  gamma |- e :<=: (b,p) = do
    (a, q :: SmallP, theta) <- gamma |- (e :=>:)
    let op = join (pol b) (pol a)
    delta <- theta |- a `op` b
    return delta


-- | Expression e synthesizes to output type A and new context Delta
instance Turnstile (:=>:) ApDelta where

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
    
