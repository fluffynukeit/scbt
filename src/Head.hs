-- | Implements Head constructor clash, Figure 20
module Head where

import Syntax

(#) :: T -> T -> Bool
Zero # (Succ t) = True
(Succ t) # Zero = True
Unit # (Bin _ _) = True
(Bin _ _) # Unit = True
(_ :->: _) # (_ :->: _) = False
(_ :+: _) # (_ :+: _) = False
(_ :*: _) # (_ :*: _) = False
(Bin _ _) # (Bin _ _) = True -- different binary connectives here
_ # _ = error "Exhausted # checks."
