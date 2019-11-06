-- | This module implements Figure 12, substituting a context for a type.
module SubstType where

import Syntax
import Context

{-subst gamma (Alpha alpha) = 
    let result = find matchingSymbol gamma
        matchingSymbol = \case
            Equals (alpha' :=: _) | alpha == alpha' -> True
            _ -> False
    in case result of
        Just (Equals (_ :=: tau)) -> subst gamma (Alpha tau)
        Nothing -> alpha
-}
