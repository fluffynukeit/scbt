{-# LANGUAGE LambdaCase #-}
-- | This module implements Figure 12, substituting a context for a type.
module SubstType where

import Syntax
import Context

{-subst gamma (AAlpha alpha) = 
    let result = find rightAlpha gamma
        rightAlpha = \case
            FAlphaT alpha' _ | alpha == alpha' -> True
            _ -> False
    in case result of
        Just (FAlphaT _ tau) -> subst gamma (AAlpha tau)
        Nothing -> alpha
-}
