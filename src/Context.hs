{-# LANGUAGE PatternSynonyms #-}
module Context 
    ( module Context
    , elem
    , find
    ) where

import Syntax
import Data.Sequence
import Data.Foldable

pattern Comma a b = (:|>) a b
pattern Empty = Data.Sequence.Empty

