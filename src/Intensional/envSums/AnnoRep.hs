--{-# LANGUAGE GADTs #-}
--{-# LANGUAGE MultiParamTypeClasses #-}
--{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE TypeOperators #-}
--{-# LANGUAGE UndecidableInstances #-}
--{-# LANGUAGE AllowAmbiguousTypes #-}
--{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveDataTypeable #-}


module Intensional.EnvSums.AnnoRep where

import Data.Data (Data(..))
import qualified Language.Haskell.TH as TH


infix 2 :::
data ConstructorTyping = TH.Name ::: Typing
    deriving (Show, Data)

infixr 4 :=>
data Typing = Base TH.Name
            | Ref TH.Name
            | Var String
            | Data TH.Name [Typing]
            | Typing :=> Typing
    deriving (Show, Data)

