{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Intensional.EnvSums.THUtils where

import qualified Language.Haskell.TH as TH
import GhcPlugins
import Data.Maybe (listToMaybe)

--From: https://ocramz.github.io/haskell/ghc/metaprogramming/2021/06/22/finding-core-th.html
lookupTHName :: CoreM () -> TH.Name -> CoreM (Maybe Name)
lookupTHName failAction thn = thNameToGhcName thn >>= \case
  Nothing -> do
    --errorMsg $ text "Could not resolve TH name" <+> text (show thn)
    failAction
    pure Nothing
  Just n -> return $ pure n

--From: https://ocramz.github.io/haskell/ghc/metaprogramming/2021/06/22/finding-core-th.html
lookupNameInGuts :: ModGuts -> Name -> Maybe (Var, CoreExpr)
lookupNameInGuts guts n = listToMaybe [ (v,e) | (v,e) <- flattenBinds (mg_binds guts) , getName v == n ]
