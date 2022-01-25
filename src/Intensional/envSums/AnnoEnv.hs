module Intensional.EnvSums.AnnoEnv (
        getTyAnnotationExprsOfType
    ) where

import GhcPlugins hiding (putMsg)
import Data.Data (Data(..))


data AExpr a = AExpr Name [a]

instance Show a => Show (AExpr a) where
    show (AExpr n xs) = "AExpr " ++ nameStableString n ++ show xs


-- Gets all expressions of type 'a' from the type annotations in the current module
-- Intended to be used like: (getTyAnnotationExprsOfType guts) :: CoreM [String]
getTyAnnotationExprsOfType :: Data a => ModGuts -> CoreM [AExpr a]
getTyAnnotationExprsOfType guts@ModGuts { mg_tcs = tcs } = foldAnnExprs . (map (annotationsOn guts)) . getNames $ tcs

-- Gets the GHC.Name(s) of types and type synonyms (data statements and type statements)
getNames :: [TyCon] -> [Name]
getNames tcs = (map tyConName) . (filter (\x -> isAlgTyCon x || isTypeSynonymTyCon x)) $ tcs

foldAnnExprs :: [CoreM (AExpr a)] -> CoreM [AExpr a]
foldAnnExprs = concatThroughMonad . (map (fmap (:[])))

-- Gets the expressions in the annotations of a given GHC.Name
annotationsOn :: Data a => ModGuts -> Name -> CoreM (AExpr a)
annotationsOn guts name = do
    anns <- getAnnotations deserializeWithData guts
    return $ AExpr name (lookupWithDefaultUFM anns [] name)

-- Generalisation of [CoreM [a]] -> CoreM [a] function.
concatThroughMonad :: (Monad n, Foldable m, Monoid (m a)) => m (n (m a)) -> n (m a)
concatThroughMonad ms = foldl (\n1 n2 -> n1 >>= \x -> fmap (mappend x) n2) (return mempty) ms

{-
-- Prints given string to console
debug :: MonadIO m => DynFlags -> String -> m ()
debug fs s = liftIO $ putMsg fs (text s)

-- Prints given SDoc to console
debugSDoc :: MonadIO m => DynFlags -> SDoc -> m ()
debugSDoc fs s = liftIO $ putMsg fs s
-}