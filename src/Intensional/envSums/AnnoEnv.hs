module Intensional.EnvSums.AnnoEnv (
        getTyAnnotationExprsOfType
    ) where

import GhcPlugins hiding (putMsg, Var)
import Data.Data (Data(..))
import qualified Intensional.EnvSums.AnnoRep as AR
import Data.Maybe (fromJust)
import Intensional.EnvSums.THUtils
import Data.Set(Set)
import qualified Data.Set as S

type AnnoType = AExpr AR.ConstructorTyping
data AExpr a = AExpr Name [a]

instance Show a => Show (AExpr a) where
    show (AExpr n xs) = "AExpr " ++ nameStableString n ++ show xs


getConstructorTypings :: ModGuts -> CoreM [AnnoType]
getConstructorTypings = getTyAnnotationExprsOfType

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

infix 2 :::
data ConstructorTyping = Name ::: Typing

infixr 4 :=>
data Typing = Base Name
            | Ref Name
            | Var String
            | Data Name [Typing]
            | Typing :=> Typing

translateNamesTy :: AR.Typing -> CoreM Typing
translateNamesTy (AR.Base n) = Base . fromJust <$> lookupTHName (return ()) n
translateNamesTy (AR.Ref n) = Ref . fromJust <$> lookupTHName (return ()) n
translateNamesTy (AR.Var x) = return $ Var x
translateNamesTy (AR.Data n xs) = do
    n' <- fromJust <$> lookupTHName (return ()) n
    xs' <- foldr (\cx cts -> cx >>= \x -> (x:) <$> cts) (return []) $ map translateNamesTy xs
    return $ Data n' xs'
translateNamesTy (l AR.:=> r) = do
    l' <- translateNamesTy l
    r' <- translateNamesTy r
    return $ l' :=> r'

translateNamesCT :: AR.ConstructorTyping -> CoreM ConstructorTyping
translateNamesCT (n AR.::: t) = do
    n' <- fromJust <$> lookupTHName (return ()) n
    t' <- translateNamesTy t
    return $ n' ::: t'

translateNamesAnno :: AnnoType -> CoreM (AExpr ConstructorTyping)
translateNamesAnno (AExpr n xs) = do
    xs' <- foldr (\cx cts -> cx >>= \x -> (x:) <$> cts) (return []) $ map translateNamesCT xs
    return $ AExpr n xs'

--Makes a set of all type names used in a typing.
--typingDomain (Int :=> Maybe Bool) = {Int, Maybe, Bool}
typingDomain :: Typing -> Set Name
typingDomain (Base n) = S.singleton n
typingDomain (Ref n) = S.singleton n
typingDomain (Var _) = S.empty
typingDomain (Data n xs) = S.insert n (S.unions $ map typingDomain xs)
typingDomain (l :=> r) = S.union (typingDomain l) (typingDomain r)

--Makes a set of all type names used in a constructor typing.
--typingDomainCon (Foo ::: Int :=> Maybe Bool) = {Int, Maybe, Bool}
typingDomainCon :: ConstructorTyping -> Set Name
typingDomainCon (_ ::: t) = typingDomain t

--typingDomainAExpr :: AExpr ConstructorTyping -> Set Name
--typingDomainAExpr (AExpr n ts) = (S.insert n) . S.unions $ map typingDomainCon ts

--Makes a set of all annotated type synonym names
dom :: [AExpr a] -> Set Name
dom = foldr (\(AExpr n _) ns -> S.insert n ns) S.empty

--Makes a complete set of all type names required by a set of type names.
closeTypings :: [AExpr ConstructorTyping] -> Set Name -> Set Name
closeTypings as ns = if ns == ns' then ns else closeTypings as ns' where
    clsTy :: [AExpr ConstructorTyping] -> Name -> Set Name
    clsTy aes n = foldr (\(AExpr n' ts) ns -> if n == n' then S.union (S.unions $ map typingDomainCon ts) ns else ns) S.empty aes

    ns' = S.unions $ S.map (clsTy as) ns

--Makes a complete set of all type names required by a single type name.
closeTyping :: [AExpr ConstructorTyping] -> Name -> Set Name
closeTyping as n = closeTypings as $ S.singleton n

