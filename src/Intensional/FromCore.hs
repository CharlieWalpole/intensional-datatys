{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}

module Intensional.FromCore
  ( freshCoreType,
    freshCoreScheme,
    fromCoreCons,
    consInstArgs,
    getVar,
  )
where

import Control.Monad.RWS
import qualified Data.IntSet as I
import qualified Data.Map as M
import GhcPlugins hiding ((<>), Expr (..), Type)
import Intensional.InferM
import Intensional.Scheme as Scheme
import ToIface
import qualified TyCoRep as Tcr
import Intensional.Types
import qualified Data.Sized as S

-- A fresh monomorphic type
freshCoreType :: Tcr.Type -> InferM (Type 1)
freshCoreType = fromCore Nothing

-- A fresh polymorphic type
freshCoreScheme :: Tcr.Type -> InferM (Scheme 1)
freshCoreScheme = fromCoreScheme Nothing

-- The type of a constructor injected into a fresh refinement environment
fromCoreCons :: DataCon -> InferM (Scheme 1)
fromCoreCons k = do
  x <- fresh
  let d = dataConTyCon k
  b <- isIneligible d
  unless b $ do
    l <- asks inferLoc
    emitKD k l (Inj x d)
  fromCoreScheme (Just x) (dataConUserType k)

-- The argument types of an instantiated constructor
consInstArgs :: RVar -> [Type 1] -> DataCon -> InferM [Type 1]
consInstArgs x as k = mapM fromCoreInst (dataConRepArgTys k)
  where
    fromCoreInst :: Tcr.Type -> InferM (Type 1)
    fromCoreInst (Tcr.TyVarTy a) =
      case lookup a (Prelude.zip (dataConUnivTyVars k) as) of
        Nothing -> return (Var (getName a))
        Just t -> return t
    fromCoreInst (Tcr.AppTy a b) = App <$> (fromCoreInst a) <*> (fromCoreInst b)
    fromCoreInst (Tcr.TyConApp d as')
      | isTypeSynonymTyCon d,
        Just (as'', s) <- synTyConDefn_maybe d =
        fromCoreInst (substTy (extendTvSubstList emptySubst (Prelude.zip as'' as')) s) -- Instantiate type synonym arguments
      | isClassTyCon d = return Ambiguous -- Disregard type class evidence
      | otherwise =
          do  b <- isIneligible d
              if b then (Data (S.singleton $ Base d)) . S.singleton <$> (mapM fromCoreInst as') 
                   else (Data (S.singleton $ Inj x d)) . S.singleton <$> (mapM fromCoreInst as')
    fromCoreInst (Tcr.FunTy _ a b) = (:=>) <$> fromCoreInst a <*> fromCoreInst b
    fromCoreInst (Tcr.LitTy l) = return (Lit $ toIfaceTyLit l)
    fromCoreInst _ = return Ambiguous

-- Convert a monomorphic core type
fromCore :: Maybe RVar -> Tcr.Type -> InferM (Type 1)
fromCore _ (Tcr.TyVarTy a) = Var <$> getExternalName a
fromCore f (Tcr.AppTy a b) = liftM2 App (fromCore f a) (fromCore f b)
fromCore f (Tcr.TyConApp d as)
  | isTypeSynonymTyCon d,
    Just (as', s) <- synTyConDefn_maybe d =
    fromCore f (substTy (extendTvSubstList emptySubst (Prelude.zip as' as)) s) -- Instantiate type synonyms
  | isClassTyCon d = return Ambiguous -- Disregard type class evidence
fromCore Nothing (Tcr.TyConApp d as) = do
  x <- fresh
  b <- isIneligible d
  if b then
    (Data (S.singleton $ Base d)) . S.singleton <$> mapM (fromCore Nothing) as
  else
    (Data (S.singleton $ Inj x d)) . S.singleton <$> mapM (fromCore Nothing) as
fromCore (Just x) (Tcr.TyConApp d as) = do
  b <- isIneligible d
  if b then
    (Data (S.singleton $ Base d)) . S.singleton <$> mapM (fromCore (Just x)) as
  else
    (Data (S.singleton $ Inj x d)) . S.singleton <$> mapM (fromCore (Just x)) as
fromCore f (Tcr.FunTy _ a b) = liftM2 (:=>) (fromCore f a) (fromCore f b)
fromCore _ (Tcr.LitTy l) = return $ Lit $ toIfaceTyLit l
fromCore _ _ = return Ambiguous -- Higher-ranked or impredicative types, casts and coercions

-- Convert a polymorphic core type
fromCoreScheme :: Maybe RVar -> Tcr.Type -> InferM (Scheme 1)
fromCoreScheme f (Tcr.ForAllTy b t) = do
  a <- getExternalName (Tcr.binderVar b)
  scheme <- fromCoreScheme f t
  return scheme {tyvars = a : tyvars scheme}
fromCoreScheme f (Tcr.FunTy _ a b) = do
  a' <- fromCore f a
  scheme <- fromCoreScheme f b -- Optimistically push arrows inside univiersal quantifier
  return scheme {body = a' :=> body scheme}
fromCoreScheme f t = Forall [] <$> fromCore f t

-- Lookup constrained variable and emit its constraints
getVar :: Var -> InferM (Scheme 1)
getVar v =
  asks (M.lookup (S.singleton $ getName v) . varEnv) >>= \case
    Just scheme -> do
      -- Localise constraints
      fre_scheme <-
        foldM
          ( \s x -> do
              y <- fresh
              return (rename x y s)
          )
          (scheme {boundvs = mempty})
          (I.toList (boundvs scheme))
      -- Emit constriants associated with a variable
      tell (constraints fre_scheme)
      return fre_scheme {Scheme.constraints = mempty}
    Nothing -> do
      var_scheme <- freshCoreScheme $ varType v
      maximise True (body var_scheme)
      return var_scheme

-- Maximise/minimise a library type, i.e. assert every constructor occurs in covariant positions
maximise :: Bool -> Type 1 -> InferM ()
maximise True (Data xs _) = 
  case xs S.!! 0 of
    Base _ -> return ()
    Inj x d -> do
      l <- asks inferLoc
      mapM_ (\k -> emitKD k l (Inj x d)) $ tyConDataCons d
maximise b (x :=> y) = maximise (not b) x >> maximise b y
maximise _ _ = return ()
