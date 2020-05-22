{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module InferCoreExpr
  ( inferProg,
  )
where

import Constraints
import Control.Monad
import Control.Monad.RWS
import CoreUtils
import qualified Data.List as L
import qualified Data.Map as M
import DataTypes
import Emit
import FromCore
import qualified GhcPlugins as Core
import Guards
import InferM
import Name
import Outputable hiding (empty)
import Scheme
import TyCon
import Types
import Prelude hiding (sum)

defaultLevel :: Monad m => d -> InferM s m (DataType d)
defaultLevel k = do
  u <- asks unrollDataTypes
  if u then return (DataType Initial k) else return (DataType Neutral k)

-- Infer constraints for a (mutually-)recursive bind
inferRec :: Monad m => Bool -> Core.CoreBind -> InferM s m (Context s)
inferRec top bgs = do
  binds <-
    sequence $
      M.fromList
        [ (n, fromCoreScheme (exprType rhs))
          | (x, rhs) <- Core.flattenBinds [bgs],
            let n = getName x
        ]
  ctx <-
    putVars binds -- Add binds for recursive calls
      $
      -- Infer rhs; subtype of recursive usage
      sequence
      $ M.fromList
        [ ( n,
            do
              scheme <- infer rhs
              emitTypeConstraint (body scheme) (body sr)
              return scheme
          )
          | (x, rhs) <- Core.flattenBinds [bgs],
            let n = getName x,
            let sr = binds M.! n
        ]
  if top
    then saturate ctx -- If generalising let or a top-level definition
    else return ctx

-- Infer constraints for a module
inferProg :: Monad m => Core.CoreProgram -> InferM s m (Context s)
inferProg = foldM (\ctx -> fmap (M.union ctx) . putVars ctx . inferRec True) M.empty

-- Infer constraints for a program expression
infer :: Monad m => Core.CoreExpr -> InferM s m (Scheme s)
infer (Core.Var v) =
  case Core.isDataConId_maybe v of
    Just k
      -- Ignore typeclass evidence
      | Core.isClassTyCon $ Core.dataConTyCon k -> return $ Mono Ambiguous
      -- Infer constructor
      | otherwise -> do
        scheme <- defaultLevel k >>= fromCoreCons
        case decompTy (body scheme) of
          -- Refinable constructor
          (_, Inj x d _) -> do
            s <- mkCon k
            emitSetConstraint s (Dom x) d >> return scheme
          -- Unrefinable constructor
          _ -> return scheme
    -- Infer variable
    Nothing -> getVar v
-- Type literal
infer l@(Core.Lit _) = fromCoreScheme $ Core.exprType l
-- Type application
infer (Core.App e1 (Core.Type e2)) = do
  t' <- fromCore e2
  scheme <- infer e1
  case scheme of
    Forall (a : as) t ->
      return $ Forall as (subTyVar a t' t)
    Mono Ambiguous -> return $ Mono Ambiguous
    _ -> error "Type is already saturated!"
-- Term application
infer (Core.App e1 e2) = infer e1 >>= \case
  Forall as Ambiguous -> Forall as Ambiguous <$ infer e2
  -- This should raise a warning for as /= []!
  Forall as (t3 :=> t4) -> do
    t2 <- mono <$> infer e2
    emitTypeConstraint t2 t3
    return $ Forall as t4
  _ -> pprPanic "Term application to non-function!" $ ppr (Core.exprType e1, Core.exprType e2)
infer (Core.Lam x e)
  | Core.isTyVar x = do
    -- Type abstraction
    a <- getExternalName x
    infer e >>= \case
      Forall as t -> return $ Forall (a : as) t
  | otherwise = do
    -- Variable abstraction
    t1 <- fromCore $ Core.varType x
    putVar (getName x) (Mono t1) (infer e) >>= \case
      Forall as t2 -> return $ Forall as (t1 :=> t2)
-- Local prog
infer (Core.Let b e) = do
  ts <- inferRec True b
  putVars ts $ infer e
infer (Core.Case e bind_e core_ret alts) = do
  -- Fresh return type
  ret <- fromCore core_ret
  -- Separate default case
  let altf = filter (\(_, _, rhs) -> not $ Core.exprIsBottom rhs) alts
  let (alts', def) = Core.findDefault altf
  -- Infer expression on which to pattern match
  t0 <- mono <$> infer e
  -- Add the variable under scrutinee to scope
  putVar (getName bind_e) (Mono t0) $ case t0 of
    -- Infer a refinable case expression
    Inj rvar d as -> do
      ks <-
        mapMaybeM
          ( \(Core.DataAlt k, xs, rhs) -> do
              reach <- isBranchReachable e k
              if reach
                then do
                  -- Add constructor arguments introduced by the pattern
                  xs_ty <- fst . decompTy <$> fromCoreConsInst (k <$ d) as
                  let ts = M.fromList [(getName x, Mono t) | (x, t) <- zip xs xs_ty]
                  branch e [k] rvar d $ do
                    -- Constructor arguments are from the same refinement environment
                    mapM_ (\(Mono kti) -> emitTypeConstraint (inj rvar kti) kti) ts
                    -- Ensure return type is valid
                    ret_i <- mono <$> putVars ts (infer rhs)
                    emitTypeConstraint ret_i ret
                  -- Record constructors
                  return (Just k)
                else return Nothing
          )
          alts'
      case def of
        Nothing -> do
          -- Ensure destructor is total if not nested
          top <- topLevel e
          s <- mkSet ks
          when top $ emitSetConstraint (Dom rvar) s d
        Just rhs ->
          -- Guard default case by constructors that have not occured
          branch e (tyConDataCons (orig d) L.\\ ks) rvar d $ do
            ret_i <- mono <$> infer rhs
            emitTypeConstraint ret_i ret
    -- Infer an unrefinable case expression
    Base d as ->
      forM_ altf $ \case
        (Core.DataAlt k, xs, rhs) -> do
          k' <- defaultLevel k
          reach <- isBranchReachable e k
          when reach $ do
            -- Add constructor arguments introduced by the pattern
            xs_ty <- fst . decompTy <$> fromCoreConsInst k' as
            let ts = M.fromList [(getName x, Mono t) | (x, t) <- zip xs xs_ty]
            -- Ensure return type is valid
            ret_i <- mono <$> putVars ts (infer rhs)
            emitTypeConstraint ret_i ret
        (_, _, rhs) -> do
          -- Ensure return type is valid
          ret_i <- mono <$> infer rhs
          emitTypeConstraint ret_i ret
    -- Ambiguous
    _ ->
      mapM_
        ( \(_, _, rhs) -> do
            ret_i <- mono <$> infer rhs
            emitTypeConstraint ret_i ret
        )
        altf
  return $ Mono ret
-- Track source location
infer (Core.Tick Core.SourceNote {Core.sourceSpan = s} e) = setLoc s $ infer e
-- Ignore other ticks
infer (Core.Tick _ e) = infer e
-- Infer cast
infer (Core.Cast e _) = do
  _ <- infer e
  return (Mono Ambiguous)
-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ = error "Unimplemented"

mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM op = foldr f (return [])
  where
    f x xs = do
      x <- op x
      case x of
        Nothing -> xs
        Just x -> do
          xs <- xs
          return (x : xs)
