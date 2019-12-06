{-#  LANGUAGE FlexibleInstances, MultiParamTypeClasses, PatternSynonyms #-}

module InferM (
  InferM,
  runInferM,
  pushCase,
  popCase,
  topLevel,
  quantifyWith,

  Context (Context, var),
  safeVar,
  safeCon,
  upArrowDataCon,
  insertVar,
  insertMany,
  
  toSort,
  toSortScheme,
  toDataCon,
  fresh,
  freshScheme
) where

import Control.Monad.RWS

import qualified Data.Map as M

import IfaceType
import ToIface
import qualified GhcPlugins as Core
import qualified TyCoRep as Tcr

import Type
import Constraint

instance Core.Uniquable IfaceTyCon where
  getUnique (IfaceTyCon n _) = Core.getUnique n

-- The inference monad;
-- a local context
-- a global expr stack for nested pattern matching, and a fresh int
type InferM = RWST Context () ([Core.Unique], Int) IO
runInferM p env = do 
  (tss, _, _) <- liftIO $ runRWST p env ([], 0)
  return tss

-- Enter a new case statement
-- Not total!
pushCase :: Core.Expr Core.Var-> InferM ()
pushCase (Core.Var v) = modify (\(us, i) -> (Core.getUnique v:us, i))

-- Exit a case statement
popCase :: InferM ()
popCase = modify (\(u:us, i) -> (us, i))

-- Is the current case statement at the top level
-- Not total!
topLevel :: Core.Expr Core.Var -> InferM Bool
topLevel (Core.Var v) = do
  (us, _) <- get
  return (Core.getUnique v `notElem` us)
  
-- The variables in scope and their type
newtype Context = Context {
  var :: M.Map Core.Name TypeScheme
}

-- Insert a variable into the context
insertVar :: Core.Name -> TypeScheme -> Context -> Context
insertVar x f ctx = ctx{var = M.insert x f $ var ctx}

-- Insert many variable into the context
insertMany :: [Core.Name] -> [TypeScheme] -> Context -> Context
insertMany [] [] ctx = ctx
insertMany (x:xs) (f:fs) ctx = insertVar x f $ insertMany xs fs ctx



quantifyWith
        :: ConGraph
           -> [TypeScheme]
           -> RWST Context () ([Core.Unique], Int) IO [TypeScheme]
quantifyWith = undefined

-- Extract a variable from (local/global) context
safeVar :: Core.Var -> InferM TypeScheme
safeVar v = do
  ctx <- ask
  case var ctx M.!? Core.getName v of
    Just ts -> return ts
    Nothing -> do
      -- We can assume the variable is in scope as GHC hasn't emitted a warning
      -- Assume all externally defined terms are unrefined
      let t = Core.varType v

      freshScheme $ toSortScheme t

-- Extract a constructor from (local/global) context and fillout the reachability tree
safeCon :: Core.DataCon -> InferM (IfaceTyCon, [Core.Name], [Sort])
safeCon k = do
  let tc   = Core.dataConTyCon k
      as   = Core.getName <$> Core.dataConUnivAndExTyVars k
      args = toSort <$> Core.dataConOrigArgTys k -- Ignore evidence

  return (toIfaceTyCon tc, as, args)

-- Instantiated constructor
upArrowDataCon :: Int -> DataCon -> [Sort] -> [Type]
upArrowDataCon x (Data _ _ []) _      = []
upArrowDataCon x (Data d as (t:ts)) as' = upArrow x (subTypeVars as as' t) : upArrowDataCon x (Data d as ts) as'

-- Refinement a data type at a stem 
upArrow :: Int -> Sort -> Type
upArrow x (SData d as)   = Inj x d as
upArrow x (SArrow t1 t2) = upArrow x t1 :=> upArrow x t2
upArrow _ (SVar a)       = TVar a
upArrow x (SApp s1 s2)   = App (upArrow x s1) s2
upArrow _ (SLit l)       = Lit l
upArrow _ (SBase b as)   = Base b as


-- Lightweight representation of Core.DataCon:
-- DataCon n as args ~~ n :: forall as . args_0 -> ... -> args_n
newtype DataCon = DataCon (Core.Name, [Core.Name], [Sort])

-- DataCons are uniquely determined by their constructor's name
instance Eq DataCon where
  {-# SPECIALIZE instance Eq DataCon #-}
  DataCon (n, _, _) == DataCon (n', _, _) = n == n'

  -- DataCon constructor
pattern Data :: Core.Name -> [Core.Name] -> [Sort] -> DataCon
pattern Data n ns ss = DataCon (n, ns, ss)


-- Extract relevant information from Core.DataCon
toDataCon :: Core.DataCon -> DataCon
toDataCon dc = Data (Core.getName dc) (Core.getName <$> Core.dataConUnivAndExTyVars dc) (toSort <$> Core.dataConOrigArgTys dc)

-- Convert a core type into a sort
toSort :: Core.Type -> Sort
toSort (Tcr.TyVarTy v)   = SVar $ Core.getName v
toSort (Tcr.AppTy t1 t2) =
  let s1 = toSort t1
      s2 = toSort t2
  in SApp s1 s2
toSort (Tcr.TyConApp t args) | Core.isTypeSynonymTyCon t =
  case Core.synTyConDefn_maybe t of
    Just (as, u) -> subTypeVars (Core.getName <$> as) (toSort <$> args) (toSort u)
toSort (Tcr.TyConApp t args) = SData (Core.getName t) (toSort <$> args)
toSort (Tcr.FunTy t1 t2) = 
  let s1 = toSort t1
      s2 = toSort t2
  in SArrow s1 s2
toSort (Tcr.LitTy l) = SLit l
-- toSort (T.ForAllTy b t) = toSort t `applySortToSort` (SVar $ Core.getName $ Core.binderVar b)
toSort t = Core.pprPanic "Core type is not a valid sort!" (Core.ppr t) -- Cast & Coercion

-- Convert a core type into a sort scheme
toSortScheme :: Core.Type -> SortScheme
toSortScheme (Tcr.TyVarTy v)       = SForall [] (SVar $ Core.getName v)
toSortScheme (Tcr.AppTy t1 t2)     = SForall [] $ SApp (toSort t1) (toSort t2)
toSortScheme (Tcr.TyConApp t args) | Core.isTypeSynonymTyCon t =
  case Core.synTyConDefn_maybe t of
    Just (as, u) -> SForall [] $ subTypeVars (Core.getName <$> as) (toSort <$> args) (toSort u)
toSortScheme (Tcr.TyConApp t args) = SForall [] $ SData (Core.getName t) (toSort <$> args)
toSortScheme (Tcr.ForAllTy b t) =
  let (SForall as st) = toSortScheme t
      a = Core.getName $ Core.binderVar b
  in SForall (a:as) st
toSortScheme (Tcr.FunTy t1@(Tcr.TyConApp _ _) t2)
  | Core.isPredTy t1 = toSortScheme t2 -- Ignore evidence of typeclasses and implicit parameters
toSortScheme (Tcr.FunTy t1 t2) = let s1 = toSort t1; SForall as s2 = toSortScheme t2 in SForall as (SArrow s1 s2)
toSortScheme t = Core.pprPanic "Core type is not a valid sort!" (Core.ppr t) -- Cast & Coercion

-- A fresh refinement variable
fresh :: Sort -> InferM Type
fresh (SVar a)       = return $ TVar a
fresh (SData d as) = do
  (stack, i) <- get
  put (stack, i + 1)
  return $ Inj i d as
fresh (SArrow s1 s2) = do
  t1 <- fresh s1
  t2 <- fresh s2
  return (t1 :=> t2)
fresh (SApp s1 s2) = do
  t1 <- fresh s1
  return $ App t1 s2
fresh (SLit l) = return $ Lit l
fresh (SBase b as) = return $ Base b as

-- A fresh refinement scheme for module/let bindings
freshScheme :: SortScheme -> InferM TypeScheme
freshScheme (SForall as (SVar a))       = return $ Forall as [] [] $ TVar a
freshScheme (SForall as s@(SData _ _)) = do
  t <- fresh s
  case t of
    Inj x d _ -> return $ Forall as [x] [] t
freshScheme (SForall as (SArrow s1 s2)) = do
  Forall _ v1 _ t1 <- freshScheme (SForall [] s1)
  Forall _ v2 _ t2 <- freshScheme (SForall [] s2)
  return $ Forall as (v1 ++ v2) [] (t1 :=> t2)
freshScheme (SForall as (SApp s1 s2)) = do
  t1 <- fresh s1
  return $ Forall as [] [] $ App t1 s2
freshScheme (SForall as (SLit l)) = return $ Forall as [] [] (Lit l)
freshScheme (SForall as (SBase b ss)) = return $ Forall as [] [] (Base b ss)