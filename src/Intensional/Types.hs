{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE CPP, DataKinds, GADTs, KindSignatures, ScopedTypeVariables, TypeOperators,
--             TypeApplications, TypeFamilies, TypeFamilyDependencies, FlexibleContexts, PolyKinds #-}

module Intensional.Types
  ( RVar,
    Domain,
    Refined (..),
    DataType (..),
    Type,
    TypeGen (..),
    -- inj,
    decompType,
    subTyVar,
    tyconOf,
  )
where

import Binary
import Data.Bifunctor
import Data.Hashable
import qualified Data.IntSet as I
import Data.Map (Map)
import GHC.Generics hiding (prec)
import GhcPlugins hiding ((<>), Expr (..), Type)
import IfaceType
import Data.Sized hiding ((++), empty)
import qualified Data.Sized as S
import Intensional.EnvSums.AnnoEnv (concatThroughMonad)

type RVar = Int

type Domain = I.IntSet

-- The class of objects containing refinement variables
class Refined t where
  domain :: t -> Domain
  rename :: RVar -> RVar -> t -> t
  prpr   :: (RVar -> SDoc) -> t -> SDoc

instance Refined b => Refined (Map a b) where
  domain = foldMap domain
  rename x y = fmap (rename x y)
  prpr m = foldr (($$) . prpr m) empty

-- A datatype identifier
-- d is TyCon, IfaceTyCon or Name
data DataType d
  = Base d
  | Inj RVar d -- Extended datatypes from the canonical environment
  deriving (Eq, Functor, Foldable, Generic, Traversable)

instance Hashable d => Hashable (DataType d)

instance Outputable d => Outputable (DataType d) where
  ppr = prpr ppr 

instance Binary d => Binary (DataType d) where
  put_ bh (Base d) = put_ bh False >> put_ bh d
  put_ bh (Inj x d) =  put_ bh True >> put_ bh x >> put_ bh d
  get bh =
    get bh >>= \case
      False -> Base <$> get bh
      True -> Inj <$> get bh <*> get bh

instance Outputable d => Refined (DataType d) where
  domain (Base _) = I.empty
  domain (Inj x _) = I.singleton x

  rename x y (Inj z d)
    | x == z = Inj y d
  rename _ _ d = d

  prpr _ (Base d) = ppr d
  prpr m (Inj x d) = hcat [text "inj_", m x] <+> ppr d

-- Check if a core datatype contains covariant arguments
-- covariant :: TyCon -> Bool
-- covariant = all pos . concatMap dataConOrigArgTys . tyConDataCons
--   where
--     pos, neg :: Type -> Bool
--     pos (FunTy t1 t2) = neg t1 && pos t2
--     pos _ = True
--     neg (FunTy t1 t2) = pos t1 && neg t2
--     neg (TyConApp _ _) = False -- These cases are overapproximate
--     neg (TyVarTy _) = False
--     neg _ = True



-- Get the tycon from a datatype
tyconOf :: DataType d -> d
tyconOf (Base d) = d
tyconOf (Inj _ d) = d

type Type n = TypeGen n TyCon

-- Monomorphic types parameterised by type constructors
data TypeGen n d
  = Var Name
  | App (TypeGen n d) (TypeGen n d)
  | Data (Sized [] n (DataType d)) (Sized [] n [TypeGen n d])
  | TypeGen n d :=> TypeGen n d
  | Lit IfaceTyLit
  | Ambiguous -- Ambiguous hides higher-ranked types and casts
  deriving (Functor, Foldable, Traversable)

-- Clone of a Outputable Core.Type
instance Outputable d => Outputable (TypeGen n d) where
  ppr = prpr ppr

instance (Binary d) => Binary (TypeGen 1 d) where
  put_ bh (Var a) = put_ bh (0 :: Int) >> put_ bh a
  put_ bh (App a b) = put_ bh (1 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Data d as) = put_ bh (2 :: Int) >> put_ bh (d S.!! 0) >> put_ bh (as S.!! 0)
  put_ bh (a :=> b) = put_ bh (3 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Lit l) = put_ bh (4 :: Int) >> put_ bh l
  put_ bh Ambiguous = put_ bh (5 :: Int)

  get bh = do
    c <- get bh
    case c :: Int of
      0 -> Var <$> get bh
      1 -> App <$> get bh <*> get bh
      2 -> Data <$> (unsafeFromList' <$> get bh) <*> ((unsafeFromList' <$>) $ concatThroughMonad [get bh])
      3 -> (:=>) <$> get bh <*> get bh
      4 -> Lit <$> get bh
      5 -> return Ambiguous
      _ -> pprPanic "Invalid binary file!" $ ppr c

instance Outputable d => Refined (TypeGen n d) where
  domain (App a b) = domain a <> domain b
  domain (Data d as) = foldMap domain d <> foldMap (foldMap domain) as
  domain (a :=> b) = domain a <> domain b
  domain _ = mempty

  rename x y (App a b) = App (rename x y a) (rename x y b)
  rename x y (Data d as) = Data (fmap (rename x y) d) (fmap (rename x y <$>) as)
  rename x y (a :=> b) = rename x y a :=> rename x y b
  rename _ _ t = t

  prpr m = pprTy topPrec
    where
      pprTy :: Outputable d => PprPrec -> TypeGen n d -> SDoc
      pprTy _ (Var a) = ppr a
      pprTy prec (App t1 t2) = hang (pprTy prec t1) 2 (pprTy appPrec t2)
      pprTy _ (Data d as) = hang (hcat (prpr m <$> (toList d))) 2 $ sep [hcat $ [text "@"] ++ fmap (pprTy appPrec) a | a <- (toList as)]
      pprTy prec (t1 :=> t2) = maybeParen prec funPrec $ sep [pprTy funPrec t1, arrow, pprTy prec t2]
      pprTy _ (Lit l) = ppr l
      pprTy _ Ambiguous = text "<?>"

-- Inject a sort into a refinement environment
-- inj :: Int -> TypeGen d -> TypeGen d
-- inj _ (Var a) = Var a
-- inj x (App a b) = App (inj x a) (inj x b)
-- inj x (Data (Base b) as) = Data (Base b) (inj x <$> as)
-- inj x (Data (Inj _ d) as) = Data (Inj x d) (inj x <$> as)
-- inj x (a :=> b) = inj x a :=> inj x b
-- inj _ (Lit l) = Lit l
-- inj _ Ambiguous = Ambiguous

-- Decompose a functions into its arguments and eventual return type
decompType :: TypeGen n d -> ([TypeGen n d], TypeGen n d)
decompType (a :=> b) = first (++ [a]) (decompType b)
decompType a = ([], a)

-- Type variable substitution
subTyVar :: Outputable d => Name -> TypeGen n d -> TypeGen n d -> TypeGen n d
subTyVar a t (Var a')
  | a == a' = t
  | otherwise = Var a'
subTyVar a t (App x y) = applyType (subTyVar a t x) (subTyVar a t y)
subTyVar a t (Data d as) = Data d (fmap (subTyVar a t <$>) as)
subTyVar a t (x :=> y) = subTyVar a t x :=> subTyVar a t y
subTyVar _ _ t = t

-- Unsaturated type application
applyType :: Outputable d => TypeGen n d -> TypeGen n d -> TypeGen n d
applyType (Var a) t = App (Var a) t
applyType (App a b) t = App (App a b) t
applyType (Data d as) t = Data d (fmap (++ [t]) as)
applyType Ambiguous _ = Ambiguous
applyType a b = pprPanic "The type is already saturated!" $ ppr (a, b)
