module Intensional.Guard where

import qualified GhcPlugins as GHC
import Binary 
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap

import Intensional.Types
import Intensional.Constructors

import Intensional.State

-- data Named a = Named {toPair :: (GHC.Name, a)}
--   deriving (Eq, Functor)

-- instance Semigroup a => Semigroup (Named a) where
--   Named (n, ks1) <> Named (_, ks2) = Named (n, ks1 <> ks2)

-- instance GHC.Uniquable (Named a) where
--   getUnique (Named (n, _)) = GHC.getUnique n

-- instance Binary a => Binary (Named a) where
--   put_ bh = put_ bh . toPair
--   get bh = Named <$> Binary.get bh


-- A set of simple inclusion constraints, i.e. k in X(d), grouped by X(d)
newtype Guard
  = Guard
      { 
        groups :: Map (RVar, State GHC.Name GHC.Name) (GHC.UniqSet GHC.Name, Set.Set (EqConstraint GHC.Name GHC.Name))
      }
  deriving (Eq)

instance Semigroup Guard where
  Guard g <> Guard g' = Guard (Map.unionWith GHC.unionUniqSets g g')

instance Monoid Guard where
  mempty = Guard mempty

instance GHC.Outputable Guard where
  ppr = prpr GHC.ppr

isEmpty :: Guard -> Bool
isEmpty (Guard g) = Map.null g

toList :: Guard -> [(Int, GHC.Name, GHC.Name)]
toList (Guard g) =
  [ (x, d, k) | ((x,d), ks) <- Map.toList g, k <- GHC.nonDetEltsUniqSet ks ]

fromList :: [(Int, GHC.Name, GHC.Name)] -> Guard
fromList = foldMap (\(x, d, k) -> singleton [k] x d)

typedVars :: Guard -> Set (RVar, GHC.Name)
typedVars (Guard g) = Map.keysSet g

instance Binary Guard where
  put_ bh = put_ bh . toList
  get bh = fromList <$> get bh

instance Refined Guard where
  domain (Guard g) = 
      Set.foldl' (\acc (x,_) -> IntSet.insert x acc) mempty (Map.keysSet g)

  rename x y (Guard g) =
    Guard (Map.foldrWithKey (\(z,d) ks m -> Map.insertWith GHC.unionUniqSets (if z == x then y else z, d) ks m) mempty g)

  prpr m n (Guard g) = GHC.pprWithCommas pprGuardAtom guardList
    where
    pprGuardAtom ((x,d), ks) = GHC.hsep [GHC.ppr ks, GHC.text "in", prpr m n (Dom (Inj x d))]
    guardList = fmap (\(x,(y, eqs)) -> (x, GHC.nonDetEltsUniqSet y)) (Map.toList g)

lookup :: RVar -> State GHC.Name GHC.Name -> Guard -> Maybe (GHC.UniqSet GHC.Name, Set.Set (EqConstraint GHC.Name GHC.Name))
lookup x d (Guard g) = Map.lookup (x,d) g

delete :: GHC.Name -> RVar -> State GHC.Name GHC.Name -> Guard -> Guard
delete k x d (Guard g) = Guard (Map.alter del (x,d) g)
  where
    del Nothing = Nothing
    del (Just (ks, eqs)) =
      let ks' = GHC.delOneFromUniqSet ks k
      in if GHC.isEmptyUniqSet ks' then Nothing else Just (ks', eqs)

deleteAll :: [GHC.Name] -> RVar -> State GHC.Name GHC.Name -> Guard -> Guard
deleteAll ms x d (Guard g) = Guard (Map.alter del (x,d) g)
  where
    del Nothing = Nothing
    del (Just (ks, eqs)) =
      let ks' = GHC.delListFromUniqSet ks ms
      in if GHC.isEmptyUniqSet ks' then Nothing else Just (ks', eqs)

-- A guard literal
-- Ignorning possibly trivial guards (e.g. 1-constructor types has already
-- happened in InferM.branch)
singleton :: [GHC.Name] -> RVar -> State GHC.Name GHC.Name -> Guard
singleton ks x d =
  Guard (Map.singleton (x, d) (GHC.addListToUniqSet mempty ks, Set.empty))

-- guardsFromList :: [GHC.Name] -> DataType GHC.Name -> Guard
-- guardsFromList ks (Inj x d) = foldr (\k gs -> singleton k (Inj x d) <> gs) mempty ks

impliedBy :: Guard -> Guard -> Bool
impliedBy (Guard g) (Guard g') =
    Map.isSubmapOfBy keyInclusion g' g
  where
    keyInclusion (u1, eq1) (u2, eq2) =
      {-# SCC keyInclusion #-}
      IntMap.isSubmapOfBy (\_ _ -> True) (GHC.ufmToIntMap $ GHC.getUniqSet u1) (GHC.ufmToIntMap $ GHC.getUniqSet u2) && Set.isSubsetOf eq1 eq2