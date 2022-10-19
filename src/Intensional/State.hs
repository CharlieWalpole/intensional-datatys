{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable, DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
    
module Intensional.State (
    State(..),
    depth,
    bound,
    substituteSVar,
    getSVar,
    isTriviallyEqual,
    isTriviallyUnequal,
    EqConstraint(..),
    SVar
    ) 
where

import qualified Data.Set as S
import GHC.Generics hiding (prec)
import Binary
import Data.Hashable

type SVar = Int

data State k d = Var SVar d
               | Delta k Int (State k d) d
    deriving (Functor, Traversable, Foldable, Generic)

data EqConstraint k d = Eq (State k d) (State k d)

instance (Binary k, Binary d) => Binary (State k d) where
    put_ bh (Var s u) = put_ bh False >> put_ bh s >> put_ bh u
    put_ bh (Delta k i s u) =  put_ bh True >> put_ bh k >> put_ bh i >> put_ bh s >> put_ bh u
    get bh =
        get bh >>= \case
            False -> Var <$> get bh <*> get bh
            True -> Delta <$> get bh <*> get bh <*> get bh <*> get bh

depth :: State k d -> Integer
depth (Var _ _) = 0
depth (Delta _ _ del _) = 1 + depth del

bound :: Ord t => (k -> Int -> t -> t) -> (SVar -> S.Set t) -> State k d -> S.Set t
bound _ dBound (Var a _) = dBound a
bound lkp dBound (Delta k i a _) =  S.map (lkp k i) $ bound lkp dBound a

substituteSVar :: (k -> Int -> t -> t) -> State k d -> (SVar -> t) -> t
substituteSVar _ (Var s _) val = val s
substituteSVar lkp (Delta k i s _) val = lkp k i $ substituteSVar lkp s val

getSVar :: State k d -> SVar
getSVar (Var s _) = s
getSVar (Delta _ _ s _) = getSVar s

isTriviallyEqual :: Ord t => (k -> Int -> t -> t) -> (SVar -> S.Set t) -> EqConstraint k d -> Bool
isTriviallyEqual lkp dBound (Eq l r) = ret where
    singleVar = getSVar l == getSVar r
    lBound = S.toList (dBound (getSVar l))
    rBound = S.toList (dBound (getSVar r))
    pairsToTest = if singleVar then map (\x -> (x, x)) lBound else cartesian lBound rBound
    testResults = [substituteSVar lkp l (\_ -> x) == substituteSVar lkp r (\_ -> y) | (x, y) <- pairsToTest]
    ret = foldr (&&) True testResults

    cartesian :: [a] -> [b] -> [(a, b)]
    cartesian xs ys = [(x, y) | x <- xs, y <- ys]

isTriviallyUnequal :: Ord t => (k -> Int -> t -> t) -> (SVar -> S.Set t) -> EqConstraint k d -> Bool
isTriviallyUnequal lkp dBound (Eq l r) = ret where
    singleVar = getSVar l == getSVar r
    lBound = S.toList (dBound (getSVar l))
    rBound = S.toList (dBound (getSVar r))
    pairsToTest = if singleVar then map (\x -> (x, x)) lBound else cartesian lBound rBound
    testResults = [substituteSVar lkp l (\_ -> x) /= substituteSVar lkp r (\_ -> y) | (x, y) <- pairsToTest]
    ret = foldr (&&) True testResults

    cartesian :: [a] -> [b] -> [(a, b)]
    cartesian xs ys = [(x, y) | x <- xs, y <- ys]

instance Eq k => Eq (State k d) where
    (Var s _) == (Var s' _) = s == s'
    (Delta k i s _) == (Delta k' i' s' _) = k == k' && i == i' && s == s'
    _ == _ = False

instance (Hashable d, Hashable k) => Hashable (State k d)

instance Eq k => Eq (EqConstraint k d) where
    (Eq l r) == (Eq l' r') = (l == l' && r == r') || (l == r' && r == l')

--If needed write a biFunctor instance ('constructor type' then 'underlying datatype')
--instance Functor State where
--    fmap _ (Var s) = Var s
--    fmap f (Delta k i s) = Delta (f k) i (fmap f s)

--Requires Functor instance for State
--instance Functor EqConstraint where
--    fmap f (Eq l r) = Eq (fmap f l) (fmap f r)
