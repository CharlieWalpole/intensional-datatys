{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Intensional.EnvSums.SumType where


import Intensional.Scheme
import qualified Data.Map as M
import Intensional.Types
import Outputable
import Data.Sized(Sized)
import qualified Data.Sized as S
import GHC.TypeNats
import Intensional.InferM(Context)
import GHC (Name)


sumEnvs :: Context n -> Context m -> Context (n+m)
sumEnvs l r = M.fromList [(S.append n1 n2, sumSchemes s1 s2) | (n1, s1) <- M.assocs l, (n2, s2) <- M.assocs r]

sumSchemes :: Scheme n -> Scheme m -> Scheme (n+m)
sumSchemes l r = l { body = res } where
    res = sumTypes (body l) (body r)

sumTypes :: Type n -> Type m -> Type (n+m)
sumTypes (Var a) (Var b) | a == b = Var a
sumTypes (App l r) (App l' r') = App (sumTypes l l') (sumTypes r r')
sumTypes (Data ds xs) (Data ds' xs') = Data (S.append ds ds') (S.append xs xs')
--sumTypes (Data (Base b) xs) (Data (Base b') ys) 
--    | b == b' && xs == ys = Data (Base b) (map (fmap (\x -> [Just x])) xs)
--sumTypes (Data (Inj x d) xs) (Data (Inj _ d') ys) = Data (Inj x resd) tres where
--    resd = [Just d, Just d']
--    tres = (map (fmap (\t -> [Just t])) (xs++ys))
sumTypes (u1 :=> u2) (u1' :=> u2') = (sumTypes u1 u1') :=> (sumTypes u2 u2')
sumTypes (Lit l) (Lit r) | l == r = Lit l
sumTypes Ambiguous Ambiguous = Ambiguous
sumTypes l r = error $ "Sum Type does not exist. l: " ++ (showSDocUnsafe $ ppr l) ++ " ; r: " ++ (showSDocUnsafe $ ppr r)

projectEnvs :: KnownNat n => Context n -> Sized [] n (Context 1)
projectEnvs = (fmap M.fromList) . h . g . f . M.toList where
    f :: KnownNat n => [(Sized [] n Name, Scheme n)] -> [Sized [] n (Name, Scheme 1)]
    f = (map (\(xs, ys) -> S.zip xs (projectSchemes ys)))

    g :: KnownNat n => [Sized [] n (Name, Scheme 1)] -> Sized [] n ([Name], [Scheme 1])
    g = (foldr k (S.replicate' ([], []))) . (map ((\(x, y) -> ([x], [y])) <$>))

    k :: Sized [] n ([Name], [Scheme 1]) -> Sized [] n ([Name], [Scheme 1]) -> Sized [] n ([Name], [Scheme 1])
    k = S.zipWith (\(ns, ts) (ns', ts') -> (ns++ns', ts++ts'))

    h :: Sized [] n ([Name], [Scheme 1]) -> Sized [] n [(Sized [] 1 Name, Scheme 1)]
    h = fmap (\(ns, ts) -> zip (map S.singleton ns) ts)

projectSchemes :: KnownNat n => Scheme n -> Sized [] n (Scheme 1)
projectSchemes (Scheme tvs bvs bdy cs) = fmap (\x -> Scheme tvs bvs x cs) (projectTypes bdy)

projectTypes :: KnownNat n => Type n -> Sized [] n (Type 1)
projectTypes (Var a) = S.replicate' (Var a)
projectTypes (Lit l) = S.replicate' (Lit l)
projectTypes Ambiguous = S.replicate' Ambiguous
projectTypes (App l r) = S.zipWith App (projectTypes l) (projectTypes r)
projectTypes (l :=> r) = S.zipWith (:=>) (projectTypes l) (projectTypes r)
projectTypes (Data ds xs) = S.zipWith Data (S.singleton <$> ds) (S.singleton <$> xs)
