{-# LANGUAGE
  MultiParamTypeClasses,
  FlexibleInstances,
  EmptyCase,
  FlexibleContexts,
  UndecidableInstances,
  DataKinds,
  KindSignatures,
  FunctionalDependencies,
  TypeFamilies,
  ConstraintKinds,
  UndecidableSuperClasses
#-}

module Control.Get where

import Data.Singletons.Prelude.Bool
import Data.Proxy

data And x y = And x y
data Or x y = OrLeft x | OrRight y

data Bottom
fromBot :: Bottom -> a
fromBot bot = case bot of

data Top = Top

fromVal :: a -> Proxy a
fromVal _ = Proxy

class GetAux as from self (ok :: Bool) | as from self -> ok where
  getAux :: self -> from -> Proxy as -> (If ok as (), Sing ok)

class GetAux as from from True => Get as from where
  get :: from -> as
  get f = res where
    res = fst $ getAux f f (fromVal res)

instance GetAux as from from True => Get as from

instance GetAux a Top b False where
  getAux _ _ _ = ((), SFalse)

instance c ~ True => GetAux Top a b c where
  getAux _ _ _ = (Top, STrue)

instance GetAux a Bottom b True where
  getAux _ bot _ = (fromBot bot, STrue)

andLeftP :: Proxy (And l r) -> Proxy l
andLeftP _ = Proxy
andRightP :: Proxy (And l r) -> Proxy r
andRightP _ = Proxy

class GetAuxAnd a b c d (e :: Bool) (f :: Bool) | b c d f -> e where
  getAuxAnd :: d -> c -> (If f a (), Sing f) -> Proxy (And a b) -> (If e (And a b) (), Sing e)

instance GetAuxAnd a b c d False False where
  getAuxAnd _ _ _ _ = ((), SFalse)

instance GetAux b c d e => GetAuxAnd a b c d e True where
  getAuxAnd d c (a, _) p = let (b, s) = getAux d c (andRightP p) in
    case s of
      STrue -> (And a b, STrue)
      SFalse -> ((), SFalse)

instance (GetAux a c d f, GetAuxAnd a b c d e f) => GetAux (And a b) c d e where
  getAux d c p = getAuxAnd d c (getAux d c (andLeftP p)) p

orLeftP :: Proxy (Or l r) -> Proxy l
orLeftP _ = Proxy
orRightP :: Proxy (Or l r) -> Proxy r
orRightP _ = Proxy

class GetAuxOr a b c d (e :: Bool) (f :: Bool) | b c d f -> e where
  getAuxOr :: d -> c -> (If f a (), Sing f) -> Proxy (Or a b) -> (If e (Or a b) (), Sing e)

instance GetAuxOr a b c d True True where
  getAuxOr _ _ (a, _) _ = (OrLeft a, STrue)

instance GetAux b c d e => GetAuxOr a b c d e False where
  getAuxOr d c _ p = let (b, s) = getAux d c (orRightP p) in
    case s of
      STrue -> (OrRight b, STrue)
      SFalse -> ((), SFalse)

instance (GetAux a c d f, GetAuxOr a b c d e f) => GetAux (Or a b) c d e where
  getAux d c p = getAuxOr d c (getAux d c (orLeftP p)) p

newtype Protected x = Protected { runProtected :: x }

instance GetAux a b b d => GetAux a (Protected b) c d where
  getAux _ (Protected b) p = getAux b b p
