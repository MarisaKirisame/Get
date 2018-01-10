{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, EmptyCase, FlexibleContexts, UndecidableInstances, DeriveFunctor, DeriveAnyClass #-}

module Control.Get where

data And x y = And x y
data Or x y = OrLeft x | OrRight y deriving (Functor, Applicative, Monad)

data Bottom
fromBot :: Bottom -> a
fromBot bot = case bot of

data Top = Top

class GetAux as orAs from orFrom self where
  getAux :: And from orFrom -> self -> Or orAs as

class GetAux as Bottom from Top from => Get as from where
  get :: from -> as
  get fr =
    case getAux (And fr Top) fr of
      OrLeft x -> fromBot x
      OrRight x -> x

instance GetAux as Bottom from Top from => Get as from

instance GetAux Top a b c d where
  getAux _ _ = OrRight Top

instance GetAux a b c d e => GetAux a b Top (And c d) e where
  getAux (And _ x) = getAux x

instance (GetAux a c d e f, GetAux b c d e f) => GetAux (And a b) c d e f where
  getAux a s =
    do
      l <- getAux a s
      r <- getAux a s
      return $ And l r

instance GetAux a (Or b c) d e f => GetAux (Or a b) c d e f where
  getAux a s =
    case getAux a s of
      OrLeft (OrLeft b) -> OrRight (OrRight b)
      OrLeft (OrRight c) -> OrLeft c
      OrRight a -> OrRight (OrLeft a)

instance GetAux a b Bottom c d where
  getAux (And bot _) = fromBot bot

instance (Get a' a, Get b b') => GetAux (a -> b) c (a' -> b') d e where
  getAux (And f a) s = _