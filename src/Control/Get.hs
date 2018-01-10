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
import Data.Constraint (Dict(..), withDict)

data And x y = And x y
data Or x y = OrLeft x | OrRight y

data Bottom
fromBot :: Bottom -> a
fromBot bot = case bot of

data Top = Top

fromVal :: a -> Proxy a
fromVal _ = Proxy

-- Lattice Specific Operation so they need to be resolved first. Write your instance at TryGetAux.
class TryGet as from self ok | as from self -> ok where
  tryGetSing :: Proxy self -> Proxy from -> Proxy as -> Sing ok
  tryGetVal :: self -> from -> Proxy as -> If ok as ()
  tryGet :: self -> from -> Proxy as -> (If ok as (), Sing ok)
  tryGet self from p = (tryGetVal self from p, tryGetSing (fromVal self) (fromVal from) p)

class TryGet as from from True => Get as from where
  get :: from -> as
  get f = res where
    res = tryGetVal f f (fromVal res)

instance TryGet as from from True => Get as from

instance TryGet Top from self True where
  tryGetVal _ _ _ = Top
  tryGetSing _ _ _ = STrue

instance ok ~ False => TryGet as Top self ok where
  tryGetVal _ _ _ = ()
  tryGetSing _ _ _ = SFalse

instance TryGet as Bottom self True where
  tryGetVal _ bot _ = fromBot bot
  tryGetSing _ _ _ = STrue

andLeftP :: Proxy (And l r) -> Proxy l
andLeftP _ = Proxy
andRightP :: Proxy (And l r) -> Proxy r
andRightP _ = Proxy

class TryGetAndL a b from self (aOK :: Bool) (andOK :: Bool) | b from self aOK -> andOK where
  tryGetAndLVal :: self -> from -> (If aOK a (), Sing aOK) -> Proxy (And a b) -> If andOK (And a b) ()
  tryGetAndLSing :: Proxy self -> Proxy from -> Sing aOK -> Proxy (And a b) -> Sing andOK

instance TryGetAndL a b from self False False where
  tryGetAndLVal _ _ _ _ = ()
  tryGetAndLSing _ _ _ _ = SFalse

instance TryGet b from self andOK => TryGetAndL a b from self True andOK where
  tryGetAndLVal self from (a, _) p = let (b, s) = tryGet self from (andRightP p) in
    case s of
      STrue -> And a b
      SFalse -> ()
  tryGetAndLSing self from _ p = tryGetSing self from (andRightP p)

instance (TryGet a from self aOK, TryGetAndL a b from self aOK andOK) => TryGet (And a b) from self andOK where
  tryGetVal self from p = tryGetAndLVal self from (tryGet self from (andLeftP p)) p
  tryGetSing self from p = tryGetAndLSing self from (tryGetSing self from (andLeftP p)) p

class TryGetAndR as b self (aOK :: Bool) (andOK :: Bool) | as b self aOK -> andOK where
  tryGetAndRVal :: self -> (If aOK as (), Sing aOK) -> b -> Proxy as -> If andOK as ()
  tryGetAndRSing :: Proxy self -> Sing aOK -> Proxy b -> Proxy as -> Sing andOK

instance TryGetAndR as b self True True where
  tryGetAndRVal _ (a, _) _ _ = a
  tryGetAndRSing _ _ _ _ = STrue

instance TryGet as b self andOK => TryGetAndR as b self False andOK where
  tryGetAndRVal self _ b p = tryGetVal self b p
  tryGetAndRSing self _ from p = tryGetSing self from p

instance (TryGet as a self aOK, TryGetAndR as b self aOK andOK) => TryGet as (And a b) self andOK where
  tryGetVal self (And a b) p = tryGetAndRVal self (tryGet self a p) b p
  tryGetSing self from p = tryGetAndRSing self (tryGetSing self (andLeftP from) p) (andRightP from) p

orLeftP :: Proxy (Or l r) -> Proxy l
orLeftP _ = Proxy
orRightP :: Proxy (Or l r) -> Proxy r
orRightP _ = Proxy

class TryGetOrL a b from self (aOK :: Bool) (orOK :: Bool) | b from self aOK -> orOK where
  tryGetOrLVal :: self -> from -> (If aOK a (), Sing aOK) -> Proxy (Or a b) -> If orOK (Or a b) ()
  tryGetOrLSing :: Proxy self -> Proxy from -> Sing aOK -> Proxy (Or a b) -> Sing orOK

instance TryGetOrL a b from self True True where
  tryGetOrLVal _ _ (a, _) _ = OrLeft a
  tryGetOrLSing _ _ _ _ = STrue

instance TryGet b from self orOK => TryGetOrL a b from self False orOK where
  tryGetOrLVal self from _ p = let (b, s) = tryGet self from (orRightP p) in
    case s of
      STrue -> OrRight b
      SFalse -> ()
  tryGetOrLSing self from _ p = tryGetSing self from (orRightP p)

instance (TryGet a from self aOK, TryGetOrL a b from self aOK orOK) => TryGet (Or a b) from self orOK where
  tryGetVal self from p = tryGetOrLVal self from (tryGet self from (orLeftP p)) p
  tryGetSing self from p = tryGetOrLSing self from (tryGetSing self from (orLeftP p)) p

class TryGetOrR as b self (aOK :: Bool) orOK | as b self aOK -> orOK where
  tryGetOrRVal :: self -> b -> Sing aOK -> Proxy as -> If orOK as ()
  tryGetOrRSing :: Proxy self -> Proxy b -> Sing aOK -> Proxy as -> Sing orOK
  tryGetOrRUnify :: Proxy self -> Proxy b -> Sing aOK -> Proxy as -> Dict (orOK ~ True) -> Dict (aOK ~ True)

instance TryGetOrR as b self False False where
  tryGetOrRVal _ _ _ _ = ()
  tryGetOrRSing _ _ _ _ = SFalse
  tryGetOrRUnify _ _ _ _ x = x

instance TryGet as b self orOK => TryGetOrR as b self True orOK where
  tryGetOrRVal self b _ p = tryGetVal self b p
  tryGetOrRSing self b _ p = tryGetSing self b p
  tryGetOrRUnify _ _ _ _ _ = Dict

instance (TryGet as a self aOK, TryGetOrR as b self aOK orOK) => TryGet as (Or a b) self orOK where
  tryGetVal self o@(OrLeft a) p =
    let
      oP = fromVal o
      orP = orRightP oP
      selfP = fromVal self
      singL = tryGetSing selfP (fromVal a) p
    in
      case tryGetOrRSing (fromVal self) orP singL p of
        STrue -> tryGetOrRUnify selfP orP singL p Dict `withDict` tryGetVal self a p
        SFalse -> ()
  tryGetVal self o@(OrRight b) p = tryGetOrRVal self b (tryGetSing (fromVal self) (orLeftP $ fromVal o) p) p
  tryGetSing self from p = tryGetOrRSing self (orRightP from) (tryGetSing self (orLeftP from) p) p

instance ok ~ True => TryGet a a self ok where
  tryGetVal _ a _ = a
  tryGetSing _ _ _ = STrue

newtype Protected x = Protected { runProtected :: x }

unProtectedP :: Proxy (Protected x) -> Proxy x
unProtectedP _ = Proxy

instance TryGet as from from ok => TryGet as (Protected from) self ok where
  tryGetVal self (Protected from) p = tryGetVal from from p
  tryGetSing _ pFrom p = let from = unProtectedP pFrom in tryGetSing from from p
