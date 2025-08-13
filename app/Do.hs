{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall -Werror -Wextra #-}

module Do where

import Data.Proxy
import Data.Type.Equality (type (~))
import Defs

bindImpl ::
  forall
    {d}
    (m :: Types --> Types)
    a
    b
    {f :: Types --> d}
    {g :: d --> Types}.
  ( m ~ (g • f),
    f ⊣ g
  ) =>
  Proxy b ->
  Act m a ->
  (a -> Act m b) ->
  Act m b
bindImpl _ ma t =
  join @m @b
    (map m t ma :: Act (m • m) b)

newtype BindDo m
  = BindDo
      ( forall a b.
        Proxy b ->
        Act m a ->
        (a -> Act m b) ->
        Act m b
      )

newtype PureDo m
  = PureDo
      (forall a. a -> Act m a)

type MonadDo m =
  forall r.
  ( ( ?bind :: BindDo m,
      ?pure :: PureDo m
    ) =>
    Act m r
  ) ->
  Act m r

(>>=) :: forall m a b. (?bind :: BindDo m) => Act m a -> (a -> Act m b) -> Act m b
(>>=) = let BindDo f = ?bind in f @a (Proxy @b)

pure :: forall m a. (?pure :: PureDo m) => a -> Act m a
pure = let PureDo u = ?pure in u

makeBind ::
  forall (m :: Types --> Types) {f} {g}.
  (Monad m, m ~ (g • f)) =>
  BindDo m
makeBind = BindDo (bindImpl @m)

makePure ::
  forall (m :: Types --> Types) {f} {g}.
  (Monad m, m ~ (g • f)) =>
  PureDo m
makePure = PureDo (unit @m)

with ::
  forall (m :: Types --> Types) {f} {g}.
  (Monad m, m ~ (g • f)) =>
  MonadDo m
with t = do
  let ?bind = makeBind @m
  let ?pure = makePure @m
  t
