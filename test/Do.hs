{-# LANGUAGE RebindableSyntax #-}

module Do where

import Cats
import Data.Proxy
import Data.Type.Equality (type (~))

bindImpl ::
  forall
    {d}
    m
    a
    b
    {f :: Types --> d}
    {g :: d --> Types}.
  ( m ~ '(g, f),
    f ⊣ g
  ) =>
  Proxy b ->
  Act (Act Composing m) a ->
  (a -> Act (Act Composing m) b) ->
  Act (Act Composing m) b
bindImpl _ ma t =
  join
    (type (Act Composing m))
    b
    ( map
        (type (Act Composing m))
        t
        ma ::
        Act (Act Composing m • Act Composing m) b
    )

newtype BindDo m
  = BindDo
      ( forall a b.
        Proxy b ->
        Act (Act Composing m) a ->
        (a -> Act (Act Composing m) b) ->
        Act (Act Composing m) b
      )

newtype PureDo m
  = PureDo
      (forall a. a -> Act (Act Composing m) a)

type AdjunctionMonadDo m =
  forall r.
  ( ( ?bind :: BindDo m,
      ?pure :: PureDo m
    ) =>
    Act (Act Composing m) r
  ) ->
  Act (Act Composing m) r

(>>=) ::
  forall m a b.
  (?bind :: BindDo m) =>
  Act (Act Composing m) a ->
  (a -> Act (Act Composing m) b) ->
  Act (Act Composing m) b
(>>=) = let BindDo f = ?bind in f @a (Proxy @b)

pure ::
  forall m a.
  (?pure :: PureDo m) =>
  a ->
  Act (Act Composing m) a
pure = let PureDo u = ?pure in u

makeBind ::
  forall {d} {f :: Types --> d} {g :: d --> Types} m.
  (AdjunctionMonad (Act Composing m), m ~ '(g, f)) =>
  BindDo m
makeBind = BindDo (bindImpl @m)

makePure ::
  forall {d} {f :: Types --> d} {g :: d --> Types} m.
  (AdjunctionMonad (Act Composing m), m ~ '(g, f)) =>
  PureDo m
makePure = PureDo (unit m _)

with ::
  forall {d} {f :: Types --> d} {g :: d --> Types}.
  forall m ->
  (AdjunctionMonad (Act Composing m), m ~ '(g, f)) =>
  AdjunctionMonadDo m
with m t = do
  let ?bind = makeBind @m
  let ?pure = makePure @m
  t
