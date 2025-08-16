module Cats.Binary where

import Cats.Category
import Cats.CrossProduct
import Cats.Functor

type BINARY_OP c = (c × c) --> c

-- Typing '☼' ` S U`
type (☼) ::
  forall {i}.
  forall (k :: CATEGORY i).
  i ->
  i ->
  BINARY_OP k ->
  i
type (☼) l r p = Act p '(l, r)
