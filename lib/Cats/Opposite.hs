module Cats.Opposite where

import Cats.Adjoint
import Cats.Associative
import Cats.Binary
import Cats.Category
import Cats.CrossProduct
import Cats.Exponential
import Cats.Functor
import Cats.Monoidal

data Op :: CATEGORY i -> CATEGORY i where
  OP :: {runOP :: k b a} -> Op k a b

type instance Obj (Op k) i = i ∈ k

instance (Semigroupoid k) => Semigroupoid (Op k) where
  OP g ∘ OP f = OP (f ∘ g)

instance (Category k) => Category (Op k) where
  identity o = OP (identity o)

-- | Reverse both the source and target categories of a functor.
-- Its object action is unchanged; arrows are mapped underneath 'OP'.
type data OpFunctor :: (d --> c) -> (Op d --> Op c)

type instance Act (OpFunctor f) x = Act f x

instance (Functor f) => Functor (OpFunctor f) where
  map _ (OP ab) = OP (map f ab)

-- | Taking opposites reverses the direction of a natural transformation.
-- As with 'EXP', naturality is an obligation of the supplied transformation.
opNat :: (f ~> g) -> (OpFunctor g ~> OpFunctor f)
opNat t = EXP \(type x) -> OP (t $$ x)

unOpNat :: (OpFunctor g ~> OpFunctor f) -> (f ~> g)
unOpNat t = EXP \(type x) -> runOP (t $$ x)

-- | Double reversal preserves the endpoints and composition order.
opOp :: k a b -> Op (Op k) a b
opOp f = OP (OP f)

unOpOp :: Op (Op k) a b -> k a b
unOpOp (OP (OP f)) = f

-- | These two functors are inverse on objects and arrows. The categories
-- remain distinct Haskell types, so crossing between them is explicit.
type data ToDoubleOp :: k --> Op (Op k)

type instance Act ToDoubleOp x = x

instance (Category k) => Functor (ToDoubleOp @k) where
  map _ = opOp

type data FromDoubleOp :: Op (Op k) --> k

type instance Act FromDoubleOp x = x

instance (Category k) => Functor (FromDoubleOp @k) where
  map _ = unOpOp

-- | An adjunction f -| g gives OpFunctor g -| OpFunctor f.
-- The dual unit is the original counit under OP, and conversely.
instance (f ⊣ g) => OpFunctor g ⊣ OpFunctor f where
  rightToLeft _ _ (OP t) = OP (leftToRight f g t)
  leftToRight _ _ (OP t) = OP (rightToLeft g f t)

-- | The same tensor on the opposite category. Unlike OpFunctor p, its
-- domain is (Op k × Op k), rather than Op (k × k).
-- Tensor arguments keep their order; only arrows are reversed.
type data OpTensor :: BINARY_OP k -> BINARY_OP (Op k)

type instance Act (OpTensor p) x = Act p x

instance (Functor p) => Functor (OpTensor p) where
  map _ (OP l :×: OP r) = OP (map p (l :×: r))

instance (Associative p) => Associative (OpTensor p) where
  lassoc _ a b c = OP (rassoc p a b c)
  rassoc _ a b c = OP (lassoc p a b c)

type instance MonoidalEmpty (OpTensor p) = MonoidalEmpty p

instance (Monoidal p) => Monoidal (OpTensor p) where
  idl = OP (coidl @_ @p)
  coidl = OP (idl @_ @p)
  idr = OP (coidr @_ @p)
  coidr = OP (idr @_ @p)
