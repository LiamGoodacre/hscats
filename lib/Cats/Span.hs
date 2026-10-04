module Cats.Span where

import Cats.Adjoint
import Cats.Category
import Cats.CrossProduct
import Cats.Curry
import Cats.Delta
import Cats.Flip
import Cats.Functor
import Cats.Opposite
import Data.Kind (Type)

-- | A span @a <- x -> b@, with its apex @x@ kept explicit.
--
-- These are diagrams in @k@. Composing spans as arrows between their endpoints
-- would additionally require pullbacks (and identifying isomorphic apices),
-- so there is no 'Category' instance for spans themselves here.
data Span :: CATEGORY i -> i -> i -> i -> Type where
  Span ::
    { spanLeft :: k x a,
      spanRight :: k x b
    } ->
    Span k x a b

-- | A cospan @a -> x <- b@, dual to a span. Composition would require pushouts.
data Cospan :: CATEGORY i -> i -> i -> i -> Type where
  Cospan ::
    { cospanLeft :: k a x,
      cospanRight :: k b x
    } ->
    Cospan k x a b

swapSpan :: Span k x a b -> Span k x b a
swapSpan (Span l r) = Span r l

swapCospan :: Cospan k x a b -> Cospan k x b a
swapCospan (Cospan l r) = Cospan r l

-- Duality: a span in k is a cospan in Op k, and conversely.

opSpan :: Span k x a b -> Cospan (Op k) x a b
opSpan (Span l r) = Cospan (OP l) (OP r)

unOpSpan :: Cospan (Op k) x a b -> Span k x a b
unOpSpan (Cospan (OP l) (OP r)) = Span l r

opCospan :: Cospan k x a b -> Span (Op k) x a b
opCospan (Cospan l r) = Span (OP l) (OP r)

unOpCospan :: Span (Op k) x a b -> Cospan k x a b
unOpCospan (Span (OP l) (OP r)) = Cospan l r

-- Applying a functor to the whole diagram.

mapSpan ::
  forall {d} {c} x a b.
  forall (f :: d --> c) ->
  (Functor f, x ∈ d, a ∈ d, b ∈ d) =>
  Span d x a b -> Span c (Act f x) (Act f a) (Act f b)
mapSpan f (Span l r) = Span (map f l) (map f r)

mapCospan ::
  forall {d} {c} x a b.
  forall (f :: d --> c) ->
  (Functor f, x ∈ d, a ∈ d, b ∈ d) =>
  Cospan d x a b -> Cospan c (Act f x) (Act f a) (Act f b)
mapCospan f (Cospan l r) = Cospan (map f l) (map f r)

-- A pair of legs is one arrow in the product category:
--   Span k x a b   ≅ (k × k) (Act (Δ₂ k) x) '(a, b)
--   Cospan k x a b ≅ (k × k) '(a, b) (Act (Δ₂ k) x)

spanToArrow :: Span k x a b -> (k × k) '(x, x) '(a, b)
spanToArrow (Span l r) = l :×: r

spanFromArrow :: (k × k) '(x, x) '(a, b) -> Span k x a b
spanFromArrow (l :×: r) = Span l r

cospanToArrow :: Cospan k x a b -> (k × k) '(a, b) '(x, x)
cospanToArrow (Cospan l r) = l :×: r

cospanFromArrow :: (k × k) '(a, b) '(x, x) -> Cospan k x a b
cospanFromArrow (l :×: r) = Cospan l r

-- | Spans vary contravariantly in their apex and covariantly in both feet.
-- This is the hom functor of @k × k@ with its source restricted along @Δ₂ k@.
type data Spans :: forall (k :: CATEGORY i) -> (Op k × (k × k)) --> Types

type instance Act (Spans k) o = Span k (Fst o) (Fst (Snd o)) (Snd (Snd o))

instance (Category k) => Functor (Spans k) where
  map _ (OP apex :×: (l :×: r)) (Span xa xb) =
    Span (l ∘ xa ∘ apex) (r ∘ xb ∘ apex)

-- | Cospans vary covariantly in their apex and contravariantly in both feet.
type data Cospans :: forall (k :: CATEGORY i) -> (k × (Op k × Op k)) --> Types

type instance Act (Cospans k) o = Cospan k (Fst o) (Fst (Snd o)) (Snd (Snd o))

instance (Category k) => Functor (Cospans k) where
  map _ (apex :×: (OP l :×: OP r)) (Cospan ax bx) =
    Cospan (apex ∘ ax ∘ l) (apex ∘ bx ∘ r)

-- Fixing the apex gives a functor of the two endpoints.

-- | @Act (SpansFrom k x) '(a, b) = Span k x a b@.
type SpansFrom :: forall (k :: CATEGORY i) -> i -> (k × k) --> Types
type SpansFrom k x = Curry₂ (Spans k) x

-- | @Act (CospansTo k x) '(a, b) = Cospan k x a b@.
type CospansTo :: forall (k :: CATEGORY i) -> i -> (Op k × Op k) --> Types
type CospansTo k x = Curry₂ (Cospans k) x

-- Fixing the endpoints instead gives a (co)presheaf of possible apices.
-- Curry₁ (Spans k) and Curry₁ (Cospans k) expose the corresponding families
-- of endpoint functors, with natural transformations induced by apex arrows.

-- | @Act (SpansBetween k a b) x = Span k x a b@.
type SpansBetween :: forall (k :: CATEGORY i) -> i -> i -> Op k --> Types
type SpansBetween k a b = Curry₂ (Flip (Spans k)) '(a, b)

-- | @Act (CospansBetween k a b) x = Cospan k x a b@.
type CospansBetween :: forall (k :: CATEGORY i) -> i -> i -> k --> Types
type CospansBetween k a b = Curry₂ (Flip (Cospans k)) '(a, b)

-- A right adjoint to the diagonal represents spans by arrows into products;
-- a left adjoint represents cospans by arrows out of coproducts.
-- For Types, use (∧) and (∨), giving x -> (a, b) and Either a b -> x.

spanToProduct ::
  forall {k} x a b.
  forall (p :: (k × k) --> k) ->
  (Δ₂ k ⊣ p, x ∈ k, a ∈ k, b ∈ k) =>
  Span k x a b -> k x (Act p '(a, b))
spanToProduct p s = leftToRight (Δ₂ k) p (spanToArrow s)

spanFromProduct ::
  forall {k} x a b.
  forall (p :: (k × k) --> k) ->
  (Δ₂ k ⊣ p, x ∈ k, a ∈ k, b ∈ k) =>
  k x (Act p '(a, b)) -> Span k x a b
spanFromProduct p f = spanFromArrow (rightToLeft p (Δ₂ k) f)

cospanToCoproduct ::
  forall {k} x a b.
  forall (p :: (k × k) --> k) ->
  (p ⊣ Δ₂ k, x ∈ k, a ∈ k, b ∈ k) =>
  Cospan k x a b -> k (Act p '(a, b)) x
cospanToCoproduct p s = rightToLeft (Δ₂ k) p (cospanToArrow s)

cospanFromCoproduct ::
  forall {k} x a b.
  forall (p :: (k × k) --> k) ->
  (p ⊣ Δ₂ k, x ∈ k, a ∈ k, b ∈ k) =>
  k (Act p '(a, b)) x -> Cospan k x a b
cospanFromCoproduct p f = cospanFromArrow (leftToRight p (Δ₂ k) f)
