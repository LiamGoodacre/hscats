-- | Universal cones and cocones for specific diagrams, and composition of
-- spans/cospans using chosen pullbacks/pushouts.
--
-- @
-- {-# LANGUAGE GHC2024, RequiredTypeArguments #-}
-- import Cats
-- import Prelude qualified as P
--
-- example :: (P.Int, P.Bool)
-- example = factorPullback productPullback P.Int
--             (Span (P.+ 1) P.even) 7
-- -- (8, False)
-- @
--
-- A universal-property witness stores operations and object evidence. Its
-- equations, including uniqueness, are obligations of the provider. The types
-- cannot check equality of arbitrary arrows or that an input cone commutes.
--
-- Two spans with fixed feet represent the same span arrow when an isomorphism
-- of apices commutes with both legs. Chosen pullbacks compose representatives;
-- different choices and bracketings are related by the unique cone-preserving
-- isomorphisms. Their associators must satisfy the pentagon, and their unitors
-- the triangle. These follow from universal uniqueness for lawful choices.
-- Raw apex types need not coincide, so no strict 'Category' instance is given
-- for t'SomeSpan'. One can instead quotient by these isomorphisms, or retain
-- them as coherence data in a bicategory. The dual statements hold for cospans.
module Cats.Pullback where

import Cats.Category
import Cats.Core
import Cats.Opposite
import Cats.Semigroupoid
import Cats.Span
import Cats.TypeEquality ((:~:) (Refl))
import Cats.Types
import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude (Either (..))
import Prelude qualified as P

-- | A pullback of @a -> z <- b@ with chosen apex @p@. Write its cospan as
-- @Cospan f g@ and its cone as @Span l r@. Require @f ∘ l = g ∘ r@.
-- For every commuting cone @Span u v@ from a valid object @x@, its mediator
-- @h = factorPullback pb x (Span u v)@ must satisfy:
--
-- @
-- l ∘ h = u
-- r ∘ h = v
-- @
-- It is the unique such arrow: if @q@ satisfies both equations then @q = h@.
-- No behavior is specified for noncommuting cones. Equality is equality of
-- arrows in @k@ (extensional equality for total functions).
data Pullback :: CATEGORY i -> i -> i -> i -> i -> Type where
  Pullback ::
    (Category k, p ∈ k, z ∈ k, a ∈ k, b ∈ k) =>
    { pullbackCospan :: Cospan k z a b,
      pullbackSpan :: Span k p a b,
      factorPullback :: forall x -> (x ∈ k) => Span k x a b -> k x p
    } ->
    Pullback k p z a b

-- | A pushout of @a <- z -> b@ with chosen apex @p@. Write its span as
-- @Span f g@ and its cocone as @Cospan l r@. Require @l ∘ f = r ∘ g@.
-- For each commuting cocone @Cospan u v@ to @x@, the mediator
-- @h = factorPushout po x (Cospan u v)@ uniquely satisfies
-- @h ∘ l = u@ and @h ∘ r = v@. Noncommuting cocones have no specified result.
data Pushout :: CATEGORY i -> i -> i -> i -> i -> Type where
  Pushout ::
    (Category k, p ∈ k, z ∈ k, a ∈ k, b ∈ k) =>
    { pushoutSpan :: Span k z a b,
      pushoutCospan :: Cospan k p a b,
      factorPushout :: forall x -> (x ∈ k) => Cospan k x a b -> k p x
    } ->
    Pushout k p z a b

-- | A chosen pullback whose apex name is existential, with its evidence stored.
data SomePullback k z a b where
  SomePullback :: Pullback k p z a b -> SomePullback k z a b

-- | A chosen pushout whose apex name is existential.
data SomePushout k z a b where
  SomePushout :: Pushout k p z a b -> SomePushout k z a b

-- | Choose a lawful pullback for every cospan. The returned witness's
-- 'pullbackCospan' must be the supplied diagram, including its actual arrows.
class (Category k) => HasPullbacks (k :: CATEGORY i) where
  pullback :: forall z a b -> (z ∈ k, a ∈ k, b ∈ k) => Cospan k z a b -> SomePullback k z a b

-- | Choose a lawful pushout for every span, retaining the supplied diagram.
class (Category k) => HasPushouts (k :: CATEGORY i) where
  pushout :: forall z a b -> (z ∈ k, a ∈ k, b ∈ k) => Span k z a b -> SomePushout k z a b

-- | The canonical comparison between pullbacks of the /same cospan/.
-- Comparing in the reverse direction gives its inverse by uniqueness.
-- This operation assumes equal diagrams, not just equal endpoint names.
comparePullbacks :: forall k p q z a b. Pullback k p z a b -> Pullback k q z a b -> k p q
comparePullbacks (Pullback _ cone _) target = factorPullback target p cone

-- | The canonical comparison between pushouts of the /same span/.
comparePushouts :: forall k p q z a b. Pushout k p z a b -> Pushout k q z a b -> k p q
comparePushouts source (Pushout _ cocone _) = factorPushout source q cocone

-- | A pullback becomes a pushout in the opposite category.
opPullback :: Pullback k p z a b -> Pushout (Op k) p z a b
opPullback (Pullback diagram cone factor) =
  Pushout (opCospan diagram) (opSpan cone) (\x cocone -> OP (factor x (unOpSpan cocone)))

-- | Inverse of 'opPullback'.
unOpPullback :: (Category k) => Pushout (Op k) p z a b -> Pullback k p z a b
unOpPullback (Pushout diagram cocone factor) =
  Pullback (unOpCospan diagram) (unOpSpan cocone) (\x cone -> runOP (factor x (opSpan cone)))

-- | A pushout becomes a pullback in the opposite category.
opPushout :: Pushout k p z a b -> Pullback (Op k) p z a b
opPushout (Pushout diagram cocone factor) =
  Pullback (opSpan diagram) (opCospan cocone) (\x cone -> OP (factor x (unOpCospan cone)))

-- | Inverse of 'opPushout'.
unOpPushout :: (Category k) => Pullback (Op k) p z a b -> Pushout k p z a b
unOpPushout (Pullback diagram cone factor) =
  Pushout (unOpSpan diagram) (unOpCospan cone) (\x cocone -> runOP (factor x (opCospan cocone)))

instance (HasPushouts k) => HasPullbacks (Op k) where
  pullback z a b diagram = case pushout z a b (unOpSpan diagram) of
    SomePushout result -> SomePullback (opPushout result)

instance (HasPullbacks k) => HasPushouts (Op k) where
  pushout z a b diagram = case pullback z a b (unOpCospan diagram) of
    SomePullback result -> SomePushout (opPullback result)

instance HasPullbacks (:~:) where
  pullback _ _ _ diagram@(Cospan Refl Refl) =
    SomePullback (Pullback diagram (Span Refl Refl) (\_ (Span Refl Refl) -> Refl))

instance HasPushouts (:~:) where
  pushout _ _ _ diagram@(Span Refl Refl) =
    SomePushout (Pushout diagram (Cospan Refl Refl) (\_ (Cospan Refl Refl) -> Refl))

-- | Pull back @f : a -> z@ along the identity on @z@. The apex is @a@;
-- commutativity forces the right leg of each input cone to be @f ∘ left@.
pullbackIdentityRight :: forall k a z. (Category k, a ∈ k, z ∈ k) => k a z -> Pullback k a z a z
pullbackIdentityRight f = Pullback (Cospan f (identity z)) (Span (identity a) f) (\_ -> spanLeft)

-- | Pull back the identity on @z@ along @f : b -> z@.
pullbackIdentityLeft :: forall k b z. (Category k, b ∈ k, z ∈ k) => k b z -> Pullback k b z z b
pullbackIdentityLeft f = Pullback (Cospan (identity z) f) (Span f (identity b)) (\_ -> spanRight)

-- | Push out @f : z -> a@ along the identity on @z@.
pushoutIdentityRight :: forall k z a. (Category k, z ∈ k, a ∈ k) => k z a -> Pushout k a z a z
pushoutIdentityRight f = Pushout (Span f (identity z)) (Cospan (identity a) f) (\_ -> cospanLeft)

-- | Push out the identity on @z@ along @f : z -> b@.
pushoutIdentityLeft :: forall k z b. (Category k, z ∈ k, b ∈ k) => k z b -> Pushout k b z z b
pushoutIdentityLeft f = Pushout (Span (identity z) f) (Cospan f (identity b)) (\_ -> cospanRight)

-- | The product of Haskell types is the pullback of their unique maps to @()@.
-- There is no claim here that every function cospan has a chosen pullback.
productPullback :: forall a b. Pullback Types (a, b) () a b
productPullback =
  Pullback
    (Cospan (P.const ()) (P.const ()))
    (Span P.fst P.snd)
    (\_ (Span l r) x -> (l x, r x))

-- | The coproduct is the pushout of the unique maps from 'Void'.
coproductPushout :: forall a b. Pushout Types (Either a b) Void a b
coproductPushout =
  Pushout
    (Span absurd absurd)
    (Cospan Left Right)
    (\_ (Cospan l r) -> P.either l r)

-- | A span with hidden apex and object evidence for all three vertices.
data SomeSpan k a b where
  SomeSpan :: (x ∈ k, a ∈ k, b ∈ k) => Span k x a b -> SomeSpan k a b

-- | A cospan with hidden apex and object evidence for all three vertices.
data SomeCospan k a b where
  SomeCospan :: (x ∈ k, a ∈ k, b ∈ k) => Cospan k x a b -> SomeCospan k a b

-- | The identity span at an object.
identitySpan :: forall {k}. forall a -> (Category k, a ∈ k) => Span k a a a
identitySpan a = Span (identity a) (identity a)

-- | The identity cospan at an object.
identityCospan :: forall {k}. forall a -> (Category k, a ∈ k) => Cospan k a a a
identityCospan a = Cospan (identity a) (identity a)

-- | Compose spans with the outer span first, using a pullback of the two
-- arrows into the shared foot. The result retains the chosen apex evidence.
-- Associativity and units hold up to the apex isomorphisms described above.
composeSpans ::
  forall k x y a b c.
  (HasPullbacks k, x ∈ k, y ∈ k, a ∈ k, b ∈ k, c ∈ k) =>
  Span k y b c -> Span k x a b -> SomeSpan k a c
composeSpans outer inner = case pullback b x y (Cospan (spanRight inner) (spanLeft outer)) of
  SomePullback (Pullback _ (Span l r) _) ->
    SomeSpan (Span (spanLeft inner ∘ l) (spanRight outer ∘ r))

-- | Compose cospans with the outer cospan first, using a pushout of the
-- arrows out of the shared foot. Laws are dual to those of 'composeSpans'.
composeCospans ::
  forall k x y a b c.
  (HasPushouts k, x ∈ k, y ∈ k, a ∈ k, b ∈ k, c ∈ k) =>
  Cospan k y b c -> Cospan k x a b -> SomeCospan k a c
composeCospans outer inner = case pushout b x y (Span (cospanRight inner) (cospanLeft outer)) of
  SomePushout (Pushout _ (Cospan l r) _) ->
    SomeCospan (Cospan (l ∘ cospanLeft inner) (r ∘ cospanRight outer))
