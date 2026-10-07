-- | Optics represented by arrows with an existential residual, and their
-- interpretations as functions, views, reviews, or represented optics.
--
-- Products, coproducts, and function spaces over 'Types' supply the residual
-- actions used by lenses, prisms, and grates. Composition combines residuals;
-- identities use @()@ for lenses and grates and @Void@ for prisms.
--
-- Category laws are extensional: lawful interpretations cannot distinguish
-- rebracketing residuals or inserting their units. 'MkTensored' stores a
-- representative, not a quotient or a canonical residual type. These laws
-- assume total, parametric code. No category structure is claimed for an
-- arbitrary tensor or arbitrary residual category.
--
-- In the supported @Like Types@ representations, a residual arrow @h@ relates
-- two representatives when their legs satisfy:
--
-- @
-- split' = map tensor (h :×: identity a) ∘ split
-- build = build' ∘ map tensor (h :×: identity b)
-- @
--
-- Lawful interpretations must give the same result on such representatives.
-- Here @h@ belongs to the tensor's left category, which is @Op Types@ for
-- function spaces. Rebracketing and unit insertion are particular cases.
--
-- Category laws and functorial interpretation do not enforce additional
-- domain laws on user-supplied optics, such as lens get-put and put-get laws.
--
-- Supported interpretations include:
--
-- * @Hom Types@: modify the focus of an iso, lens, prism, or grate.
-- * @HomFrom ViewLike xy@: view through an iso or lens.
-- * @HomFrom ReviewLike xy@: review through an iso or prism.
-- * @HomFrom k xy@: record an optic in its own category @k@.
--
-- For example, with a qualified Prelude import as @P@:
--
-- @
-- lens \@(Hom Types) P.id P.id P.show (True, 7 :: Int) P.== (True, "7")
-- @
module Cats.Optics where

import Cats.Category
import Cats.CrossProduct
import Cats.Delta
import Cats.Functor
import Cats.Hom
import Cats.Yoneda
import Data.Kind (Constraint, Type)
import Data.Type.Equality (type (~))
import Data.Void (Void, absurd)
import Prelude qualified as P

newtype Viewer :: CATEGORY o -> CATEGORY (o, o) where
  Viewer :: {runViewer :: arr (Fst st) (Fst ab)} -> Viewer arr ab st

type instance Obj (Viewer arr) o = o ∈ (arr × arr)

instance (Semigroupoid arr) => Semigroupoid (Viewer arr) where
  Viewer f ∘ Viewer g = Viewer (g ∘ f)

instance (Category arr) => Category (Viewer arr) where
  identity _ = Viewer (identity _)

data Like :: CATEGORY o -> CATEGORY (o, o) where
  Like ::
    !(arr (Fst st) (Fst ab)) ->
    !(arr (Snd ab) (Snd st)) ->
    Like arr ab st

type instance Obj (Like arr) o = o ∈ (arr × arr)

instance (Semigroupoid arr) => Semigroupoid (Like arr) where
  Like f g ∘ Like h i = Like (h ∘ f) (g ∘ i)

instance (Category arr) => Category (Like arr) where
  identity _ = Like (identity _) (identity _)

type TensoredObjects ::
  forall o (l :: CATEGORY o) (r :: CATEGORY o) (arr :: CATEGORY o).
  ((l × r) --> arr) ->
  o ->
  (o, o) ->
  (o, o)
type TensoredObjects tensor e ab =
  '( Act tensor '(e, Fst ab),
     Act tensor '(e, Snd ab)
   )

-- | An optic with a hidden residual. The constructor retains the residual's
-- object evidence even if the tensor's 'Act' family does not determine it.
data
  Tensored ::
    forall (l :: CATEGORY o) (r :: CATEGORY o) (arr :: CATEGORY o).
    ((l × r) --> arr) ->
    CATEGORY (o, o) ->
    CATEGORY (o, o)
  where
  -- | The residual must be a valid object in the tensor's left category.
  -- Endpoint object evidence is supplied by the optic category at use sites.
  MkTensored ::
    forall {l} {r} {k} {tensor :: (l × r) --> k} {arr} e ab st.
    (e ∈ l) =>
    !(arr (TensoredObjects tensor e ab) st) ->
    Tensored tensor arr ab st

type instance Obj (Tensored tensor arr) o = o ∈ arr

instance Semigroupoid (Tensored (∧) (Like Types)) where
  MkTensored (Like outerGet outerPut) ∘ MkTensored (Like innerGet innerPut) =
    MkTensored
      ( Like
          ( \s -> case outerGet s of
              (e, a) -> case innerGet a of
                (f, x) -> ((e, f), x)
          )
          (\((e, f), y) -> outerPut (e, innerPut (f, y)))
      )

instance Category (Tensored (∧) (Like Types)) where
  identity _ = MkTensored (Like (\a -> ((), a)) P.snd)

instance Semigroupoid (Tensored (∨) (Like Types)) where
  MkTensored (Like outerMatch outerBuild) ∘ MkTensored (Like innerMatch innerBuild) =
    MkTensored
      ( Like
          ( \s -> case outerMatch s of
              P.Left e -> P.Left (P.Left e)
              P.Right a -> case innerMatch a of
                P.Left f -> P.Left (P.Right f)
                P.Right x -> P.Right x
          )
          ( \case
              P.Left (P.Left e) -> outerBuild (P.Left e)
              P.Left (P.Right f) -> outerBuild (P.Right (innerBuild (P.Left f)))
              P.Right y -> outerBuild (P.Right (innerBuild (P.Right y)))
          )
      )

instance Category (Tensored (∨) (Like Types)) where
  identity _ = MkTensored @Void (Like P.Right (P.either absurd P.id))

instance Semigroupoid (Tensored (Hom Types) (Like Types)) where
  MkTensored (Like outerSplit outerBuild) ∘ MkTensored (Like innerSplit innerBuild) =
    MkTensored
      ( Like
          (\s (e, f) -> innerSplit (outerSplit s e) f)
          (\values -> outerBuild (\e -> innerBuild (\f -> values (e, f))))
      )

instance Category (Tensored (Hom Types) (Like Types)) where
  identity _ = MkTensored @() (Like (\a () -> a) (\values -> values ()))

type data Direction = RTL | LTR

type ReverseDirection :: Direction -> Direction
type family ReverseDirection dir where
  ReverseDirection RTL = LTR
  ReverseDirection LTR = RTL

data Glass :: Direction -> CATEGORY (o, o) -> CATEGORY (o, o) where
  Window :: !(proarr '(a, b) '(s, t)) -> Glass RTL proarr '(a, b) '(s, t)
  Mirror :: !(proarr '(t, s) '(b, a)) -> Glass LTR proarr '(a, b) '(s, t)

type instance Obj (Glass RTL k) e = (e ~ '(Fst e, Snd e), e ∈ k)

type instance Obj (Glass LTR k) e = (e ~ '(Fst e, Snd e), '(Snd e, Fst e) ∈ k)

instance (Semigroupoid k) => Semigroupoid (Glass RTL k) where
  Window abst ∘ Window xyab = Window (abst ∘ xyab)

instance (Semigroupoid k) => Semigroupoid (Glass LTR k) where
  Mirror abst ∘ Mirror xyab = Mirror (xyab ∘ abst)

instance (Category k) => Category (Glass RTL k) where
  identity _ = Window (identity _)

instance (Category k) => Category (Glass LTR k) where
  identity _ = Mirror (identity _)

type Reversible :: CATEGORY (o, o) -> CATEGORY (o, o) -> Constraint
class Reversible input output | input -> output, output -> input where
  reversed :: input '(a, b) '(s, t) -> output '(t, s) '(b, a)

instance Reversible (Like arr) (Like arr) where
  reversed (Like sa bt) = Like bt sa

instance
  (m ~ ReverseDirection w, ReverseDirection m ~ w) =>
  Reversible (Glass m arr) (Glass w arr)
  where
  reversed (Window k) = Mirror k
  reversed (Mirror k) = Window k

type IsoLike = Glass RTL (Like Types)

type OsiLike = Glass LTR (Like Types)

type ViewLike = Glass RTL (Viewer Types)

type ReviewLike = Glass LTR (Viewer Types)

type data InOptic :: forall d -> (c --> Types) -> d --> Types

type instance Act (InOptic d c) o = Act c o

instance Functor (InOptic IsoLike (Hom (->))) where
  map _ (Window (Like sa bt)) ar = bt ∘ ar ∘ sa

instance Functor (InOptic IsoLike (HomFrom ViewLike xy)) where
  map _ (Window (Like sa _bt)) (Window ar) = Window (Viewer sa ∘ ar)

instance Functor (InOptic IsoLike (HomFrom ReviewLike xy)) where
  map _ (Window (Like _sa bt)) (Mirror (Viewer yb)) = Mirror (Viewer (bt ∘ yb))

-- Interpreting an optic in its own covariant representable records it by
-- composition. In particular, applying a constructor to identity builds a
-- represented optic that can subsequently be composed or reversed.
instance (Category k) => Functor (InOptic k (HomFrom k xy)) where
  map _ outer inner = outer ∘ inner

-- Shapes

type TupleShaped c = Tensored (∧) (Like c)

type EitherShaped c = Tensored (∨) (Like c)

type DomShaped c = Tensored (Hom Types) (Like c)

-- Optic likes

type LensLike = Glass RTL (TupleShaped Types)

type ColensLike = Glass LTR (TupleShaped Types)

type PrismLike = Glass RTL (EitherShaped Types)

type CoprismLike = Glass LTR (EitherShaped Types)

type GrateLike = Glass RTL (DomShaped Types)

type CograteLike = Glass LTR (DomShaped Types)

instance Functor (InOptic LensLike (Hom Types)) where
  map _ (Window (MkTensored (Like split build))) ab =
    build ∘ (\(e, a) -> (e, ab a)) ∘ split

instance Functor (InOptic LensLike (HomFrom ViewLike xy)) where
  map _ (Window (MkTensored (Like split _build))) (Window ar) =
    Window (Viewer (P.snd ∘ split) ∘ ar)

instance Functor (InOptic PrismLike (Hom Types)) where
  map _ (Window (MkTensored (Like match build))) ab =
    build ∘ P.either P.Left (P.Right ∘ ab) ∘ match

instance Functor (InOptic PrismLike (HomFrom ReviewLike xy)) where
  map _ (Window (MkTensored (Like _match build))) (Mirror (Viewer yb)) =
    Mirror (Viewer (build ∘ P.Right ∘ yb))

instance Functor (InOptic GrateLike (Hom Types)) where
  map _ (Window (MkTensored (Like split build))) ab =
    build ∘ (\values -> ab ∘ values) ∘ split

-- Aliases

type Optical ::
  forall {i} {j} {c :: CATEGORY (i, j)}.
  (c --> Types) -> i -> j -> i -> j -> Type
type Optical p a b s t =
  Act p '(a, b) -> Act p '(s, t)

-- | An interpretation may come from any category of pairs, including a
-- representable on 'ViewLike' or 'ReviewLike'. Requiring its domain to be a
-- product of categories would exclude those interpretations.
type OpticOf ::
  forall {o} {c :: CATEGORY (o, o)}.
  CATEGORY (o, o) ->
  (c --> Types) ->
  o ->
  o ->
  o ->
  o ->
  Type
type OpticOf k p a b s t =
  (Functor p, Functor (InOptic k p)) =>
  Optical p a b s t

type Optic ::
  forall {o}.
  CATEGORY (o, o) ->
  (o -> o -> o -> o -> Type)
type Optic k a b s t =
  forall c (p :: c --> Types).
  OpticOf k p a b s t

type DataIso = InOptic IsoLike

type DataLens = InOptic LensLike

type DataPrism = InOptic PrismLike

type DataGrate = InOptic GrateLike

type Iso a b s t = Optic IsoLike a b s t

type Lens a b s t = Optic LensLike a b s t

type Prism a b s t = Optic PrismLike a b s t

type Grate a b s t = Optic GrateLike a b s t

-- | Interpret a pair of arrows into and out of the focus.
iso ::
  forall p a b s t.
  (s -> a) ->
  (b -> t) ->
  OpticOf IsoLike p a b s t
iso sa bt =
  map
    (DataIso p)
    (Window (Like sa bt))

-- | Split a structure into a residual and a focus, then rebuild it from the
-- same residual and the updated focus. The focus and structure may change type.
lens ::
  forall p a b s t e.
  (s -> Act (∧) '(e, a)) ->
  (Act (∧) '(e, b) -> t) ->
  OpticOf LensLike p a b s t
lens sea ebt =
  map
    (DataLens p)
    (Window (MkTensored (Like sea ebt)))

-- | Match a focus or retain a failure residual. The focus function is applied
-- only on a successful match; the builder handles both cases.
prism ::
  forall p a b s t e.
  (s -> Act (∨) '(e, a)) ->
  (Act (∨) '(e, b) -> t) ->
  OpticOf PrismLike p a b s t
prism sea ebt =
  map
    (DataPrism p)
    (Window (MkTensored (Like sea ebt)))

-- | Expose focuses indexed by a residual and rebuild from their updated
-- values. A represented grate also supports 'zipWithGrate'.
grate ::
  forall p a b s t e.
  (s -> Act (Hom Types) '(e, a)) ->
  (Act (Hom Types) '(e, b) -> t) ->
  OpticOf GrateLike p a b s t
grate sea ebt =
  map
    (DataGrate p)
    (Window (MkTensored (Like sea ebt)))

-- | Combine corresponding focuses of two structures using a represented
-- grate. Its shared residual identifies the same position in both inputs.
zipWithGrate :: GrateLike '(a, b) '(s, t) -> (a -> a -> b) -> s -> s -> t
zipWithGrate (Window (MkTensored (Like split build))) combine left right =
  build (\e -> combine (split left e) (split right e))
