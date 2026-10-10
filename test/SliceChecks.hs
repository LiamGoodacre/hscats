module SliceChecks (checks) where

import AdjunctionChecks (OnlyTrue (..))
import Cats
import Data.Kind (Type)
import Prelude (Bool (..), Int, String)
import Prelude qualified as P

type data ShiftedDouble :: Type

type data Double :: Type

type data Plain :: Type

type data Negation :: Type

type data NegatedShift :: Type

type data EncodeBool :: Type

type data Parity :: Type

type data ConstrainedF :: Type

type data ConstrainedG :: Type

instance NamedArrow Types ShiftedDouble where
  type ArrowSource Types ShiftedDouble = Int
  type ArrowTarget Types ShiftedDouble = Int
  namedArrow _ n = 2 P.* (n P.+ 1)

instance NamedArrow Types Double where
  type ArrowSource Types Double = Int
  type ArrowTarget Types Double = Int
  namedArrow _ = (P.* 2)

instance NamedArrow Types Plain where
  type ArrowSource Types Plain = Int
  type ArrowTarget Types Plain = Int
  namedArrow _ = P.id

instance NamedArrow Types Negation where
  type ArrowSource Types Negation = Int
  type ArrowTarget Types Negation = Int
  namedArrow _ = P.negate

instance NamedArrow Types NegatedShift where
  type ArrowSource Types NegatedShift = Int
  type ArrowTarget Types NegatedShift = Int
  namedArrow _ n = P.negate (2 P.* (n P.+ 1))

instance NamedArrow Types EncodeBool where
  type ArrowSource Types EncodeBool = Bool
  type ArrowTarget Types EncodeBool = Int
  namedArrow _ = P.fromEnum

instance NamedArrow Types Parity where
  type ArrowSource Types Parity = Int
  type ArrowTarget Types Parity = Bool
  namedArrow _ = P.even

instance NamedArrow OnlyTrue ConstrainedF where
  type ArrowSource OnlyTrue ConstrainedF = 'True
  type ArrowTarget OnlyTrue ConstrainedF = 'True
  namedArrow _ = TArrow (\n -> 3 P.* (n P.+ 1))

instance NamedArrow OnlyTrue ConstrainedG where
  type ArrowSource OnlyTrue ConstrainedG = 'True
  type ArrowTarget OnlyTrue ConstrainedG = 'True
  namedArrow _ = TArrow (P.* 3)

sf :: Slice Types Int ShiftedDouble Double
sf = Slice (P.+ 1)

sg :: Slice Types Int Double Plain
sg = Slice (P.* 2)

sh :: Slice Types Int Plain Negation
sh = Slice P.negate

cf :: Coslice Types Int Plain Double
cf = Coslice (P.* 2)

cg :: Coslice Types Int Double ShiftedDouble
cg = Coslice (P.+ 2)

ch :: Coslice Types Int ShiftedDouble NegatedShift
ch = Coslice P.negate

same :: (Int -> Int) -> (Int -> Int) -> Bool
same f g = P.all (\n -> f n P.== g n) [-3 .. 3]

checks :: [(String, Bool)]
checks =
  [ ( "Slice objects distinguish arrows with the same endpoints",
      namedArrow ShiftedDouble 7 P.== 16 P.&& namedArrow Double 7 P.== 14
    ),
    ( "Slice triangle",
      same (namedArrow Double ∘ runSlice sf) (namedArrow ShiftedDouble)
    ),
    ( "Coslice triangle",
      same (runCoslice cg ∘ namedArrow Double) (namedArrow ShiftedDouble)
    ),
    ( "Slice composition order and commuting triangle",
      runSlice (sg ∘ sf) 7 P.== 16
        P.&& same (namedArrow Plain ∘ runSlice (sg ∘ sf)) (namedArrow ShiftedDouble)
    ),
    ( "Coslice composition order and commuting triangle",
      runCoslice (cg ∘ cf) 7 P.== 16
        P.&& same (runCoslice (cg ∘ cf) ∘ namedArrow Plain) (namedArrow ShiftedDouble)
    ),
    ( "Slice identity laws",
      same (runSlice (identity Double ∘ sf)) (runSlice sf)
        P.&& same (runSlice (sf ∘ identity ShiftedDouble)) (runSlice sf)
    ),
    ( "Coslice identity laws",
      same (runCoslice (identity Double ∘ cf)) (runCoslice cf)
        P.&& same (runCoslice (cf ∘ identity Plain)) (runCoslice cf)
    ),
    ( "Slice associativity",
      same (runSlice (sh ∘ (sg ∘ sf))) (runSlice ((sh ∘ sg) ∘ sf))
    ),
    ( "Coslice associativity",
      same (runCoslice (ch ∘ (cg ∘ cf))) (runCoslice ((ch ∘ cg) ∘ cf))
    ),
    ( "Slice forgetful functor preserves identity and composition",
      same (map (SliceDomain Types Int) (identity ShiftedDouble)) P.id
        P.&& same (map (SliceDomain Types Int) (sg ∘ sf)) (map (SliceDomain Types Int) sg ∘ map (SliceDomain Types Int) sf)
    ),
    ( "Coslice forgetful functor preserves identity and composition",
      same (map (CosliceCodomain Types Int) (identity Plain)) P.id
        P.&& same (map (CosliceCodomain Types Int) (cg ∘ cf)) (map (CosliceCodomain Types Int) cg ∘ map (CosliceCodomain Types Int) cf)
    ),
    ( "Slice arrows may change their domain object",
      let h = Slice P.fromEnum :: Slice Types Int EncodeBool Plain
       in P.all (\b -> namedArrow Plain (runSlice h b) P.== namedArrow EncodeBool b) [False, True]
            P.&& map (SliceDomain Types Int) h True P.== 1
    ),
    ( "Coslice arrows may change their codomain object",
      let h = Coslice P.even :: Coslice Types Int Plain Parity
       in P.all (\n -> runCoslice h (namedArrow Plain n) P.== namedArrow Parity n) [-3 .. 3]
            P.&& map (CosliceCodomain Types Int) h 7 P.== False
    ),
    ( "Slice preserves constrained non-Type object evidence",
      let h = Slice (TArrow (P.+ 1)) :: Slice OnlyTrue 'True ConstrainedF ConstrainedG
       in case (map (SliceDomain OnlyTrue (type 'True)) (identity ConstrainedG ∘ h), namedArrow ConstrainedG, namedArrow ConstrainedF) of
            (TArrow f, TArrow g, TArrow target) -> same (g ∘ f) target
    ),
    ( "Coslice preserves constrained non-Type object evidence",
      let h = Coslice (TArrow (P.+ 3)) :: Coslice OnlyTrue 'True ConstrainedG ConstrainedF
       in case (map (CosliceCodomain OnlyTrue (type 'True)) (h ∘ identity ConstrainedG), namedArrow ConstrainedG, namedArrow ConstrainedF) of
            (TArrow f, TArrow g, TArrow target) -> same (f ∘ g) target
    )
  ]
