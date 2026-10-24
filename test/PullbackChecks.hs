module PullbackChecks (checks) where

import Cats
import Data.Void (Void)
import Prelude (Bool (..), Int, String)
import Prelude qualified as P

-- The two-object ordered category False <= True. Every hom set is finite,
-- so the tests can enumerate all cones, cocones, and candidate mediators.
data B a where
  BFalse :: B 'False
  BTrue :: B 'True

class KnownB a where
  known :: B a

instance KnownB 'False where known = BFalse

instance KnownB 'True where known = BTrue

data Order a b where
  FF :: Order 'False 'False
  FT :: Order 'False 'True
  TT :: Order 'True 'True

deriving instance P.Eq (Order a b)

type instance Obj Order a = KnownB a

instance Semigroupoid Order where
  FF ∘ FF = FF
  FT ∘ FF = FT
  TT ∘ FT = FT
  TT ∘ TT = TT

instance Category Order where
  identity a = case known @a of BFalse -> FF; BTrue -> TT

instance HasPullbacks Order where
  pullback _ _ _ diagram = case diagram of
    Cospan FF FF -> SomePullback (Pullback diagram (Span FF FF) (\_ -> spanLeft))
    Cospan FT FT -> SomePullback (Pullback diagram (Span FF FF) (\_ -> spanLeft))
    Cospan FT TT -> SomePullback (Pullback diagram (Span FF FT) (\_ -> spanLeft))
    Cospan TT FT -> SomePullback (Pullback diagram (Span FT FF) (\_ -> spanRight))
    Cospan TT TT -> SomePullback (Pullback diagram (Span TT TT) (\_ -> spanLeft))

instance HasPushouts Order where
  pushout _ _ _ diagram = case diagram of
    Span FF FF -> SomePushout (Pushout diagram (Cospan FF FF) (\_ -> cospanLeft))
    Span FF FT -> SomePushout (Pushout diagram (Cospan FT TT) (\_ -> cospanRight))
    Span FT FF -> SomePushout (Pushout diagram (Cospan TT FT) (\_ -> cospanLeft))
    Span FT FT -> SomePushout (Pushout diagram (Cospan TT TT) (\_ -> cospanLeft))
    Span TT TT -> SomePushout (Pushout diagram (Cospan TT TT) (\_ -> cospanLeft))

data Object where
  Object :: (KnownB a) => B a -> Object

objects :: [Object]
objects = [Object BFalse, Object BTrue]

arrows :: B a -> B b -> [Order a b]
arrows BFalse BFalse = [FF]
arrows BFalse BTrue = [FT]
arrows BTrue BFalse = []
arrows BTrue BTrue = [TT]

validPullback :: forall z a b. (KnownB z, KnownB a, KnownB b) => Cospan Order z a b -> Bool
validPullback diagram@(Cospan f g) = case pullback z a b diagram of
  SomePullback (pb@(Pullback (Cospan f' g') (Span l r) _) :: Pullback Order p z a b) ->
    f P.== f'
      P.&& g P.== g'
      P.&& f ∘ l P.== g ∘ r
      P.&& comparePullbacks pb pb P.== identity p
      P.&& P.and
        [ let h = factorPullback pb x (Span u v)
           in l ∘ h P.== u
                P.&& r ∘ h P.== v
                P.&& [q | q <- arrows sx (known @p), l ∘ q P.== u, r ∘ q P.== v] P.== [h]
        | Object (sx :: B x) <- objects,
          u <- arrows sx (known @a),
          v <- arrows sx (known @b),
          f ∘ u P.== g ∘ v
        ]

validPushout :: forall z a b. (KnownB z, KnownB a, KnownB b) => Span Order z a b -> Bool
validPushout diagram@(Span f g) = case pushout z a b diagram of
  SomePushout (po@(Pushout (Span f' g') (Cospan l r) _) :: Pushout Order p z a b) ->
    f P.== f'
      P.&& g P.== g'
      P.&& l ∘ f P.== r ∘ g
      P.&& comparePushouts po po P.== identity p
      P.&& P.and
        [ let h = factorPushout po x (Cospan u v)
           in h ∘ l P.== u
                P.&& h ∘ r P.== v
                P.&& [q | q <- arrows (known @p) sx, q ∘ l P.== u, q ∘ r P.== v] P.== [h]
        | Object (sx :: B x) <- objects,
          u <- arrows (known @a) sx,
          v <- arrows (known @b) sx,
          u ∘ f P.== v ∘ g
        ]

asBool :: B a -> Bool
asBool BFalse = False
asBool BTrue = True

spans :: (KnownB a, KnownB b) => B a -> B b -> [SomeSpan Order a b]
spans a b = [SomeSpan (Span l r) | Object x <- objects, l <- arrows x a, r <- arrows x b]

cospans :: (KnownB a, KnownB b) => B a -> B b -> [SomeCospan Order a b]
cospans a b = [SomeCospan (Cospan l r) | Object x <- objects, l <- arrows a x, r <- arrows b x]

apex :: forall a b. SomeSpan Order a b -> Bool
apex (SomeSpan (_ :: Span Order x a b)) = asBool (known @x)

coapex :: forall a b. SomeCospan Order a b -> Bool
coapex (SomeCospan (_ :: Cospan Order x a b)) = asBool (known @x)

compose :: SomeSpan Order b c -> SomeSpan Order a b -> SomeSpan Order a c
compose (SomeSpan f) (SomeSpan g) = composeSpans f g

cocompose :: SomeCospan Order b c -> SomeCospan Order a b -> SomeCospan Order a c
cocompose (SomeCospan f) (SomeCospan g) = composeCospans f g

bools :: [Bool]
bools = [False, True]

functions :: [a] -> [Bool -> a]
functions values = [\b -> if b then t else f | f <- values, t <- values]

same :: (P.Eq b) => [a] -> (a -> b) -> (a -> b) -> Bool
same xs f g = P.all (\x -> f x P.== g x) xs

swappedProduct :: Pullback Types (Bool, Int) () Int Bool
swappedProduct =
  Pullback
    (Cospan (P.const ()) (P.const ()))
    (Span P.snd P.fst)
    (\_ (Span l r) x -> (r x, l x))

swappedCoproduct :: Pushout Types (P.Either Bool Int) Void Int Bool
swappedCoproduct =
  Pushout
    (pushoutSpan (coproductPushout @Int @Bool))
    (Cospan P.Right P.Left)
    (\_ (Cospan l r) -> P.either r l)

checks :: [(String, Bool)]
checks =
  [ ( "All five Order cospans have a unique pullback mediator for every cone",
      let results = [validPullback (Cospan f g) | Object z <- objects, Object a <- objects, Object b <- objects, f <- arrows a z, g <- arrows b z]
       in P.length results P.== 5 P.&& P.and results
    ),
    ( "All five Order spans have a unique pushout mediator for every cocone",
      let results = [validPushout (Span f g) | Object z <- objects, Object a <- objects, Object b <- objects, f <- arrows z a, g <- arrows z b]
       in P.length results P.== 5 P.&& P.and results
    ),
    ( "Product pullback factorization and exhaustive finite-function uniqueness",
      let pb = productPullback @Bool @Bool
          Span l r = pullbackSpan pb
          candidates = functions [(a, b) | a <- bools, b <- bools]
       in P.and
            [ let h = factorPullback pb Bool (Span u v)
               in same bools (l ∘ h) u
                    P.&& same bools (r ∘ h) v
                    P.&& P.length [q | q <- candidates, same bools (l ∘ q) u, same bools (r ∘ q) v] P.== 1
            | u <- functions bools,
              v <- functions bools
            ]
    ),
    ( "Coproduct pushout factorization and exhaustive finite-function uniqueness",
      let po = coproductPushout @Bool @Bool
          Cospan l r = pushoutCospan po
          candidates = [P.either u v | u <- functions bools, v <- functions bools]
       in P.and
            [ let h = factorPushout po Bool (Cospan u v)
               in same bools (h ∘ l) u
                    P.&& same bools (h ∘ r) v
                    P.&& P.length [q | q <- candidates, same bools (q ∘ l) u, same bools (q ∘ r) v] P.== 1
            | u <- functions bools,
              v <- functions bools
            ]
    ),
    ( "Pullbacks along either identity retain the factorization",
      let f = P.even :: Int -> Bool
          h = (P.* 3) :: Int -> Int
       in same [-3 .. 3] (factorPullback (pullbackIdentityRight f) Int (Span h (f ∘ h))) h
            P.&& same [-3 .. 3] (factorPullback (pullbackIdentityLeft f) Int (Span (f ∘ h) h)) h
    ),
    ( "Pushouts along either identity retain the factorization",
      let f = P.fromEnum :: Bool -> Int
          h = P.show :: Int -> String
       in same [-3 .. 3] (factorPushout (pushoutIdentityRight f) String (Cospan h (h ∘ f))) h
            P.&& same [-3 .. 3] (factorPushout (pushoutIdentityLeft f) String (Cospan (h ∘ f) h)) h
    ),
    ( "Canonical pullback comparisons are inverse across different apex types",
      let p = productPullback @Int @Bool
          f = comparePullbacks p swappedProduct
          g = comparePullbacks swappedProduct p
       in same [(n, b) | n <- [-3 .. 3], b <- bools] (g ∘ f) P.id
            P.&& same [(b, n) | n <- [-3 .. 3], b <- bools] (f ∘ g) P.id
            P.&& f (7, True) P.== (True, 7)
    ),
    ( "Canonical pushout comparisons are inverse across different apex types",
      let p = coproductPushout @Int @Bool
          f = comparePushouts p swappedCoproduct
          g = comparePushouts swappedCoproduct p
       in same [P.Left 7, P.Right True, P.Right False] (g ∘ f) P.id
            P.&& same [P.Left True, P.Left False, P.Right 7] (f ∘ g) P.id
            P.&& f (P.Left 7) P.== P.Right 7
    ),
    ( "Pullback duality preserves projections and mediators",
      let pb = unOpPullback (opPullback (productPullback @Int @Bool))
          Span l r = pullbackSpan pb
       in l (7, True) P.== 7
            P.&& r (7, True)
            P.&& factorPullback pb Int (Span (P.+ 1) P.even) 7 P.== (8, False)
    ),
    ( "Pushout duality preserves injections and mediators",
      let po = unOpPushout (opPushout (coproductPushout @Int @Bool))
          Cospan l r = pushoutCospan po
       in l 7 P.== P.Left 7
            P.&& r True P.== P.Right True
            P.&& factorPushout po String (Cospan P.show P.show) (P.Left 7) P.== "7"
    ),
    ( "Selected constructions dualize through opposite categories",
      case ( pullback (type 'False) (type 'False) (type 'True) (Cospan (OP FF) (OP FT)),
             pushout (type 'True) (type 'False) (type 'True) (Span (OP FT) (OP TT))
           ) of
        (SomePullback (Pullback _ (Span (OP l) (OP r)) factor), SomePushout (Pushout _ (Cospan (OP u) (OP v)) cofactor)) ->
          case (runOP (factor (type 'True) (Span (OP FT) (OP TT))), runOP (cofactor (type 'False) (Cospan (OP FF) (OP FT)))) of
            (h, g) -> h ∘ l P.== FT P.&& h ∘ r P.== TT P.&& u ∘ g P.== FF P.&& v ∘ g P.== FT
    ),
    ( "Equality category constructions support non-Type object names",
      case ( pullback (type 'True) (type 'True) (type 'True) (Cospan Refl Refl),
             pushout (type 'False) (type 'False) (type 'False) (Span Refl Refl)
           ) of
        (SomePullback (Pullback _ (Span Refl Refl) factor), SomePushout (Pushout _ (Cospan Refl Refl) cofactor)) ->
          case (factor (type 'True) (Span Refl Refl), cofactor (type 'False) (Cospan Refl Refl)) of (Refl, Refl) -> True
    ),
    ( "Span composition chooses the meet apex for every composable pair",
      P.and [apex (compose g f) P.== (apex f P.&& apex g) | Object a <- objects, Object b <- objects, Object c <- objects, f <- spans a b, g <- spans b c]
    ),
    ( "Cospan composition chooses the join apex for every composable pair",
      P.and [coapex (cocompose g f) P.== (coapex f P.|| coapex g) | Object a <- objects, Object b <- objects, Object c <- objects, f <- cospans a b, g <- cospans b c]
    ),
    ( "Span left and right units up to apex isomorphism",
      P.and
        [ apex (compose (SomeSpan (identitySpan b)) f) P.== apex f P.&& apex (compose f (SomeSpan (identitySpan a))) P.== apex f
        | Object (sa :: B a) <- objects,
          Object (sb :: B b) <- objects,
          f <- spans sa sb
        ]
    ),
    ( "Cospan left and right units up to apex isomorphism",
      P.and
        [ coapex (cocompose (SomeCospan (identityCospan b)) f) P.== coapex f P.&& coapex (cocompose f (SomeCospan (identityCospan a))) P.== coapex f
        | Object (sa :: B a) <- objects,
          Object (sb :: B b) <- objects,
          f <- cospans sa sb
        ]
    ),
    ( "Span associativity up to the unique apex isomorphism",
      P.and
        [ apex (compose h (compose g f)) P.== apex (compose (compose h g) f)
        | Object a <- objects,
          Object b <- objects,
          Object c <- objects,
          Object d <- objects,
          f <- spans a b,
          g <- spans b c,
          h <- spans c d
        ]
    ),
    ( "Cospan associativity up to the unique apex isomorphism",
      P.and
        [ coapex (cocompose h (cocompose g f)) P.== coapex (cocompose (cocompose h g) f)
        | Object a <- objects,
          Object b <- objects,
          Object c <- objects,
          Object d <- objects,
          f <- cospans a b,
          g <- cospans b c,
          h <- cospans c d
        ]
    )
  ]
