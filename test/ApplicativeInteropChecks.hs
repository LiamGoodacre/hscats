module ApplicativeInteropChecks (checks) where

import Cats
import Cats.Applicative qualified as A
import Control.Applicative (ZipList (..))
import Prelude (Bool (..), Char, Int, String)
import Prelude qualified as P

type Writer = Constructor ((,) [String])

type Zipped = Constructor ZipList

-- Each comparison observes the full writer log, or a finite ZipList prefix.
-- The latter permits unit naturality to exercise the infinite pure instance.
productLaws ::
  forall (f :: Types --> Types) ->
  (A.Applicative f) =>
  (Act f String -> Act f String -> Bool) ->
  [Act f Int] ->
  [Act f Bool] ->
  [Act f Char] ->
  [(String, Bool)]
productLaws f same ns bs cs =
  [ ( "product naturality",
      P.and
        [ same
            (map f (P.show @Int) (A.liftA2 @Int @Int @Int f (P.+) xs ys))
            (A.liftA2 @Int @Int @String f (\x y -> P.show (x P.+ y)) xs ys)
        | xs <- ns,
          ys <- ns
        ]
    ),
    ( "unit naturality",
      P.all (\n -> same (map f (P.show @Int) (A.pure f n)) (A.pure f (P.show n))) [-3 .. 3 :: Int]
    ),
    ( "product respects maps of both inputs",
      P.and
        [ same
            (A.liftA2 @Int @Int @String f (\x y -> P.show (x P.- y)) (map f ((P.+) @Int 5) xs) (map f (P.fromEnum @Bool) ys))
            (A.liftA2 @Int @Bool @String f (\x b -> P.show (x P.+ 5 P.- P.fromEnum b)) xs ys)
        | xs <- ns,
          ys <- bs
        ]
    ),
    ( "product associativity",
      let render :: Int -> Bool -> Char -> String
          render n b c = P.show n P.++ (if b then "yes" else "no") P.++ [c]
       in P.and
            [ same
                (A.liftA2 f (\(n, b) c -> render n b c) (A.liftA2 @Int @Bool @(Int, Bool) f (,) xs ys) zs)
                (A.liftA2 f (\n (b, c) -> render n b c) xs (A.liftA2 @Bool @Char @(Bool, Char) f (,) ys zs))
            | xs <- ns,
              ys <- bs,
              zs <- cs
            ]
    ),
    ( "left unit",
      P.all (\xs -> same (A.liftA2 @() @Int @String f (\() n -> P.show n) (A.pure f ()) xs) (map f (P.show @Int) xs)) ns
    ),
    ( "right unit",
      P.all (\xs -> same (A.liftA2 @Int @() @String f (\n () -> P.show n) xs (A.pure f ())) (map f (P.show @Int) xs)) ns
    )
  ]

checks :: [(String, Bool)]
checks =
  [ ("Writer " P.++ label, ok)
  | (label, ok) <-
      productLaws
        Writer
        (P.==)
        [([], 0), (["n1", "n2"], 7), (["n3"], -2)]
        [([], False), (["b"], True)]
        [([], 'a'), (["c1", "c2"], 'b')]
  ]
    P.++ [ ("ZipList " P.++ label, ok)
         | (label, ok) <-
             productLaws
               Zipped
               (\x y -> P.take 10 (getZipList x) P.== P.take 10 (getZipList y))
               (P.map ZipList [[], [0], [1, 2, 3], [-2, 7]])
               (P.map ZipList [[], [True], [False, True]])
               (P.map ZipList [[], ['a'], ['b', 'c', 'd']])
         ]
