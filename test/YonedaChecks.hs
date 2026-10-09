module YonedaChecks (checks) where

import AdjunctionChecks (OnlyTrue (..))
import Cats
import Prelude (Bool (..), Int, String)
import Prelude qualified as P

checks :: [(String, Bool)]
checks =
  [ ( "HomTo maps by precomposition",
      map (HomTo Types Int) (OP (P.length :: String -> Int)) (P.+ 3) "abcd" P.== 7
    ),
    ( "HomFrom maps by postcomposition",
      map (HomFrom Types Int) (P.show :: Int -> String) (P.* 3) 7 P.== "21"
    ),
    ( "Yoneda varies the fixed target",
      (map (YonedaEmbedding Types) (P.show :: Int -> String) $$ Bool) P.fromEnum True P.== "1"
    ),
    ( "Coyoneda varies the fixed source contravariantly",
      (map (CoyonedaEmbedding Types) (OP (P.length :: String -> Int)) $$ Bool) P.even "abcd" P.== True
    ),
    ( "Yoneda components are natural in the source",
      let t = map (YonedaEmbedding Types) (P.show :: Int -> String)
          l = map (HomTo Types String) (OP P.length) ∘ (t $$ Int)
          r = (t $$ String) ∘ map (HomTo Types Int) (OP P.length)
       in P.all (\s -> l (P.+ 3) s P.== r (P.+ 3) s) ["", "a", "abc"]
    ),
    ( "Coyoneda components are natural in the target",
      let t = map (CoyonedaEmbedding Types) (OP (P.length :: String -> Int))
          l = map (HomFrom Types String) P.show ∘ (t $$ Bool)
          r = (t $$ String) ∘ map (HomFrom Types Int) P.show
       in P.all (\s -> l P.even s P.== r P.even s) ["", "a", "abc"]
    ),
    ( "Representables preserve evidence for constrained non-Type objects",
      case
          ( map (type (HomTo OnlyTrue 'True)) (OP (TArrow (P.+ 1))) (TArrow (P.* 3)),
            map (type (HomFrom OnlyTrue 'True)) (TArrow (P.+ 1)) (TArrow (P.* 3))
          )
        of
          (TArrow l, TArrow r) -> P.all (\n -> l n P.== 3 P.* (n P.+ 1) P.&& r n P.== 3 P.* n P.+ 1) [-3 .. 3]
    )
  ]
