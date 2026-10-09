-- | Public facade for categories, functors, natural transformations, tensors,
-- profunctors, optics, and spans. Use qualified imports of "Cats.Applicative",
-- "Cats.Monad", and "Cats.Do" for their overlapping operation names.
-- 'Monad', 'Comonad', 'flatMap', and 'extend' are also available here;
-- 'unit', 'counit', 'join', and 'duplicate' here take an adjunction pair.
module Cats (module Exports) where

import Cats.Adjoint as Exports
import Cats.Associative as Exports
import Cats.Binary as Exports
import Cats.Cat as Exports
import Cats.Category as Exports
import Cats.Compose as Exports
import Cats.Constructor as Exports
import Cats.CrossProduct as Exports
import Cats.Curry as Exports
import Cats.Day as Exports
import Cats.Delta as Exports
import Cats.Eval as Exports
import Cats.Exponential as Exports
import Cats.Flip as Exports
import Cats.FromAdjoint as Exports
import Cats.Functor as Exports
import Cats.Hom as Exports
import Cats.Id as Exports
import Cats.Monad as Exports (Comonad, Monad, extend, flatMap)
import Cats.MonoidObject as Exports
import Cats.Monoidal as Exports
import Cats.Opposite as Exports
import Cats.Optics as Exports
import Cats.Procompose as Exports
import Cats.Profunctor as Exports
import Cats.Span as Exports
import Cats.Yoneda as Exports

-- How do I type that?
-- '₀' : ` 0 s`
-- '₁' : ` 1 s`
-- '₂' : ` 2 s`
-- '☼' : ` S U`
-- '∘' : ` O b`
-- '•' : ` o o`
-- '∈' : ` ( -`
-- '×' : ` / \`
-- '∧' : ` A N`
-- '∨' : ` O R`
-- '⊣' : ` u 22a3` or ` u 22a3`
-- '∀' : ` F A`
-- '∃' : ` T E`
