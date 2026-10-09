# Maintained experiments

These modules are separate from the public library. The `hscats-examples` test
target compiles every module and runs the illustrative computations. It is
included in `cabal test all`.

```sh
cabal test hscats-examples --offline --test-show-details=direct
cabal repl test:hscats-examples
```

| Module | Scope and validation |
| --- | --- |
| `CategoryExamples` | Single-object monoids, endomorphisms, the terminal category, and natural-number inequalities. Preserves the abstract monoid compile examples and checks concrete identities/composition. |
| `KanExamples` | Existential right Kan extension and codensity tags, currently targeting `Types`. Examples evaluate extensions along `Id`, map values and transformations, and use the adjunction unit/counit. |
| `FreeExamples` | Church-encoded free-monad experiment restricted to adjunction composites through `Types`. Examples interpret and map an operation using a state effect; this is not a general free-monad API. |
| `RepresentableExamples` | The representable adjunction into `Op Types` and an existential Coyoneda encoding, with transposition and evaluation examples. |
| `MonoidalSketches` | Proposed braided/symmetric/closed class signatures. Compile-checked only: there are no instances or coherence tests, and these classes are not a public contract. |

The runtime examples check the illustrated behavior; they do not establish all
categorical laws for these experimental encodings. Library law checks and the
active state, traversal, and recursion-scheme examples remain under `test/`.

Obsolete commented fixed-point/vector and polymorphic-recursion experiments
were removed. Any reintroduction should be a compiling, named example here.
The unused `ProductD`/`ProductF` encoding was retired; the library can express
that object action with `(∧) • (f &&& g)`. The unused `TraversableV2` proposal
was also retired; the exercised traversal formulation remains in `test/Main.hs`.
