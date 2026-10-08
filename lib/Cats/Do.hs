-- | Qualified do-notation for any monad on 'Types'. Import this module
-- qualified and enable @QualifiedDo@. The explicit tag selects the operations
-- even when 'Act' does not determine its functor argument:
--
-- @
-- {-# LANGUAGE BlockArguments, QualifiedDo, RequiredTypeArguments, TypeAbstractions #-}
--
-- import Cats
-- import Cats.Do qualified as Do
-- import Prelude (Int, (+))
--
-- example :: [Int]
-- example = Do.with (type (Constructor [])) Do.do
--   x <- [1, 2]
--   Do.pure (x + 10)
-- @
--
-- Nested calls to 'with' may select different monads. This module supports
-- binding, sequencing, and pure values; refutable patterns require a failure
-- operation and are outside this interface.
module Cats.Do (MonadDo, with, (>>=), (>>), pure, BindDo, PureDo) where

import Cats.Category (Types, member)
import Cats.Functor
import Cats.Monad qualified as M
import Data.Proxy (Proxy (..))

-- | Binding operations supplied by 'with'. The abstract type can be used in
-- @?bind@ constraints on helpers that share the enclosing do block's monad.
newtype BindDo (m :: Types --> Types)
  = BindDo
      ( forall a b.
        Proxy b -> Act m a -> (a -> Act m b) -> Act m b
      )

-- | Unit operations supplied by 'with', for a helper's @?pure@ constraint.
newtype PureDo (m :: Types --> Types) = PureDo (forall a. a -> Act m a)

-- | A computation supplied with the operations selected by 'with'.
type MonadDo m =
  forall r.
  ((?bind :: BindDo m, ?pure :: PureDo m) => Act m r) -> Act m r

infixl 1 >>=, >>

-- | Sequence a computation and pass its result to the next one.
(>>=) :: forall m a b. (?bind :: BindDo m) => Act m a -> (a -> Act m b) -> Act m b
(>>=) = let BindDo f = ?bind in f @a (Proxy @b)

-- | Sequence computations, discarding the first result.
(>>) :: forall m a b. (?bind :: BindDo m) => Act m a -> Act m b -> Act m b
ma >> mb = (>>=) @m @a @b ma (\_ -> mb)

-- | Lift a value using the currently selected monad.
pure :: forall m a. (?pure :: PureDo m) => a -> Act m a
pure = let PureDo f = ?pure in f

-- | Supply the operations of a monad to a qualified do block.
with :: forall (m :: Types --> Types) -> (M.Monad m) => MonadDo m
with m body =
  -- Supply concrete Types object evidence before consulting the monad's
  -- quantified functor superclasses (also needed when Haddock typechecks).
  let ?bind =
        BindDo @m
          ( \(_ :: Proxy b) (ma :: Act m a) f ->
              member (type Types) a do
                member (type Types) b do
                  M.flatMap @a @b m f ma
          )
      ?pure = PureDo @m (\(x :: a) -> member (type Types) a (M.unit m a x))
   in body
