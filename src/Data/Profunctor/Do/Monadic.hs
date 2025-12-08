module Data.Profunctor.Do.Monadic
  ( -- *
    (>>=)
  , (>>)
  , fail
  , return
  , boundRec
  ) where

import Control.Lens
import Control.Monad.Fix
import Data.Profunctor.Monadic
import Prelude hiding ((>>), (>>=), fail)
import qualified Prelude

(>>=)
  :: (Monadic m p, forall x. MonadFix (p m x))
  => p m a a -> (a -> p m b b) -> p m b b
infixl 1 >>=
x >>= f = mdo
  a <- lmap (const a) x
  f a

(>>)
  :: (Monadic m p, forall x. MonadFix (p m x))
  => p m a a -> p m b b -> p m b b
infixl 1 >>
x >> y = x >>= const y

fail
  :: (Monadic m p, MonadFail m)
  => String -> p m a a
fail = liftP . Prelude.fail

boundRec
  :: (Monadic m p, Applicative m, forall x. MonadFix (p m x))
  => (a -> Optic' (p m) m b ()) -> Optic' (p m) m b a
boundRec f = monochrome (\a -> a >>= rmap withMonochrome_ f)
