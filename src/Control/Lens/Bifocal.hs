module Control.Lens.Bifocal
  ( Bifocal
  , ABifocal
  ) where

-- import Control.Arrow
import Control.Lens.Monocle
-- import Control.Lens.Internal.Token
-- import Data.Functor.Alt
import Data.Functor.Identity
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Void

type Bifocal s t a b = forall p f.
  (Distributor p, Applicative f) => p a (f b) -> p s (f t)

type ABifocal s t a b =
  Dist (Monocular a b) a (Identity b)
    -> Dist (Monocular a b) s (Identity t)

runBinocular
  :: Distributor p
  => Dist (Monocular a b) s t
  -> (b -> t)
  -> p a b
  -> p s t
runBinocular (DistVoid k) f p = dimap (absurd . k) f p
runBinocular (DistEither k x y) f p = dither k id id (runMonocular x (\_ -> p)) (runBinocular y f p)
