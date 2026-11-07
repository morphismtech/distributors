-- The laws are stated as written, which HLint would simplify.
{- HLINT ignore "Use <$>" -}
{- HLINT ignore "Alternative law, left identity" -}
{- HLINT ignore "Alternative law, right identity" -}
{- HLINT ignore "Monad law, left identity" -}
{- HLINT ignore "Monad law, right identity" -}
{- HLINT ignore "Use >=>" -}
module Properties.Homogeneous (homogeneousProperties) where

import Control.Applicative
import Control.Arrow ((+++))
import Control.Monad ((<=<))
import Data.Functor.Compose (Compose (..))
import Data.Foldable (toList)
import Data.List (transpose)
import Data.Int (Int8)
import Data.Maybe (fromMaybe)
import Data.Monoid.Disjunctive
import Data.Profunctor
import Data.Profunctor.Monadic (Monadic)
import Data.Profunctor.Monoidal (Monoidal)
import Data.Profunctor.Monoidal.Cocartesian
import Data.Proxy (Proxy (..))
import Data.Traversable.Homogeneous
import Data.Void
import GHC.Generics (Par1 (..), (:*:) (..))
import Numeric.Natural (Natural)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck
import Witherable (Filterable (..))

-- | Types of finitely many values, to observe profunctors on all inputs.
class Eq s => Finite s where
  universe :: [s]
instance Finite () where
  universe = [()]
instance Finite Bool where
  universe = [False, True]
instance Finite Void where
  universe = []
instance (Finite a, Finite b) => Finite (Either a b) where
  universe = map Left universe <> map Right universe

-- | An `Indexing`'s count, indices of all sources, & selections, a little past.
indexing :: Finite s => Indexing s t -> (Natural, [Natural], [Maybe t])
indexing (Indexing count which select) =
  (count, map which universe, map select [0 .. count + 1])

natural :: Gen Natural
natural = fromInteger . getNonNegative <$> arbitrary

genIndexing :: forall s t. Finite s => Gen t -> Gen (Indexing s t)
genIndexing gen = do
  count <- (`mod` 5) <$> natural
  which <- vectorOf (length (universe :: [s])) natural
  selected <- vectorOf (fromIntegral count) gen
  pure $ Indexing count
    (\s -> fromMaybe 0 (lookup s (zip universe which)))
    (\i -> lookup i (zip [0 ..] selected))

lunit :: Profunctor p => p a b -> p (Either Void a) (Either Void b)
lunit = dimap (either absurd id) Right

runit :: Profunctor p => p a b -> p (Either a Void) (Either b Void)
runit = dimap (either id absurd) Left

assocE :: Either (Either a b) c -> Either a (Either b c)
assocE = either (either Left (Right . Left)) (Right . Right)

unassocE :: Either a (Either b c) -> Either (Either a b) c
unassocE = either (Left . Left) (either (Left . Right) Right)

swapE :: Either a b -> Either b a
swapE = either Right Left

-- | All the sources of a shape, of a finite type.
sources :: (Traversable f, Finite s) => f () -> [f s]
sources shape = traverse (const universe) shape

-- | A function of sources, by a table of its results.
tabulated :: (Foldable f, Eq s) => [f s] -> [r] -> r -> f s -> r
tabulated inputs results def ss =
  fromMaybe def (lookup (toList ss) (zip (map toList inputs) results))

-- | Observing & generating `Zipporah`s of a profunctor & a functor.
data Zipper p g h = Zipper
  { observeZipper
      :: forall f s t. (Traversable f, Finite s)
      => f () -> Zipporah p f g s t -> [h t]
  , generateZipper
      :: forall f s t. (Traversable f, Finite s)
      => f () -> Gen t -> Gen (Zipporah p f g s t)
  }

-- | `Zipporah`s of functions, to an `Alternative`.
functionZipper :: Alternative g => (forall t. Gen t -> Gen (g t)) -> Zipper (->) g g
functionZipper genG = Zipper
  { observeZipper = \shape (Zipporah z) -> map z (sources shape)
  , generateZipper = \shape gen -> do
      let inputs = sources shape
      results <- vectorOf (length inputs) (genG gen)
      pure (Zipporah (tabulated inputs results empty))
  }

-- | `Zipporah`s of `Star`s of a writer, to `Maybe`.
writerZipper :: Zipper (Star ((,) [Int])) Maybe (Compose ((,) [Int]) Maybe)
writerZipper = Zipper
  { observeZipper = \shape (Zipporah (Star z)) -> map (Compose . z) (sources shape)
  , generateZipper = \shape gen -> do
      let inputs = sources shape
      results <- vectorOf (length inputs)
        ((,) <$> resize 2 arbitrary <*> liftArbitrary gen)
      pure (Zipporah (Star (tabulated inputs results ([], Nothing))))
  }

-- | The laws of `Zipporah`, up to `Alternator`, of the sources of a shape.
zippingLaws
  :: forall p g h f.
     ( Choice p, Monoidal p, Alternative g, Filterable g, Traversable f
     , forall t. Eq t => Eq (h t), forall t. Show t => Show (h t) )
  => Zipper p g h -> String -> f () -> Spec
zippingLaws zipper name shape = describe name $ do
  let
    obs :: Finite s => Zipporah p f g s t -> [h t]
    obs = observeZipper zipper shape
    gen :: Finite s => Gen t -> Gen (Zipporah p f g s t)
    gen = generateZipper zipper shape
    z = gen arbitrary :: Gen (Zipporah p f g Bool Int)
    zf = gen (applyFun <$> arbitrary) :: Gen (Zipporah p f g Bool (Int -> Int))
    ze = gen arbitrary :: Gen (Zipporah p f g (Either Bool ()) (Either Int ()))
  prop "dimap id id = id" $ forAllBlind z $ \p ->
    obs (dimap id id p) === obs p
  prop "dimap (f . g) (h . i) = dimap g h . dimap f i" $ forAllBlind z $
    \p (Fun _ f) (Fun _ g) (Fun _ h) (Fun _ i) ->
      obs (dimap (f . g) (h . i) p :: Zipporah p f g Bool Int)
        === obs (dimap g (h :: Int -> Int) (dimap (f :: Bool -> Bool) i p))
  prop "pure id <*> v = v" $ forAllBlind z $ \v ->
    obs (pure id <*> v) === obs v
  prop "pure (.) <*> u <*> v <*> w = u <*> (v <*> w)" $
    forAllBlind zf $ \u -> forAllBlind zf $ \v -> forAllBlind z $ \w ->
      obs (pure (.) <*> u <*> v <*> w) === obs (u <*> (v <*> w))
  prop "pure f <*> pure x = pure (f x)" $ \(Fun _ f) (x :: Int) ->
    obs (pure f <*> pure x :: Zipporah p f g Bool Int)
      === obs (pure (f x) :: Zipporah p f g Bool Int)
  prop "u <*> pure y = pure ($ y) <*> u" $ forAllBlind zf $ \u (y :: Int) ->
    obs (u <*> pure y) === obs (pure ($ y) <*> u)
  prop "empty <|> x = x = x <|> empty" $ forAllBlind z $ \x ->
    obs (empty <|> x) === obs x .&&. obs (x <|> empty) === obs x
  prop "(x <|> y) <|> w = x <|> (y <|> w)" $
    forAllBlind z $ \x -> forAllBlind z $ \y -> forAllBlind z $ \w ->
      obs ((x <|> y) <|> w) === obs (x <|> (y <|> w))
  prop "mapMaybe Just = id" $ forAllBlind z $ \p ->
    obs (mapMaybe Just p) === obs p
  prop "mapMaybe f . mapMaybe g = mapMaybe (f <=< g)" $ forAllBlind z $
    \p (Fun _ f) (Fun _ g) ->
      obs (mapMaybe (f :: Int -> Maybe Int) (mapMaybe (g :: Int -> Maybe Int) p))
        === obs (mapMaybe (f <=< g) p)
  prop "zeroP >+< p = lunit p" $ forAllBlind z $ \p ->
    obs (zeroP >+< p) === obs (lunit p)
  prop "p >+< zeroP = runit p" $ forAllBlind z $ \p ->
    obs (p >+< zeroP) === obs (runit p)
  prop "p >+< q >+< r = assoc ((p >+< q) >+< r)" $
    forAllBlind z $ \p -> forAllBlind z $ \q -> forAllBlind z $ \r ->
      obs (p >+< q >+< r) === obs (dimap unassocE assocE ((p >+< q) >+< r))
  prop "dimap (f +++ g) (h +++ i) (p >+< q) = dimap f h p >+< dimap g i q" $
    forAllBlind z $ \p -> forAllBlind z $ \q (Fun _ f) (Fun _ g) (Fun _ h) (Fun _ i) ->
        obs (dimap (f +++ g) (h +++ i) (p >+< q)
          :: Zipporah p f g (Either Bool Bool) (Either Int Int))
          === obs (dimap f (h :: Int -> Int) p >+< dimap g (i :: Int -> Int) q)
  prop "rmap Left = lmap Left . left'" $ forAllBlind z $ \p ->
    obs (rmap Left p :: Zipporah p f g Bool (Either Int ()))
      === obs (lmap Left (left' p))
  prop "left' = dimap swapE swapE . right'" $ forAllBlind z $ \p ->
    obs (left' p :: Zipporah p f g (Either Bool ()) (Either Int ()))
      === obs (dimap swapE swapE (right' p))
  prop "left' . left' = dimap assocE unassocE . left'" $ forAllBlind z $ \p ->
    obs (left' (left' p)
      :: Zipporah p f g (Either (Either Bool ()) ()) (Either (Either Int ()) ()))
      === obs (dimap assocE unassocE (left' p))
  prop "unleft = unright . dimap swapE swapE" $ forAllBlind ze $ \p ->
    obs (unleft p) === obs (unright (dimap swapE swapE p))
  prop "rmap (either id absurd) = unleft . lmap (either id absurd)" $
    forAllBlind (gen (Left <$> arbitrary)
      :: Gen (Zipporah p f g Bool (Either Int Void))) $ \p ->
        obs (rmap (either id absurd) p)
          === obs (unleft (lmap (either id absurd) p) :: Zipporah p f g Bool Int)
  prop "left' = alternate . Left" $ forAllBlind z $ \p ->
    obs (left' p :: Zipporah p f g (Either Bool ()) (Either Int ()))
      === obs (alternate (Left p)
        :: Zipporah p f g (Either Bool ()) (Either Int ()))
  prop "right' = alternate . Right" $ forAllBlind z $ \p ->
    obs (right' p :: Zipporah p f g (Either () Bool) (Either () Int))
      === obs (alternate (Right p)
        :: Zipporah p f g (Either () Bool) (Either () Int))
  prop "x >+< y = alternate (Left x) >|< alternate (Right y)" $
    forAllBlind z $ \x -> forAllBlind z $ \y ->
      obs (x >+< y) === obs (alternate (Left x) >|< alternate (Right y))

-- | The `Monad` laws of `Zipporah`, to `Maybe`, of the sources of a shape.
zippingMonadLaws
  :: forall p h f.
     ( Monadic p, Traversable f
     , forall t. Eq t => Eq (h t), forall t. Show t => Show (h t) )
  => Zipper p Maybe h -> String -> f () -> Spec
zippingMonadLaws zipper name shape = describe name $ do
  let
    obs :: Finite s => Zipporah p f Maybe s t -> [h t]
    obs = observeZipper zipper shape
    zb = generateZipper zipper shape arbitrary :: Gen (Zipporah p f Maybe Bool Bool)
    kleisli = (\(k0, k1) b -> if b then k0 else k1) <$> ((,) <$> zb <*> zb)
  prop "pure a >>= k = k a" $ forAllBlind kleisli $ \k a ->
    obs (pure a >>= k) === obs (k a)
  prop "m >>= pure = m" $ forAllBlind zb $ \m ->
    obs (m >>= pure) === obs m
  prop "(m >>= k) >>= h = m >>= (\\x -> k x >>= h)" $
    forAllBlind zb $ \m -> forAllBlind kleisli $ \k -> forAllBlind kleisli $ \h ->
      obs ((m >>= k) >>= h) === obs (m >>= (\x -> k x >>= h))

-- | The laws of `Zipporah`s, of no, two & three sources.
zipporahLaws :: Spec
zipporahLaws = do
  let
    shapes :: (forall f. Traversable f => String -> f () -> Spec) -> Spec
    shapes laws = do
      laws "of no sources" Proxy
      laws "of two sources" (Par1 () :*: Par1 ())
      laws "of three sources" (Par1 () :*: Par1 () :*: Par1 ())
    maybes = functionZipper liftArbitrary
    lists = functionZipper (\gen -> choose (0, 2) >>= (`vectorOf` gen))
  describe "Zipporah (->) f Maybe" $ do
    shapes (zippingLaws maybes)
    shapes (zippingMonadLaws maybes)
  describe "Zipporah (->) f []" $ shapes (zippingLaws lists)
  describe "Zipporah (Star ((,) [Int])) f Maybe" $ do
    shapes (zippingLaws writerZipper)
    shapes (zippingMonadLaws writerZipper)

homogeneousProperties :: Spec
homogeneousProperties = do
  describe "Indexing" $ do
    let ix = genIndexing arbitrary :: Gen (Indexing Bool Int)
        ixf = genIndexing (applyFun <$> arbitrary)
          :: Gen (Indexing Bool (Int -> Int))
    prop "pure id <*> v = v" $ forAllBlind ix $ \v ->
      indexing (pure id <*> v) === indexing v
    prop "pure (.) <*> u <*> v <*> w = u <*> (v <*> w)" $
      forAllBlind ixf $ \u -> forAllBlind ixf $ \v -> forAllBlind ix $ \w ->
        indexing (pure (.) <*> u <*> v <*> w) === indexing (u <*> (v <*> w))
    prop "u <*> pure y = pure ($ y) <*> u" $ forAllBlind ixf $ \u (y :: Int) ->
      indexing (u <*> pure y) === indexing (pure ($ y) <*> u)
    prop "zeroP >+< p = lunit p" $ forAllBlind ix $ \p ->
      indexing (zeroP >+< p) === indexing (lunit p)
    prop "p >+< zeroP = runit p" $ forAllBlind ix $ \p ->
      indexing (p >+< zeroP) === indexing (runit p)
    prop "p >+< q >+< r = assoc ((p >+< q) >+< r)" $
      forAllBlind ix $ \p -> forAllBlind ix $ \q -> forAllBlind ix $ \r ->
        indexing (p >+< q >+< r)
          === indexing (dimap unassocE assocE ((p >+< q) >+< r))
    prop "unleft = unright . dimap swapE swapE" $
      forAllBlind (genIndexing arbitrary
        :: Gen (Indexing (Either Bool ()) (Either Int ()))) $ \p ->
          indexing (unleft p) === indexing (unright (dimap swapE swapE p))
    prop "rmap (either id absurd) = unleft . lmap (either id absurd)" $
      forAllBlind (genIndexing (Left <$> arbitrary)
        :: Gen (Indexing Bool (Either Int Void))) $ \p ->
          indexing (rmap (either id absurd) p)
            === indexing (unleft (lmap (either id absurd) p) :: Indexing Bool Int)
  zipporahLaws
  describe "Enumerable & Homogeneous" $ do
    it "numbers copies left to right" $
      map fromEnumerable [(LT, ()), (EQ, ()), (GT, ())] `shouldBe` [0, 1, 2]
    prop "toEnumerable inverts fromEnumerable" $ \(c :: Char) ->
      map (toEnumerable c) [0 .. 3]
        === map Just [(LT, c), (EQ, c), (GT, c)] <> [Nothing :: Maybe (Ordering, Char)]
        .&&. fmap fromEnumerable (toEnumerable c 2 :: Maybe (Ordering, Char))
          === Just 2
    prop "fromEnumerable is fromEnum, from minBound" $ \(e :: Int8) (c :: Char) ->
      fromEnumerable (e, c)
        === fromIntegral (fromEnum e - fromEnum (minBound :: Int8))
    prop "succEnumerable is succ, but at maxBound" $ \(e :: Ordering) (c :: Char) ->
      succEnumerable (e, c)
        === if e == maxBound then Nothing else Just (succ e, c)
    prop "predEnumerable is pred, but at minBound" $ \(e :: Int8) (c :: Char) ->
      predEnumerable (e, c)
        === if e == minBound then Nothing else Just (pred e, c)
    prop "enumerateFrom is enumFrom" $ \(e :: Ordering) (c :: Char) ->
      enumerateFrom (e, c) === [(e', c) | e' <- [e ..]]
    prop "zipWithHomogeneous zips lists of the same length" $
      \(Fun _ f) (xs :: [Int]) (ys :: [Int]) ->
        zipWithHomogeneous (curry f) xs ys === if length xs == length ys
          then Just (zipWith (curry f) xs ys :: [Int])
          else Nothing
    prop "zipWithHomogeneous3 is zipWith3, of the same lengths" $
      \(Fun _ f) (xs :: [Int]) (ys :: [Int]) (zs :: [Int]) ->
        zipWithHomogeneous3 (\x y z -> f (x, y, z) :: Int) xs ys zs
          === if length xs == length ys && length ys == length zs
            then Just (zipWith3 (\x y z -> f (x, y, z)) xs ys zs)
            else Nothing
    it "zips no sources of a sum as its first copy" $
      zipHomogeneous (\Proxy -> Just 'a') (Proxy :: Proxy (Maybe Char))
        `shouldBe` Just (Just 'a')
    prop "transposeHomogeneous is transpose, of the same lengths" $
      \(xs :: [Int]) (xss :: [[Int]]) ->
        transposeHomogeneous (xs : xss)
          === if all ((== length xs) . length) xss
            then Just (transpose (xs : xss))
            else Nothing
    prop "zipWithHomogeneousM acts on the positions which match" $
      \(xs :: [Int]) (ys :: [Int]) ->
        zipWithHomogeneousM (\x y -> ([x], x + y)) xs ys
          === ( take (min (length xs) (length ys)) xs
              , if length xs == length ys then Just (zipWith (+) xs ys) else Nothing )
