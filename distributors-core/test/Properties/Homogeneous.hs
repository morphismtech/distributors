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
import Control.Lens (ReifiedLens (..), ReifiedPrism (..), _Just, iview, over, preview, review, set, toListOf, traverseOf, view)
import Control.Lens.Diopter
import Control.Lens.Prismoid (APrismoid, clonePrismoid, lefted, severaled, severaled1, somed, withPrismoid)
import Control.Lens.Comonocle
import Control.Lens.Grate (cotraverseOf)
import Control.Lens.Monocle
import Control.Lens.PartialIso (withPartialIso)
import Control.Monad ((<=<))
import Data.Functor.Compose (Compose (..))
import Data.Complex (Complex (..))
import Data.Foldable (toList)
import Data.Functor.Identity (Identity (..))
import Data.List (transpose)
import Data.Int (Int8)
import Data.Maybe (fromMaybe)
import Data.Monoid.Disjunctive
import Data.Profunctor
import Data.Profunctor.Distributor (noSep)
import Data.Profunctor.Monadic (Monadic)
import Data.Profunctor.Monoidal (Monoidal)
import Data.Profunctor.Monoidal.Cocartesian
import Data.Proxy (Proxy (..))
import Data.Traversable.Homogeneous
import Data.Traversable.Homogeneous.Enumerable
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

-- | An `Enumerator`'s count, indices of all sources, & selections, a little past.
enumerator :: Finite s => Enumerator s t -> (Natural, [Natural], [Maybe t])
enumerator (Enumerator count which select) =
  (count, map which universe, map select [0 .. count + 1])

natural :: Gen Natural
natural = fromInteger . getNonNegative <$> arbitrary

genEnumerator :: forall s t. Finite s => Gen t -> Gen (Enumerator s t)
genEnumerator gen = do
  count <- (`mod` 5) <$> natural
  which <- vectorOf (length (universe :: [s])) natural
  selected <- vectorOf (fromIntegral count) gen
  pure $ Enumerator count
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
  describe "Enumerator" $ do
    let ix = genEnumerator arbitrary :: Gen (Enumerator Bool Int)
        ixf = genEnumerator (applyFun <$> arbitrary)
          :: Gen (Enumerator Bool (Int -> Int))
    prop "pure id <*> v = v" $ forAllBlind ix $ \v ->
      enumerator (pure id <*> v) === enumerator v
    prop "pure (.) <*> u <*> v <*> w = u <*> (v <*> w)" $
      forAllBlind ixf $ \u -> forAllBlind ixf $ \v -> forAllBlind ix $ \w ->
        enumerator (pure (.) <*> u <*> v <*> w) === enumerator (u <*> (v <*> w))
    prop "u <*> pure y = pure ($ y) <*> u" $ forAllBlind ixf $ \u (y :: Int) ->
      enumerator (u <*> pure y) === enumerator (pure ($ y) <*> u)
    prop "zeroP >+< p = lunit p" $ forAllBlind ix $ \p ->
      enumerator (zeroP >+< p) === enumerator (lunit p)
    prop "p >+< zeroP = runit p" $ forAllBlind ix $ \p ->
      enumerator (p >+< zeroP) === enumerator (runit p)
    prop "p >+< q >+< r = assoc ((p >+< q) >+< r)" $
      forAllBlind ix $ \p -> forAllBlind ix $ \q -> forAllBlind ix $ \r ->
        enumerator (p >+< q >+< r)
          === enumerator (dimap unassocE assocE ((p >+< q) >+< r))
    prop "unleft = unright . dimap swapE swapE" $
      forAllBlind (genEnumerator arbitrary
        :: Gen (Enumerator (Either Bool ()) (Either Int ()))) $ \p ->
          enumerator (unleft p) === enumerator (unright (dimap swapE swapE p))
    prop "rmap (either id absurd) = unleft . lmap (either id absurd)" $
      forAllBlind (genEnumerator (Left <$> arbitrary)
        :: Gen (Enumerator Bool (Either Int Void))) $ \p ->
          enumerator (rmap (either id absurd) p)
            === enumerator (unleft (lmap (either id absurd) p) :: Enumerator Bool Int)
  zipporahLaws
  describe "Comonocle & Diopter combinators" $ do
    prop "countComonocle _BoundedEnum is the number of values" $
      countComonocle (_BoundedEnum @Int8) === 256 .&&. countComonocle (_BoundedEnum @Bool) === 2
    prop "fromComonocle _BoundedEnum inverts indexComonocle" $ \(e :: Int8) ->
      preview (fromComonocle _BoundedEnum)
        (fst (iview (indexComonocle _BoundedEnum) e), ()) === Just e
    prop "succComonocle _BoundedEnum is succ, but at maxBound" $ \(e :: Int8) ->
      withPartialIso (succComonocle _BoundedEnum) const e
        === if e == maxBound then Nothing else Just (succ e)
    prop "predComonocle _BoundedEnum is pred, but at minBound" $ \(e :: Int8) ->
      withPartialIso (predComonocle _BoundedEnum) const e
        === if e == minBound then Nothing else Just (pred e)
    prop "enumerateComonocle _BoundedEnum is enumFrom" $ \(e :: Ordering) ->
      enumerateComonocle _BoundedEnum e === [e ..]
    prop "enumerateFromThenComonocle _BoundedEnum is enumFromThen" $
      \(e :: Int8) e' -> take 600 (enumerateFromThenComonocle _BoundedEnum e e')
        === take 600 [e, e' ..]
    prop "enumerateFromToComonocle _BoundedEnum is enumFromTo" $
      \(e :: Int8) e' -> enumerateFromToComonocle _BoundedEnum e e' === [e .. e']
    prop "enumerateFromThenToComonocle _BoundedEnum is enumFromThenTo" $
      \(e :: Int8) e' e'' ->
        take 600 (enumerateFromThenToComonocle _BoundedEnum e e' e'')
          === take 600 [e, e' .. e'']
    prop "zipMonocle at Identity sources is traverseOf" $ \(c :: Complex Int) ->
      let f x = if even x then Just x else Nothing
      in zipMonocle ditraversed (f . runIdentity) (Identity c)
        === traverseOf ditraversed f c
    prop "zipMonocle at Identity effects is cotraverseOf" $
      \(cs :: [Complex Int]) ->
        runIdentity (zipMonocle ditraversed (Identity . sum) cs)
          === cotraverseOf ditraversed sum cs
    prop "zipWithMonocle ditraversed zips componentwise" $
      \(x :+ y :: Complex Int) (x' :+ y') ->
        zipWithMonocle ditraversed (-) (x :+ y) (x' :+ y') === (x - x') :+ (y - y')
    prop "replicateMonocle ditraversed is replicateM 2" $ \(xs :: [Int]) ->
      map (toListOf ditraversed) (replicateMonocle ditraversed xs :: [Complex Int])
        === sequenceA [xs, xs]
    prop "withDitraversal splits into the foci, in order" $
      \(s :: (Int, Complex Int)) ->
        withDitraversal (crossMonocle id ditraversed)
          (\split _ -> toList (split s))
          === toListOf (crossMonocle id ditraversed) s
    prop "ditraversal inverts withDitraversal" $
      \(s :: (Int, Complex Int)) (Fun _ f :: Fun Int Int) ->
        withDitraversal (crossMonocle id ditraversed)
          (\split merge -> over (ditraversal (Ditraversal split merge)) f s)
          === over (crossMonocle id ditraversed) f s
    prop "withDitraversal inverts ditraversal" $
      \(x :: Int) y (Fun _ f :: Fun Int Int) ->
        let d = Ditraversal (uncurry (:+)) (\(u :+ v) -> (u, v))
        in withDitraversal (ditraversal d)
            (\split merge -> (toList (split (x, y)), merge (f <$> split (x, y))))
          === ([x, y], (f x, f y))
    it "tabulateMonocle numbers foci left to right" $
      toListOf ditraversed (tabulateMonocle ditraversed id :: Complex Natural)
        `shouldBe` [0, 1]
    prop "copiesComonocle has a copy for each, exactly one matching" $
      \(e :: Int8) ->
        length (copiesComonocle (_BoundedEnum @Int8)) === 256
          .&&. length
            [ () | Prism copy <- copiesComonocle _BoundedEnum
            , Just () <- [preview copy e] ] === 1
    prop "copiesComonocle are lawful prisms" $ \(s :: Either Int Int) a ->
      conjoin
        [ preview copy (review copy a) === Just a
            .&&. maybe (property True) (\a' -> review copy a' === s)
              (preview copy s)
        | Prism copy <- copiesComonocle (altComonocle id id) ]
    prop "fociMonocle has a focus for each, viewing toListOf" $
      \(s :: (Int, Complex Int)) ->
        [view foc s | Lens foc <- fociMonocle (crossMonocle id ditraversed)]
          === toListOf (crossMonocle id ditraversed) s
    prop "fociMonocle are lawful lenses" $ \(s :: (Int, Complex Int)) a b ->
      conjoin
        [ view foc (set foc a s) === a
            .&&. set foc (view foc s) s === s
            .&&. set foc b (set foc a s) === set foc b s
        | Lens foc <- fociMonocle (crossMonocle id ditraversed) ]
    prop "clonePrismoid keeps both directions" $
      \(xs :: [Int]) (e :: Either Int Char) (m :: Maybe Int) (Fun _ k :: Fun Int Int) ->
        let
          roundTrip :: APrismoid s s Int Int -> s -> Maybe s
          roundTrip o s = withPrismoid o $ \match build -> build . fmap k <$> match s
        in
          roundTrip (clonePrismoid somed) xs === roundTrip somed xs
            .&&. roundTrip (clonePrismoid lefted) e === roundTrip lefted e
            .&&. roundTrip (clonePrismoid _Just) m === roundTrip _Just m
            .&&. roundTrip (clonePrismoid manied) xs === roundTrip manied xs
    prop "a Prism, as a Prismoid, fails on a mismatch" $ \(m :: Maybe Int) ->
      withPrismoid (_Just :: APrismoid (Maybe Int) (Maybe Int) Int Int)
        (\match _ -> toList <$> match m)
        === fmap pure m
    prop "severaled1 noSep is somed, & severaled noSep is manied" $ \(xs :: [Int]) ->
      withPrismoid (severaled1 noSep :: APrismoid [Int] [Int] Int Int) (\match _ -> toList <$> match xs)
        === withPrismoid somed (\match _ -> toList <$> match xs)
        .&&. withPrismoid (severaled noSep :: APrismoid [Int] [Int] Int Int) (\match _ -> toList <$> match xs)
          === withPrismoid manied (\match _ -> toList <$> match xs)
    prop "somed matches one or more" $ \(xs :: [Int]) ->
      withPrismoid somed (\match _ -> toList <$> match xs)
        === if null xs then Nothing else Just xs
    prop "zipDiopter homogenized is zipHomogeneous" $ \(xss :: [[Int]]) ->
      zipDiopter homogenized (Just . sum) ([1, 2] : xss)
        === zipHomogeneous (Just . sum) ([1, 2 :: Int] : xss)
    prop "zipWithDiopter manied is zipWithHomogeneous" $ \(xs :: [Int]) ys ->
      zipWithDiopter manied (+) xs ys === zipWithHomogeneous (+) xs ys
  describe "Enumerable & Homogeneous" $ do
    let tagged = map (fst :: (Int8, Char) -> Int8)
    prop "enumerateFromThen is enumFromThen" $ \(e :: Int8) e' c ->
      take 600 (tagged (enumerateFromThen (e, c) (e', ())))
        === take 600 [e, e' ..]
    prop "enumerateFromTo is enumFromTo" $ \(e :: Int8) e' c ->
      tagged (enumerateFromTo (e, c) (e', ())) === [e .. e']
    prop "enumerateFromThenTo is enumFromThenTo" $ \(e :: Int8) e' e'' c ->
      take 600 (tagged (enumerateFromThenTo (e, c) (e', ()) (e'', ())))
        === take 600 [e, e' .. e'']
    prop "enumerate holds the first focus" $ \(e :: Int8) e' (c :: Char) ->
      all ((== c) . snd)
        (take 600 (enumerateFromThenTo (e, c) (e', ()) (maxBound, ())))
    it "numbers copies left to right" $
      map (fst . review fromEnumerable) [(LT, ()), (EQ, ()), (GT, ())]
        `shouldBe` [0, 1, 2]
    prop "fromEnumerable is a prism, inverting its review" $ \(c :: Char) ->
      map (\i -> preview fromEnumerable (i, c)) [0 .. 3]
        === map Just [(LT, c), (EQ, c), (GT, c)] <> [Nothing :: Maybe (Ordering, Char)]
        .&&. fmap (review fromEnumerable)
          (preview fromEnumerable (2, c) :: Maybe (Ordering, Char))
          === Just (2, c)
    prop "fromEnumerable is fromEnum, from minBound" $ \(e :: Int8) (c :: Char) ->
      review fromEnumerable (e, c)
        === (fromIntegral (fromEnum e - fromEnum (minBound :: Int8)), c)
    prop "succEnumerable is succ, but at maxBound" $ \(e :: Ordering) (c :: Char) ->
      withPartialIso succEnumerable const (e, c)
        === if e == maxBound then Nothing else Just (succ e, c)
    prop "predEnumerable is pred, but at minBound" $ \(e :: Int8) (c :: Char) ->
      withPartialIso predEnumerable const (e, c)
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
