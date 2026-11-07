-- The laws are stated as written, which HLint would simplify.
{- HLINT ignore "Use <$>" -}
{- HLINT ignore "Alternative law, left identity" -}
{- HLINT ignore "Alternative law, right identity" -}
{- HLINT ignore "Monad law, left identity" -}
{- HLINT ignore "Monad law, right identity" -}
{- HLINT ignore "Use >=>" -}
module Properties.Homogeneous (homogeneousProperties) where

import Control.Applicative
import Data.Foldable (toList)
import Data.Maybe (fromMaybe)
import Data.Monoid.Disjunctive
import Data.Profunctor
import Data.Profunctor.Monoidal.Cocartesian
import Data.Proxy (Proxy (..))
import Data.Traversable.Homogeneous
import Data.Void
import Numeric.Natural (Natural)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

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

counting :: Finite s => Counting s t -> (Natural, [Natural])
counting (Counting count which) = (count, map which universe)

zipping :: Finite s => Zipping s t -> [Maybe t]
zipping (Zipping z) = [z s0 s1 | s0 <- universe, s1 <- universe]

natural :: Gen Natural
natural = fromInteger . getNonNegative <$> arbitrary

genCounting :: forall s t. Finite s => Gen (Counting s t)
genCounting = do
  count <- natural
  which <- vectorOf (length (universe :: [s])) natural
  pure (Counting count (\s -> fromMaybe 0 (lookup s (zip universe which))))

genZipping :: Finite s => Gen t -> Gen (Zipping s t)
genZipping gen = do
  let pairs = [(s0, s1) | s0 <- universe, s1 <- universe]
  results <- vectorOf (length pairs) (liftArbitrary gen)
  pure (Zipping (\s0 s1 -> fromMaybe Nothing (lookup (s0, s1) (zip pairs results))))

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

-- | Two & three sources, for `MultiZipping`.
data Two a = Two a a
  deriving stock (Functor, Foldable, Traversable)
data Three a = Three a a a
  deriving stock (Functor, Foldable, Traversable)

multiZipping
  :: (Traversable f, Finite s) => f () -> MultiZipping f s t -> [Maybe t]
multiZipping shape (MultiZipping z) = map z (traverse (const universe) shape)

genMultiZipping
  :: (Traversable f, Finite s) => f () -> Gen t -> Gen (MultiZipping f s t)
genMultiZipping shape gen = do
  let inputs = map toList (traverse (const universe) shape)
  results <- vectorOf (length inputs) (liftArbitrary gen)
  pure (MultiZipping (\ss -> fromMaybe Nothing (lookup (toList ss) (zip inputs results))))

-- | The laws of `MultiZipping`, of the sources of a shape.
multiZippingLaws :: forall f. Traversable f => String -> f () -> Spec
multiZippingLaws name shape = describe ("MultiZipping " <> name) $ do
  let
    obs :: Finite s => MultiZipping f s t -> [Maybe t]
    obs = multiZipping shape
    z = genMultiZipping shape arbitrary :: Gen (MultiZipping f Bool Int)
    zf = genMultiZipping shape (applyFun <$> arbitrary)
      :: Gen (MultiZipping f Bool (Int -> Int))
    ze = genMultiZipping shape arbitrary
      :: Gen (MultiZipping f (Either Bool ()) (Either Int ()))
  prop "pure (.) <*> u <*> v <*> w = u <*> (v <*> w)" $
    forAllBlind zf $ \u -> forAllBlind zf $ \v -> forAllBlind z $ \w ->
      obs (pure (.) <*> u <*> v <*> w) === obs (u <*> (v <*> w))
  prop "zeroP >+< p = lunit p" $ forAllBlind z $ \p ->
    obs (zeroP >+< p) === obs (lunit p)
  prop "p >+< zeroP = runit p" $ forAllBlind z $ \p ->
    obs (p >+< zeroP) === obs (runit p)
  prop "p >+< q >+< r = assoc ((p >+< q) >+< r)" $
    forAllBlind z $ \p -> forAllBlind z $ \q -> forAllBlind z $ \r ->
      obs (p >+< q >+< r) === obs (dimap unassocE assocE ((p >+< q) >+< r))
  prop "rmap Left = lmap Left . left'" $ forAllBlind z $ \p ->
    obs (rmap Left p :: MultiZipping f Bool (Either Int ()))
      === obs (lmap Left (left' p))
  prop "left' = dimap swapE swapE . right'" $ forAllBlind z $ \p ->
    obs (left' p :: MultiZipping f (Either Bool ()) (Either Int ()))
      === obs (dimap swapE swapE (right' p))
  prop "left' . left' = dimap assocE unassocE . left'" $ forAllBlind z $ \p ->
    obs (left' (left' p)
      :: MultiZipping f (Either (Either Bool ()) ()) (Either (Either Int ()) ()))
      === obs (dimap assocE unassocE (left' p))
  prop "unleft = unright . dimap swapE swapE" $ forAllBlind ze $ \p ->
    obs (unleft p) === obs (unright (dimap swapE swapE p))
  prop "x >+< y = alternate (Left x) >|< alternate (Right y)" $
    forAllBlind z $ \x -> forAllBlind z $ \y ->
      obs (x >+< y) === obs (alternate (Left x) >|< alternate (Right y))

type C = Counting Bool ()
type Z = Zipping Bool Int

homogeneousProperties :: Spec
homogeneousProperties = do
  describe "Counting" $ do
    let c = genCounting :: Gen C
    prop "pure id <*> v = v" $ forAllBlind c $ \v ->
      counting (pure id <*> v) === counting v
    prop "pure (.) <*> u <*> v <*> w = u <*> (v <*> w)" $
      forAllBlind c $ \u -> forAllBlind c $ \v -> forAllBlind c $ \w ->
        counting (pure (.) <*> (id <$ u) <*> (id <$ v) <*> w)
          === counting ((id <$ u) <*> ((id <$ v) <*> w))
    prop "u <*> pure y = pure ($ y) <*> u" $ forAllBlind c $ \u ->
      counting ((id <$ u) <*> pure ()) === counting (pure ($ ()) <*> (id <$ u))
    prop "zeroP >+< p = lunit p" $ forAllBlind c $ \p ->
      counting (zeroP >+< p) === counting (lunit p)
    prop "p >+< zeroP = runit p" $ forAllBlind c $ \p ->
      counting (p >+< zeroP) === counting (runit p)
    prop "p >+< q >+< r = assoc ((p >+< q) >+< r)" $
      forAllBlind c $ \p -> forAllBlind c $ \q -> forAllBlind c $ \r ->
        counting (p >+< q >+< r)
          === counting (dimap unassocE assocE ((p >+< q) >+< r))
    let ce = genCounting :: Gen (Counting (Either Bool ()) (Either () ()))
    prop "unleft = unright . dimap swapE swapE" $ forAllBlind ce $ \p ->
      counting (unleft p) === counting (unright (dimap swapE swapE p))
    prop "rmap (either id absurd) = unleft . lmap (either id absurd)" $
      forAllBlind (genCounting :: Gen (Counting Bool (Either () Void))) $ \p ->
        counting (rmap (either id absurd) p)
          === counting (unleft (lmap (either id absurd) p) :: C)
  describe "Zipping" $ do
    let z = genZipping arbitrary :: Gen Z
        zf = genZipping (applyFun <$> arbitrary)
          :: Gen (Zipping Bool (Int -> Int))
    prop "pure id <*> v = v" $ forAllBlind z $ \v ->
      zipping (pure id <*> v) === zipping v
    prop "pure (.) <*> u <*> v <*> w = u <*> (v <*> w)" $
      forAllBlind zf $ \u -> forAllBlind zf $ \v -> forAllBlind z $ \w ->
        zipping (pure (.) <*> u <*> v <*> w) === zipping (u <*> (v <*> w))
    prop "pure f <*> pure x = pure (f x)" $ \(Fun _ f) (x :: Int) ->
      zipping (pure f <*> pure x :: Z) === zipping (pure (f x) :: Z)
    prop "u <*> pure y = pure ($ y) <*> u" $ forAllBlind zf $ \u (y :: Int) ->
      zipping (u <*> pure y) === zipping (pure ($ y) <*> u)
    prop "empty <|> x = x = x <|> empty" $ forAllBlind z $ \x ->
      zipping (empty <|> x) === zipping x .&&. zipping (x <|> empty) === zipping x
    prop "(x <|> y) <|> w = x <|> (y <|> w)" $
      forAllBlind z $ \x -> forAllBlind z $ \y -> forAllBlind z $ \w ->
        zipping ((x <|> y) <|> w) === zipping (x <|> (y <|> w))
    let zb = genZipping arbitrary :: Gen (Zipping Bool Bool)
        kleisli = (\f t -> if t then fst f else snd f) <$> ((,) <$> zb <*> zb)
    prop "pure a >>= k = k a" $ forAllBlind kleisli $ \k a ->
      zipping (pure a >>= k) === zipping (k a)
    prop "m >>= pure = m" $ forAllBlind zb $ \m ->
      zipping (m >>= pure) === zipping m
    prop "(m >>= k) >>= h = m >>= (\\x -> k x >>= h)" $
      forAllBlind zb $ \m -> forAllBlind kleisli $ \k -> forAllBlind kleisli $ \h ->
        zipping ((m >>= k) >>= h) === zipping (m >>= (\x -> k x >>= h))
    prop "zeroP >+< p = lunit p" $ forAllBlind z $ \p ->
      zipping (zeroP >+< p) === zipping (lunit p)
    prop "p >+< zeroP = runit p" $ forAllBlind z $ \p ->
      zipping (p >+< zeroP) === zipping (runit p)
    prop "p >+< q >+< r = assoc ((p >+< q) >+< r)" $
      forAllBlind z $ \p -> forAllBlind z $ \q -> forAllBlind z $ \r ->
        zipping (p >+< q >+< r)
          === zipping (dimap unassocE assocE ((p >+< q) >+< r))
    prop "rmap Left = lmap Left . left'" $ forAllBlind z $ \p ->
      zipping (rmap Left p :: Zipping Bool (Either Int ()))
        === zipping (lmap Left (left' p))
    prop "left' = dimap swapE swapE . right'" $ forAllBlind z $ \p ->
      zipping (left' p :: Zipping (Either Bool ()) (Either Int ()))
        === zipping (dimap swapE swapE (right' p))
    prop "left' . left' = dimap assocE unassocE . left'" $ forAllBlind z $ \p ->
      zipping (left' (left' p) :: Zipping (Either (Either Bool ()) ()) (Either (Either Int ()) ()))
        === zipping (dimap assocE unassocE (left' p))
    let ze = genZipping arbitrary
          :: Gen (Zipping (Either Bool ()) (Either Int ()))
    prop "unleft = unright . dimap swapE swapE" $ forAllBlind ze $ \p ->
      zipping (unleft p) === zipping (unright (dimap swapE swapE p))
    prop "rmap (either id absurd) = unleft . lmap (either id absurd)" $
      forAllBlind (genZipping (Left <$> arbitrary)
        :: Gen (Zipping Bool (Either Int Void))) $ \p ->
          zipping (rmap (either id absurd) p)
            === zipping (unleft (lmap (either id absurd) p) :: Z)
    prop "left' = alternate . Left" $ forAllBlind z $ \p ->
      zipping (left' p :: Zipping (Either Bool ()) (Either Int ()))
        === zipping (alternate (Left p) :: Zipping (Either Bool ()) (Either Int ()))
    prop "x >+< y = alternate (Left x) >|< alternate (Right y)" $
      forAllBlind z $ \x -> forAllBlind z $ \y ->
        zipping (x >+< y)
          === zipping (alternate (Left x) >|< alternate (Right y))
  multiZippingLaws "of no sources" Proxy
  multiZippingLaws "of two sources" (Two () ())
  multiZippingLaws "of three sources" (Three () () ())
  describe "Enumerable & Homogeneous" $ do
    it "numbers copies left to right" $
      map indexEnumerable [False1 (), True1 ()] `shouldBe` [0, 1]
    prop "zipWithHomogeneous zips lists of the same length" $
      \(Fun _ f) (xs :: [Int]) (ys :: [Int]) ->
        zipWithHomogeneous (curry f) xs ys === if length xs == length ys
          then Just (zipWith (curry f) xs ys :: [Int])
          else Nothing
    prop "MultiZipping of two is Zipping" $
      \(Fun _ f) (xs :: [Int]) (ys :: [Int]) ->
        multiZipWith (\(Two x y) -> f (x, y) :: Int) (Two xs ys)
          === zipWithHomogeneous (curry f) xs ys
    prop "zipWithHomogeneous3 is zipWith3, of the same lengths" $
      \(Fun _ f) (xs :: [Int]) (ys :: [Int]) (zs :: [Int]) ->
        zipWithHomogeneous3 (\x y z -> f (x, y, z) :: Int) xs ys zs
          === if length xs == length ys && length ys == length zs
            then Just (zipWith3 (\x y z -> f (x, y, z)) xs ys zs)
            else Nothing
    it "zips no sources of a sum as its first copy" $
      multiZipWith (\Proxy -> 'a') (Proxy :: Proxy (Maybe Char))
        `shouldBe` Just (Just 'a')
  where
    multiZipWith
      :: (Homogeneous t, Traversable f) => (f a -> b) -> f (t a) -> Maybe (t b)
    multiZipWith f = runMultiZipping (homogeneously (MultiZipping (Just . f)))
