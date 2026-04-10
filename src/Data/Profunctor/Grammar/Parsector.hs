{-|
Module      : Data.Profunctor.Grammar.Parsector
Description : grammar distributor with errors
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Leijen,
[Parsec: Direct Style Monadic Parser Combinators For The Real World]
(https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/parsec-paper-letter.pdf)
-}

module Data.Profunctor.Grammar.Parsector
  ( -- * Parsector
    Parsector (..)
  , parsecP
  , unparsecP
  , ParsecState (..)
  , ParsecError (..)
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Data.Function (fix)
import Control.Lens
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Lens.PartialIso
import Control.Monad
import Control.Monad.Fail.Try
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Profunctor.Monoidal
import Data.Tree
import GHC.Exts
import Prelude hiding (id, (.))
import Witherable

{- | `Parsector` is an invertible @LL(1)@ parser which is intended
to provide detailed error information, based on [Parsec]
(https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/parsec-paper-letter.pdf).
-}
newtype Parsector s a b = Parsector
  {runParsector :: forall x. (ParsecState s b -> x) -> ParsecState s a -> x}

{- | Run `Parsector` as a parser: consume tokens from @s@,
left to right, returning a `ParsecState` whose `parsecResult`
is either a successful output syntax value or a `ParsecError`. -}
parsecP
  :: Categorized (Item s)
  => Parsector s a b
  -> s -- ^ input stream
  -> ParsecState s b
parsecP p s = runParsector p id (ParsecState False 0 s mempty (Left mempty))

{- | Run `Parsector` as a printer: given a syntax value @a@ and
an input stream, append tokens to @s@ left to right,
returning a `ParsecState` whose `parsecResult` is
either a `ParsecError` or a successful output syntax value,
in which case, `parsecStream` is the output stream. -}
unparsecP
  :: Categorized (Item s)
  => Parsector s a b
  -> a -- ^ input syntax
  -> s -- ^ input stream
  -> ParsecState s b
unparsecP p a s = runParsector p id (ParsecState False 0 s mempty (Right a))

{- | `ParsecState` is both the input and output type of the
underlying function inside `Parsector`.
@Parsector s a b@ is equivalent to

@ParsecState s a -> ParsecState s b@

So `ParsecState` has a dual interpretation as input and output. -}
data ParsecState s a = ParsecState
  { parsecLooked :: !Bool
    {- ^ @True@ once the parser has consumed at least one token
    since the last `<|>` / `try` decision point.
    Controls LL(1) commitment: a failure with `parsecLooked` @True@
    is propagated immediately without trying alternatives.
    Reset to @False@ by `try` on failure.
    -}
  , parsecOffset :: !Word
    -- ^ Number of tokens consumed from the start of the stream.
  , parsecStream :: s -- ^ stream
  , parsecHint   :: ParsecError s
    {- ^ Hint: the merged `ParsecError`s from all empty-failing
    alternatives at the current position.
    Carried forward on the *success* path by `<|>` and `>>=` so that
    downstream failures include the full set of expected tokens. -}
  , parsecResult :: Either (ParsecError s) a
    {- ^ As an input: Either parse mode or print mode with syntax value.
    As an output: Either a failure or success with syntax value.
    -}
  }

{- | `ParsecError` is the error payload produced by `Parsector`,
inside a failed `parsecResult` of a `ParsecState` output.
-}
data ParsecError s = ParsecError
  { parsecExpect :: TokenClass (Item s)
    {- ^ Class of expected token `Item`s at the `parsecOffset`.
    `tokenClass`es and `Tokenized` combinators specify expectations.
    `<|>` merges them via disjunction `>||<`.
    Contrast with the actual `parsecStream`,
    which is either empty or begins with an unexpected token.
    -}
  , parsecLabels :: [Tree String]
    {- ^ Forest of `rule` labels active at the `parsecOffset`.
    Each `rule` wraps its inner labels in a new `Node`.
    `ruleRec` & `fail` also create label nodes.
    When two empty failures are merged by `<|>`,
    their forests are concatenated as siblings.
    Use `drawForest` to display.
    -}
  }

-- ParsecError instances
deriving stock instance
  ( Categorized (Item s)
  , Show (Item s), Show (Categorize (Item s))
  ) => Show (ParsecError s)
deriving stock instance
  ( Categorized (Item s)
  , Read (Item s), Read (Categorize (Item s))
  ) => Read (ParsecError s)
deriving stock instance Categorized (Item s) => Eq (ParsecError s)
deriving stock instance Categorized (Item s) => Ord (ParsecError s)
instance Categorized (Item s) => Semigroup (ParsecError s) where
  ParsecError e1 l1 <> ParsecError e2 l2 = ParsecError (e1 >||< e2) (l1 ++ l2)
instance Categorized (Item s) => Monoid (ParsecError s) where
  mempty = ParsecError falseB []

-- ParsecState instances
deriving stock instance Functor (ParsecState s)
deriving stock instance Foldable (ParsecState s)
deriving stock instance Traversable (ParsecState s)
deriving stock instance
  ( Categorized (Item s)
  , Show (Item s), Show (Categorize (Item s))
  , Show a, Show s
  ) => Show (ParsecState s a)
deriving stock instance
  ( Categorized (Item s)
  , Read (Item s), Read (Categorize (Item s))
  , Read a, Read s
  ) => Read (ParsecState s a)
deriving stock instance
  ( Categorized (Item s)
  , Eq a, Eq s
  ) => Eq (ParsecState s a)
deriving stock instance
  ( Categorized (Item s)
  , Ord a, Ord s
  ) => Ord (ParsecState s a)

-- Parsector instances
instance
  ( Categorized token, Item s ~ token
  , Cons s s token token, Snoc s s token token
  ) => Tokenized token (Parsector s token token) where
  anyToken = tokenClass anyToken
  token t = tokenClass (token t)
  oneOf ts = tokenClass (oneOf ts)
  notOneOf ts = tokenClass (notOneOf ts)
  asIn cat = tokenClass (asIn cat)
  notAsIn cat = tokenClass (notAsIn cat)
instance
  ( Categorized token, Item s ~ token
  , Cons s s token token, Snoc s s token token
  ) => TokenAlgebra token (Parsector s token token) where
    tokenClass test = Parsector $ \callback query ->
      let
        stream = parsecStream query
        mode = parsecResult query
        offset = parsecOffset query
        replyOk tok str = query
          { parsecLooked = True
          , parsecHint   = mempty
          , parsecStream = str
          , parsecOffset = offset + 1
          , parsecResult = Right tok
          }
        replyErr = query
          { parsecHint   = mempty
          , parsecResult = Left (ParsecError test []) }
      in
        callback $ case mode of
          -- print mode
          Right tok
            | tokenClass test tok -> replyOk tok (snoc stream tok)
            | otherwise -> replyErr
          -- parse mode
          Left _ -> case uncons stream of
            Just (tok, rest)
              | tokenClass test tok -> replyOk tok rest
              | otherwise -> replyErr
            Nothing -> replyErr
instance BackusNaurForm (Parsector s a b) where
  -- | Wraps inner `parsecLabels` in a new `Node name` on failure.
  -- Has no effect on success.
  rule name p = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply -> callback $
      case parsecResult reply of
        Left (ParsecError expect labels) -> reply
          {parsecResult = Left (ParsecError expect [Node name labels])}
        Right _ -> reply
  ruleRec name = rule name . fix
instance
  ( Categorized token, Item s ~ token
  , Cons s s token token, Snoc s s token token
  ) => TerminalSymbol token (Parsector s () ())
instance Functor (Parsector s a) where
  fmap = rmap
instance Categorized (Item s) => Applicative (Parsector s a) where
  pure b = Parsector $ \callback query ->
    callback query { parsecResult = Right b }
  (<*>) = ap

instance Categorized (Item s) => Monad (Parsector s a) where
  return = pure
  p >>= f = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply ->
      case parsecResult reply of
        Left err -> callback reply {parsecResult = Left err}
        Right b ->
          let
            hintP  = parsecHint reply
            fQuery = reply
              { parsecLooked = False
              , parsecHint   = mempty
              , parsecResult = parsecResult query
              }
          in
            flip (runParsector (f b)) fQuery $ \fReply -> callback $
              if parsecLooked fReply
                then fReply
                else case parsecResult fReply of
                  Left err -> fReply
                    { parsecLooked = parsecLooked reply
                    , parsecResult = Left (hintP <> err)
                    }
                  Right _ -> fReply
                    { parsecLooked = parsecLooked reply
                    , parsecHint   = hintP <> parsecHint fReply
                    }
instance Categorized (Item s) => Alternative (Parsector s a) where
  -- | Always fails without consuming input; expects nothing.
  empty = Parsector $ \callback query ->
    callback query { parsecResult = Left mempty }
  p <|> q = Parsector $ \callback query ->
    flip (runParsector p) query $ \replyP -> callback $
      case parsecResult replyP of
        -- if p succeeds, take p's branch
        Right _ -> replyP
        -- if p failed after consuming (committed), propagate immediately
        Left _ | parsecLooked replyP -> replyP
        -- if p failed without consuming, try q
        Left errP -> flip (runParsector q) query $ \replyQ ->
          case (parsecLooked replyQ, parsecResult replyQ) of
            -- q consumed (ok or err): propagate as-is, drop errP
            (True, _)         -> replyQ
            -- q empty ok: carry errP forward as hint for downstream
            (False, Right _)  -> replyQ { parsecHint = errP <> parsecHint replyQ }
            -- both empty fail: merge errors
            (False, Left errQ) -> replyP { parsecResult = Left (errP <> errQ) }
instance Categorized (Item s) => MonadPlus (Parsector s a)
instance Categorized (Item s) => MonadFail (Parsector s a) where
  fail msg = rule msg empty
instance Categorized (Item s) => MonadTry (Parsector s a) where
  -- | On failure, resets `parsecLooked` to @False@, allowing
  -- the enclosing `<|>` to try the next alternative even if @p@
  -- consumed input. Has no effect on success.
  try p = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply -> callback $
      case parsecResult reply of
        Left _ -> reply { parsecLooked = False }
        Right _ -> reply
instance Categorized (Item s) => Filterable (Parsector s a) where
  mapMaybe = dimapMaybe Just
instance Category (Parsector s) where
  id = Parsector id
  Parsector q . Parsector p = Parsector (p . q)
instance Categorized (Item s) => Arrow (Parsector s) where
  arr f = Parsector $ \callback reply -> callback (f <$> reply)
  (***) = (>*<)
  first = first'
  second = second'
instance Categorized (Item s) => ArrowZero (Parsector s) where
  zeroArrow = empty
instance Categorized (Item s) => ArrowPlus (Parsector s) where
  (<+>) = (<|>)
instance Categorized (Item s) => ArrowChoice (Parsector s) where
  (+++) = (>+<)
  left = left'
  right = right'
instance Profunctor (Parsector s) where
  dimap f g (Parsector p) = Parsector $
    dimap (lmap (fmap g)) (lmap (fmap f)) p
instance Strong (Parsector s) where
  first' p = Parsector $ \callback reply0 ->
    flip (runParsector p) (fst <$> reply0) $ \reply1 ->
      callback reply1
        { parsecResult = (,)
            <$> parsecResult reply1
            <*> (snd <$> parsecResult reply0)
        }
  second' p = Parsector $ \callback reply0 ->
    flip (runParsector p) (snd <$> reply0) $ \reply1 ->
      callback reply1
        { parsecResult = (,)
            <$> (fst <$> parsecResult reply0)
            <*> parsecResult reply1
        }
instance Categorized (Item s) => Choice (Parsector s) where
  left' = alternate . Left
  right' = alternate . Right
instance Categorized (Item s) => Distributor (Parsector s)
instance Categorized (Item s) => Alternator (Parsector s) where
  alternate (Left p) = Parsector $ \callback query -> callback $
    let
      replyOk = query
        { parsecResult = case parsecResult query of
            Left err       -> Left err
            Right (Left a) -> Right a
            Right (Right _) -> Left mempty
        }
      replyErr = query { parsecResult = Left mempty }
    in
      case (parsecResult query, parsecResult replyOk) of
        (Right _, Left _) -> replyErr
        _________________ ->
          flip (runParsector p) replyOk $ \reply -> reply
            { parsecResult = fmap Left (parsecResult reply) }
  alternate (Right p) = Parsector $ \callback query -> callback $
    let
      replyOk = query
        { parsecResult = case parsecResult query of
            Left err        -> Left err
            Right (Left _)  -> Left mempty
            Right (Right b) -> Right b
        }
      replyErr = query { parsecResult = Left mempty }
    in
      case (parsecResult query, parsecResult replyOk) of
        (Right _, Left _) -> replyErr
        _________________ ->
          flip (runParsector p) replyOk $ \reply -> reply
            { parsecResult = fmap Right (parsecResult reply) }
  optionP def p = Parsector $ \callback query ->
    case parsecResult query of
      Left _ -> runParsector (p <|> pureP def) callback query
      Right _ -> runParsector (pureP def <|> p) callback query
instance Categorized (Item s) => Cochoice (Parsector s) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Categorized (Item s) => Filtrator (Parsector s) where
  filtrate p =
    ( Parsector $ \callback query ->
        flip (runParsector p) (Left <$> query) $ \reply ->
          callback reply
            { parsecResult =
                parsecResult reply >>= either Right (const (Left mempty))
            }
    , Parsector $ \callback query ->
        flip (runParsector p) (Right <$> query) $ \reply ->
          callback reply
            { parsecResult =
                parsecResult reply >>= either (const (Left mempty)) Right
            }
    )
