{-|
Module      : Data.Profunctor.Grammar.Parsector
Description : grammar distributor with failures
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
  , ParsecFailure (..)
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Lens
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Lens.PartialIso
import Control.Monad
import Data.Monoid.Disjunctive
import Data.Profunctor
import Data.Profunctor.Unsafe ((#.), (.#))
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal.Cocartesian
import Data.Profunctor.Filtrator
import Data.Profunctor.Monoidal
import Data.Tree
import GHC.Exts
import Prelude hiding (id, (.))
import Witherable (Filterable (..))

{- | t'Parsector' is an invertible @LL(1)@ parser which is intended
to provide detailed failure information, based on [Parsec]
(https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/parsec-paper-letter.pdf).
-}
newtype Parsector s a b = Parsector
  {runParsector :: forall x. (ParsecState s b -> x) -> ParsecState s a -> x}

{- | Run t'Parsector' as a parser: consume tokens from @s@,
left to right, returning a t'ParsecState' whose `parsecResult`
is `Nothing` on failure and `Just` the output syntax value on success. -}
parsecP
  :: Categorized (Item s)
  => Parsector s a b
  -> s -- ^ input stream
  -> ParsecState s b
parsecP p s = runParsector p id (ParsecState False 0 s mempty Nothing)

{- | Run t'Parsector' as a printer: given a syntax value @a@ and
an input stream, append tokens to @s@ left to right,
returning a t'ParsecState' whose `parsecResult` is
`Nothing` on failure or `Just` a successful output syntax value,
in which case, `parsecStream` is the output stream. -}
unparsecP
  :: Categorized (Item s)
  => Parsector s a b
  -> a -- ^ input syntax
  -> s -- ^ input stream
  -> ParsecState s b
unparsecP p a s = runParsector p id (ParsecState False 0 s mempty (Just a))

{- | t'ParsecState' is both the input and output type of the
underlying function inside t'Parsector'.
@Parsector s a b@ is equivalent to

@ParsecState s a -> ParsecState s b@

So t'ParsecState' has a dual interpretation as input and output. -}
data ParsecState s a = ParsecState
  { parsecLooked :: !Bool
    {- ^ `True` once the parser has consumed/produced at least one token
    since the last `<|>` / `try` decision point.
    Controls @LL(1)@ commitment: a failure with `parsecLooked` `True`
    is propagated immediately without trying alternatives.
    Reset to `False` by `try` on failure.
    -}
  , parsecOffset :: !Word
    -- ^ Number of tokens consumed from the start of the stream.
  , parsecStream :: s -- ^ stream
  , parsecFailure  :: ParsecFailure s
    {- ^ t'ParsecFailure' channel.

    * If `parsecResult` is `Nothing`, this is the hard failure.
    * If `parsecResult` is `Just`, this is deferred failure/hint info
      from empty-failing alternatives at the current position.

    `<|>` and `>>=` propagate and merge this field to preserve
    expected-token reporting on downstream failures.
    -}
  , parsecResult :: Maybe a
    {- ^
    As input, `Nothing` means parse mode and
    `Just` means print mode with an input syntax value.

    As output `Nothing` means failure (inspect `parsecFailure`) and
    `Just` means success with an output syntax value.
    -}
  }

{- | t'ParsecFailure' is the failure payload produced by t'Parsector',
stored in `parsecFailure`.
t'ParsecFailure' is a `Monoid` and t'Parsector' merges failures/hints
when control flow reaches the same offset without commitment.
-}
data ParsecFailure s = ParsecFailure
  { parsecExpect :: TokenClass (Item s)
    {- ^ Class of expected token `Item`s at the `parsecOffset`.
    `tokenClass`es and `Tokenized` combinators specify expectations.
    Under `<>`, expectations are combined with disjunction `>|<`.
    In case of a parse failure, contrast with the actual `parsecStream`,
    which is either unexpectedly empty or begins with an unexpected token.
    -}
  , parsecLabels :: [Tree String]
    {- ^ Forest of `rule` labels active at the `parsecOffset`.
    Each `rule` wraps its inner labels in a new `Node`.
    `ruleRec` & `fail` also create label nodes.
    Under `<>`, forests are concatenated as siblings.
    Use `drawForest` to display.
    -}
  }

-- ParsecFailure instances
deriving stock instance
  ( Categorized (Item s)
  , Show (Item s), Show (Categorize (Item s)), Show (TokenSet (Item s))
  ) => Show (ParsecFailure s)
deriving stock instance
  ( Categorized (Item s)
  , Read (Item s), Read (Categorize (Item s)), Read (TokenSet (Item s))
  ) => Read (ParsecFailure s)
deriving stock instance Categorized (Item s) => Eq (ParsecFailure s)
deriving stock instance Categorized (Item s) => Ord (ParsecFailure s)
instance Categorized (Item s) => Semigroup (ParsecFailure s) where
  ParsecFailure e1 l1 <> ParsecFailure e2 l2 = ParsecFailure (e1 >|< e2) (l1 ++ l2)
instance Categorized (Item s) => Monoid (ParsecFailure s) where
  mempty = ParsecFailure falseP []

-- ParsecState instances
deriving stock instance Functor (ParsecState s)
deriving stock instance Foldable (ParsecState s)
deriving stock instance Traversable (ParsecState s)
deriving stock instance
  ( Categorized (Item s)
  , Show (Item s), Show (Categorize (Item s)), Show (TokenSet (Item s))
  , Show a, Show s
  ) => Show (ParsecState s a)
deriving stock instance
  ( Categorized (Item s)
  , Read (Item s), Read (Categorize (Item s)), Read (TokenSet (Item s))
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
    {-# SPECIALISE instance TokenAlgebra Char (Parsector String Char Char) #-}
    -- The test & failures are made once, rather than for each token.
    tokenClass test = matches `seq` Parsector (\callback query ->
      let
        stream = parsecStream query
        mode = parsecResult query
        offset = parsecOffset query
        replyOk tok str = query
          { parsecLooked = True
          , parsecFailure  = noFailure
          , parsecStream = str
          , parsecOffset = offset + 1
          , parsecResult = Just tok
          }
        replyErr = query
          { parsecFailure  = failure
          , parsecResult = Nothing }
      in
        callback $ case mode of
          -- print mode
          Just tok
            | matches tok -> replyOk tok (snoc stream tok)
            | otherwise -> replyErr
          -- parse mode
          Nothing -> case uncons stream of
            Just (tok, rest)
              | matches tok -> replyOk tok rest
              | otherwise -> replyErr
            Nothing -> replyErr)
      where
        matches :: token -> Bool
        matches = tokenClass test
        noFailure = mempty
        failure = ParsecFailure test []
instance BackusNaurForm (Parsector s a b)
instance Ruled (Parsector s a b) where
  -- | Wraps inner `parsecLabels` in a new `Node name` on failure.
  -- Has no effect on success.
  rule name p = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply -> callback $
      case parsecResult reply of
        Nothing -> reply
          { parsecFailure =
              let ParsecFailure expect labels = parsecFailure reply
              in ParsecFailure expect [Node name labels]
          }
        Just _ -> reply
instance
  ( Categorized token, Item s ~ token
  , Cons s s token token, Snoc s s token token
  ) => TerminalSymbol token (Parsector s () ()) where
    {-# SPECIALISE instance TerminalSymbol Char (Parsector String () ()) #-}
    {- | Like @only str ?< tokens str@, checking its tokens in one loop,
    failing without consuming at the first token, and committed after.
    -}
    terminal str = Parsector $ \callback query -> callback $
      case str of
        [] -> query {parsecResult = Just ()}
        _ -> go str query
      where
        go [] state = state {parsecResult = Just ()}
        go (tok : rest) state =
          let
            next str' = state
              { parsecLooked = True
              , parsecFailure = mempty
              , parsecStream = str'
              , parsecOffset = parsecOffset state + 1
              }
            failure = state
              { parsecFailure = ParsecFailure (token tok) []
              , parsecResult = Nothing
              }
          in
            case parsecResult state of
              Just () -> go rest (next (snoc (parsecStream state) tok))
              Nothing -> case uncons (parsecStream state) of
                Just (tok', str') | tok' == tok -> go rest (next str')
                _ -> failure
instance
  ( Item s ~ Char
  , Cons s s Char Char, Snoc s s Char Char
  , x ~ (), y ~ ()
  ) => IsString (Parsector s x y) where
  fromString = terminal
instance Functor (Parsector s a) where
  fmap = rmap
instance Categorized (Item s) => Applicative (Parsector s a) where
  pure b = Parsector $ \callback query ->
    callback query { parsecResult = Just b }
  (<*>) = liftA2 id
  -- | Like `>>=`, without a continuation of the first result.
  liftA2 f p q = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply ->
      case parsecResult reply of
        Nothing -> callback reply { parsecResult = Nothing }
        Just b ->
          flip (runParsector q) (bound query reply) $ \qReply ->
            callback (rebound reply (f b <$> qReply))

instance Categorized (Item s) => Monad (Parsector s a) where
  return = pure
  p >>= f = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply ->
      case parsecResult reply of
        Nothing -> callback reply { parsecResult = Nothing }
        Just b ->
          flip (runParsector (f b)) (bound query reply) $ \fReply ->
            callback (rebound reply fReply)

-- | The query of the second of a sequence, after the first's reply.
bound
  :: Categorized (Item s)
  => ParsecState s a -> ParsecState s b -> ParsecState s a
bound query reply = reply
  { parsecLooked = False
  , parsecFailure = mempty
  , parsecResult = parsecResult query
  }

{- | The reply of a sequence, from the first's & the second's replies,
which keeps the first's hints when the second hasn't consumed.
-}
rebound
  :: Categorized (Item s)
  => ParsecState s b -> ParsecState s c -> ParsecState s c
rebound reply next
  | parsecLooked next = next
  | otherwise = next
      { parsecLooked = parsecLooked reply
      , parsecFailure = parsecFailure reply <> parsecFailure next
      }

instance Categorized (Item s) => Alternative (Parsector s a) where
  -- | Always fails without consuming input; expects nothing.
  empty = Parsector $ \callback query ->
    callback query { parsecFailure = mempty, parsecResult = Nothing }
  p <|> q = Parsector $ \callback query ->
    flip (runParsector p) query $ \replyP -> callback $
      case parsecResult replyP of
        -- if p succeeds, take p's branch
        Just _ -> replyP
        -- if p failed after consuming (committed), propagate immediately
        Nothing | parsecLooked replyP -> replyP
        -- if p failed without consuming, try q
        Nothing ->
          let errP = parsecFailure replyP
          in flip (runParsector q) query $ \replyQ ->
          case (parsecLooked replyQ, parsecResult replyQ) of
            -- q consumed (ok or err): propagate as-is, drop errP
            (True, _)         -> replyQ
            -- q empty ok: carry errP forward as hint for downstream
            (False, Just _)   -> replyQ { parsecFailure = errP <> parsecFailure replyQ }
            -- both empty fail: merge failures
            (False, Nothing)  -> replyP { parsecFailure = errP <> parsecFailure replyQ }
instance Categorized (Item s) => MonadPlus (Parsector s a)
instance Categorized (Item s) => MonadFail (Parsector s a) where
  fail msg = rule msg empty
instance Tried (Parsector s a b) where
  -- | On failure, resets `parsecLooked` to @False@, allowing
  -- the enclosing `<|>` to try the next alternative even if @p@
  -- consumed input. Also restores the stream/offset decision state.
  -- Has no effect on success.
  try p = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply -> callback $
      case parsecResult reply of
        Nothing -> query
          { parsecLooked = False
          , parsecFailure  = parsecFailure reply
          , parsecResult = Nothing
          }
        Just _ -> reply
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
  dimap f g (Parsector p) = Parsector $ \callback query ->
    p (callback . fmap g) (fmap f query)
  lmap f (Parsector p) = Parsector $ \callback query ->
    p callback (fmap f query)
  rmap g (Parsector p) = Parsector $ \callback -> p (callback . fmap g)
  (#.) _ = coerce
  p .# _ = coerce p
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
-- | Like `alternate`, without a sum of branches.
instance Categorized (Item s) => Choice (Parsector s) where
  left' (Parsector p) = Parsector $ \callback query ->
    case parsecResult query of
      Just (Right _) ->
        callback query { parsecFailure = mempty, parsecResult = Nothing }
      result -> p (callback . fmap Left)
        query { parsecResult = either Just (const Nothing) =<< result }
  right' (Parsector p) = Parsector $ \callback query ->
    case parsecResult query of
      Just (Left _) ->
        callback query { parsecFailure = mempty, parsecResult = Nothing }
      result -> p (callback . fmap Right)
        query { parsecResult = either (const Nothing) Just =<< result }
instance Categorized (Item s) => CocartesianMonoidal (Parsector s)
instance Categorized (Item s) => Distributor (Parsector s) where
  {- | Like @eotList . swapped >~ p >*< manyP p >+< oneP@, in one loop,
  with its hints: a failure of @p@ without consuming ends the list,
  merging its expectations with those of the last element.
  -}
  manyP (Parsector p) = Parsector $ \callback query ->
    let
      -- the first element is tried on the query itself
      parsedFirst reply = case parsecResult reply of
        Just b -> parsedRest [b] reply
        Nothing
          | parsecLooked reply -> callback reply {parsecResult = Nothing}
          | otherwise -> callback query
              { parsecResult = Just []
              , parsecFailure = parsecFailure reply <> parsecFailure query
              }
      -- the rest are tried after the reply to the last
      parsedRest bs reply = p
        (\next -> case parsecResult next of
          Just b -> parsedRest (b : bs) next
          Nothing -> ended False bs reply next)
        (afresh reply) {parsecResult = Nothing}
      printedFirst as reply = case parsecResult reply of
        Just b -> printedRest [b] as reply
        Nothing -> callback reply {parsecResult = Nothing}
      printedRest bs as reply = case as of
        [] -> callback reply {parsecResult = Just (reverse bs)}
        a : as' -> p
          (\next -> case parsecResult next of
            Just b -> printedRest (b : bs) as' next
            Nothing -> ended True bs reply next)
          (afresh reply) {parsecResult = Just a}
      {- an element failed after the last one's reply, ending a parsed list,
      or failing a printed one, unless it was committed -}
      ended printing bs reply next
        | parsecLooked next = callback next {parsecResult = Nothing}
        | printing = callback next
            { parsecLooked = parsecLooked reply
            , parsecFailure = parsecFailure reply <> parsecFailure next
            , parsecResult = Nothing
            }
        | otherwise = callback reply
            { parsecFailure = parsecFailure reply <> parsecFailure next
            , parsecResult = Just (reverse bs)
            }
      afresh reply = reply {parsecLooked = False, parsecFailure = mempty}
    in
      case parsecResult query of
        Nothing -> p parsedFirst query {parsecResult = Nothing}
        Just [] -> callback query {parsecResult = Just []}
        Just (a : as) -> p (printedFirst as) query {parsecResult = Just a}
instance Categorized (Item s) => DisjunctiveMonoid (Parsector s a b)
instance Categorized (Item s) => CocartesianChoice (Parsector s) where
  alternate (Left p) = Parsector $ \callback query -> callback $
    let
      replyOk = query
        { parsecResult = case parsecResult query of
            Nothing         -> Nothing
            Just (Left a)   -> Just a
            Just (Right _)  -> Nothing
        }
      replyErr = query { parsecFailure = mempty, parsecResult = Nothing }
    in
      case (parsecResult query, parsecResult replyOk) of
        (Just _, Nothing) -> replyErr
        _________________ ->
          flip (runParsector p) replyOk $ \reply -> reply
            { parsecResult = fmap Left (parsecResult reply) }
  alternate (Right p) = Parsector $ \callback query -> callback $
    let
      replyOk = query
        { parsecResult = case parsecResult query of
            Nothing         -> Nothing
            Just (Left _)   -> Nothing
            Just (Right b)  -> Just b
        }
      replyErr = query { parsecFailure = mempty, parsecResult = Nothing }
    in
      case (parsecResult query, parsecResult replyOk) of
        (Just _, Nothing) -> replyErr
        _________________ ->
          flip (runParsector p) replyOk $ \reply -> reply
            { parsecResult = fmap Right (parsecResult reply) }
instance Categorized (Item s) => Alternator (Parsector s) where
  optionP def p = Parsector $ \callback query ->
    case parsecResult query of
      Nothing -> runParsector (p <|> pureP def) callback query
      Just _ -> runParsector (pureP def <|> p) callback query
instance Categorized (Item s) => Cochoice (Parsector s) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Categorized (Item s) => Filtrator (Parsector s) where
  filtrate p =
    ( Parsector $ \callback query ->
        flip (runParsector p) (Left <$> query) $ \reply ->
          callback reply
          { parsecFailure = case parsecResult reply of
            Just (Right _) -> mempty
            _ -> parsecFailure reply
          , parsecResult =
            parsecResult reply >>= either Just (const Nothing)
          }
    , Parsector $ \callback query ->
        flip (runParsector p) (Right <$> query) $ \reply ->
          callback reply
          { parsecFailure = case parsecResult reply of
            Just (Left _) -> mempty
            _ -> parsecFailure reply
          , parsecResult =
            parsecResult reply >>= either (const Nothing) Just
          }
    )
