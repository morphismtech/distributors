{- |
Module      : Control.Lens.Grammar.Class
Description : grammar classes & base types' grammars
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

The classes of types' grammars, over their tokens, regular, context-free
& context-sensitive, & the grammars of base types.
-}

module Control.Lens.Grammar.Class
  ( RegGrammar (..)
  , Grammar (..)
  , CtxGrammar (..)
  ) where

import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Data.Bits (Bits, toIntegralSized)
import Data.Char (isDigit)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.Maybe (isJust)
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import Data.Profunctor.Monoidal.Cocartesian
import Data.Word (Word8, Word16, Word32, Word64)
import Numeric.Natural (Natural)

{- | A type's regular grammar, over its tokens, which is also its
context-free & context-sensitive grammar. -}
class Grammar token a => RegGrammar token a where
  regGrammar :: RegGrammatical token p => p a a

{- | A type's context-free grammar, over its tokens, which is also its
context-sensitive grammar; its regular grammar, by default. -}
class CtxGrammar token a => Grammar token a where
  grammar :: Grammatical token p => p a a
  default grammar :: (RegGrammar token a, Grammatical token p) => p a a
  grammar = regGrammar @token

{- | A type's context-sensitive grammar, over its tokens;
its context-free grammar, by default. -}
class CtxGrammar token a where
  ctxGrammar :: CtxGrammatical token p => p a a
  default ctxGrammar :: (Grammar token a, CtxGrammatical token p) => p a a
  ctxGrammar = grammar @token

-- Base types --

instance CtxGrammar Char Char
instance Grammar Char Char where grammar = rule "Char" (regGrammar @Char)
instance RegGrammar Char Char where regGrammar = tokenAny @Char

instance CtxGrammar Char String
instance Grammar Char String where grammar = rule "String" (regGrammar @Char)
instance RegGrammar Char String where regGrammar = manyP (tokenAny @Char)

instance CtxGrammar Char Natural
instance Grammar Char Natural where grammar = rule "Natural" (regGrammar @Char)
instance RegGrammar Char Natural where regGrammar = naturalG

instance CtxGrammar Char Integer
instance Grammar Char Integer where grammar = rule "Integer" (regGrammar @Char)
instance RegGrammar Char Integer where regGrammar = integerG

instance CtxGrammar Char Double
instance Grammar Char Double where grammar = rule "Double" (regGrammar @Char)
instance RegGrammar Char Double where regGrammar = floatingG

instance CtxGrammar Char Float
instance Grammar Char Float where grammar = rule "Float" (regGrammar @Char)
instance RegGrammar Char Float where regGrammar = floatingG

{- Sized integers' syntax is `Integer`'s, but a literal out of their range
fails to build, which only a `CtxGrammar`'s `Filtrator` can, so they have
no regular expression or Backus-Naur form. -}
instance CtxGrammar Char Int where ctxGrammar = rule "Int" sizedG
instance CtxGrammar Char Int8 where ctxGrammar = rule "Int8" sizedG
instance CtxGrammar Char Int16 where ctxGrammar = rule "Int16" sizedG
instance CtxGrammar Char Int32 where ctxGrammar = rule "Int32" sizedG
instance CtxGrammar Char Int64 where ctxGrammar = rule "Int64" sizedG
instance CtxGrammar Char Word where ctxGrammar = rule "Word" sizedG
instance CtxGrammar Char Word8 where ctxGrammar = rule "Word8" sizedG
instance CtxGrammar Char Word16 where ctxGrammar = rule "Word16" sizedG
instance CtxGrammar Char Word32 where ctxGrammar = rule "Word32" sizedG
instance CtxGrammar Char Word64 where ctxGrammar = rule "Word64" sizedG

-- ASCII decimal digits, at least one.
decimalG :: RegGrammatical Char p => p String String
decimalG = someP (oneOf ['0' .. '9'])

-- An optional minus, as whether a number is negative.
negativeG :: RegGrammatical Char p => p Bool Bool
negativeG = iso (\b -> if b then Just () else Nothing) isJust
  >~ optionalP (terminal "-")

-- Printing canonically, parsing leading zeros too, an improper iso.
naturalG :: RegGrammatical Char p => p Natural Natural
naturalG = iso show read >~ decimalG

-- Printing canonically, parsing leading zeros & -0 too, an improper iso.
integerG :: RegGrammatical Char p => p Integer Integer
integerG = iso
  (\n -> (n < 0, show (abs n)))
  (\(negative, digits) -> (if negative then negate else id) (read digits))
  >~ negativeG >*< decimalG

-- Integers in a range, failing to build out of it.
sizedG
  :: forall a p. (Integral a, Bits a, CtxGrammatical Char p) => p a a
sizedG = prism' toInteger toIntegralSized ?< integerG

{- Floating point numbers, @NaN@, or signed @Infinity@ or decimals with
an optional fraction & exponent, printing as `show` does & parsing as
`read` does, an improper iso, keeping the sign of zero. -}
floatingG
  :: (RealFloat a, Read a, Show a, RegGrammatical Char p) => p a a
floatingG = iso toFloating fromFloating >~
  terminal "NaN" >+< negativeG >*< (terminal "Infinity" >+< numberG)
  where
    numberG = decimalG
      >*< optionalP (terminal "." >* decimalG)
      >*< optionalP (oneOf "eE" >*< optionalP (oneOf "+-") >*< decimalG)
    toFloating x
      | isNaN x = Left ()
      | otherwise = Right
          ( x < 0 || isNegativeZero x
          , if isInfinite x then Left () else Right (split (show (abs x))) )
    fromFloating = \case
      Left () -> 0 / 0
      Right (negative, magnitude) -> (if negative then negate else id) $
        either (const (1 / 0)) (read . unsplit) magnitude
    split shown =
      let
        (whole, rest) = span isDigit shown
        (fraction, rest') = case rest of
          '.' : more -> let (ds, more') = span isDigit more in (Just ds, more')
          _ -> (Nothing, rest)
        exponent' = case rest' of
          e : more | e `elem` ("eE" :: String) -> case more of
            s : ds | s `elem` ("+-" :: String) -> Just (e, (Just s, ds))
            ds -> Just (e, (Nothing, ds))
          _ -> Nothing
      in
        (whole, (fraction, exponent'))
    unsplit (whole, (fraction, exponent')) = whole
      <> maybe "" ('.' :) fraction
      <> maybe "" (\(e, (s, ds)) -> e : maybe "" pure s <> ds) exponent'

