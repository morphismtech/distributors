{- |
Module      : Control.Lens.Grammar.Class
Description : grammar classes & numerals
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

The classes of types' grammars, over their tokens, regular, context-free
& context-sensitive, & numerals, by their digits. Haskell types' grammars,
equivalent to their `Read` & `Show` instances, are in
"Control.Lens.Grammar.Prec".
-}

module Control.Lens.Grammar.Class
  ( RegGrammar (..)
  , Grammar (..)
  , CtxGrammar (..)
    -- * Numerals
  , digit
  , numeral
  ) where

import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Token
import Data.Char (isDigit, isLetter, ord, toLower, toUpper)
import Data.Profunctor.Distributor

-- $setup
-- >>> import Control.Lens.Grammar

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

{- | A digit in a base, from 2 to 36, by its value: @0-9@, then letters,
printing in lowercase, & parsing either case.

>>> [d | (d, "") <- parseP (digit (16 :: Int) :: Parsor String [] Int Int) "F"]
[15]
-}
digit :: (Integral n, Choice p, Tokenized Char (p Char Char)) => n -> p n n
digit base = prism' valueOf charOf >? oneOf chars
  where
    values = take (fromIntegral base) (['0' .. '9'] <> ['a' .. 'z'])
    chars = values <> [toUpper c | c <- values, isLetter c]
    valueOf c
      | isDigit c = fromIntegral (ord c - ord '0')
      | otherwise = fromIntegral (ord (toLower c) - ord 'a' + 10)
    charOf d
      | 0 <= d && d < base = Just (values !! fromIntegral d)
      | otherwise = Nothing

{- | A natural number in a base, from 2 to 36, by its digits, most
significant first, printing without leading zeros, & parsing them too,
an improper iso.

>>> ($ "") <$> printP (numeral (16 :: Integer) :: Printor String Maybe Integer Integer) 255
Just "ff"
-}
numeral :: (Integral n, Alternator p, Tokenized Char (p Char Char)) => n -> p n n
numeral base = iso digitsOf (foldl' (\n d -> n * base + d) 0) >~ someP (digit base)
  where
    digitsOf n
      | n < base = [n]
      | otherwise = let (q, r) = n `quotRem` base in digitsOf q <> [r]
