module Examples.Heredoc
  ( Heredoc (..)
  , heredocP
  , heredocExamples
  ) where

import Control.Lens.Grammar

-- | A heredoc, @<<TAG@, its body's lines, then @TAG@ again,
-- closing it at the first line equal to its tag.
data Heredoc = Heredoc
  { heredocTag :: String
  , heredocBody :: [String]
  } deriving stock (Eq, Ord, Show, Read)

-- | A heredoc's lines, its tag, its body, then its tag again.
heredocLines :: Iso' Heredoc [String]
heredocLines = iso
  (\(Heredoc tag body) -> tag : body ++ [tag])
  (\case
    tag : rest -> Heredoc tag (if null rest then [] else init rest)
    [] -> Heredoc "" [])

-- | Heredocs, by their lines, `delimited` by their tag,
-- a context-sensitive grammar, which needs a `Varifocal`.
heredocP
  :: forall p m.
     ( MonadicTrans p, Alternator (p m), MonadPlus m, Filterable m
     , Tokenized Char (p m Char Char), TerminalSymbol Char (p m () ()) )
  => p m Heredoc Heredoc
heredocP = heredocLines >~ symbol "<<" >* contextually (delimited (==)) lineP
  where
    symbol :: String -> p m () ()
    symbol = terminal
    lineP = manyP (notOneOf "\n") *< symbol "\n"

heredocExamples :: [(Heredoc, String)]
heredocExamples =
  [ (Heredoc "EOF" ["hello", "world"], "<<EOF\nhello\nworld\nEOF\n")
  , (Heredoc "X" [], "<<X\nX\n")
  , (Heredoc "END" ["", "not END", "ENDING"], "<<END\n\nnot END\nENDING\nEND\n")
  ]
