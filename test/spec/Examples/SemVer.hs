module Examples.SemVer
  ( SemVer (..)
  , semverGrammar
  , semverExamples
  ) where

import Control.Applicative
import Control.Lens.Grammar
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Lens.PartialIso
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import Numeric.Natural

-- | Semantic version structure following semver.org specification
-- Format: <major>.<minor>.<patch>[-<prerelease>][+<buildmetadata>]
-- Example: 1.2.3-alpha.1+build.123
data SemVer = SemVer
  { semverMajor :: Natural         -- e.g., 1
  , semverMinor :: Natural         -- e.g., 2
  , semverPatch :: Natural         -- e.g., 3
  , semverPreRelease :: [String]  -- e.g., "alpha.1", "rc.2"
  , semverBuildMetadata :: [String]  -- e.g., "build.123", "20130313144700"
  }
  deriving (Eq, Ord, Show, Read)

makeNestedPrisms ''SemVer

-- | Grammar for semantic versions following semver.org specification
-- Regular grammar:
--   semver = version ["-" prerelease] ["+" buildmetadata]
--   version = number "." number "." number
--   number = digit+
--   prerelease = identifier ("." identifier)*
--   buildmetadata = identifier ("." identifier)*
--   identifier = [0-9A-Za-z-]+
semverGrammar :: RegGrammar Char SemVer
semverGrammar = _SemVer
  >?  numberG
  >*< terminal "." >* numberG
  >*< terminal "." >* numberG
  >*< option [] (terminal "-" >* identifiersG)
  >*< option [] (terminal "+" >* identifiersG)
  where
    numberG = iso show read >~ someP (asIn @Char DecimalNumber)
    identifiersG = several1 (sepBy (terminal ".")) (someP charG)
    charG = asIn LowercaseLetter
      <|> asIn UppercaseLetter
      <|> asIn DecimalNumber
      <|> token '-'

semverExamples :: [(SemVer, String)]
semverExamples =
  [ (SemVer 0 0 1 [] [],
     "0.0.1")
  , (SemVer 1 0 0 [] [],
     "1.0.0")
  , (SemVer 1 2 3 [] [],
     "1.2.3")
  , (SemVer 1 0 0 ["alpha"] [],
     "1.0.0-alpha")
  , (SemVer 1 0 0 ["alpha", "1"] [],
     "1.0.0-alpha.1")
  , (SemVer 1 0 0 ["0", "3", "7"] [],
     "1.0.0-0.3.7")
  , (SemVer 1 0 0 ["x", "7", "z", "92"] [],
     "1.0.0-x.7.z.92")
  , (SemVer 1 0 0 [] ["20130313144700"],
     "1.0.0+20130313144700")
  , (SemVer 1 0 0 [] ["exp", "sha", "5114f85"],
     "1.0.0+exp.sha.5114f85")
  , (SemVer 1 0 0 ["beta"] ["exp", "sha", "5114f85"],
     "1.0.0-beta+exp.sha.5114f85")
  , (SemVer 1 0 0 ["beta", "11"] ["exp", "sha", "5114f85"],
     "1.0.0-beta.11+exp.sha.5114f85")
  , (SemVer 2 1 5 ["rc", "1"] ["build", "123"],
     "2.1.5-rc.1+build.123")
  ]
