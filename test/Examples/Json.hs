module Examples.Json
  ( Json (..)
  , jsonGrammar
  , jsonExamples
  ) where

import Control.Applicative
import Control.Lens hiding (element)
import Control.Lens.Grammar
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Numeric.Natural

-- | Abstract syntax tree for JSON values
data Json
  = JNull
  | JBool Bool
  | JNumber Natural -- simplified to only decimal natural numbers
  | JString String
  | JArray [Json]
  | JObject (Map String Json)
  deriving stock (Eq, Ord, Show, Read)

-- Generate prisms
makePrisms ''Json

-- | JSON grammar following the McKeeman Form specification from json.org.
-- The inner rules are mutually recursive: element ↔ value ↔ array ↔
-- elements ↔ element, and element ↔ value ↔ object ↔ members ↔ member
-- ↔ element. Only a rule bound via `ruleRec` produces a stub that
-- breaks the cycle; a plain `rule` invocation forces its body, so
-- every cyclic back-edge must instead use the `element` stub produced
-- by the inner `ruleRec "element"` below.
jsonGrammar :: Grammar Char Json
jsonGrammar = ruleRec "json" $ \_json ->
  ruleRec "element" $ \element ->
    ws >* valueG element *< ws
  where
    -- value = object | array | string | number | "true" | "false" | "null"
    valueG element = rule "value" $ choice
      [ _JNull >? terminal "null"
      , _JBool . only True >? terminal "true"
      , _JBool . only False >? terminal "false"
      , _JNumber >? numberG
      , _JString >? stringG
      , _JArray >? arrayG element
      , _JObject >? objectG element
      ]

    -- object = '{' ws '}' | '{' members '}'
    objectG element = rule "object" $ choice
      [ only Map.empty >?
          terminal "{" >* ws >* terminal "}"
      , iso Map.toList Map.fromList >~
          terminal "{" >* membersG element *< terminal "}"
      ]

    -- members = member | member ',' members
    membersG element = rule "members" $
      several1 (sepWith ",") (memberG element)

    -- member = ws string ws ':' element
    memberG element = rule "member" $
      ws >* stringG *< ws *< terminal ":" >*< element

    -- array = '[' ws ']' | '[' elements ']'
    arrayG element = rule "array" $ choice
      [ only [] >? terminal "[" >* ws >* terminal "]"
      , terminal "[" >* elementsG element *< terminal "]"
      ]

    -- elements = element | element ',' elements
    elementsG element = rule "elements" $
      several1 (sepWith ",") element

    -- string = '"' characters '"'
    stringG = rule "string" $
      terminal "\"" >* manyP characterG *< terminal "\""

    -- character = '0020' . '10FFFF' - '"' - '\' | '\' escape
    characterG = rule "character" $
      tokenClass (oneOf ['\x0020' .. '\x10FFFF'] >&&< notOneOf ['\"','\\'])
      <|> terminal "\\" >* escapeG

    -- escape = '"' | '\' | '/' | 'b' | 'f' | 'n' | 'r' | 't'
    escapeG = rule "escape" $ choice
      [ only '"' >? terminal "\""
      , only '\\' >? terminal "\\"
      , only '/' >? terminal "/"
      , only '\b' >? terminal "b"
      , only '\f' >? terminal "f"
      , only '\n' >? terminal "n"
      , only '\r' >? terminal "r"
      , only '\t' >? terminal "t"
      ]

    -- number = decimal natural number
    numberG = rule "number" $
      iso show read >~ someP (asIn @Char DecimalNumber)

    -- Simplified: zero or more whitespace characters
    ws = rule "ws" $
      iso (\() -> "") (\_ -> ()) >~ manyP (token @Char ' ')

-- | Example JSON values for testing
jsonExamples :: [(Json, String)]
jsonExamples =
  [ (JNull, "null")
  , (JBool True, "true")
  , (JBool False, "false")
  , (JNumber 0, "0")
  , (JNumber 42, "42")
  , (JString "", "\"\"")
  , (JString "hello", "\"hello\"")
  , (JString "hello world", "\"hello world\"")
  , (JString "\"quoted\"", "\"\\\"quoted\\\"\"")
  , (JString "line1\nline2", "\"line1\\nline2\"")
  , (JArray [], "[]")
  , (JArray [JNumber 1, JNumber 2, JNumber 3], "[1,2,3]")
  , (JArray [JBool True, JBool False], "[true,false]")
  , (JObject Map.empty, "{}")
  , (JObject (Map.fromList [("key", JString "value")]), "{\"key\":\"value\"}")
  , (JObject (Map.fromList [("a", JNumber 1), ("b", JNumber 2)]),
     "{\"a\":1,\"b\":2}")
  , (JObject (Map.fromList
      [ ("name", JString "Alice")
      , ("age", JNumber 30)
      , ("active", JBool True)
      ]), "{\"active\":true,\"age\":30,\"name\":\"Alice\"}")
  , (JArray [JObject (Map.fromList [("x", JNumber 1)]),
             JObject (Map.fromList [("x", JNumber 2)])],
     "[{\"x\":1},{\"x\":2}]")
  ]
