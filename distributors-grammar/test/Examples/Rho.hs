module Examples.Rho
  ( Proc (..)
  , Name (..)
  , rhoGrammar
  , rhoExamples
  , rholangGrammar
  , rholangExamples
  ) where

import Control.Lens
import Control.Lens.Grammar

-- | Processes of Meredith & Radestock's reflective higher-order calculus,
-- the ρ-calculus, "A reflective higher-order calculus", FInCo 2005.
data Proc
  = Zero                 -- ^ null process, @0@
  | Input Name Name Proc -- ^ input, @x(y).P@
  | Lift Name Proc       -- ^ lift, @x⟨|P|⟩@
  | Drop Name            -- ^ drop, @⌝x⌜@
  | Par Proc Proc        -- ^ parallel, @P | Q@
  deriving stock (Eq, Ord, Show, Read)

-- | Names are quoted processes, @⌜P⌝@.
newtype Name = Quote Proc
  deriving stock (Eq, Ord, Show, Read)

makeNestedPrisms ''Proc
makePrisms ''Name

-- | What follows an action's subject name, an input's or a lift's.
data Act = InputAct Name Proc | LiftAct Proc

makeNestedPrisms ''Act

-- | An action, by its subject name & what follows it.
_Act :: Prism' Proc (Name, Act)
_Act = prism' build match
  where
    build (x, InputAct y p) = Input x y p
    build (x, LiftAct p) = Lift x p
    match = \case
      Input x y p -> Just (x, InputAct y p)
      Lift x p -> Just (x, LiftAct p)
      _ -> Nothing

-- | The paper's notation, factoring an action's subject name, which
-- inputs & lifts share, to be @LL(1)@.
rhoGrammar :: forall p. Grammatical Char p => p Proc Proc
rhoGrammar = ruleRec "proc" $ \rho -> rule "par" $
  sepWith " | " (chain1 Left _Par) (ruleRec "atom" (atomG rho))
  where
    atomG :: p Proc Proc -> p Proc Proc -> p Proc Proc
    actG :: p Proc Proc -> p Proc Proc -> p Act Act
    nameG :: p Proc Proc -> p Name Name
    atomG rho atom = orP
      [ _Zero >? terminal "0"
      , _Drop >? terminal "⌝" >* nameG rho *< terminal "⌜"
      , _Act >? nameG rho >*< actG rho atom
      , terminal "(" >* rho *< terminal ")"
      ]
    actG rho atom = rule "act" $
      _InputAct >? terminal "(" >* nameG rho *< terminal ")." >*< atom
      >|< _LiftAct >? terminal "⟨|" >* rho *< terminal "|⟩"
    nameG rho = rule "name" $
      _Quote >? terminal "⌜" >* rho *< terminal "⌝"

-- | An ASCII notation, after Rholang's: @\@P@ quotes, @*x@ drops,
-- @x!(P)@ lifts & @for(y <- x){P}@ inputs.
rholangGrammar :: forall p. Grammatical Char p => p Proc Proc
rholangGrammar = ruleRec "proc" $ \rho -> rule "par" $
  sepWith " | " (chain1 Left _Par) (ruleRec "atom" (atomG rho))
  where
    atomG :: p Proc Proc -> p Proc Proc -> p Proc Proc
    nameG :: p Proc Proc -> p Name Name
    atomG rho atom = orP
      [ _Zero >? terminal "0"
      , _Drop >? terminal "*" >* nameG atom
      , _Lift >? nameG atom *< terminal "!(" >*< rho *< terminal ")"
      , _Input . swapped' >? terminal "for(" >* nameG atom
          *< terminal " <- " >*< nameG atom *< terminal "){" >*< rho *< terminal "}"
      , terminal "(" >* rho *< terminal ")"
      ]
    nameG atom = rule "name" $ _Quote >? terminal "@" >* atom
    -- @for(y <- x)@ binds @y@ first, as @x(y)@ doesn't
    swapped' = iso (\(x, (y, p)) -> (y, (x, p))) (\(y, (x, p)) -> (x, (y, p)))

-- | @⌜0⌝@, the first name.
zeroName :: Name
zeroName = Quote Zero

-- | Output's sugar, @x[y] = x⟨|⌝y⌜|⟩@.
output :: Name -> Name -> Proc
output x y = Lift x (Drop y)

-- | The replicator, @D(x) = x(y).(x[y] | ⌝y⌜)@, at @y = ⌜0⌝@.
dup :: Name -> Proc
dup x = Input x zeroName (Par (output x zeroName) (Drop zeroName))

-- | Replication, @!P(x) = x⟨|D(x) | P|⟩ | D(x)@.
replicate' :: Proc -> Name -> Proc
replicate' p x = Par (Lift x (Par (dup x) p)) (dup x)

rhoSamples :: [Proc]
rhoSamples =
  [ Zero
  , output zeroName zeroName
  , Input zeroName zeroName Zero
  , Drop zeroName
  , Par Zero (Par Zero Zero)
  , Par (Par Zero Zero) Zero
  , Input zeroName zeroName (Par Zero Zero)
  , Lift (Quote (output zeroName zeroName)) (Input zeroName zeroName Zero)
  , dup zeroName
  , replicate' Zero zeroName
  ]

rhoExamples :: [(Proc, String)]
rhoExamples = zip rhoSamples
  [ "0"
  , "⌜0⌝⟨|⌝⌜0⌝⌜|⟩"
  , "⌜0⌝(⌜0⌝).0"
  , "⌝⌜0⌝⌜"
  , "0 | (0 | 0)"
  , "0 | 0 | 0"
  , "⌜0⌝(⌜0⌝).(0 | 0)"
  , "⌜⌜0⌝⟨|⌝⌜0⌝⌜|⟩⌝⟨|⌜0⌝(⌜0⌝).0|⟩"
  , "⌜0⌝(⌜0⌝).(⌜0⌝⟨|⌝⌜0⌝⌜|⟩ | ⌝⌜0⌝⌜)"
  , "⌜0⌝⟨|⌜0⌝(⌜0⌝).(⌜0⌝⟨|⌝⌜0⌝⌜|⟩ | ⌝⌜0⌝⌜) | 0|⟩ | ⌜0⌝(⌜0⌝).(⌜0⌝⟨|⌝⌜0⌝⌜|⟩ | ⌝⌜0⌝⌜)"
  ]

rholangExamples :: [(Proc, String)]
rholangExamples = zip rhoSamples
  [ "0"
  , "@0!(*@0)"
  , "for(@0 <- @0){0}"
  , "*@0"
  , "0 | (0 | 0)"
  , "0 | 0 | 0"
  , "for(@0 <- @0){0 | 0}"
  , "@@0!(*@0)!(for(@0 <- @0){0})"
  , "for(@0 <- @0){@0!(*@0) | *@0}"
  , "@0!(for(@0 <- @0){@0!(*@0) | *@0} | 0) | for(@0 <- @0){@0!(*@0) | *@0}"
  ]

instance CtxGrammar Char Proc
instance Grammar Char Proc where grammar = rhoGrammar
