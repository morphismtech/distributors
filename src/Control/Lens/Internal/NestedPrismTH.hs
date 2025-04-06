{- |
Module      : Control.Lens.Internal.NestedPrismTH
Description : nested pair prisms
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Internal.NestedPrismTH
  ( makeNestedPrisms
  ) where

import Control.Applicative
import Control.Lens.Getter
import Control.Lens.Internal.TH
import Control.Lens.Lens
import Control.Monad
import Data.Char (isUpper)
import qualified Data.List as List
import Data.Set.Lens
import Data.Traversable
import Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D
import Language.Haskell.TH.Lens
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Prelude

-- | Main entry point into Prism generation for a given type constructor name.
makeNestedPrisms :: Name -> DecsQ
makeNestedPrisms typeName =
  do info <- D.reifyDatatype typeName
     let cons = D.datatypeCons info
     makeConsPrisms (datatypeTypeKinded info) (map normalizeCon cons)

-- | Generate prisms for the given type, and normalized constructors.
-- This function dispatches between Iso generation, and normal top-level
makeConsPrisms :: Type -> [NCon] -> DecsQ
-- special case: single constructor -> make iso
makeConsPrisms t [con@(NCon _ [] [] _)] = makeConIso t con
-- top-level definitions
makeConsPrisms t cons =
  fmap concat $ for cons $ \con ->
    do let conName = view nconName con
       stab <- computeOpticType t cons con
       let n = prismName conName
       sequenceA
         ( [ sigD n (return (quantifyType [] (stabToType Set.empty stab)))
           , valD (varP n) (normalB (makeConOpticExp stab cons con)) []
           ]
           ++ inlinePragma n
         )

data OpticType = PrismType | ReviewType

data Stab  = Stab Cxt OpticType Type Type Type Type

stabSimple :: Stab -> Bool
stabSimple (Stab _ _ s t a b) = s == t && a == b

stabToType :: Set Name -> Stab -> Type
stabToType clsTVBNames stab@(Stab cx ty s t a b) =
  quantifyType' clsTVBNames cx stabTy
  where
  stabTy =
    case ty of
      PrismType  | stabSimple stab -> prism'TypeName  `conAppsT` [t,b]
                 | otherwise       -> prismTypeName   `conAppsT` [s,t,a,b]
      ReviewType                   -> reviewTypeName  `conAppsT` [t,b]

stabType :: Stab -> OpticType
stabType (Stab _ o _ _ _ _) = o

computeOpticType :: Type -> [NCon] -> NCon -> Q Stab
computeOpticType t cons con =
  do let cons' = List.delete con cons
     if null (_nconVars con)
         then computePrismType t (view nconCxt con) cons' con
         else computeReviewType t (view nconCxt con) (view nconTypes con)

computeReviewType :: Type -> Cxt -> [Type] -> Q Stab
computeReviewType s' cx tys =
  do let t = s'
     s <- fmap VarT (newName "s")
     a <- fmap VarT (newName "a")
     b <- toNestedTupleT (map return tys)
     return (Stab cx ReviewType s t a b)

-- | Compute the full type-changing Prism type given an outer type,
-- list of constructors, and target constructor name. Additionally
-- return 'True' if the resulting type is a "simple" prism.
computePrismType :: Type -> Cxt -> [NCon] -> NCon -> Q Stab
computePrismType t cx cons con =
  do let ts      = view nconTypes con
         unbound = setOf typeVars t Set.\\ setOf typeVars cons
     sub <- sequenceA (Map.fromSet (newName . nameBase) unbound)
     b   <- toNestedTupleT (map return ts)
     a   <- toNestedTupleT (map return (substTypeVars sub ts))
     let s = substTypeVars sub t
     return (Stab cx PrismType s t a b)

computeIsoType :: Type -> [Type] -> TypeQ
computeIsoType t' fields =
  do sub <- sequenceA (Map.fromSet (newName . nameBase) (setOf typeVars t'))
     let t = return                    t'
         s = return (substTypeVars sub t')
         b = toNestedTupleT (map return                    fields)
         a = toNestedTupleT (map return (substTypeVars sub fields))
         ty | Map.null sub = appsT (conT iso'TypeName) [t,b]
            | otherwise    = appsT (conT isoTypeName) [s,t,a,b]
     quantifyType [] <$> ty

-- | Construct either a Review or Prism as appropriate
makeConOpticExp :: Stab -> [NCon] -> NCon -> ExpQ
makeConOpticExp stab cons con =
  case stabType stab of
    PrismType  -> makeConPrismExp stab cons con
    ReviewType -> makeConReviewExp con

-- | Construct an iso declaration
makeConIso :: Type -> NCon -> DecsQ
makeConIso s con =
  do let ty      = computeIsoType s (view nconTypes con)
         defName = prismName (view nconName con)
     sequenceA
       ( [ sigD       defName  ty
         , valD (varP defName) (normalB (makeConIsoExp con)) []
         ] ++
         inlinePragma defName
       )

-- | Construct prism expression
--
-- prism <<reviewer>> <<remitter>>
makeConPrismExp ::
  Stab ->
  [NCon] {- ^ constructors       -} ->
  NCon   {- ^ target constructor -} ->
  ExpQ
makeConPrismExp stab cons con = appsE [varE prismValName, reviewer, remitter]
  where
  ts = view nconTypes con
  fields  = length ts
  conName = view nconName con
  reviewer                   = makeReviewer       conName fields
  remitter | stabSimple stab = makeSimpleRemitter conName (length cons) fields
           | otherwise       = makeFullRemitter cons conName

-- | Construct an Iso expression
--
-- iso <<reviewer>> <<remitter>>
makeConIsoExp :: NCon -> ExpQ
makeConIsoExp con = appsE [varE isoValName, remitter, reviewer]
  where
  conName = view nconName con
  fields  = length (view nconTypes con)
  reviewer = makeReviewer    conName fields
  remitter = makeIsoRemitter conName fields

-- | Construct a Review expression
--
-- unto (\(x,y,z) -> Con x y z)
makeConReviewExp :: NCon -> ExpQ
makeConReviewExp con = appE (varE untoValName) reviewer
  where
  conName = view nconName con
  fields  = length (view nconTypes con)
  reviewer = makeReviewer conName fields

------------------------------------------------------------------------
-- Prism and Iso component builders
------------------------------------------------------------------------

-- | Construct the review portion of a prism.
--
-- (\(x,y,z) -> Con x y z) :: b -> t
makeReviewer :: Name -> Int -> ExpQ
makeReviewer conName fields =
  do xs <- newNames "x" fields
     lam1E (toNestedTupleP (map varP xs))
           (conE conName `appsE1` map varE xs)

-- | Construct the remit portion of a prism.
-- Pattern match only target constructor, no type changing
--
-- (\x -> case s of
--          Con x y z -> Right (x,y,z)
--          _         -> Left x
-- ) :: s -> Either s a

makeSimpleRemitter ::
  Name {- The name of the constructor on which this prism focuses -} ->
  Int  {- The number of constructors the parent data type has     -} ->
  Int  {- The number of fields the constructor has                -} ->
  ExpQ
makeSimpleRemitter conName numCons fields =
  do x  <- newName "x"
     xs <- newNames "y" fields
     let matches =
           [ match (conP conName (map varP xs))
                   (normalB (appE (conE rightDataName) (toNestedTupleE (map varE xs))))
                   []
           ] ++
           [ match wildP (normalB (appE (conE leftDataName) (varE x))) []
           | numCons > 1 -- Only generate a catch-all case if there is at least
                         -- one constructor besides the one being focused on.
           ]
     lam1E (varP x) (caseE (varE x) matches)

-- | Pattern match all constructors to enable type-changing
--
-- (\x -> case s of
--          Con x y z -> Right (x,y,z)
--          Other_n w   -> Left (Other_n w)
-- ) :: s -> Either t a
makeFullRemitter :: [NCon] -> Name -> ExpQ
makeFullRemitter cons target =
  do x <- newName "x"
     lam1E (varP x) (caseE (varE x) (map mkMatch cons))
  where
  mkMatch (NCon conName _ _ n) =
    do xs <- newNames "y" (length n)
       match (conP conName (map varP xs))
             (normalB
               (if conName == target
                  then appE (conE rightDataName) (toNestedTupleE (map varE xs))
                  else appE (conE leftDataName) (conE conName `appsE1` map varE xs)))
             []

-- | Construct the remitter suitable for use in an 'Iso'
--
-- (\(Con x y z) -> (x,y,z)) :: s -> a
makeIsoRemitter :: Name -> Int -> ExpQ
makeIsoRemitter conName fields =
  do xs <- newNames "x" fields
     lam1E (conP conName (map varP xs))
           (toNestedTupleE (map varE xs))

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

-- | Normalized constructor
data NCon = NCon
  { _nconName :: Name
  , _nconVars :: [Name]
  , _nconCxt  :: Cxt
  , _nconTypes :: [Type]
  }
  deriving (Eq)
instance HasTypeVars NCon where
  typeVarsEx s f (NCon x vars y z) = NCon x vars <$> typeVarsEx s' f y <*> typeVarsEx s' f z
    where s' = List.foldl' (flip Set.insert) s vars

nconName :: Lens' NCon Name
nconName f x = fmap (\y -> x {_nconName = y}) (f (_nconName x))

nconCxt :: Lens' NCon Cxt
nconCxt f x = fmap (\y -> x {_nconCxt = y}) (f (_nconCxt x))

nconTypes :: Lens' NCon [Type]
nconTypes f x = fmap (\y -> x {_nconTypes = y}) (f (_nconTypes x))

-- | Normalize a single 'Con' to its constructor name and field types.
normalizeCon :: D.ConstructorInfo -> NCon
normalizeCon info = NCon (D.constructorName info)
                         (D.tvName <$> D.constructorVars info)
                         (D.constructorContext info)
                         (D.constructorFields info)

-- | Compute a prism's name by prefixing an underscore for normal
-- constructors and period for operators.
prismName ::
  Name {- ^ type constructor        -} ->
  Name {- ^ prism name              -}
prismName n =
  case nameBase n of
    [] -> error "prismName: empty name base?"
    nb@(x:_) | isUpper x -> mkName (prefix '_' nb)
             | otherwise -> mkName (prefix '.' nb) -- operator
  where
    prefix :: Char -> String -> String
    prefix char str = char:str


-- | Construct a tuple type given a list of types.
toNestedTupleT :: [TypeQ] -> TypeQ
toNestedTupleT [] = appsT (tupleT 0) []
toNestedTupleT [x] = x
toNestedTupleT (x:xs) = appsT (tupleT 2) [x, toNestedTupleT xs]

-- | Construct a tuple value given a list of expressions.
toNestedTupleE :: [ExpQ] -> ExpQ
toNestedTupleE [] = tupE []
toNestedTupleE [x] = x
toNestedTupleE (x:xs) = tupE [x, toNestedTupleE xs]

-- | Construct a tuple pattern given a list of patterns.
toNestedTupleP :: [PatQ] -> PatQ
toNestedTupleP [] = tupP []
toNestedTupleP [x] = x
toNestedTupleP (x:xs) = tupP [x, toNestedTupleP xs]
