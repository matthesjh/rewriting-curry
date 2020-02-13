--------------------------------------------------------------------------------
--- Library for representation of first-order terms.
---
--- This library is the basis of other libraries for the manipulation of
--- first-order terms, e.g., unification of terms. Therefore, this library also
--- defines other structures, like term equations.
---
--- @author Jan-Hendrik Matthes
--- @version February 2020
--- @category algorithm
--------------------------------------------------------------------------------

module Rewriting.Term
  ( VarIdx, Term (..), TermEq, TermEqs
  , showVarIdx, showTerm, showTermEq, showTermEqs, tConst, tOp, tRoot, tCons
  , tConsAll, tVars, tVarsAll, isConsTerm, isVarTerm, isGround, isLinear
  , isNormal, maxVarInTerm, minVarInTerm, normalizeTerm, renameTermVars, mapTerm
  , eqConsPattern
  ) where

import Char           (isAlphaNum)
import Data.FiniteMap (listToFM, lookupFM)
import List           (intercalate, maximum, minimum, nub)
import Maybe          (fromMaybe)

-- -----------------------------------------------------------------------------
-- Representation of first-order terms and term equations
-- -----------------------------------------------------------------------------

--- A variable represented as an integer greater than or equal to zero.
type VarIdx = Int

--- Representation of a first-order term, parameterized over the kind of
--- function symbols, e.g., strings.
---
--- @cons TermVar v     - The variable term with variable `v`.
--- @cons TermCons c ts - The constructor term with constructor `c` and
---                       argument terms `ts`.
data Term f = TermVar VarIdx | TermCons f [Term f]
  deriving (Eq, Show)

--- A term equation represented as a pair of terms and parameterized over the
--- kind of function symbols, e.g., strings.
type TermEq f = (Term f, Term f)

--- Multiple term equations represented as a list of term equations and
--- parameterized over the kind of function symbols, e.g., strings.
type TermEqs f = [TermEq f]

-- -----------------------------------------------------------------------------
-- Pretty-printing of first-order terms and term equations
-- -----------------------------------------------------------------------------

--- Transforms a variable into a string representation.
showVarIdx :: VarIdx -> String
showVarIdx v | v >= 0    = if q == 0 then [c] else c : show q
             | otherwise = ""
  where
    (q, r) = divMod v 26
    c = "abcdefghijklmnopqrstuvwxyz" !! r

--- Transforms a term into a string representation.
showTerm :: (f -> String) -> Term f -> String
showTerm s = showTerm' False
  where
    showTerm' _ (TermVar v)     = showVarIdx v
    showTerm' b (TermCons c ts) = case ts of
      []     -> cStr
      [l, r] -> if any isAlphaNum cStr
                  then prefixString
                  else parensIf b (showTerm' True l ++ " " ++ cStr ++ " "
                                                    ++ showTerm' True r)
      _      -> prefixString
     where
       cStr         = s c
       prefixString = cStr ++ "("
                           ++ intercalate "," (map (showTerm' False) ts) ++ ")"

--- Transforms a term equation into a string representation.
showTermEq :: (f -> String) -> TermEq f -> String
showTermEq s (l, r) = showTerm s l ++ " = " ++ showTerm s r

--- Transforms a list of term equations into a string representation.
showTermEqs :: (f -> String) -> TermEqs f -> String
showTermEqs s = unlines . map (showTermEq s)

-- -----------------------------------------------------------------------------
-- Functions for first-order terms
-- -----------------------------------------------------------------------------

--- Returns a term with the given constructor and no argument terms.
tConst :: f -> Term f
tConst c = TermCons c []

--- Returns an infix operator term with the given constructor and the given left
--- and right argument term.
tOp :: Term f -> f -> Term f -> Term f
tOp l c r = TermCons c [l, r]

--- Returns the root symbol (variable or constructor) of a term.
tRoot :: Term f -> Either VarIdx f
tRoot (TermVar v)    = Left v
tRoot (TermCons c _) = Right c

--- Returns a list without duplicates of all constructors in a term.
tCons :: Eq f => Term f -> [f]
tCons = nub . tConsAll

--- Returns a list of all constructors in a term. The resulting list may contain
--- duplicates.
tConsAll :: Term f -> [f]
tConsAll (TermVar _)     = []
tConsAll (TermCons c ts) = c : concatMap tConsAll ts

--- Returns a list without duplicates of all variables in a term.
tVars :: Term _ -> [VarIdx]
tVars = nub . tVarsAll

--- Returns a list of all variables in a term. The resulting list may contain
--- duplicates.
tVarsAll :: Term _ -> [VarIdx]
tVarsAll (TermVar v)     = [v]
tVarsAll (TermCons _ ts) = concatMap tVarsAll ts

--- Checks whether a term is a constructor term.
isConsTerm :: Term _ -> Bool
isConsTerm (TermVar _)    = False
isConsTerm (TermCons _ _) = True

--- Checks whether a term is a variable term.
isVarTerm :: Term _ -> Bool
isVarTerm = not . isConsTerm

--- Checks whether a term is a ground term (contains no variables).
isGround :: Term _ -> Bool
isGround = null . tVarsAll

--- Checks whether a term is linear (contains no variable more than once).
isLinear :: Term _ -> Bool
isLinear = unique . tVarsAll

--- Checks whether a term is normal (behind a variable is not a constructor).
isNormal :: Term _ -> Bool
isNormal (TermVar _)         = True
isNormal (TermCons _ [])     = True
isNormal (TermCons c (t:ts)) = case t of
  TermVar _    -> all isVarTerm ts
  TermCons _ _ -> isNormal t && isNormal (TermCons c ts)

--- Returns the maximum variable in a term or `Nothing` if no variable exists.
maxVarInTerm :: Term _ -> Maybe VarIdx
maxVarInTerm t = case tVars t of
                   []       -> Nothing
                   vs@(_:_) -> Just (maximum vs)

--- Returns the minimum variable in a term or `Nothing` if no variable exists.
minVarInTerm :: Term _ -> Maybe VarIdx
minVarInTerm t = case tVars t of
                   []       -> Nothing
                   vs@(_:_) -> Just (minimum vs)

--- Normalizes a term by renaming all variables with an increasing order,
--- starting from the minimum possible variable.
normalizeTerm :: Term f -> Term f
normalizeTerm t = normalize t
  where
    sub = listToFM (<) (zip (tVars t) (map TermVar [0..]))

    normalize t'@(TermVar v)  = fromMaybe t' (lookupFM sub v)
    normalize (TermCons c ts) = TermCons c (map normalize ts)

--- Renames the variables in a term by the given number.
renameTermVars :: Int -> Term f -> Term f
renameTermVars i (TermVar v)     = TermVar (v + i)
renameTermVars i (TermCons c ts) = TermCons c (map (renameTermVars i) ts)

--- Transforms a term by applying a transformation on all constructors.
mapTerm :: (a -> b) -> Term a -> Term b
mapTerm _ (TermVar v)     = TermVar v
mapTerm f (TermCons c ts) = TermCons (f c) (map (mapTerm f) ts)

--- Checks whether the constructor pattern of the first term is equal to the
--- constructor pattern of the second term. Returns `True` if both terms have
--- the same constructor and the same arity.
eqConsPattern :: Eq f => Term f -> Term f -> Bool
eqConsPattern (TermVar _)       _                 = False
eqConsPattern (TermCons _ _)    (TermVar _)       = False
eqConsPattern (TermCons c1 ts1) (TermCons c2 ts2) =
  c1 == c2 && length ts1 == length ts2

-- -----------------------------------------------------------------------------
-- Definition of helper functions
-- -----------------------------------------------------------------------------

--- Encloses a string in parentheses if the given condition is true.
parensIf :: Bool -> String -> String
parensIf b s = if b then "(" ++ s ++ ")" else s

--- Checks whether a list contains no element more than once.
unique :: Eq a => [a] -> Bool
unique []                    = True
unique (x:xs) | notElem x xs = unique xs
              | otherwise    = False