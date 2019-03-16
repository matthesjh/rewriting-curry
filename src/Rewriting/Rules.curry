------------------------------------------------------------------------------
--- Library for representation of rules and term rewriting systems.
---
--- @author Jan-Hendrik Matthes
--- @version November 2016
--- @category algorithm
------------------------------------------------------------------------------

module Rewriting.Rules
  ( Rule, TRS
  , showRule, showTRS, rRoot, rCons, rVars, maxVarInRule, minVarInRule
  , maxVarInTRS, minVarInTRS, renameRuleVars, renameTRSVars, normalizeRule
  , normalizeTRS, isVariantOf, isLeftLinear, isLeftNormal, isRedex, isPattern
  , isConsBased, isDemandedAt
  ) where

import Function (on, both)
import List (union, maximum, minimum)
import Maybe (mapMaybe)
import Rewriting.Substitution (listToSubst, applySubst)
import Rewriting.Term

-- ---------------------------------------------------------------------------
-- Representation of rules and term rewriting systems
-- ---------------------------------------------------------------------------

--- A rule represented as a pair of terms and parameterized over the kind of
--- function symbols, e.g., strings.
type Rule f = (Term f, Term f)

--- A term rewriting system represented as a list of rules and parameterized
--- over the kind of function symbols, e.g., strings.
type TRS f = [Rule f]

-- ---------------------------------------------------------------------------
-- Pretty-printing of rules and term rewriting systems
-- ---------------------------------------------------------------------------

-- \x2192 = RIGHTWARDS ARROW

--- Transforms a rule into a string representation.
showRule :: (f -> String) -> Rule f -> String
showRule s (l, r) = (showTerm s l) ++ " \x2192 " ++ (showTerm s r)

--- Transforms a term rewriting system into a string representation.
showTRS :: (f -> String) -> TRS f -> String
showTRS s = unlines . (map (showRule s))

-- ---------------------------------------------------------------------------
-- Functions for rules and term rewriting systems
-- ---------------------------------------------------------------------------

--- Returns the root symbol (variable or constructor) of a rule.
rRoot :: Rule f -> Either VarIdx f
rRoot (l, _) = tRoot l

--- Returns a list without duplicates of all constructors in a rule.
rCons :: Eq f => Rule f -> [f]
rCons (l, r) = union (tCons l) (tCons r)

--- Returns a list without duplicates of all variables in a rule.
rVars :: Rule _ -> [VarIdx]
rVars (l, _) = tVars l

--- Returns the maximum variable in a rule or `Nothing` if no variable exists.
maxVarInRule :: Rule _ -> Maybe VarIdx
maxVarInRule (l, _) = maxVarInTerm l

--- Returns the minimum variable in a rule or `Nothing` if no variable exists.
minVarInRule :: Rule _ -> Maybe VarIdx
minVarInRule (l, _) = minVarInTerm l

--- Returns the maximum variable in a term rewriting system or `Nothing` if no
--- variable exists.
maxVarInTRS :: TRS _ -> Maybe VarIdx
maxVarInTRS trs = case mapMaybe maxVarInRule trs of
                    []       -> Nothing
                    vs@(_:_) -> Just (maximum vs)

--- Returns the minimum variable in a term rewriting system or `Nothing` if no
--- variable exists.
minVarInTRS :: TRS _ -> Maybe VarIdx
minVarInTRS trs = case mapMaybe minVarInRule trs of
                    []       -> Nothing
                    vs@(_:_) -> Just (minimum vs)

--- Renames the variables in a rule by the given number.
renameRuleVars :: Int -> Rule f -> Rule f
renameRuleVars i = both (renameTermVars i)

--- Renames the variables in every rule of a term rewriting system by the
--- given number.
renameTRSVars :: Int -> TRS f -> TRS f
renameTRSVars i = map (renameRuleVars i)

--- Normalizes a rule by renaming all variables with an increasing order,
--- starting from the minimum possible variable.
normalizeRule :: Rule f -> Rule f
normalizeRule r = let sub = listToSubst (zip (rVars r) (map TermVar [0..]))
                   in both (applySubst sub) r

--- Normalizes all rules in a term rewriting system by renaming all variables
--- with an increasing order, starting from the minimum possible variable.
normalizeTRS :: TRS f -> TRS f
normalizeTRS = map normalizeRule

--- Checks whether the first rule is a variant of the second rule.
isVariantOf :: Eq f => Rule f -> Rule f -> Bool
isVariantOf = on (==) normalizeRule

--- Checks whether a term rewriting system is left-linear.
isLeftLinear :: TRS _ -> Bool
isLeftLinear = all (isLinear . fst)

--- Checks whether a term rewriting system is left-normal.
isLeftNormal :: TRS _ -> Bool
isLeftNormal = all (isNormal . fst)

--- Checks whether a term is reducible with some rule
--- of the given term rewriting system.
isRedex :: Eq f => TRS f -> Term f -> Bool
isRedex trs t = any ((eqConsPattern t) . fst) trs

--- Checks whether a term is a pattern, i.e., an root-reducible term
--- where the argaccording to the given term rewriting
--- system.
isPattern :: Eq f => TRS f -> Term f -> Bool
isPattern _   (TermVar _)       = False
isPattern trs t@(TermCons _ ts) = isRedex trs t && all isVarOrCons ts
 where
  isVarOrCons (TermVar _)         = True
  isVarOrCons t'@(TermCons _ ts') = not (isRedex trs t') && all isVarOrCons ts'

--- Checks whether a term rewriting system is constructor-based.
isConsBased :: Eq f => TRS f -> Bool
isConsBased trs = all ((isPattern trs) . fst) trs

--- Checks whether the given argument position of a rule is demanded. Returns
--- `True` if the corresponding argument term is a constructor term.
isDemandedAt :: Int -> Rule _ -> Bool
isDemandedAt _ (TermVar _, _)     = False
isDemandedAt i (TermCons _ ts, _) = (i > 0) && (i <= (length ts))
                                      && (isConsTerm (ts !! (i - 1)))