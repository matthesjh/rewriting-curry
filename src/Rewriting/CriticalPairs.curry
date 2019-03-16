------------------------------------------------------------------------------
--- Library for representation and computation of critical pairs.
---
--- @author Jan-Hendrik Matthes
--- @version August 2016
--- @category algorithm
------------------------------------------------------------------------------

module Rewriting.CriticalPairs
  ( CPair
  , showCPair, showCPairs, cPairs, isOrthogonal, isWeakOrthogonal
  ) where

import List (nub)
import Rewriting.Position (eps, positions, (|>), replaceTerm)
import Rewriting.Rules
import Rewriting.Substitution (applySubst)
import Rewriting.Term (Term, showTerm, isConsTerm)
import Rewriting.Unification (unify)

-- ---------------------------------------------------------------------------
-- Representation of critical pairs
-- ---------------------------------------------------------------------------

--- A critical pair represented as a pair of terms and parameterized over the
--- kind of function symbols, e.g., strings.
type CPair f = (Term f, Term f)

-- ---------------------------------------------------------------------------
-- Pretty-printing of critical pairs
-- ---------------------------------------------------------------------------

-- \x3008 = LEFT ANGLE BRACKET
-- \x3009 = RIGHT ANGLE BRACKET

--- Transforms a critical pair into a string representation.
showCPair :: (f -> String) -> CPair f -> String
showCPair s (l, r) = "\x3008" ++ (showTerm s l) ++ ", " ++ (showTerm s r)
                       ++ "\x3009"

--- Transforms a list of critical pairs into a string representation.
showCPairs :: (f -> String) -> [CPair f] -> String
showCPairs s = unlines . (map (showCPair s))

-- ---------------------------------------------------------------------------
-- Computation of critical pairs
-- ---------------------------------------------------------------------------

--- Returns the critical pairs of a term rewriting system.
cPairs :: Eq f => TRS f -> [CPair f]
cPairs trs
  = let trs' = maybe trs (\v -> renameTRSVars (v + 1) trs) (maxVarInTRS trs)
     in nub [(applySubst sub r1,
              replaceTerm (applySubst sub l1) p (applySubst sub r2)) |
             rule1@(l1, r1) <- trs',
             p <- positions l1, let l1p = l1 |> p, isConsTerm l1p,
             rule2@(l2, r2) <- trs,
             (Right sub) <- [unify [(l1p, l2)]],
             (p /= eps) || (not (isVariantOf rule1 rule2))]

-- ---------------------------------------------------------------------------
-- Functions for term rewriting systems and critical pairs
-- ---------------------------------------------------------------------------

--- Checks whether a term rewriting system is orthogonal.
isOrthogonal :: Eq f => TRS f -> Bool
isOrthogonal trs = (isLeftLinear trs) && (null (cPairs trs))

--- Checks whether a term rewriting system is weak-orthogonal.
isWeakOrthogonal :: Eq f => TRS f -> Bool
isWeakOrthogonal trs = (isLeftLinear trs) && (all (uncurry (==)) (cPairs trs))