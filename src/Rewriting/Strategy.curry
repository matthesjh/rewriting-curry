------------------------------------------------------------------------------
--- Library for representation and computation of reductions on first-order
--- terms and representation of reduction strategies.
---
--- @author Jan-Hendrik Matthes
--- @version November 2016
--- @category algorithm
------------------------------------------------------------------------------

module Rewriting.Strategy
  ( RStrategy, Reduction (..)
  , showReduction, redexes, seqRStrategy, parRStrategy, liRStrategy
  , loRStrategy, riRStrategy, roRStrategy, piRStrategy, poRStrategy, reduce
  , reduceL, reduceBy, reduceByL, reduceAt, reduceAtL, reduction, reductionL
  , reductionBy, reductionByL
  ) where

import List (nub, intercalate, groupBy, sortBy, minimumBy)
import Rewriting.Position
import Rewriting.Rules (TRS, renameRuleVars, renameTRSVars)
import Rewriting.Substitution (applySubst)
import Rewriting.Term (Term, showTerm, maxVarInTerm)
import Rewriting.Unification (unify)

-- ---------------------------------------------------------------------------
-- Representation of reduction strategies
-- ---------------------------------------------------------------------------

--- A reduction strategy represented as a function that takes a term rewriting
--- system and a term and returns the redex positions where the term should be
--- reduced, parameterized over the kind of function symbols, e.g., strings.
type RStrategy f = TRS f -> Term f -> [Pos]

-- ---------------------------------------------------------------------------
-- Representation of reductions on first-order terms
-- ---------------------------------------------------------------------------

--- Representation of a reduction on first-order terms, parameterized over the
--- kind of function symbols, e.g., strings.
---
--- @cons NormalForm t - The normal form with term `t`.
--- @cons RStep t ps r - The reduction of term `t` at positions `ps` to
---                      reduction `r`.
data Reduction f = NormalForm (Term f) | RStep (Term f) [Pos] (Reduction f)

-- ---------------------------------------------------------------------------
-- Pretty-printing of reductions on first-order terms
-- ---------------------------------------------------------------------------

-- \x2192 = RIGHTWARDS ARROW

--- Transforms a reduction into a string representation.
showReduction :: (f -> String) -> Reduction f -> String
showReduction s (NormalForm t) = showTerm s t
showReduction s (RStep t ps r) = (showTerm s t) ++ "\n\x2192" ++ "["
                                   ++ (intercalate "," (map showPos ps))
                                   ++ "] " ++ (showReduction s r)

-- ---------------------------------------------------------------------------
-- Functions for definition of reduction strategies
-- ---------------------------------------------------------------------------

--- Returns the redex positions of a term according to the given term
--- rewriting system.
redexes :: Eq f => TRS f -> Term f -> [Pos]
redexes trs t
  = let trs' = maybe trs (\v -> renameTRSVars (v + 1) trs) (maxVarInTerm t)
     in nub [p | p <- positions t, let tp = t |> p,
                 (l, _) <- trs',
                 (Right sub) <- [unify [(l, tp)]],
                 tp == (applySubst sub l)]

--- Returns a sequential reduction strategy according to the given ordering
--- function.
seqRStrategy :: Eq f => (Pos -> Pos -> Ordering) -> RStrategy f
seqRStrategy cmp trs t = case redexes trs t of
                           []       -> []
                           ps@(_:_) -> [minimumBy cmp ps]

--- Returns a parallel reduction strategy according to the given ordering
--- function.
parRStrategy :: Eq f => (Pos -> Pos -> Ordering) -> RStrategy f
parRStrategy cmp trs t = case redexes trs t of
                           []       -> []
                           ps@(_:_) -> head (groupBy g (sortBy s ps))
  where
    g :: Pos -> Pos -> Bool
    g p q = (cmp p q) == EQ
    s :: Pos -> Pos -> Bool
    s p q = (cmp p q) /= GT

-- ---------------------------------------------------------------------------
-- Definition of common reduction strategies
-- ---------------------------------------------------------------------------

--- The leftmost innermost reduction strategy.
liRStrategy :: Eq f => RStrategy f
liRStrategy = seqRStrategy liOrder
  where
    liOrder :: Pos -> Pos -> Ordering
    liOrder p q | p == q     = EQ
                | leftOf p q = LT
                | below p q  = LT
                | otherwise  = GT

--- The leftmost outermost reduction strategy.
loRStrategy :: Eq f => RStrategy f
loRStrategy = seqRStrategy loOrder
  where
    loOrder :: Pos -> Pos -> Ordering
    loOrder p q | p == q     = EQ
                | leftOf p q = LT
                | above p q  = LT
                | otherwise  = GT

--- The rightmost innermost reduction strategy.
riRStrategy :: Eq f => RStrategy f
riRStrategy = seqRStrategy riOrder
  where
    riOrder :: Pos -> Pos -> Ordering
    riOrder p q | p == q      = EQ
                | rightOf p q = LT
                | below p q   = LT
                | otherwise   = GT

--- The rightmost outermost reduction strategy.
roRStrategy :: Eq f => RStrategy f
roRStrategy = seqRStrategy roOrder
  where
    roOrder :: Pos -> Pos -> Ordering
    roOrder p q | p == q      = EQ
                | rightOf p q = LT
                | above p q   = LT
                | otherwise      = GT

--- The parallel innermost reduction strategy.
piRStrategy :: Eq f => RStrategy f
piRStrategy = parRStrategy piOrder
  where
    piOrder :: Pos -> Pos -> Ordering
    piOrder p q | p == q    = EQ
                | below p q = LT
                | above p q = GT
                | otherwise = EQ

--- The parallel outermost reduction strategy.
poRStrategy :: Eq f => RStrategy f
poRStrategy = parRStrategy poOrder
  where
    poOrder :: Pos -> Pos -> Ordering
    poOrder p q | p == q    = EQ
                | above p q = LT
                | below p q = GT
                | otherwise = EQ

-- ---------------------------------------------------------------------------
-- Functions for reductions on first-order terms
-- ---------------------------------------------------------------------------

--- Reduces a term with the given strategy and term rewriting system.
reduce :: Eq f => RStrategy f -> TRS f -> Term f -> Term f
reduce s trs t = case s trs t of
                   []       -> t
                   ps@(_:_) -> reduce s trs (reduceAtL trs ps t)

--- Reduces a term with the given strategy and list of term rewriting systems.
reduceL :: Eq f => RStrategy f -> [TRS f] -> Term f -> Term f
reduceL s trss = reduce s (concat trss)

--- Reduces a term with the given strategy and term rewriting system by the
--- given number of steps.
reduceBy :: Eq f => RStrategy f -> TRS f -> Int -> Term f -> Term f
reduceBy s trs n t
  | n <= 0    = t
  | otherwise = case s trs t of
                  []       -> t
                  ps@(_:_) -> reduceBy s trs (n - 1) (reduceAtL trs ps t)

--- Reduces a term with the given strategy and list of term rewriting systems
--- by the given number of steps.
reduceByL :: Eq f => RStrategy f -> [TRS f] -> Int -> Term f -> Term f
reduceByL s trss = reduceBy s (concat trss)

--- Reduces a term with the given term rewriting system at the given redex
--- position.
reduceAt :: Eq f => TRS f -> Pos -> Term f -> Term f
reduceAt []     _ t = t
reduceAt (x:rs) p t
  = case unify [(l, tp)] of
      (Left _)                           -> reduceAt rs p t
      (Right s) | tp == (applySubst s l) -> replaceTerm t p (applySubst s r)
                | otherwise              -> reduceAt rs p t
  where
    tp = t |> p
    (l, r) = maybe x (\v -> renameRuleVars (v + 1) x) (maxVarInTerm tp)

--- Reduces a term with the given term rewriting system at the given redex
--- positions.
reduceAtL :: Eq f => TRS f -> [Pos] -> Term f -> Term f
reduceAtL _   []     t = t
reduceAtL trs (p:ps) t = reduceAtL trs ps (reduceAt trs p t)

--- Returns the reduction of a term with the given strategy and term rewriting
--- system.
reduction :: Eq f => RStrategy f -> TRS f -> Term f -> Reduction f
reduction s trs t
  = case s trs t of
      []       -> NormalForm t
      ps@(_:_) -> RStep t ps (reduction s trs (reduceAtL trs ps t))

--- Returns the reduction of a term with the given strategy and list of term
--- rewriting systems.
reductionL :: Eq f => RStrategy f -> [TRS f] -> Term f -> Reduction f
reductionL s trss = reduction s (concat trss)

--- Returns the reduction of a term with the given strategy, the given term
--- rewriting system and the given number of steps.
reductionBy :: Eq f => RStrategy f -> TRS f -> Int -> Term f -> Reduction f
reductionBy s trs n t
  | n <= 0    = NormalForm t
  | otherwise = case s trs t of
                  []       -> NormalForm t
                  ps@(_:_) -> let t' = reduceAtL trs ps t
                               in RStep t ps (reductionBy s trs (n - 1) t')

--- Returns the reduction of a term with the given strategy, the given list of
--- term rewriting systems and the given number of steps.
reductionByL :: Eq f => RStrategy f -> [TRS f] -> Int -> Term f -> Reduction f
reductionByL s trss = reductionBy s (concat trss)