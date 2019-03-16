------------------------------------------------------------------------------
--- Library for specifying the unification on first-order terms.
---
--- This library implements a general unification algorithm. Because the
--- algorithm is easy to understand, but rather slow, it serves as a
--- specification for more elaborate implementations.
---
--- @author Michael Hanus, Jan-Hendrik Matthes, Jonas Oberschweiber,
---         Bjoern Peemoeller
--- @version August 2016
--- @category algorithm
------------------------------------------------------------------------------

module Rewriting.UnificationSpec
  ( UnificationError (..)
  , showUnificationError, unify, unifiable
  ) where

import Either (isRight)
import Function (both)
import Rewriting.Substitution (Subst, emptySubst, extendSubst)
import Rewriting.Term

-- ---------------------------------------------------------------------------
-- Representation of unification errors
-- ---------------------------------------------------------------------------

--- Representation of a unification error, parameterized over the kind of
--- function symbols, e.g., strings.
---
--- @cons Clash t1 t2    - The constructor term `t1` is supposed to be equal
---                        to the constructor term `t2` but has a different
---                        constructor.
--- @cons OccurCheck v t - The variable `v` is supposed to be equal to the
---                        term `t` in which it occurs as a subterm.
data UnificationError f = Clash (Term f) (Term f) | OccurCheck VarIdx (Term f)

-- ---------------------------------------------------------------------------
-- Pretty-printing of unification errors
-- ---------------------------------------------------------------------------

--- Transforms a unification error into a string representation.
showUnificationError :: (f -> String) -> UnificationError f -> String
showUnificationError s (Clash t1 t2)    = "Clash: " ++ (showTerm s t1)
                                            ++ " is not equal to "
                                            ++ (showTerm s t2) ++ "."
showUnificationError s (OccurCheck v t) = "OccurCheck: " ++ (showVarIdx v)
                                            ++ " occurs in " ++ (showTerm s t)
                                            ++ "."

-- ---------------------------------------------------------------------------
-- Functions for unification on first-order terms
-- ---------------------------------------------------------------------------

--- Unifies a list of term equations. Returns either a unification error or a
--- substitution.
unify :: (Eq f, Show f) => TermEqs f -> Either (UnificationError f) (Subst f)
unify = (either Left (Right . eqsToSubst)) . (unify' [])
  where
    eqsToSubst []              = emptySubst
    eqsToSubst (eq@(l, r):eqs)
      = case l of
          (TermVar v)    -> extendSubst (eqsToSubst eqs) v r
          (TermCons _ _) ->
            case r of
              (TermVar v)    -> extendSubst (eqsToSubst eqs) v l
              (TermCons _ _) -> error ("eqsToSubst: " ++ (show eq))

--- Checks whether a list of term equations can be unified.
unifiable :: (Eq f, Show f) => TermEqs f -> Bool
unifiable = isRight . unify

--- Unifies a list of term equations. The first argument specifies the current
--- substitution represented by term equations. Returns either a unification
--- error or a substitution represented by term equations.
unify' :: Eq f => TermEqs f -> TermEqs f
       -> Either (UnificationError f) (TermEqs f)
unify' sub []                                               = Right sub
unify' sub ((TermVar v, r@(TermCons _ _)):eqs)              = elim sub v r eqs
unify' sub ((l@(TermCons _ _), TermVar v):eqs)              = elim sub v l eqs
unify' sub ((TermVar v, r@(TermVar v')):eqs) | v == v'      = unify' sub eqs
                                             | otherwise    = elim sub v r eqs
unify' sub ((l@(TermCons c1 ts1), r@(TermCons c2 ts2)):eqs)
  | c1 == c2  = unify' sub ((zip ts1 ts2) ++ eqs)
  | otherwise = Left (Clash l r)

--- Substitutes a variable by a term inside a substitution and a list of term
--- equations that have yet to be unified. Also adds a mapping from that
--- variable to that term to the substitution.
elim :: Eq f => TermEqs f -> VarIdx -> Term f -> TermEqs f
     -> Either (UnificationError f) (TermEqs f)
elim sub v t eqs | dependsOn (TermVar v) t = Left (OccurCheck v t)
                 | otherwise               = unify' sub' (substitute v t eqs)
  where
    sub' = (TermVar v, t):(map (\(l, r) -> (l, termSubstitute v t r)) sub)

--- Substitutes a variable by a term inside another term.
termSubstitute :: VarIdx -> Term f -> Term f -> Term f
termSubstitute v t x@(TermVar v') | v == v'   = t
                                  | otherwise = x
termSubstitute v t (TermCons c ts) = TermCons c (termsSubstitute v t ts)

--- Substitutes a variable by a term inside a list of terms.
termsSubstitute :: VarIdx -> Term f -> [Term f] -> [Term f]
termsSubstitute v t = map (termSubstitute v t)

--- Substitutes a variable by a term inside a list of term equations.
substitute :: VarIdx -> Term f -> TermEqs f -> TermEqs f
substitute v t = map (substituteSingle v t)

--- Substitutes a variable by a term inside a term equation.
substituteSingle :: VarIdx -> Term f -> TermEq f -> TermEq f
substituteSingle v t = both (termSubstitute v t)

--- Checks whether the first term occurs as a subterm of the second term.
dependsOn :: Eq f => Term f -> Term f -> Bool
dependsOn l r = and [not (l == r), dependsOn' l r]
  where
    dependsOn' t v@(TermVar _)   = t == v
    dependsOn' t (TermCons _ ts) = any id (map (dependsOn' t) ts)