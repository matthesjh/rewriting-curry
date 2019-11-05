--------------------------------------------------------------------------------
--- Library for representation of unification on first-order terms.
---
--- This library implements a unification algorithm using reference tables.
---
--- @author Michael Hanus, Jan-Hendrik Matthes, Jonas Oberschweiber,
---         Bjoern Peemoeller
--- @version November 2019
--- @category algorithm
--------------------------------------------------------------------------------

module Rewriting.Unification
  ( UnificationError (..)
  , showUnificationError, unify, unifiable
  ) where

import Either (isRight)
import List (mapAccumL)

import Data.FiniteMap (FM, emptyFM, addToFM, lookupFM)
import Rewriting.Substitution (Subst, emptySubst, extendSubst)
import Rewriting.Term (VarIdx, Term (..), TermEq, TermEqs)
import Rewriting.UnificationSpec (UnificationError (..), showUnificationError)

-- -----------------------------------------------------------------------------
-- Representation of internal data structures
-- -----------------------------------------------------------------------------

--- An `RTerm` is the unification algorithm's internal term representation.
--- Its `RTermVar` and `RTermCons` constructors are similar to the `TermVar`
--- and `TermCons` constructors of the original `Term` data type, but it has
--- an additional `Ref` constructor. This `Ref` constructor is used to
--- represent references into a reference table.
data RTerm f = Ref VarIdx | RTermVar VarIdx | RTermCons f [RTerm f]
 deriving (Eq, Show)

--- A reference table used to store the values referenced by `Ref` terms
--- represented as a finite map from variables to `RTerm`s and parameterized
--- over the kind of function symbols, e.g., strings.
type RefTable f = FM VarIdx (RTerm f)

--- An `RTerm` equation represented as a pair of `RTerm`s and parameterized
--- over the kind of function symbols, e.g., strings.
type REq f = (RTerm f, RTerm f)

--- Multiple `RTerm` equations represented as a list of `RTerm` equations and
--- parameterized over the kind of function symbols, e.g., strings.
type REqs f = [REq f]

-- -----------------------------------------------------------------------------
-- Definition of exported functions
-- -----------------------------------------------------------------------------

--- Unifies a list of term equations. Returns either a unification error or a
--- substitution.
unify :: Eq f => TermEqs f -> Either (UnificationError f) (Subst f)
unify eqs = let (rt, reqs) = termEqsToREqs eqs
             in either Left
                       (\(rt', reqs') -> Right (eqsToSubst rt' reqs'))
                       (unify' rt [] reqs)

--- Checks whether a list of term equations can be unified.
unifiable :: Eq f => TermEqs f -> Bool
unifiable = isRight . unify

-- -----------------------------------------------------------------------------
-- Conversion to internal structure
-- -----------------------------------------------------------------------------

--- Converts a list of term equations into a list of `RTerm` equations and
--- places references into a fresh reference table.
termEqsToREqs :: TermEqs f -> (RefTable f, REqs f)
termEqsToREqs = mapAccumL termEqToREq (emptyFM (<))

--- Converts a term equation into an `RTerm` equation. The given reference
--- table is used to store references.
termEqToREq :: RefTable f -> TermEq f -> (RefTable f, REq f)
termEqToREq rt (l, r) = let (rt1, l') = termToRTerm rt l
                            (rt2, r') = termToRTerm rt1 r
                         in (rt2, (l', r'))

--- Converts a term to an `RTerm`, placing all variable terms in the given
--- reference table and replacing them by references inside the result
--- `RTerm`.
termToRTerm :: RefTable f -> Term f -> (RefTable f, RTerm f)
termToRTerm rt (TermVar v)     = (addToFM rt v (RTermVar v), Ref v)
termToRTerm rt (TermCons c ts) = let (rt', ts') = mapAccumL termToRTerm rt ts
                                  in (rt', RTermCons c ts')

-- -----------------------------------------------------------------------------
-- Conversion from internal structure
-- -----------------------------------------------------------------------------

--- Converts a list of `RTerm` equations to a substitution by turning every
--- equation of the form `(RTermVar v, t)` or `(t, RTermVar v)` into a mapping
--- `(v, t)`. Equations that do not have a variable term on either side are
--- ignored. Works on `RTerm`s, dereferences all `Ref`s.
eqsToSubst :: RefTable f -> REqs f -> Subst f
eqsToSubst _  []           = emptySubst
eqsToSubst rt ((l, r):eqs)
  = case l of
      (Ref _)         -> eqsToSubst rt ((deref rt l, r):eqs)
      (RTermVar v)    -> extendSubst (eqsToSubst rt eqs) v (rTermToTerm rt r)
      (RTermCons _ _) ->
        case r of
          (Ref _)      -> eqsToSubst rt ((l, deref rt r):eqs)
          (RTermVar v) -> extendSubst (eqsToSubst rt eqs) v (rTermToTerm rt l)
          _            -> eqsToSubst rt eqs

--- Converts an `RTerm` to a term by dereferencing all references inside the
--- `RTerm`. The given reference table is used for reference lookups.
rTermToTerm :: RefTable f -> RTerm f -> Term f
rTermToTerm rt t@(Ref _)        = rTermToTerm rt (deref rt t)
rTermToTerm _  (RTermVar v)     = TermVar v
rTermToTerm rt (RTermCons c ts) = TermCons c (map (rTermToTerm rt) ts)

--- Dereferences an `RTerm` by following chained references. Simply returns
--- the same value for `RTermVar` and `RTermCons`. The given reference table
--- is used for reference lookups.
deref :: RefTable f -> RTerm f -> RTerm f
deref rt (Ref i)           = case lookupFM rt i of
                               Nothing  -> error ("deref: " ++ (show i))
                               (Just t) -> case t of
                                             (Ref _)         -> deref rt t
                                             (RTermVar _)    -> t
                                             (RTermCons _ _) -> t
deref _  t@(RTermVar _)    = t
deref _  t@(RTermCons _ _) = t

-- -----------------------------------------------------------------------------
-- Unification algorithm
-- -----------------------------------------------------------------------------

--- Internal unification function, the core of the algorithm.
unify' :: Eq f => RefTable f -> REqs f -> REqs f
       -> Either (UnificationError f) (RefTable f, REqs f)
-- No equations left, we are done.
unify' rt sub []              = Right (rt, sub)
unify' rt sub (eq@(l, r):eqs)
  = case eq of
      -- Substitute the variable by the constructor term.
      (RTermVar v, RTermCons _ _)           -> elim rt sub v r eqs
      (RTermCons _ _, RTermVar v)           -> elim rt sub v l eqs
      -- If both variables are equal, simply remove the equation.
      -- Otherwise substitute the first variable by the second variable.
      (RTermVar v, RTermVar v') | v == v'   -> unify' rt sub eqs
                                | otherwise -> elim rt sub v r eqs
      -- If both constructors have the same name, equate their arguments.
      -- Otherwise fail with a clash.
      (RTermCons c1 ts1, RTermCons c2 ts2)
        | c1 == c2  -> unify' rt sub ((zip ts1 ts2) ++ eqs)
        | otherwise -> Left (Clash (rTermToTerm rt l) (rTermToTerm rt r))
      -- If we encounter a Ref, simply dereference it and try again.
      _ -> unify' rt sub ((deref rt l, deref rt r):eqs)

--- Substitutes a variable by a term inside a list of equations that have
--- yet to be unified and the right-hand sides of all equations of the result
--- list. Also adds a mapping from that variable to that term to the result
--- list.
elim :: Eq f => RefTable f -> REqs f -> VarIdx -> RTerm f -> REqs f
     -> Either (UnificationError f) (RefTable f, REqs f)
elim rt sub v t eqs
  | dependsOn rt (RTermVar v) t = Left (OccurCheck v (rTermToTerm rt t))
  | otherwise
    = case t of
        (Ref _)         -> error "elim"
        -- Make sure to place a Ref in the reference table and substitution,
        -- not the RTermVar itself.
        (RTermVar v')   -> let rt' = addToFM rt v (Ref v')
                            in unify' rt' ((RTermVar v, Ref v'):sub) eqs
        (RTermCons _ _) -> unify' (addToFM rt v t) ((RTermVar v, t):sub) eqs

--- Checks whether the first term occurs as a subterm of the second term.
dependsOn :: Eq f => RefTable f -> RTerm f -> RTerm f -> Bool
dependsOn rt l r = (l /= r) && (dependsOn' r)
  where
    dependsOn' x@(Ref _)        = (deref rt x) == l
    dependsOn' t@(RTermVar _)   = l == t
    dependsOn' (RTermCons _ ts) = or (map dependsOn' ts)