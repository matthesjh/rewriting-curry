--------------------------------------------------------------------------------
--- Library for representation and computation of narrowings on first-order
--- terms and representation of narrowing strategies.
---
--- @author Jan-Hendrik Matthes
--- @version October 2020
--- @category algorithm
--------------------------------------------------------------------------------

module Rewriting.Narrowing
  ( NStrategy, Narrowing (..), NarrowingTree (..), NOptions (..)
  , defaultNOptions, showNarrowing, stdNStrategy, imNStrategy, omNStrategy
  , loNStrategy, lazyNStrategy, wnNStrategy, narrowBy, narrowByL, narrowingBy
  , narrowingByL, narrowingTreeBy, narrowingTreeByL, solveEq, solveEqL
  , dotifyNarrowingTree, writeNarrowingTree
  ) where

import Data.Map                   (elems)
import List                       (maximum)
import Maybe                      (fromMaybe, mapMaybe)
import State

import Rewriting.DefinitionalTree
import Rewriting.Position
import Rewriting.Rules
import Rewriting.Strategy         (RStrategy, poRStrategy, reduce)
import Rewriting.Substitution
import Rewriting.Term
import Rewriting.Unification      (UnificationError (..), unifiable, unify)

-- -----------------------------------------------------------------------------
-- Representation of narrowing strategies
-- -----------------------------------------------------------------------------

--- A narrowing strategy represented as a function that takes a term rewriting
--- system and a term and returns a list of triples consisting of a position, a
--- rule and a substitution, parameterized over the kind of function symbols,
--- e.g., strings.
type NStrategy f = TRS f -> Term f -> [(Pos, Rule f, Subst f)]

-- -----------------------------------------------------------------------------
-- Representation of narrowings on first-order terms
-- -----------------------------------------------------------------------------

--- Representation of a narrowing on first-order terms, parameterized over the
--- kind of function symbols, e.g., strings.
---
--- @cons NTerm t         - The narrowed term `t`.
--- @cons NStep t p sub n - The narrowing of term `t` at position `p` with
---                         substitution `sub` to narrowing `n`.
data Narrowing f = NTerm (Term f) | NStep (Term f) Pos (Subst f) (Narrowing f)

-- -----------------------------------------------------------------------------
-- Representation of narrowing trees for first-order terms
-- -----------------------------------------------------------------------------

--- Representation of a narrowing tree for first-order terms, parameterized over
--- the kind of function symbols, e.g., strings.
---
--- @cons NTree t ns - The narrowing of term `t` to a new term with a list of
---                    narrowing steps `ns`.
data NarrowingTree f = NTree (Term f) [(Pos, Subst f, NarrowingTree f)]

-- -----------------------------------------------------------------------------
-- Representation of narrowing options for solving term equations
-- -----------------------------------------------------------------------------

--- Representation of narrowing options for solving term equations,
--- parameterized over the kind of function symbols, e.g., strings.
---
--- @field normalize - Indicates whether a term should be normalized before
---                    computing further narrowing steps.
--- @field rStrategy - The reduction strategy to normalize a term.
data NOptions f = NOptions { normalize :: Bool, rStrategy :: RStrategy f }

--- The default narrowing options.
defaultNOptions :: Eq f => NOptions f
defaultNOptions = NOptions { normalize = False, rStrategy = poRStrategy }

-- -----------------------------------------------------------------------------
-- Pretty-printing of narrowings on first-order terms
-- -----------------------------------------------------------------------------

-- \x2192 = RIGHTWARDS ARROW

--- Transforms a narrowing into a string representation.
showNarrowing :: (f -> String) -> Narrowing f -> String
showNarrowing s (NTerm t)         = showTerm s t
showNarrowing s (NStep t p sub n) =
  showTerm s t ++ "\n\x2192" ++ "[" ++ showPos p ++ ", "
               ++ showSubst s (restrictSubst sub (tVars t)) ++ "] "
               ++ showNarrowing s n

-- -----------------------------------------------------------------------------
-- Definition of common narrowing strategies
-- -----------------------------------------------------------------------------

--- The standard narrowing strategy.
stdNStrategy :: Eq f => NStrategy f
stdNStrategy trs t = [(p, rule, sub) | p <- positions t,
                                       let tp = t |> p, isConsTerm tp,
                                       rule@(l, _) <- trs,
                                       Right sub <- [unify [(tp, l)]]]

--- The innermost narrowing strategy.
imNStrategy :: Eq f => NStrategy f
imNStrategy trs t = [(p, rule, sub) | p <- positions t,
                                      let tp = t |> p, isPattern trs tp,
                                      rule@(l, _) <- trs,
                                      Right sub <- [unify [(tp, l)]]]

--- The outermost narrowing strategy.
omNStrategy :: Eq f => NStrategy f
omNStrategy trs t = let ns = stdNStrategy trs t
                     in [n | n@(p, _, _) <- ns,
                             all (\p' -> not (above p' p))
                                 [p' | (p', _, _) <- ns, p' /= p]]

--- The leftmost outermost narrowing strategy.
loNStrategy :: Eq f => NStrategy f
loNStrategy trs t =
  let ns = stdNStrategy trs t
   in [n | n@(p, _, _) <- ns,
           all (\p' -> not (above p' p || leftOf p' p))
               [p' | (p', _, _) <- ns, p' /= p]]

--- The lazy narrowing strategy.
lazyNStrategy :: Eq f => NStrategy f
lazyNStrategy trs t = let lps = lazyPositions trs t
                       in filter (\(p, _, _) -> elem p lps) (stdNStrategy trs t)

--- Returns a list of all lazy positions in a term according to the given term
--- rewriting system.
lazyPositions :: Eq f => TRS f -> Term f -> [Pos]
lazyPositions _   (TermVar _)       = []
lazyPositions trs t@(TermCons _ ts)
  | isRedex trs t = if null rs then lps else eps:lps
  | otherwise     = [i:p | (i, t') <- zip [1..] ts, p <- lazyPositions trs t']
  where
    ftrs = filter (eqConsPattern t . fst) trs
    rs = [r | r@(l, _) <- ftrs, unifiable [(t, l)]]
    dps = [i | (i, _) <- zip [1..] ts, any (isDemandedAt i) ftrs]
    lps = [i:p | i <- dps, p <- lazyPositions trs (ts !! (i - 1))]

--- The weakly needed narrowing strategy.
wnNStrategy :: Eq f => NStrategy f
wnNStrategy trs t =
  let dts = defTrees trs
      v = fromMaybe 0 (minVarInTRS trs)
   in case loDefTrees dts t of
        Nothing        -> []
        Just (_, [])   -> []
        Just (p, dt:_) -> [(p .> q, r, sub) |
                           (q, r, sub) <- wnNStrategy' dts v (t |> p) dt]

--- Returns the narrowing steps for the weakly needed narrowing strategy
--- according to the given definitional tree and the given next possible
--- variable.
wnNStrategy' :: Eq f => [DefTree f] -> VarIdx -> Term f -> DefTree f
             -> [(Pos, Rule f, Subst f)]
wnNStrategy' _   v t (Leaf r) =
  let rule@(l, _) = renameRuleVars v (normalizeRule r)
   in [(eps, rule, sub) | Right sub <- [unify [(t, l)]]]
wnNStrategy' dts v t (Branch pat p dts') =
  case selectDefTrees dts (t |> p) of
    []   -> concatMap (wnNStrategy' dts v t) (filterDTS dts')
    dt:_ -> case unify [(t, renameTermVars v (normalizeTerm pat))] of
              Left _    -> []
              Right tau ->
                let tau' = restrictSubst tau (tVars t)
                    t' = applySubst tau' t
                    v' = max v (maybe 0 (+ 1) (maxVarInTerm t'))
                 in [(p .> p', rule, composeSubst sub tau') |
                     (p', rule, sub) <- wnNStrategy' dts v' (t' |> p) dt]
  where
    filterDTS = filter (\dt -> let dtp = renameTermVars v (dtPattern dt)
                                in unifiable [(t, dtp)])
wnNStrategy' dts v t (Or _ dts') = concatMap (wnNStrategy' dts v t) dts'

-- -----------------------------------------------------------------------------
-- Functions for narrowings on first-order terms
-- -----------------------------------------------------------------------------

--- Narrows a term with the given strategy and term rewriting system by the
--- given number of steps.
narrowBy :: NStrategy f -> TRS f -> Int -> Term f -> [(Subst f, Term f)]
narrowBy s trs n t | n <= 0    = []
                   | otherwise = let v = maybe 0 (+ 1) (maxVarInTerm t)
                                  in narrowBy' v emptySubst s trs n t

--- Narrows a term with the given strategy and list of term rewriting systems by
--- the given number of steps.
narrowByL :: NStrategy f -> [TRS f] -> Int -> Term f -> [(Subst f, Term f)]
narrowByL s trss = narrowBy s (concat trss)

--- Narrows a term with the given strategy, the given term rewriting system, the
--- already existing substitution and the given next possible variable by the
--- given number of steps.
narrowBy' :: VarIdx -> Subst f -> NStrategy f -> TRS f -> Int -> Term f
          -> [(Subst f, Term f)]
narrowBy' v sub s trs n t
  | n <= 0    = [(sub, t)]
  | otherwise = case s (renameTRSVars v (normalizeTRS trs)) t of
                  []       -> [(sub, t)]
                  ns@(_:_) -> concatMap combine ns
  where
    combine (p, (_, r), sub') =
      let t' = applySubst sub' (replaceTerm t p r)
          rsub' = restrictSubst sub' (tVars t)
          v' = case mapMaybe maxVarInTerm (elems rsub') of
                 []       -> v
                 vs@(_:_) -> maximum vs + 1
       in narrowBy' v' (composeSubst rsub' sub) s trs (n - 1) t'

--- Returns a list of narrowings for a term with the given strategy, the given
--- term rewriting system and the given number of steps.
narrowingBy :: NStrategy f -> TRS f -> Int -> Term f -> [Narrowing f]
narrowingBy s trs n t | n <= 0    = []
                      | otherwise = let v = maybe 0 (+ 1) (maxVarInTerm t)
                                     in narrowingBy' v emptySubst s trs n t

--- Returns a list of narrowings for a term with the given strategy, the given
--- list of term rewriting systems and the given number of steps.
narrowingByL :: NStrategy f -> [TRS f] -> Int -> Term f -> [Narrowing f]
narrowingByL s trss = narrowingBy s (concat trss)

--- Returns a list of narrowings for a term with the given strategy, the given
--- term rewriting system, the already existing substitution, the given next
--- possible variable and the given number of steps.
narrowingBy' :: VarIdx -> Subst f -> NStrategy f -> TRS f -> Int -> Term f
             -> [Narrowing f]
narrowingBy' v sub s trs n t
  | n <= 0    = [NTerm t]
  | otherwise = case s (renameTRSVars v (normalizeTRS trs)) t of
                  []       -> [NTerm t]
                  ns@(_:_) -> concatMap combine ns
  where
    combine (p, (_, r), sub') =
      let t' = applySubst sub' (replaceTerm t p r)
          rsub' = restrictSubst sub' (tVars t)
          phi = composeSubst rsub' sub
          v' = case mapMaybe maxVarInTerm (elems rsub') of
                 []       -> v
                 vs@(_:_) -> maximum vs + 1
       in map (NStep t p phi) (narrowingBy' v' phi s trs (n - 1) t')

--- Returns a narrowing tree for a term with the given strategy, the given
--- term rewriting system and the given number of steps.
narrowingTreeBy :: NStrategy f -> TRS f -> Int -> Term f -> NarrowingTree f
narrowingTreeBy s trs n t
  | n <= 0    = NTree t []
  | otherwise = let v = maybe 0 (+ 1) (maxVarInTerm t)
                 in narrowingTreeBy' v emptySubst s trs n t

--- Returns a narrowing tree for a term with the given strategy, the given list
--- of term rewriting systems and the given number of steps.
narrowingTreeByL :: NStrategy f -> [TRS f] -> Int -> Term f -> NarrowingTree f
narrowingTreeByL s trss = narrowingTreeBy s (concat trss)

--- Returns a narrowing tree for a term with the given strategy, the given term
--- rewriting system, the already existing substitution, the given next possible
--- variable and the given number of steps.
narrowingTreeBy' :: VarIdx -> Subst f -> NStrategy f -> TRS f -> Int -> Term f
                 -> NarrowingTree f
narrowingTreeBy' v sub s trs n t | n <= 0    = NTree t []
                                 | otherwise = NTree t (map combine (s trs' t))
  where
    trs' = renameTRSVars v (normalizeTRS trs)

    combine (p, (_, r), sub') =
      let t' = applySubst sub' (replaceTerm t p r)
          rsub' = restrictSubst sub' (tVars t)
          phi = composeSubst rsub' sub
          v' = case mapMaybe maxVarInTerm (elems rsub') of
                 []       -> v
                 vs@(_:_) -> maximum vs + 1
       in (p, phi, narrowingTreeBy' v' phi s trs (n - 1) t')

--- Solves a term equation with the given strategy, the given term rewriting
--- system and the given options. The term has to be of the form
--- `TermCons c [l, r]` with `c` being a constructor like `=`. The term `l` and
--- the term `r` are the left-hand side and the right-hand side of the term
--- equation.
solveEq :: Eq f => NOptions f -> NStrategy f -> TRS f -> Term f -> [Subst f]
solveEq _    _ _   (TermVar _)       = []
solveEq opts s trs t@(TermCons _ ts) = case ts of
  [_, _] -> let vs = tVars t
                v = maybe 0 (+ 1) (maxVarInTerm t)
             in map (`restrictSubst` vs) (solveEq' opts v emptySubst s trs t)
  _      -> []

--- Solves a term equation with the given strategy, the given list of term
--- rewriting systems and the given options. The term has to be of the form
--- `TermCons c [l, r]` with `c` being a constructor like `=`. The term `l` and
--- the term `r` are the left-hand side and the right-hand side of the term
--- equation.
solveEqL :: Eq f => NOptions f -> NStrategy f -> [TRS f] -> Term f -> [Subst f]
solveEqL opts s trss = solveEq opts s (concat trss)

--- Solves a term equation with the given strategy, the given term rewriting
--- system, the already existing substitution, the given next possible variable
--- and the given options. The term has to be of the form `TermCons c [l, r]`
--- with `c` being a constructor like `=`. The term `l` and the term `r` are the
--- left-hand side and the right-hand side of the term equation.
solveEq' :: Eq f => NOptions f -> VarIdx -> Subst f -> NStrategy f -> TRS f
         -> Term f -> [Subst f]
solveEq' _    _ _   _ _   (TermVar _)       = []
solveEq' opts v sub s trs t@(TermCons _ ts) = case ts of
  [_, _] -> case unify [(l, r)] of
              Left (Clash t1 t2) | (isRedex trs t1) || (isRedex trs t2)
                                             -> concatMap solve (s trs' nt)
                                 | otherwise -> []
              Left (OccurCheck _ _) -> []
              Right sub'            -> [composeSubst sub' sub]
  _      -> []
 where
   trs' = renameTRSVars v (normalizeTRS trs)
   nt@(TermCons _ [l, r]) = if (normalize opts)
                              then reduce (rStrategy opts) trs t
                              else t

   solve (p, (_, r'), sub') =
     let t' = applySubst sub' (replaceTerm nt p r')
         rsub' = restrictSubst sub' (tVars nt)
         v' = case mapMaybe maxVarInTerm (elems rsub') of
                []       -> v
                vs@(_:_) -> maximum vs + 1
      in solveEq' opts v' (composeSubst rsub' sub) s trs t'

-- -----------------------------------------------------------------------------
-- Graphical representation of narrowing trees
-- -----------------------------------------------------------------------------

--- A node represented as a pair of an integer and a term and parameterized over
--- the kind of function symbols, e.g., strings.
type Node f = (Int, Term f)

--- An edge represented as a tuple of a start node, a substitution and an end
--- node and parameterized over the kind of function symbols, e.g., strings.
type Edge f = (Node f, Subst f, Node f)

--- A graph represented as a pair of nodes and edges and parameterized over the
--- kind of function symbols, e.g., strings.
type Graph f = ([Node f], [Edge f])

--- Transforms a narrowing tree into a graph representation.
toGraph :: NarrowingTree f -> Graph f
toGraph ng = fst (fst (runState (toGraph' ng) 0))
  where
    toGraph' (NTree t ngs) =
      newIdx `bindS`
        \i -> let n = (i, t)
               in mapS (edge n) ngs `bindS`
                    \gs -> let (ns, es) = unzip gs
                            in returnS ((n : concat ns, concat es), n)

    edge n1 (_, sub, ng') = toGraph' ng' `bindS`
                              \((ns, es), n2) -> returnS (ns, (n1, sub, n2):es)

    newIdx = getS `bindS` \i -> putS (i + 1) `bindS_` returnS i

--- Transforms a narrowing tree into a graphical representation by using the
--- *DOT graph description language*.
dotifyNarrowingTree :: (f -> String) -> NarrowingTree f -> String
dotifyNarrowingTree s ng = "digraph narrowing_tree {\n"
  ++ "  graph [margin=0.0];\n"
  ++ "  node [fontname=\"Menlo\",fontsize=10.0,shape=box];\n"
  ++ unlines (map showNode ns)
  ++ "  edge [fontname=\"Menlo\",fontsize=7.0];\n"
  ++ unlines (map showEdge es)
  ++ "}"
  where
    (ns, es) = toGraph ng

    showNode (n, t) =
      "  " ++ showVarIdx n ++ " [label=\"" ++ showTerm s t ++ "\"];"

    showEdge ((n1, t), sub, (n2, _)) =
      "  " ++ showVarIdx n1 ++ " -> " ++ showVarIdx n2 ++ " [label=\""
           ++ showSubst s (restrictSubst sub (tVars t)) ++ "\"];"

--- Writes the graphical representation of a narrowing tree with the
--- *DOT graph description language* to a file with the given filename.
writeNarrowingTree :: (f -> String) -> NarrowingTree f -> String -> IO ()
writeNarrowingTree s ng fn = writeFile fn (dotifyNarrowingTree s ng)