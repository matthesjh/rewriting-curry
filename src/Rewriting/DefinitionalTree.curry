------------------------------------------------------------------------------
--- Library for representation and computation of definitional trees and
--- representation of the reduction strategy phi.
---
--- @author Jan-Hendrik Matthes
--- @version August 2016
--- @category algorithm
------------------------------------------------------------------------------

module Rewriting.DefinitionalTree
  ( DefTree (..)
  , dtRoot, dtPattern, hasDefTree, selectDefTrees, fromDefTrees, idtPositions
  , defTrees, defTreesL, loDefTrees, phiRStrategy, dotifyDefTree, writeDefTree
  ) where

import Function (on, both)
import List
import Maybe (listToMaybe, catMaybes)
import Rewriting.Position (Pos, eps, positions, (.>), (|>), replaceTerm)
import Rewriting.Rules
import Rewriting.Strategy (RStrategy)
import Rewriting.Substitution (applySubst)
import Rewriting.Term
import Rewriting.Unification (unify, unifiable)
import State

-- ---------------------------------------------------------------------------
-- Representation of definitional trees
-- ---------------------------------------------------------------------------

--- Representation of a definitional tree, parameterized over the kind of
--- function symbols, e.g., strings.
---
--- @cons Leaf r           - The leaf with rule `r`.
--- @cons Branch pat p dts - The branch with pattern `pat`, inductive position
---                          `p` and definitional subtrees `dts`.
--- @cons Or pat dts       - The or node with pattern `pat` and definitional
---                          subtrees `dts`.
data DefTree f = Leaf (Rule f)
               | Branch (Term f) Pos [DefTree f]
               | Or (Term f) [DefTree f]

-- ---------------------------------------------------------------------------
-- Functions for definitional trees
-- ---------------------------------------------------------------------------

--- Returns the root symbol (variable or constructor) of a definitional tree.
dtRoot :: DefTree f -> Either VarIdx f
dtRoot (Leaf r)         = rRoot r
dtRoot (Branch pat _ _) = tRoot pat
dtRoot (Or pat _)       = tRoot pat

--- Returns the pattern of a definitional tree.
dtPattern :: DefTree f -> Term f
dtPattern (Leaf (l, _))    = l
dtPattern (Branch pat _ _) = pat
dtPattern (Or pat _)       = pat

--- Checks whether a term has a definitional tree with the same constructor
--- pattern in the given list of definitional trees.
hasDefTree :: Eq f => [DefTree f] -> Term f -> Bool
hasDefTree dts t = any ((eqConsPattern t) . dtPattern) dts

--- Returns a list of definitional trees with the same constructor pattern for
--- a term from the given list of definitional trees.
selectDefTrees :: Eq f => [DefTree f] -> Term f -> [DefTree f]
selectDefTrees dts t = filter ((eqConsPattern t) . dtPattern) dts

--- Returns the definitional tree with the given index from the given list of
--- definitional trees or the provided default definitional tree if the given
--- index is not in the given list of definitional trees.
fromDefTrees :: DefTree f -> Int -> [DefTree f] -> DefTree f
fromDefTrees dt _ []                                         = dt
fromDefTrees dt n dts@(_:_) | (n >= 0) && (n < (length dts)) = dts !! n
                            | otherwise                      = dt

--- Returns a list of all inductive positions in a term rewriting system.
idtPositions :: TRS _ -> [Pos]
idtPositions []             = []
idtPositions trs@((l, _):_)
  = case l of
      (TermVar _)     -> []
      (TermCons _ ts) -> [[i] | i <- [1..(length ts)],
                                all (isDemandedAt i) trs]

--- Returns a list of definitional trees for a term rewriting system.
defTrees :: Eq f => TRS f -> [DefTree f]
defTrees = (concatMap defTreesS) . (groupBy eqCons) . (sortBy eqCons)
  where
    eqCons = on eqConsPattern fst

--- Returns a list of definitional trees for a list of term rewriting systems.
defTreesL :: Eq f => [TRS f] -> [DefTree f]
defTreesL = defTrees . concat

--- Returns a list of definitional trees for a term rewriting system, whose
--- rules have the same constructor pattern.
defTreesS :: Eq f => TRS f -> [DefTree f]
defTreesS []             = []
defTreesS trs@((l, _):_)
  = case l of
      (TermVar _)     -> []
      (TermCons c ts) ->
        let arity = length ts
            pat = TermCons c (map TermVar [0..(arity - 1)])
            pss = permutations (idtPositions trs)
         in catMaybes [defTreesS' arity trs ps pat | ps <- pss]

--- Returns a definitional tree for a term rewriting system, whose rules have
--- the same constructor pattern, with the given list of inductive positions,
--- the given pattern and the given next possible variable or `Nothing` if no
--- such definitional tree exists.
defTreesS' :: Eq f => VarIdx -> TRS f -> [Pos] -> Term f -> Maybe (DefTree f)
defTreesS' _ []          []     _   = Nothing
defTreesS' v [r]         []     pat = mkLeaf v pat r
defTreesS' v trs@(_:_:_) []     pat
  = mkOr v pat (partition (isDemandedAt 1) trs)
defTreesS' v trs         (p:ps) pat = Just (Branch pat p dts)
  where
    nls = nub [normalizeTerm (l |> p) | (l, _) <- trs]
    ts = map (renameTermVars v) nls
    pats = [replaceTerm pat p t | t <- ts]
    dts = catMaybes [defTreesS' v' (selectRules v' pat') ps pat' |
                     pat' <- pats,
                     let v' = max v (maybe 0 (+ 1) (maxVarInTerm pat'))]

    selectRules v' t = [r | r@(l, _) <- renameTRSVars v' trs,
                            unifiable [(l, t)]]

--- Returns a definitional tree for the given pattern, the given rule and the
--- given next possible variable or `Nothing` if no such definitional tree
--- exists.
mkLeaf :: Eq f => VarIdx -> Term f -> Rule f -> Maybe (DefTree f)
mkLeaf v pat r
  = case unify [(l, pat)] of
      (Left _)                      -> Nothing
      (Right sub)
        | pat == (applySubst sub l) -> Just (Leaf (both (applySubst sub) r'))
        | otherwise                 ->
          let (ip:ips) = [p | p <- positions pat, isVarTerm (pat |> p)]
              pat' = replaceTerm pat ip (l |> ip)
              v' = max v (maybe 0 (+ 1) (maxVarInTerm pat'))
           in Just (Branch pat ip (catMaybes [defTreesS' v' [r] ips pat']))
  where
    r'@(l, _) = renameRuleVars v (normalizeRule r)

--- Returns a definitional tree for the given pattern, the given pair of term
--- rewriting systems and the given next possible variable or `Nothing` if no
--- such definitional tree exists. Only the rules in the first term rewriting
--- system of the pair have a demanded first argument position.
mkOr :: Eq f => VarIdx -> Term f -> (TRS f, TRS f) -> Maybe (DefTree f)
mkOr _ _   ([], [])               = Nothing
mkOr v pat ([], rs2@(_:_))        = let mdts = map (mkLeaf v pat) rs2
                                     in Just (Or pat (catMaybes mdts))
mkOr v pat (rs1@(_:_), [])
  = defTreesS' v rs1 (intersect (idtPositions rs1) (varPositions pat)) pat
mkOr v pat (rs1@(_:_), rs2@(_:_))
  = let vps = varPositions pat
        mdts = [defTreesS' v rs (intersect (idtPositions rs) vps) pat |
                rs <- [rs1, rs2]]
     in Just (Or pat (catMaybes mdts))

--- Returns a list of all variable argument positions in a term.
varPositions :: Term _ -> [Pos]
varPositions (TermVar _)     = []
varPositions (TermCons _ ts) = [[i] | i <- [1..(length ts)],
                                      isVarTerm (ts !! (i - 1))]

-- ---------------------------------------------------------------------------
-- Functions for the reduction strategy phi
-- ---------------------------------------------------------------------------

--- Returns the position and the definitional trees from the given list of
--- definitional trees for the leftmost outermost defined constructor in a
--- term or `Nothing` if no such pair exists.
loDefTrees :: Eq f => [DefTree f] -> Term f -> Maybe (Pos, [DefTree f])
loDefTrees []        _ = Nothing
loDefTrees dts@(_:_) t = listToMaybe (loDefTrees' eps t)
  where
    loDefTrees' _ (TermVar _)       = []
    loDefTrees' p c@(TermCons _ ts)
      | hasDefTree dts c = [(p, selectDefTrees dts c)]
      | otherwise        = [lp | (p', t') <- zip [1..] ts,
                                 lp <- loDefTrees' (p .> [p']) t']

--- The reduction strategy phi. It uses the definitional tree with the given
--- index for all constructor terms if possible or at least the first one.
phiRStrategy :: Eq f => Int -> RStrategy f
phiRStrategy n trs t
  = let dts = defTrees trs
     in case loDefTrees dts t of
          Nothing                 -> []
          (Just (_, []))          -> []
          (Just (p, dts'@(dt:_))) ->
            case phiRStrategy' n dts (t |> p) (fromDefTrees dt n dts') of
              Nothing   -> []
              (Just p') -> [p .> p']

--- Returns the position for the reduction strategy phi where a term should be
--- reduced according to the given definitional tree or `Nothing` if no such
--- position exists. It uses the definitional tree with the given index for
--- all constructor terms if possible or at least the first one.
phiRStrategy' :: Eq f => Int -> [DefTree f] -> Term f -> DefTree f -> Maybe Pos
phiRStrategy' _ _   t                (Leaf (l, _))
  | unifiable [(l', t)]                                = Just eps
  | otherwise                                          = Nothing
  where
    l' = maybe l (\v -> renameTermVars (v + 1) l) (maxVarInTerm t)
phiRStrategy' _ _   (TermVar _)      (Branch _ _ _)    = Nothing
phiRStrategy' n dts t@(TermCons _ _) (Branch _ p dts')
  = case t |> p of
      (TermVar _)       -> Nothing
      tp@(TermCons _ _) ->
        case selectDefTrees dts tp of
          []       ->
            case find (\dt -> eqConsPattern tp ((dtPattern dt) |> p)) dts' of
              Nothing   -> Nothing
              (Just dt) -> phiRStrategy' n dts t dt
          x@(dt:_) -> case phiRStrategy' n dts tp (fromDefTrees dt n x) of
                        Nothing   -> Nothing
                        (Just p') -> Just (p .> p')
phiRStrategy' _ _   _                (Or _ _)          = Nothing

-- ---------------------------------------------------------------------------
-- Graphical representation of definitional trees
-- ---------------------------------------------------------------------------

--- A node represented as a tuple of an integer, a possible inductive position
--- and a term and parameterized over the kind of function symbols, e.g.,
--- strings.
type Node f = (Int, Maybe Pos, Term f)

--- An edge represented as a tuple of a boolean to distinguish between branch
--- (`False`) and rule (`True`) edges, a start node and an end node and
--- parameterized over the kind of function symbols, e.g., strings.
type Edge f = (Bool, Node f, Node f)

--- A graph represented as a tuple of nodes and edges and parameterized over
--- the kind of function symbols, e.g., strings.
type Graph f = ([Node f], [Edge f])

--- Transforms a definitional tree into a graph representation.
toGraph :: DefTree f -> Graph f
toGraph dt = fst (fst (runState (toGraph' dt) 0))
  where
    toGraph' :: DefTree f -> State Int (Graph f, Node f)
    toGraph' (Leaf (l, r))
      = newIdx `bindS`
          (\i -> let n = (i, Nothing, l)
                  in (mapS (ruleEdge n) [r]) `bindS` (addNode n))
    toGraph' (Branch pat p dts)
      = newIdx `bindS`
          (\i -> let n = (i, Just p, pat)
                  in (mapS (branchEdge n) dts) `bindS` (addNode n))
    toGraph' (Or pat dts)
      = newIdx `bindS`
          (\i -> let n = (i, Nothing, pat)
                  in (mapS (branchEdge n) dts) `bindS` (addNode n))
    addNode :: Node f -> [Graph f] -> State Int (Graph f, Node f)
    addNode n gs = let (ns, es) = unzip gs
                    in returnS ((n:(concat ns), concat es), n)
    branchEdge :: Node f -> DefTree f -> State Int (Graph f)
    branchEdge n1 dt'
      = (toGraph' dt') `bindS`
          (\((ns, es), n2) -> returnS (ns, (False, n1, n2):es))
    ruleEdge :: Node f -> Term f -> State Int (Graph f)
    ruleEdge n1 t = newIdx `bindS` (\i -> let n = (i, Nothing, t)
                                           in returnS ([n], [(True, n1, n)]))
    newIdx :: State Int Int
    newIdx = getS `bindS` (\i -> (putS (i + 1)) `bindS_` (returnS i))

--- Transforms a term into a string representation and surrounds the subterm
--- at the given position with the html `<u>` and `</u>` tags.
showTermWithPos :: (f -> String) -> (Maybe Pos, Term f) -> String
showTermWithPos s = showTP False
  where
    showTerm' _ (TermVar v)     = showVarIdx v
    showTerm' b (TermCons c ts)
      = case ts of
          []     -> s c
          [l, r] -> parensIf b ((showTerm' True l) ++ " " ++ (s c) ++ " "
                      ++ (showTerm' True r))
          _      -> (s c) ++ "("
                      ++ (intercalate "," (map (showTerm' False) ts)) ++ ")"

    showTP b (Nothing, t)                 = showTerm' b t
    showTP b (Just [], t)                 = "<u>" ++ (showTerm' b t) ++ "</u>"
    showTP _ (Just (_:_), TermVar v)      = showVarIdx v
    showTP b (Just (p:ps), TermCons c ts)
      = case [(mp, t) | (i, t) <- zip [1..] ts,
                        let mp = if i == p then (Just ps) else Nothing] of
          []     -> s c
          [l, r] -> parensIf b ((showTP True l) ++ " " ++ (s c) ++ " "
                      ++ (showTP True r))
          ts'    -> (s c) ++ "(" ++ (intercalate "," (map (showTP False) ts'))
                      ++ ")"

--- Transforms a definitional tree into a graphical representation by using
--- the *DOT graph description language*.
dotifyDefTree :: (f -> String) -> DefTree f -> String
dotifyDefTree s dt = "digraph DefinitionalTree {\n\t"
                       ++ "node [fontname=Helvetica,fontsize=10,shape=box];\n"
                       ++ (unlines (map showNode ns))
                       ++ "\tedge [arrowhead=none];\n"
                       ++ (unlines (map showEdge es)) ++ "}"
  where
    (ns, es) = toGraph dt

    showNode (n, p, t) = "\t" ++ (showVarIdx n) ++ " [label=<"
                           ++ (showTermWithPos s (p, t)) ++ ">];"

    showEdge (b, (n1, _, _), (n2, _, _))
      = let opts = if b then " [arrowhead=normal];" else ";"
         in "\t" ++ (showVarIdx n1) ++ " -> " ++ (showVarIdx n2) ++ opts

--- Writes the graphical representation of a definitional tree with the
--- *DOT graph description language* to a file with the given filename.
writeDefTree :: (f -> String) -> DefTree f -> String -> IO ()
writeDefTree s dt fn = writeFile fn (dotifyDefTree s dt)

-- ---------------------------------------------------------------------------
-- Definition of helper functions
-- ---------------------------------------------------------------------------

--- Encloses a string in parenthesis if the given condition is true.
parensIf :: Bool -> String -> String
parensIf b s = if b then "(" ++ s ++ ")" else s