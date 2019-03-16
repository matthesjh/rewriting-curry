------------------------------------------------------------------------------
--- Library for representation of positions in first-order terms.
---
--- @author Jan-Hendrik Matthes
--- @version November 2016
--- @category algorithm
------------------------------------------------------------------------------

{-# OPTIONS_CYMAKE -Wno-incomplete-patterns #-}

module Rewriting.Position
  ( Pos
  , showPos, eps, above, below, leftOf, rightOf, disjoint
  , positions, (.>), (|>), replaceTerm
  ) where

import List (intercalate, isPrefixOf)
import Rewriting.Term (Term (..))

-- ---------------------------------------------------------------------------
-- Representation of positions in first-order terms
-- ---------------------------------------------------------------------------

--- A position in a term represented as a list of integers greater than zero.
type Pos = [Int]

-- ---------------------------------------------------------------------------
-- Pretty-printing of positions in first-order terms
-- ---------------------------------------------------------------------------

-- \x00b7 = MIDDLE DOT
-- \x03b5 = GREEK SMALL LETTER EPSILON

--- Transforms a position into a string representation.
showPos :: Pos -> String
showPos []       = "\x03b5"
showPos ps@(_:_) = intercalate "\x00b7" (map show ps)

-- ---------------------------------------------------------------------------
-- Functions for positions in first-order terms
-- ---------------------------------------------------------------------------

--- The root position of a term.
eps :: Pos
eps = []

--- Checks whether the first position is above the second position.
above :: Pos -> Pos -> Bool
above = isPrefixOf

--- Checks whether the first position is below the second position.
below :: Pos -> Pos -> Bool
below = flip above

--- Checks whether the first position is left from the second position.
leftOf :: Pos -> Pos -> Bool
leftOf []     _      = False
leftOf (_:_)  []     = False
leftOf (p:ps) (q:qs) = case compare p q of
                         LT -> True
                         EQ -> leftOf ps qs
                         GT -> False

--- Checks whether the first position is right from the second position.
rightOf :: Pos -> Pos -> Bool
rightOf = flip leftOf

--- Checks whether two positions are disjoint.
disjoint :: Pos -> Pos -> Bool
disjoint p q = not ((above p q) || (below p q))

--- Returns a list of all positions in a term.
positions :: Term _ -> [Pos]
positions (TermVar _)     = [eps]
positions (TermCons _ ts) = eps:[i:p | (i, t) <- zip [1..] ts,
                                       p <- positions t]

--- Concatenates two positions.
(.>) :: Pos -> Pos -> Pos
(.>) = (++)

-- ---------------------------------------------------------------------------
-- Functions for subterm selection and term replacement
-- ---------------------------------------------------------------------------

--- Returns the subterm of a term at the given position if the position exists
--- within the term.
(|>) :: Term f -> Pos -> Term f
t               |> []    = t
(TermCons _ ts) |> (i:p) = (ts !! (i - 1)) |> p

--- Replaces the subterm of a term at the given position with the given term
--- if the position exists within the term.
replaceTerm :: Term f -> Pos -> Term f -> Term f
replaceTerm _                 []    s = s
replaceTerm t@(TermVar _)     (_:_) _ = t
replaceTerm t@(TermCons c ts) (i:p) s
  | (i > 0) && (i <= (length ts))     = TermCons c ts'
  | otherwise                         = t
  where
    (ts1, ti:ts2) = splitAt (i - 1) ts
    ts' = ts1 ++ ((replaceTerm ti p s):ts2)