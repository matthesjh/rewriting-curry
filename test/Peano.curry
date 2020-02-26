--------------------------------------------------------------------------------
--- Library for representation of peano numbers.
---
--- @author Jan-Hendrik Matthes
--- @version February 2020
--- @category general
--------------------------------------------------------------------------------

{-# OPTIONS_FRONTEND -Wno-incomplete-patterns #-}

module Peano
  ( Peano (..)
  , addPeano, subPeano, multPeano, leqPeano, peanoToInt, intToPeano
  ) where

-- -----------------------------------------------------------------------------
-- Representation of peano numbers
-- -----------------------------------------------------------------------------

--- A peano number represented as either zero or the successor of another peano
--- number.
data Peano = Zero | Succ Peano

-- -----------------------------------------------------------------------------
-- Functions for peano numbers
-- -----------------------------------------------------------------------------

--- Adds two peano numbers.
addPeano :: Peano -> Peano -> Peano
addPeano Zero     y = y
addPeano (Succ x) y = Succ (addPeano x y)

--- Subtracts the second peano number from the first peano number.
subPeano :: Peano -> Peano -> Peano
subPeano x        Zero     = x
subPeano (Succ x) (Succ y) = subPeano x y

--- Multiplies two peano numbers.
multPeano :: Peano -> Peano -> Peano
multPeano Zero     _ = Zero
multPeano (Succ x) y = addPeano y (multPeano x y)

--- Checks whether the first peano number is less than or equal to the second
--- peano number.
leqPeano :: Peano -> Peano -> Bool
leqPeano Zero     _        = True
leqPeano (Succ _) Zero     = False
leqPeano (Succ x) (Succ y) = leqPeano x y

-- -----------------------------------------------------------------------------
-- Transformation of peano numbers
-- -----------------------------------------------------------------------------

--- Transforms a peano number into an integer.
peanoToInt :: Peano -> Int
peanoToInt Zero     = 0
peanoToInt (Succ p) = 1 + peanoToInt p

--- Transforms an integer into a peano number.
intToPeano :: Int -> Peano
intToPeano i | i == 0 = Zero
             | i > 0  = Succ (intToPeano (i - 1))