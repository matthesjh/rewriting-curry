--------------------------------------------------------------------------------
--- Module for testing the rewriting libraries.
---
--- @author Jan-Hendrik Matthes
--- @version February 2020
--- @category general
--------------------------------------------------------------------------------

module RewritingTest where

import Data.FiniteMap             (eltsFM)

import Rewriting.CriticalPairs
import Rewriting.DefinitionalTree
import Rewriting.Files
import Rewriting.Narrowing
import Rewriting.Position
import Rewriting.Rules
import Rewriting.Strategy
import Rewriting.Substitution
import Rewriting.Term
import Rewriting.Unification

-- -----------------------------------------------------------------------------
-- Definition of common variable terms
-- -----------------------------------------------------------------------------

varU :: Term _
varU = TermVar 20

varW :: Term _
varW = TermVar 22

varX :: Term _
varX = TermVar 23

varY :: Term _
varY = TermVar 24

varZ :: Term _
varZ = TermVar 25

-- -----------------------------------------------------------------------------
-- Tests for unification on first-order terms
-- -----------------------------------------------------------------------------

-- F(A, G(x, F(z)), H(z))
unTerm1 :: Term String
unTerm1 = TermCons "F" [tConst "A",
                        TermCons "G" [varX, TermCons "F" [varZ]],
                        TermCons "H" [varZ]]

-- F(y, G(y, F(B)), H(y))
unTerm2 :: Term String
unTerm2 = TermCons "F" [varY,
                        TermCons "G" [varY, TermCons "F" [tConst "B"]],
                        TermCons "H" [varY]]

-- F(A, G(x, z), y)
unTerm3 :: Term String
unTerm3 = TermCons "F" [tConst "A", TermCons "G" [varX, varZ], varY]

-- F(u, G(y, F(x)), F(x))
unTerm4 :: Term String
unTerm4 = TermCons "F" [varU,
                        TermCons "G" [varY, TermCons "F" [varX]],
                        TermCons "F" [varX]]

-- F(G(x, x), F(G(y, y), G(z, z)))
unTerm5 :: Term String
unTerm5 = TermCons "F" [TermCons "G" [varX, varX],
                        TermCons "F" [TermCons "G" [varY, varY],
                                      TermCons "G" [varZ, varZ]]]

-- F(y, F(z, u))
unTerm6 :: Term String
unTerm6 = TermCons "F" [varY, TermCons "F" [varZ, varU]]

unTest :: Eq f => (f -> String) -> Term f -> Term f -> IO ()
unTest s l r =
  putStrLn (either (showUnificationError s) (showSubst s) (unify [(l, r)]))

-- Clash: B is not equal to A.
unTest1 :: IO ()
unTest1 = unTest id unTerm1 unTerm2

-- OccurCheck: y occurs in F(y).
unTest2 :: IO ()
unTest2 = unTest id unTerm3 unTerm4

-- {u -> G(G(G(x, x), G(x, x)), G(G(x, x), G(x, x))), y -> G(x, x),
--  z -> G(G(x, x), G(x, x))}
unTest3 :: IO ()
unTest3 = unTest id unTerm5 unTerm6

-- -----------------------------------------------------------------------------
-- Tests for computation of critical pairs
-- -----------------------------------------------------------------------------

-- 0 + y -> y
-- s(x) + y -> s(x + y)
-- x + 0 -> x
-- x + s(y) -> s(x + y)
peanoAddTRS :: TRS String
peanoAddTRS = [(tOp (tConst "0") "+" varY, varY),
               (tOp (TermCons "s" [varX]) "+" varY,
                TermCons "s" [tOp varX "+" varY]),
               (tOp varX "+" (tConst "0"), varX),
               (tOp varX "+" (TermCons "s" [varY]),
                TermCons "s" [tOp varX "+" varY])]

-- x * 1 -> x
-- x * ^-1(x) -> 1
-- (x * y) * z -> x * (y * z)
groupAxiomsTRS :: TRS String
groupAxiomsTRS = [(tOp varX "*" (tConst "1"), varX),
                  (tOp varX "*" (TermCons "^-1" [varX]), tConst "1"),
                  (tOp (tOp varX "*" varY) "*" varZ,
                   tOp varX "*" (tOp varY "*" varZ))]

cPairsTest :: Eq f => (f -> String) -> TRS f -> IO ()
cPairsTest s = putStr . showCPairs s . cPairs

-- {0, 0}
-- {s(x), s(0 + x)}
-- {s(x + 0), s(x)}
-- {s(x + s(y)), s(s(x) + y)}
-- {s(x), s(x + 0)}
-- {s(0 + x), s(x)}
-- {s(s(x) + y), s(x + s(y))}
peanoAddCPairsTest :: IO ()
peanoAddCPairsTest = cPairsTest id peanoAddTRS

-- {x * y, x * (y * 1)}
-- {1, x * (y * ^-1(x * y))}
-- {x * (y * 1), x * y}
-- {x * (y * ^-1(x * y)), 1}
-- {x * (1 * y), x * y}
-- {x * (^-1(x) * y), 1 * y}
-- {(w * x) * (y * z), (w * (x * y)) * z}
groupAxiomsCPairsTest :: IO ()
groupAxiomsCPairsTest = cPairsTest id groupAxiomsTRS

-- -----------------------------------------------------------------------------
-- Tests for reductions on first-order terms
-- -----------------------------------------------------------------------------

-- a -> b
-- b -> c(c(a))
-- f(x, b, y) -> d
reduceTRS :: TRS String
reduceTRS = [(tConst "a", tConst "b"),
             (tConst "b", TermCons "c" [TermCons "c" [tConst "a"]]),
             (TermCons "f" [varX, tConst "b", varY], tConst "d")]

-- f(a, a, d)
reduceTerm :: Term String
reduceTerm = TermCons "f" [tConst "a", tConst "a", tConst "d"]

reduceTest :: Eq f => (f -> String) -> RStrategy f -> TRS f -> Int -> Term f
           -> IO ()
reduceTest s rs trs n t = putStrLn (showReduction s (reductionBy rs trs n t))

-- f(a, a, d) -> f(c(c(c(c(b)))), a, d)
reduceLITest :: IO ()
reduceLITest = reduceTest id liRStrategy reduceTRS 5 reduceTerm

-- f(a, a, d) -> f(c(c(c(c(b)))), a, d)
reduceLOTest :: IO ()
reduceLOTest = reduceTest id loRStrategy reduceTRS 5 reduceTerm

-- f(a, a, d) -> f(a, c(c(c(c(b)))), d)
reduceRITest :: IO ()
reduceRITest = reduceTest id riRStrategy reduceTRS 5 reduceTerm

-- f(a, a, d) -> d
reduceROTest :: IO ()
reduceROTest = reduceTest id roRStrategy reduceTRS 5 reduceTerm

-- f(a, a, d) -> f(c(c(c(c(b)))), c(c(c(c(b)))), d)
reducePITest :: IO ()
reducePITest = reduceTest id piRStrategy reduceTRS 5 reduceTerm

-- f(a, a, d) -> d
reducePOTest :: IO ()
reducePOTest = reduceTest id poRStrategy reduceTRS 5 reduceTerm

-- -----------------------------------------------------------------------------
-- Tests for definitional trees and the reduction strategy phi
-- -----------------------------------------------------------------------------

defTreeTest :: Eq f => (f -> String) -> TRS f -> IO ()
defTreeTest s trs = case defTrees trs of
                      []        -> putStrLn "There is no definitional tree."
                      dts@(_:_) -> putStr (unlines (map (dotifyDefTree s) dts))

-- [] ++ [] -> []
-- [] ++ (x : y) -> x : y
-- (x : y) ++ [] -> x : y
-- (w : x) ++ (y : z) -> w : (x ++ (y : z))
concatTRS :: TRS String
concatTRS = [(tOp (tConst "[]") "++" (tConst "[]"), tConst "[]"),
             (tOp (tConst "[]") "++" (tOp varX ":" varY), tOp varX ":" varY),
             (tOp (tOp varX ":" varY) "++" (tConst "[]"), tOp varX ":" varY),
             (tOp (tOp varW ":" varX) "++" (tOp varY ":" varZ),
              tOp varW ":" (tOp varX "++" (tOp varY ":" varZ)))]

-- ((True : []) ++ []) ++ ((False : (True : [])) ++ ([] ++ (False : [])))
concatTerm :: Term String
concatTerm = tOp (tOp (tOp (tConst "True") ":" (tConst "[]")) "++"
                      (tConst "[]")) "++"
                 (tOp (tOp (tConst "False") ":"
                           (tOp (tConst "True") ":" (tConst "[]"))) "++"
                      (tOp (tConst "[]") "++"
                           (tOp (tConst "False") ":" (tConst "[]"))))

concatDefTreeTest :: IO ()
concatDefTreeTest = defTreeTest id concatTRS

-- ((True : []) ++ []) ++ ((False : (True : [])) ++ ([] ++ (False : [])))
--   -> True : (False : (True : (False : [])))
concatPhi1Test :: IO ()
concatPhi1Test = reduceTest id (phiRStrategy 0) concatTRS 7 concatTerm

-- ((True : []) ++ []) ++ ((False : (True : [])) ++ ([] ++ (False : [])))
--   -> True : (False : (True : (False : [])))
concatPhi2Test :: IO ()
concatPhi2Test = reduceTest id (phiRStrategy 1) concatTRS 7 concatTerm

-- 0 + 0 -> 0
-- 0 + s(y) -> s(y)
-- s(x) + 0 -> s(x)
-- s(x) + s(y) -> s(s(x + y))
peanoAddTRS2 :: TRS String
peanoAddTRS2 = [(tOp (tConst "0") "+" (tConst "0"), tConst "0"),
                (tOp (tConst "0") "+" (TermCons "s" [varY]),
                 TermCons "s" [varY]),
                (tOp (TermCons "s" [varX]) "+" (tConst "0"),
                 TermCons "s" [varX]),
                (tOp (TermCons "s" [varX]) "+" (TermCons "s" [varY]),
                 TermCons "s" [TermCons "s" [tOp varX "+" varY]])]

-- ((s(0) + s(0)) + s(0)) + (0 + s(0 + 0))
peanoAddTerm :: Term String
peanoAddTerm = let so = TermCons "s" [tConst "0"]
                in tOp (tOp (tOp so "+" so) "+" so) "+"
                       (tOp (tConst "0") "+" (TermCons "s" [tOp (tConst "0") "+"
                                                                (tConst "0")]))

peanoAddDefTreeTest :: IO ()
peanoAddDefTreeTest = defTreeTest id peanoAddTRS2

-- ((s(0) + s(0)) + s(0)) + (0 + s(0 + 0)) -> s(s(s(s(0))))
peanoAddPhi1Test :: IO ()
peanoAddPhi1Test = reduceTest id (phiRStrategy 0) peanoAddTRS2 8 peanoAddTerm

-- ((s(0) + s(0)) + s(0)) + (0 + s(0 + 0)) -> s(s(s(s(0))))
peanoAddPhi2Test :: IO ()
peanoAddPhi2Test = reduceTest id (phiRStrategy 1) peanoAddTRS2 8 peanoAddTerm

-- bcoin -> False
-- bcoin -> True
bcoinTRS :: TRS String
bcoinTRS = [(tConst "bcoin", tConst "False"), (tConst "bcoin", tConst "True")]

bcoinDefTreeTest :: IO ()
bcoinDefTreeTest = defTreeTest id bcoinTRS

-- False and y -> False
-- x and False -> False
-- True and True -> True
andTRS :: TRS String
andTRS = [(tOp (tConst "False") "and" varY, tConst "False"),
          (tOp varX "and" (tConst "False"), tConst "False"),
          (tOp (tConst "True") "and" (tConst "True"), tConst "True")]

andDefTreeTest :: IO ()
andDefTreeTest = defTreeTest id andTRS

-- x xor False -> x
-- False xor True -> True
-- True xor True -> False
xorTRS :: TRS String
xorTRS = [(tOp varX "xor" (tConst "False"), varX),
          (tOp (tConst "False") "xor" (tConst "True"), tConst "True"),
          (tOp (tConst "True") "xor" (tConst "True"), tConst "False")]

xorDefTreeTest :: IO ()
xorDefTreeTest = defTreeTest id xorTRS

-- True or x -> True
-- x or True -> True
-- False or False -> False
porTRS :: TRS String
porTRS = [(tOp (tConst "True") "or" varX, tConst "True"),
          (tOp varX "or" (tConst "True"), tConst "True"),
          (tOp (tConst "False") "or" (tConst "False"), tConst "False")]

porDefTreeTest :: IO ()
porDefTreeTest = defTreeTest id porTRS

-- f(True) -> True
-- f(True) -> False
-- f(False) -> True
overlapLitFunTRS :: TRS String
overlapLitFunTRS = [(TermCons "f" [tConst "True"], tConst "True"),
                    (TermCons "f" [tConst "True"], tConst "False"),
                    (TermCons "f" [tConst "False"], tConst "True")]

overlapLitFunDefTreeTest :: IO ()
overlapLitFunDefTreeTest = defTreeTest id overlapLitFunTRS

-- -----------------------------------------------------------------------------
-- Tests for narrowings on first-order terms
-- -----------------------------------------------------------------------------

narrowingGraphTest :: (f -> String) -> NStrategy f -> TRS f -> Int -> Term f
                   -> IO ()
narrowingGraphTest s ns trs n t =
  putStrLn (dotifyNarrowingTree s (narrowingTreeBy ns trs n t))

solveEqTest :: Eq f => (f -> String) -> Int -> NOptions f -> NStrategy f
            -> TRS f -> Term f -> IO ()
solveEqTest s n opts ns trs t =
  putStr (unlines (take n (map (showSubst s) (solveEq opts ns trs t))))

-- 0 + y -> y
-- s(x) + y -> s(x + y)
peanoAddTRS3 :: TRS String
peanoAddTRS3 = [(tOp (tConst "0") "+" varY, varY),
                (tOp (TermCons "s" [varX]) "+" varY,
                 TermCons "s" [tOp varX "+" varY])]

-- s(x) + y = s(s(s(0)))
peanoAddEq :: Term String
peanoAddEq = tOp (tOp (TermCons "s" [varX]) "+" varY) "="
                 (TermCons "s" [TermCons "s" [TermCons "s" [tConst "0"]]])

peanoAddNarrowingGraphTest :: IO ()
peanoAddNarrowingGraphTest =
  narrowingGraphTest id stdNStrategy peanoAddTRS3 4 peanoAddEq

-- {x -> 0, y -> s(s(0))}
-- {x -> s(0), y -> s(0)}
-- {x -> s(s(0)), y -> 0}
peanoAddSolveEqTest :: IO ()
peanoAddSolveEqTest =
  solveEqTest id 3 defaultNOptions stdNStrategy peanoAddTRS3 peanoAddEq

-- [] ++ y -> y
-- (w : x) ++ y -> w : (x ++ y)
-- length([]) -> 0
-- length(x : y) -> s(length(y))
concatLengthTRS :: TRS String
concatLengthTRS = [(tOp (tConst "[]") "++" varY, varY),
                   (tOp (tOp varW ":" varX) "++" varY,
                    tOp varW ":" (tOp varX "++" varY)),
                   (TermCons "length" [tConst "[]"], tConst "0"),
                   (TermCons "length" [tOp varX ":" varY],
                    TermCons "s" [TermCons "length" [varY]])]

-- length(x ++ y) = s(s(0))
concatLengthEq :: Term String
concatLengthEq = tOp (TermCons "length" [tOp varX "++" varY]) "="
                     (TermCons "s" [TermCons "s" [tConst "0"]])

concatLengthNarrowingGraphTest :: IO ()
concatLengthNarrowingGraphTest =
  narrowingGraphTest id stdNStrategy concatLengthTRS 4 concatLengthEq

-- {x -> [], y -> a : (b : [])}
-- {x -> a : [], y -> b : []}
-- {x -> a : (b : []), y -> []}
concatLengthSolveEqTest :: IO ()
concatLengthSolveEqTest =
  solveEqTest id 3 defaultNOptions stdNStrategy concatLengthTRS concatLengthEq

-- (x + y) + z = 0
peanoAddEq2 :: Term String
peanoAddEq2 = tOp (tOp (tOp varX "+" varY) "+" varZ) "=" (tConst "0")

-- {x -> 0, y -> 0, z -> 0}
peanoAddSolveEq2IMTest :: IO ()
peanoAddSolveEq2IMTest =
  solveEqTest id 1 defaultNOptions imNStrategy peanoAddTRS3 peanoAddEq2

-- {x -> 0, y -> 0, z -> 0}
peanoAddSolveEq2NIMTest :: IO ()
peanoAddSolveEq2NIMTest =
  let opts = defaultNOptions { normalize = True }
   in solveEqTest id 1 opts imNStrategy peanoAddTRS3 peanoAddEq2

peanoAdd2IMNarrowingGraphTest :: IO ()
peanoAdd2IMNarrowingGraphTest =
  narrowingGraphTest id imNStrategy peanoAddTRS3 4 peanoAddEq2

-- bcoin and x
andbcoinTerm :: Term String
andbcoinTerm = tOp (tConst "bcoin") "and" varX

andbcoinWNNarrowingGraphTest :: IO ()
andbcoinWNNarrowingGraphTest =
  narrowingGraphTest id wnNStrategy (bcoinTRS ++ andTRS) 4 andbcoinTerm

-- 0 + y -> y
-- s(x) + y -> s(x + y)
-- 0 * y -> 0
-- s(x) * y -> y + (x * y)
peanoAddMultTRS :: TRS String
peanoAddMultTRS = [(tOp (tConst "0") "+" varY, varY),
                   (tOp (TermCons "s" [varX]) "+" varY,
                    TermCons "s" [tOp varX "+" varY]),
                   (tOp (tConst "0") "*" varY, tConst "0"),
                   (tOp (TermCons "s" [varX]) "*" varY,
                    tOp varY "+" (tOp varX "*" varY))]

-- (x * y) * z = 0
peanoMultEq :: Term String
peanoMultEq = tOp (tOp (tOp varX "*" varY) "*" varZ) "=" (tConst "0")

-- {x -> 0, y -> a, z -> b}
-- {x -> s(0), y -> 0, z -> a}
-- {x -> s(0), y -> s(0), z -> 0}
peanoMultSolveEqIMTest :: IO ()
peanoMultSolveEqIMTest =
  solveEqTest id 3 defaultNOptions imNStrategy peanoAddMultTRS peanoMultEq

-- {x -> 0, y -> a}
-- {x -> s(0), y -> 0}
-- {x -> s(0), y -> s(0), z -> 0}
peanoMultSolveEqNIMTest :: IO ()
peanoMultSolveEqNIMTest =
  let opts = defaultNOptions { normalize = True }
   in solveEqTest id 3 opts imNStrategy peanoAddMultTRS peanoMultEq

peanoMultIMNarrowingGraphTest :: IO ()
peanoMultIMNarrowingGraphTest =
  narrowingGraphTest id imNStrategy peanoAddMultTRS 4 peanoMultEq

-- [] ++ y -> y
-- (w : x) ++ y -> w : (x ++ y)
-- take(Z, x) -> []
-- take(S(x), []) -> []
-- take(S(x), (y:z)) -> y : take(x, z)
peanoTakeTRS :: TRS String
peanoTakeTRS = [(tOp (tConst "[]") "++" varY, varY),
                (tOp (tOp varW ":" varX) "++" varY,
                 tOp varW ":" (tOp varX "++" varY)),
                (TermCons "take" [tConst "Z", varX], tConst "[]"),
                (TermCons "take" [TermCons "S" [varX], tConst "[]"],
                 tConst "[]"),
                (TermCons "take" [TermCons "S" [varX], tOp varY ":" varZ],
                 tOp varY ":" (TermCons "take" [varX, varZ]))]

-- take(w, x ++ (y ++ z)) = [1]
peanoTakeEq :: Term String
peanoTakeEq = tOp (TermCons "take" [varW, tOp varX "++" (tOp varY "++" varZ)])
                  "=" (tOp (tConst "1") ":" (tConst "[]"))

-- {w -> S(Z), x -> [], y -> [], z -> 1 : a}
-- {w -> S(S(a)), x -> [], y -> [], z -> 1 : []}
-- {w -> S(Z), x -> 1 : [], y -> [], z -> a}
-- {w -> S(S(a)), x -> 1 : [], y -> [], z -> []}
peanoTakeSolveEqIMTest :: IO ()
peanoTakeSolveEqIMTest =
  solveEqTest id 4 defaultNOptions imNStrategy peanoTakeTRS peanoTakeEq

peanoTakeIMNarrowingGraphTest :: IO ()
peanoTakeIMNarrowingGraphTest =
  narrowingGraphTest id imNStrategy peanoTakeTRS 4 peanoTakeEq

-- {w -> S(Z), x -> [], y -> [], z -> 1 : a}
-- {w -> S(S(a)), x -> [], y -> [], z -> 1 : []}
-- {w -> S(Z), x -> [], y -> 1 : a, z -> b}
-- {w -> S(S(a)), x -> [], y -> 1 : [], z -> []}
-- {w -> S(Z), x -> 1 : a}
-- {w -> S(S(a)), x -> 1 : [], y -> [], z -> []}
peanoTakeSolveEqWNTest :: IO ()
peanoTakeSolveEqWNTest =
  solveEqTest id 6 defaultNOptions wnNStrategy peanoTakeTRS peanoTakeEq

peanoTakeWNNarrowingGraphTest :: IO ()
peanoTakeWNNarrowingGraphTest =
  narrowingGraphTest id wnNStrategy peanoTakeTRS 4 peanoTakeEq

-- -----------------------------------------------------------------------------
-- Tests for reading and transforming Curry programs
-- -----------------------------------------------------------------------------

-- addPeano(Zero, a) -> a
-- addPeano(Succ(b), c) -> Succ(addPeano(b, c))
--
-- intToPeano(a)
--   -> _if_(a == 0, Zero, _if_(a > 0, Succ(intToPeano(a - 1)), failed))
-- _if_(True, a, b) -> a
-- _if_(False, a, b) -> b
--
-- leqPeano(Zero, a) -> True
-- leqPeano(Succ(b), Zero) -> False
-- leqPeano(Succ(c), Succ(d)) -> leqPeano(c, d)
--
-- multPeano(Zero, a) -> Zero
-- multPeano(Succ(b), c) -> addPeano(c, multPeano(b, c))
--
-- peanoToInt(Zero) -> 0
-- peanoToInt(Succ(a)) -> 1 + peanoToInt(a)
--
-- subPeano(a, Zero) -> a
-- subPeano(Succ(b), Succ(c)) -> subPeano(b, c)
readPeanoModuleTest :: IO ()
readPeanoModuleTest = do
  res <- readCurryProgram "Peano"
  case res of
    Left _        -> putStrLn "Error while parsing the Curry file."
    Right (fm, _) -> putStr (unlines (map (showTRS snd) (eltsFM fm)))