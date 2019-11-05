--------------------------------------------------------------------------------
--- Library to read and transform a curry program into an equivalent
--- representation, where every function gets assigned the corresponding term
--- rewriting system and every type has a corresponding type declaration.
---
--- @author Jan-Hendrik Matthes
--- @version November 2019
--- @category algorithm
--------------------------------------------------------------------------------

module Rewriting.Files
  ( TRSData, TypeData, RWData
  , showQName, readQName, condQName, condTRS, readCurryProgram, fromCurryProg
  , fromFuncDecl, fromRule, fromLiteral, fromPattern, fromRhs, fromExpr
  ) where

import AbstractCurry.Files    (tryReadCurryFile)
import AbstractCurry.Types
import Data.FiniteMap         (FM, listToFM)

import Rewriting.Rules        (Rule, TRS, rCons)
import Rewriting.Substitution
import Rewriting.Term         (Term (..), tConst)

-- -----------------------------------------------------------------------------
-- Representation of term rewriting system data and type data
-- -----------------------------------------------------------------------------

--- Mappings from a function name to the corresponding term rewriting system
--- represented as a finite map from qualified names to term rewriting
--- systems.
type TRSData = FM QName (TRS QName)

--- Information about types represented as a list of type declarations.
type TypeData = [CTypeDecl]

--- Representation of term rewriting system data and type data as a pair.
type RWData = (TRSData, TypeData)

-- -----------------------------------------------------------------------------
-- Pretty-printing and reading of qualified names
-- -----------------------------------------------------------------------------

--- Transforms a qualified name into a string representation.
showQName :: QName -> String
showQName (mn, fn) | null mn   = fn
                   | otherwise = mn ++ "." ++ fn

--- Transforms a string into a qualified name.
readQName :: String -> QName
readQName s = case break (== '.') s of
                qn@(_, []) -> qn
                (mn, _:fn) -> (mn, fn)

-- -----------------------------------------------------------------------------
-- Functions for transforming (abstract) curry programs
-- -----------------------------------------------------------------------------

--- Returns the qualified name for an `if-then-else`-constructor.
condQName :: QName
condQName = pre "_if_"

--- Returns the term rewriting system for an `if-then-else`-function.
condTRS :: TRS QName
condTRS = let tTrue = tConst (pre "True")
              tFalse = tConst (pre "False")
           in [(TermCons condQName [tTrue, TermVar 0, TermVar 1], TermVar 0),
               (TermCons condQName [tFalse, TermVar 0, TermVar 1], TermVar 1)]

--- Tries to read and transform a curry program into an equivalent
--- representation, where every function gets assigned the corresponding term
--- rewriting system and every type has a corresponding type declaration.
readCurryProgram :: String -> IO (Either String RWData)
readCurryProgram fn = do res <- tryReadCurryFile fn
                         case res of
                           (Left e)   -> return (Left e)
                           (Right cp) -> return (Right (fromCurryProg cp))

--- Transforms an abstract curry program into an equivalent representation,
--- where every function gets assigned the corresponding term rewriting system
--- and every type has a corresponding type declaration.
fromCurryProg :: CurryProg -> RWData
fromCurryProg (CurryProg _ _ _ _ _ ts fs _)
  = (listToFM (<) (map fromFuncDecl fs), ts)

--- Transforms an abstract curry function declaration into a pair with
--- function name and corresponding term rewriting system.
fromFuncDecl :: CFuncDecl -> (QName, TRS QName)
fromFuncDecl (CFunc fn _ _ _ rs)
  = let (trs, trss) = unzip (map (fromRule fn) rs)
        cond = if elem condQName (concatMap rCons trs) then condTRS else []
     in (fn, trs ++ (concat trss) ++ cond)
fromFuncDecl (CmtFunc _ fn a v t rs) = fromFuncDecl (CFunc fn a v t rs)

--- Transforms an abstract curry rule for the function with the given name
--- into a pair of a rule and a term rewriting system.
fromRule :: QName -> CRule -> (Rule QName, TRS QName)
fromRule fn (CRule ps rhs)
  = let (ts, subs) = unzip (map (fromPattern fn) ps)
        (r, sub, trs) = fromRhs fn rhs
        sub' = foldr composeSubst emptySubst (sub:subs)
     in ((TermCons fn ts, applySubst sub' r), trs)

--- Transforms an abstract curry literal into a term.
fromLiteral :: CLiteral -> Term QName
fromLiteral (CIntc i)    = tConst ("%i", show i)
fromLiteral (CFloatc f)  = tConst ("%f", show f)
fromLiteral (CCharc c)   = tConst ("%c", [c])
fromLiteral (CStringc s) = tConst ("%s", s)

--- Transforms an abstract curry pattern for the function with the given name
--- into a pair of a term and a substitution.
fromPattern :: QName -> CPattern -> (Term QName, Subst QName)
fromPattern _  (CPVar (v, _))    = (TermVar v, emptySubst)
fromPattern _  (CPLit l)         = (fromLiteral l, emptySubst)
fromPattern fn (CPComb c ps)
  = let (ts, subs) = unzip (map (fromPattern fn) ps)
     in (TermCons c ts, foldr composeSubst emptySubst subs)
fromPattern fn (CPAs (v, _) p)   = let (t, sub) = fromPattern fn p
                                    in (t, extendSubst sub v t)
fromPattern fn (CPFuncComb c ps)
  = let (ts, subs) = unzip (map (fromPattern fn) ps)
     in (TermCons c ts, foldr composeSubst emptySubst subs)
fromPattern fn (CPLazy p)        = fromPattern fn p
fromPattern fn (CPRecord _ _)    = error (pError "fromPattern" "CPRecord" fn)

--- Transforms an abstract curry right-hand side of a rule for the function
--- with the given name into a tuple of a term, a substitution and a term
--- rewriting system.
fromRhs :: QName -> CRhs -> (Term QName, Subst QName, TRS QName)
fromRhs fn (CSimpleRhs e _)   = fromExpr fn e
fromRhs fn (CGuardedRhs gs _) = fromGuard fn gs

--- Transforms a list of abstract curry guarded expressions for the function
--- with the given name into a tuple of a term, a substitution and a term
--- rewriting system.
fromGuard :: QName -> [(CExpr, CExpr)] -> (Term QName, Subst QName, TRS QName)
fromGuard _  []          = (tConst (pre "failed"), emptySubst, [])
fromGuard fn ((c, e):gs)
  = let (ct, cs, ctrs) = fromExpr fn c
        (et, es, etrs) = fromExpr fn e
        (gt, gsub, gtrs) = fromGuard fn gs
        sub = composeSubst cs (composeSubst es gsub)
     in (TermCons condQName [ct, et, gt], sub, ctrs ++ etrs ++ gtrs)

--- Transforms an abstract curry expression for the function with the given
--- name into a tuple of a term, a substitution and a term rewriting system.
fromExpr :: QName -> CExpr -> (Term QName, Subst QName, TRS QName)
fromExpr _  (CVar (v, _))    = (TermVar v, emptySubst, [])
fromExpr _  (CLit l)         = (fromLiteral l, emptySubst, [])
fromExpr _  (CSymbol s)      = (tConst s, emptySubst, [])
fromExpr fn (CApply fe e)
  = let (ft, fs, ftrs) = fromExpr fn fe
        (et, es, etrs) = fromExpr fn e
        sub = composeSubst fs es
     in case ft of
          (TermVar _)     -> error "fromExpr: Argument is not a function!"
          (TermCons c ts) -> (TermCons c (ts ++ [et]), sub, ftrs ++ etrs)
fromExpr fn (CLambda _ _)    = error (pError "fromExpr" "CLambda" fn)
fromExpr fn (CLetDecl _ _)   = error (pError "fromExpr" "CLetDecl" fn)
fromExpr fn (CDoExpr _)      = error (pError "fromExpr" "CDoExpr" fn)
fromExpr fn (CListComp _ _)  = error (pError "fromExpr" "CListComp" fn)
fromExpr fn (CCase _ _ _)    = error (pError "fromExpr" "CCase" fn)
fromExpr fn (CTyped e _)     = fromExpr fn e
fromExpr fn (CRecConstr _ _) = error (pError "fromExpr" "CRecConstr" fn)
fromExpr fn (CRecUpdate _ _) = error (pError "fromExpr" "CRecUpdate" fn)

-- -----------------------------------------------------------------------------
-- Definition of helper functions
-- -----------------------------------------------------------------------------

--- Error message for the given function and the feature, that is not
--- supported within the given abstract curry function.
pError :: String -> String -> QName -> String
pError fn f acf
  = let fn' = if null fn then "" else fn ++ ": "
        f' = if null f then "Feature" else f
     in case showQName acf of
          []      -> fn' ++ f' ++ " currently not supported!"
          x@(_:_) -> fn' ++ f' ++ " in " ++ x ++ " currently not supported!"