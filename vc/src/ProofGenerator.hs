module ProofGenerator (tacticsOfStmt, tacticsOfStmt', finish) where

import Types (
  Expr (..),
  Stmt (..), nameOfNode,
 )

import PrimOps (yulPrimOps)
import Utils (
  capitalize,
 )

tacticsOfExpr :: Expr -> String
tacticsOfExpr (Call f _) = rwPrimop f
tacticsOfExpr (CrossContractCall {}) = "Expression splitter failed to split the expression. kekW"
tacticsOfExpr (Var {}) = "-- simp [Var']"
tacticsOfExpr (Lit {}) = "-- simp [Lit']"

tacticsOfCond :: String
tacticsOfCond = "simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]"

assignCall :: String -> String
assignCall name = unlines [
    "rw [cons]; simp only [LetCall', AssignCall']",
    "simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]",
    "-- EXPR \6",
    "try simp",
    "generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs",
    "intros h",
    "try intros h'",
    "refine' Exists.intro s (And.intro (" ++ name ++ "_abs_of_code hs) ?_)",
    "swap; clear hs",
    "try revert h'",
    "revert h"
  ]

abstraction :: String -> String
abstraction name = unlines [
  "-- abstraction offsetting",
  "rw [cons]",
  "generalize hxs : Block _ = xs",
  "abstract " ++ name ++ "_abs_of_code " ++ name ++ " with ss hs",
  "try rw [← hs₁, hok] at hs",
  "intros h",
  "try intros h'",
  "refine' Exists.intro ss (And.intro hs ?_)",
  "swap; clear hs",
  "try revert h'",
  "revert h",
  "subst xs"]

rwPrimop :: String -> String
rwPrimop primop = if primop == "delegatecall" then "-- delegate call" else "rw [EVM" ++ capitalize primop ++ "']"

finish :: String
finish = unlines [
    "-- finish offsetting",
    "subst hs₉",
    "intros hbody",
    "subst hbody",
    "subst hs₁",
    "rw [← hok]",
    "repeat {rw [lookup_insert' (by aesop)]}",
    "repeat {rw [lookup_insert_of_ne (by decide)]}",
    "try rw [lookup_initcall_1]",
    "try rw [lookup_initcall_2 ?_]",
    "try rw [lookup_initcall_3 ?_]",
    "try rw [lookup_initcall_4 ?_]",
    "try rw [lookup_initcall_5 ?_]",
    "all_goals try decide",
    "let_unfold s₂",
    "simp [multifill']",
    "try {rw [reviveJump_insert (by aesop)]}",
    "repeat {rw [lookup_insert' (by aesop)]}",
    "try simp",
    "rw [hok]",
    "intros h",
    "exact h"
  ]

tacticsOfStmt' :: Bool -> Stmt -> String
tacticsOfStmt' _ (Block body) = foldMap (\s -> tacticsOfStmt' True s ++ "\n") body
tacticsOfStmt' _ (LetInit _ (Call f _)) =
    if f `elem` yulPrimOps
    then unlines [
          "rw [cons]; simp only [LetPrimCall', AssignPrimCall']",
          "simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]",
          rwPrimop f,
          "try simp"]
    else assignCall f
tacticsOfStmt' _ (LetInit {}) = "rw [cons]; simp only [LetEq', Assign', Lit', Var']"
tacticsOfStmt' _ (Assignment _ (Call f _)) =
  if f `elem` yulPrimOps
  then unlines [
         "rw [cons]; simp only [LetPrimCall', AssignPrimCall']",
         "simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]",
         rwPrimop f,
         "try simp"]
  else assignCall f
tacticsOfStmt' _ (Assignment {}) = "rw [cons]; simp only [LetEq', Assign', Lit', Var']"
tacticsOfStmt' _ (Declaration {}) = "rw [cons, Let']"
tacticsOfStmt' _ (ExpressionStmt (Call f args)) =
  if f `elem` yulPrimOps
  then unlines [
    "rw [cons, ExprStmtPrimCall']; try simp only",
    "simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]",
    "-- EXPR \4",
    rwPrimop f,
    "try simp"]
  else let preamble = unlines [
             "rw [cons, ExprStmtCall']; try simp only",
             "simp [evalArgs, head', reverse', multifill', PrimCall', Lit', Var', execPrimCall, evalPrimCall]"]
           postamble = unlines [
             "try simp",
             "",
             "generalize hs : execCall _ _ _ _ = s; try rw [← hs₁, hok] at hs",
             "intros h",
             "try intros h'",
             "refine' Exists.intro s (And.intro (" ++ f ++ "_abs_of_code hs) ?_)",
             "swap; clear hs",
             "try revert h'",
             "revert h"] in
       preamble ++ foldMap (\e -> tacticsOfExpr e ++ "\n") args ++ postamble
tacticsOfStmt' _ (ExpressionStmt (CrossContractCall {})) = "Cross contract call not implemented yet."
tacticsOfStmt' _ (ExpressionStmt e) = tacticsOfExpr e
tacticsOfStmt' abs node@(Switch c legs dflt) =
  if abs
  then abstraction (nameOfNode node)
  else
    unlines [
    "unfold execSwitchCases",
    tacticsOfCond,
    tacticsOfExpr c,
    concatMap ((tacticsOfStmt' abs . Block) . snd) legs,
    "generalize hdefault : exec _ _ _ = sdef",
    "unfold execSwitchCases",
    "subst hdefault",
    tacticsOfStmt' abs (Block dflt)]
tacticsOfStmt' abs node@(For {}) =
  if abs
  then abstraction (nameOfNode node) else "TOP LEVEL FOR?!"
tacticsOfStmt' abs node@(If c body) =
  if not abs
  then unlines [tacticsOfCond, tacticsOfExpr c, tacticsOfStmt' True (Block body)]
  else abstraction (nameOfNode node)
tacticsOfStmt' _ Continue = "rw [cons, Continue']"
tacticsOfStmt' _ Break = "rw [cons, Break']"
tacticsOfStmt' _ Leave = "rw [cons, Leave']"
tacticsOfStmt' _ stmt = "-- " ++ show stmt

tacticsOfStmt :: Stmt -> String
tacticsOfStmt stmt =
  unlines . map ("  " ++ ) . lines $
  unlines [
    tacticsOfStmt' False stmt,
    "-- tacticsOfStmt offsetting",
    "try rw [nil]",
    "try simp [Bool.toUInt256, UInt256.size]",
    "intros h",
    "exact h"
  ]