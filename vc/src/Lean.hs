module Lean (
  LeanName,
  Lemma (..),
  LemmaOption (..),
  Tactic (..),
  addTacs,
  isBasic,
  modifyLemmaType,
  setFirstRun,
  Implicity (..),
  explicitArityOfLemma,
) where

import Data.Char (toLower)
import Data.List (intercalate)

type LeanName = String

data Tactic
  = -- Atomic
    Repeat [Tactic]
  | AllGoals Tactic
  | Chain [Tactic]
  | Constructor
  | Exact String
  | Intros [String]
  | Rewrite [LeanName]
  | Rfl
  | Skip
  | Sorry
  | Swap
  | Tauto
  | Try Tactic
  | Unfold [LeanName]
  | First [Tactic]
  | RefactorMe String
  | OnProof [Tactic]
  | OnProofSorry [Tactic]
  | OnGeneration [Tactic]
  | WithSimpleConclusion Tactic
  | Zeta
  | -- Simplification
    YulDeclOrAssignSimp
  | YulDefaultInitSimp
  | YulDeclOrAssignSome
  | YulDeclOrAssignNone
  | YulEvalArgs
  | YulFoldHappy
  | AesopNormal
  | Assign
  | Next
  | Refuel
  | YulNormLiteral
  | YulNorm LeanName
  | YulResultPopToSimp
  | YulSeqSimp
  | YulStateSimp
  | Terminate
  | YulUnifyMetavars
  | -- Basic
    YulCall
  | YulIdentifier
  | YulLiteral
  | YulBlock
  | YulVariableDeclarationNone
  | YulVariableDeclarationSome
  | YulAssignment
  | YulIf
  | YulExpressionStmt
  | YulSwitch
  | YulFor
  | YulBreak
  | YulContinue
  | YulLeave
  | -- Misc
    DumpGoal String
  | DumpHyp LeanName String
  | LeanComment String
  | Invisible
  deriving (Eq)

isBasic :: Tactic -> Bool
isBasic YulCall = True
isBasic YulIdentifier = True
isBasic YulLiteral = True
isBasic YulBlock = True
isBasic YulVariableDeclarationNone = True
isBasic YulVariableDeclarationSome = True
isBasic YulAssignment = True
isBasic YulIf = True
isBasic YulExpressionStmt = True
isBasic YulSwitch = True
isBasic YulFor = True
isBasic YulBreak = True
isBasic YulContinue = True
isBasic YulLeave = True
isBasic _ = False

instance Show Tactic where
  -- Atomic
  show (Repeat tacs) = "repeat (" <> intercalate ", " (map show tacs) <> ")"
  show (AllGoals tac) = "all_goals (" <> show tac <> ")"
  show (Chain tacs) = intercalate "; " (map show tacs)
  show Constructor = "constructor"
  show (Exact term) = "exact " <> term
  show (Intros idents) = "intros " ++ unwords idents
  show (Rewrite lemmas) = "rewrite [" <> intercalate ", " lemmas <> "]"
  show Rfl = "rfl"
  show Skip = "skip"
  show Sorry = "sorry"
  show Swap = "swap"
  show Tauto = "tauto"
  show (Try tac) = "try ( " <> show tac <> " )"
  show (Unfold defs) = "unfold " <> unwords defs
  show (First tactics) = "first | " <> intercalate " | " (map show tactics)
  show (OnProof tactics) = "on_proof (" <> intercalate "; " (map show tactics) <> ")"
  show (OnProofSorry tactics) = "on_proof_sorry (" <> intercalate "; " (map show tactics) <> ")"
  show (OnGeneration tactics) = "on_generation (" <> intercalate "; " (map show tactics) <> ")"
  show (WithSimpleConclusion tac) = "with_simple_conclusion " ++ show tac
  show Zeta = "zeta"
  -- Simplification
  show YulDeclOrAssignSimp = "YUL_declOrAssign_simp"
  show YulDeclOrAssignSome = "YUL_declOrAssign_some"
  show YulDeclOrAssignNone = "YUL_declOrAssign_none"
  show YulDefaultInitSimp = "YUL_defaultInit_simp"
  show YulEvalArgs = "YUL_eval_args"
  show YulFoldHappy = "YUL_fold_happy"
  show AesopNormal = "aesop_normal"
  show Assign = "assign"
  show Next = "next"
  show Refuel = "refuel"
  show YulNormLiteral = "YUL_norm_literal"
  show (YulNorm f) = "YUL_norm_" ++ f
  show YulResultPopToSimp = "YUL_resultPopTo_simp"
  show YulSeqSimp = "YUL_seq_simp"
  show YulStateSimp = "YUL_state_simp"
  show Terminate = "terminate"
  show YulUnifyMetavars = "YUL_unify_metavars"
  -- Misc
  show (DumpGoal path) = "dump_goal \"" ++ path ++ "\""
  show (DumpHyp h path) = "dump_hyp " <> h <> " \"" <> path <> "\"" 
  -- Basic
  show YulCall = "YUL_functionCall"
  show YulIdentifier = "YUL_identifier"
  show YulLiteral = "YUL_literal"
  show YulBlock = show (Rewrite ["Block'"])
  show YulVariableDeclarationNone = "YUL_variableDeclaration_none"
  show YulVariableDeclarationSome = "YUL_variableDeclaration_some"
  show YulAssignment = "YUL_assignment"
  show YulIf = "YUL_if"
  show YulExpressionStmt = "YUL_expressionStmt"
  show YulSwitch = "YUL_switch"
  show YulFor = "YUL_for"
  show YulBreak = "YUL_break"
  show YulContinue = "YUL_continue"
  show YulLeave = "YUL_leave"
  show (LeanComment comment) = "\n  -- " ++ comment
  show (RefactorMe str) = str
  show Invisible = ""

data LemmaOption
  = DisplayRhsOfEq Bool
  | PpProofsWithType Bool
  | MaxRecDepth Integer
  | FirstRun Bool

instance Show LemmaOption where
  show (DisplayRhsOfEq opt) = "displayRhsOfEq " <> map toLower (show opt)
  show (PpProofsWithType opt) = "pp.proofs.withType " <> map toLower (show opt)
  show (MaxRecDepth depth) = "maxRecDepth " <> show depth
  show (FirstRun isFirstRun) = "firstRun " <> map toLower (show isFirstRun)

setOption :: LemmaOption -> String
setOption option = "set_option " <> show option <> " in"

replaceOptionFirstRun :: Bool -> [LemmaOption] -> [LemmaOption]
replaceOptionFirstRun newValue [] = [FirstRun newValue]
replaceOptionFirstRun newValue ((FirstRun _) : os) = FirstRun newValue : os
replaceOptionFirstRun newValue (o : os) = o : replaceOptionFirstRun newValue os

setFirstRun :: Bool -> Lemma -> Lemma
setFirstRun newFirstRun lem@(Lemma _ _ _ options _) = lem {lmOptions = replaceOptionFirstRun newFirstRun options}

data Implicity = Implicit | Explicit deriving (Eq)

data Lemma = Lemma
  { lmName :: LeanName
  , lmHyps :: [(LeanName, LeanName, Implicity)]
  , lmType :: LeanName
  , lmOptions :: [LemmaOption]
  , lmProof :: [Tactic]
  }

modifyLemmaType :: (LeanName -> LeanName) -> Lemma -> Lemma
modifyLemmaType f lemma@(Lemma _ _ prop _ _) = lemma {lmType = f prop}

addTacs :: Lemma -> [Tactic] -> Lemma
addTacs lemma@(Lemma _ _ _ _ proof) tacs = lemma {lmProof = proof ++ tacs}

arityOfLemma :: Lemma -> Int
arityOfLemma = length . lmHyps

explicitArityOfLemma :: Lemma -> Int
explicitArityOfLemma = length . filter (\(_, _, implicity) -> implicity == Explicit) . lmHyps

instance Show Lemma where
  show (Lemma lmName lmHyps lmType lmOptions lmProof) =
    unlines (map setOption lmOptions)
      <> "lemma "
      <> lmName
      <> " "
      <> unwords (map showHyp lmHyps)
      <> " : "
      <> lmType
      <> " := by\n  "
      <> intercalate "\n  " (map show lmProof)
    where
      showHypInner name "" = name
      showHypInner name ty = name <> " : " <> ty
      showHyp (name, ty, Implicit) = "{" <> showHypInner name ty <> "}"
      showHyp (name, ty, Explicit) = "(" <> showHypInner name ty <> ")"
