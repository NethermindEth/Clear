module Types (
  Formattable (..),
  Identifier,
  FuncName,
  ContractName,
  FuncNamePair,
  Literal (..),
  Expr (..),
  FuncDef (..),
  FuncDef' (..),
  Stmt (..),
  TopLvlStmt (..),
  InnerObject (..),
  Object (..),
  objStmts,
  funcDefOfStmt,
  getContracts,
  mkDef,
  mkDefs,
  uninitializedNames,
  SegName,
  Segment (..),
  funcDefDeps,
  stmtDeps,
  nameOfNode,
  FileName,
  Code,
  Import,
  Imports
) where

import Control.Arrow (second)
import Control.Monad.Trans.State
import Data.Foldable (foldrM)
import qualified Data.List as L

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as S

import PrimOps (yulPrimOps)
import Data.Hashable

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~ YUL AST ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

type FuncName = String
type Identifier = String
type ContractName = String
type FuncNamePair = (ContractName, FuncName)
type FileName     = String
type Import       = (String, (ContractName, Bool))
type Imports      = [Import]
type Code         = Stmt

data Literal
  = Number Integer
  | Str String
  deriving (Eq, Ord, Show)

instance (Hashable Literal) where
  hashWithSalt s (Number n) = hashWithSalt s n
  hashWithSalt s (Str str) = hashWithSalt s str

data Expr
  = Call FuncName [Expr]
  | CrossContractCall FuncName Identifier [Expr]
  | Var Identifier
  | Lit Literal
  deriving (Eq, Ord, Show)

instance (Hashable Expr) where
  hashWithSalt s (Call fName body) = s `hashWithSalt` fName `hashWithSalt` sum (map (hashWithSalt s) body) -- Are these qualified to just hash the name?
  hashWithSalt s (CrossContractCall fName ident body) = s `hashWithSalt` fName `hashWithSalt` ident `hashWithSalt` sum (map (hashWithSalt s) body)
  hashWithSalt s (Var ident) = hashWithSalt s ident
  hashWithSalt s (Lit lit) = hashWithSalt s lit

data FuncDef' = FuncDef' FuncName [Identifier] [Identifier] [Stmt]
  deriving (Eq, Show)

data FuncDef = FuncDef
  { fdName :: FuncName
  , fdContract :: Identifier
  , fdArgs :: [Identifier]
  , fdReturns :: [Identifier]
  , fdBody :: [Stmt]
  }
  deriving (Eq, Ord, Show)

data TopLvlStmt = UnusedBlock | FuncDefStmt FuncDef'
  deriving (Show)

data Stmt
  = Block [Stmt]
  | LetInit (NonEmpty Identifier) Expr
  | Assignment (NonEmpty Identifier) Expr
  | Declaration (NonEmpty Identifier)
  | ExpressionStmt Expr
  | Switch Expr [(Literal, [Stmt])] [Stmt]
  | For [Stmt] Expr [Stmt] [Stmt]
  | If Expr [Stmt]
  | Continue
  | Break
  | Leave
  | InlineComment String
  | MultilineComment String
  deriving (Eq, Ord, Show)

instance (Hashable Stmt) where
  hashWithSalt s (Block body) = sum (map (hashWithSalt s) body)
  hashWithSalt s (LetInit idn e) = s `hashWithSalt` idn `hashWithSalt` e
  hashWithSalt s (Assignment lhs e) = s `hashWithSalt` lhs `hashWithSalt` e
  hashWithSalt s (Declaration idn) = hashWithSalt s idn
  hashWithSalt s (ExpressionStmt e) = hashWithSalt s e
  hashWithSalt s (Switch what cases dflt) = s `hashWithSalt` what `hashWithSalt` cases `hashWithSalt` dflt
  hashWithSalt s (For pre init post body) = s `hashWithSalt` pre `hashWithSalt` init `hashWithSalt` post `hashWithSalt` body
  hashWithSalt s (If cnd body) = s `hashWithSalt` cnd `hashWithSalt` body
  hashWithSalt s Continue = hashWithSalt s "Continue"
  hashWithSalt s Break = hashWithSalt s "Break"
  hashWithSalt s Leave = hashWithSalt s "Leave"
  hashWithSalt s (InlineComment _) = s
  hashWithSalt s (MultilineComment _) = s

data InnerObject = InnerObject String String [TopLvlStmt]
  deriving (Show)

data Object = Object String String [TopLvlStmt] InnerObject
  deriving (Show)

objStmts :: Object -> (ContractName, [TopLvlStmt])
objStmts (Object _ objId _ (InnerObject _ _ ys)) = (takeWhile (/= '_') objId, ys)

funcDefOfStmt :: TopLvlStmt -> Maybe FuncDef'
funcDefOfStmt (FuncDefStmt f) = Just f
funcDefOfStmt _ = Nothing

getContracts :: [Object] -> [(ContractName, [FuncDef'])]
getContracts = map (second (mapMaybe funcDefOfStmt) . objStmts)

mkDef :: ContractName -> FuncDef' -> FuncDef
mkDef c (FuncDef' name args rets body) = FuncDef name c args rets body

mkDefs :: (ContractName, [FuncDef']) -> [FuncDef]
mkDefs (c, fs') = map (mkDef c) fs'

_funcDefNotation :: FuncDef -> String
_funcDefNotation fd = "<f " <> src fd <> ">"

nameOfNode :: Stmt -> String
nameOfNode node =
  case node of
    (For {})                    -> forPrefix ++ show nodeHash
    (ExpressionStmt (Call f _)) -> f -- Functions are already named; fortuitous!
    (If {})                     -> ifPrefix ++ show nodeHash
    (Switch {})                 -> switchPrefix ++ show nodeHash
    _                           -> "<<ERROR>> - No abstraction associated with: " ++ show node
  where ifPrefix  = "if_"
        forPrefix = "for_"
        switchPrefix = "switch_"
        nodeHash  = abs . hash $ node

----------------------------------------------------------------------------
-- searching for names not initialized in scope of the current statement  --
----------------------------------------------------------------------------

-- basic types and infrastructure

type DefinedNames = S.Set Identifier
type CollectM a = State DefinedNames a

-- including defined identifiers in the monad

addDefinedNames :: NonEmpty Identifier -> CollectM ()
addDefinedNames ids = modify (\defs -> foldr S.insert defs ids)

-- checking if an identifier is a defined name

isDefinedName :: Identifier -> CollectM Bool
isDefinedName n = gets (n `S.member`)

-- type class and instances for the algorithm of getting uninitialized names.

class CollectNames a where
  collect :: a -> CollectM (S.Set Identifier)

instance (CollectNames a) => CollectNames [a] where
  collect xs = S.unions <$> mapM collect xs

instance CollectNames Stmt where
  collect (Block stmts) = collect stmts
  collect (LetInit ids e) = do
    addDefinedNames ids
    collect e
  collect (Assignment ids e) = do
    idsE <- collect e
    let ins x ac = do
          b <- isDefinedName x
          pure $ if b then ac else S.insert x ac
    foldrM ins idsE ids
  collect (Declaration ids) = addDefinedNames ids >> pure S.empty
  collect (ExpressionStmt e) = collect e
  collect (Switch e binds deft) =
    S.unions <$> mapM collect (ExpressionStmt e : concatMap snd binds ++ deft)
  collect (For inits e stmts post) =
    S.unions <$> mapM collect (ExpressionStmt e : inits ++ stmts ++ post)
  collect (If e stmts) =
    S.unions <$> mapM collect (ExpressionStmt e : stmts)
  collect _ = pure S.empty

instance CollectNames Expr where
  collect (Call _ es) = collect es
  collect (CrossContractCall _ _ es) = collect es
  collect (Var n) = do
    b <- isDefinedName n
    pure $
      if b
        then S.empty
        else S.singleton n
  collect _ = pure S.empty

uninitializedNames :: Stmt -> S.Set Identifier
uninitializedNames s = evalState (collect s) S.empty

extensionallyModeledFunctions :: [FuncName]
extensionallyModeledFunctions = []

isPrimitive :: FuncName -> Bool
isPrimitive i = (i `elem` yulPrimOps) || (i `elem` extensionallyModeledFunctions)

exprDeps :: ContractName -> Expr -> Set FuncNamePair
exprDeps c (Call name args)
  | not (isPrimitive name) = S.insert (c, name) subDeps
  | otherwise = subDeps
  where
    subDeps = S.unions (map (exprDeps c) args)
exprDeps _ (CrossContractCall name c args) = S.insert (c, name) (S.unions $ map (exprDeps c) args)
exprDeps _ _ = S.empty

stmtDeps :: ContractName -> Stmt -> Set FuncNamePair
stmtDeps c (Block blk) = S.unions (map (stmtDeps c) blk)
stmtDeps c (If e body) = S.unions $ exprDeps c e : map (stmtDeps c) body
stmtDeps c (LetInit _ e) = exprDeps c e
stmtDeps c (Assignment _ e) = exprDeps c e
stmtDeps c (ExpressionStmt e) = exprDeps c e
stmtDeps c (Switch e cases def) = S.unions $ exprDeps c e : (map (stmtDeps c) . concat $ def : map snd cases)
stmtDeps c (For init cond body post) = S.unions $ exprDeps c cond : map (stmtDeps c) (init ++ body ++ post)
stmtDeps _ _ = S.empty

-- | Get names of all functions called within a block (non-recursively).
funcDefDeps :: FuncDef -> [FuncNamePair]
funcDefDeps (FuncDef _ c _ _ body) = S.toList . S.unions . map (stmtDeps c) $ body

data Segment = Segment
  { segName         :: String
  , segAbstractions :: Imports
  , segCode         :: Stmt
  , segContract     :: (FuncDef, (ContractName, Bool))
  } deriving Show

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~ PRETTY PRINTING ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- | Print the Yul source of something with indentation.
class Formattable a where
  src :: a -> String

-- | Indent each line of a string by 4 spaces.
tab :: String -> String
tab = L.intercalate "\n" . map ("    " ++) . lines

sep :: [Identifier] -> String
sep = L.intercalate ", "

fmtSep :: (Formattable a) => [a] -> String
fmtSep = sep . map src

decl :: FuncName -> [Identifier] -> String
decl name [] = "function " ++ name ++ "()"
decl name args = "function " ++ name ++ "(" ++ sep args ++ ")"

returns :: [Identifier] -> String
returns [] = ""
returns [ret] = "-> " ++ ret
returns rets = "-> " ++ sep rets

fmtCase :: (Literal, [Stmt]) -> String
fmtCase (x, stmts) = unwords ["case", src x, src (Block stmts)]

-- A handful of helpers, I am not sure how 'robust' we want to build this.
type SegName = String

instance Formattable Expr where
  src (CrossContractCall name c args) = c ++ "." ++ name ++ "(" ++ fmtSep args ++ ")"
  src (Call name args) = name ++ "(" ++ fmtSep args ++ ")"
  src (Var name) = name
  src (Lit x) = src x

instance Formattable Literal where
  src (Number n) = show n
  src (Str s) = s

instance Formattable FuncDef' where
  src (FuncDef' name args rets stmts) = unwords [decl name args, returns rets, "\n" ++ src (Block stmts)]

instance Formattable FuncDef where
  src (FuncDef name _ args rets stmts) = unwords [decl name args, returns rets, "\n" ++ src (Block stmts)]

instance Formattable Stmt where
  src (Block []) = "{ }"
  src (Block [a@(Assignment _ _)]) = "{" ++ src a ++ "}"
  src (Block [e@(ExpressionStmt _)]) = "{" ++ src e ++ "}"
  src (Block [Continue]) = "{" ++ src Continue ++ "}"
  src (Block [Break]) = "{" ++ src Break ++ "}"
  src (Block [Leave]) = "{" ++ src Leave ++ "}"
  src (Block stmts) = "{\n" ++ L.intercalate "\n" (map (tab . src) stmts) ++ "\n}"
  src (Declaration names) = "let " ++ sep (NE.toList names)
  src (LetInit names expr) = "let " ++ sep (NE.toList names) ++ " := " ++ src expr
  src (Assignment names expr) = sep (NE.toList names) ++ " := " ++ src expr
  src (If cond stmts) = unwords ["if", src cond, "\n" ++ src (Block stmts)]
  src (ExpressionStmt expr) = src expr
  src (Switch expr cases stmts) =
    "switch "
      ++ src expr
      ++ " "
      ++ unlines (map fmtCase cases)
      ++ "default\n"
      ++ src (Block stmts)
  src (For pre cond post body) = "for " ++ unwords (map src [Block pre, ExpressionStmt cond, Block post, Block body])
  src Continue = "continue"
  src Break = "break"
  src Leave = "leave"
  src (InlineComment _) = ""
  src (MultilineComment _) = ""
