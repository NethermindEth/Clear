{-# LANGUAGE TupleSections #-}

module Preprocessor (preprocess, preprocessFile, preprocessDefs) where

import Algebra.Graph.AdjacencyMap (stars)
import Algebra.Graph.AdjacencyMap.Algorithm (topSort)
import Control.Arrow (second)
import Data.List (intercalate, sortBy, foldl', findIndex, isPrefixOf, tails)
import qualified Data.List.NonEmpty as NE
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Relude.Extra.Foldable1 (foldMap1)
import qualified Data.List.Split as SP (splitOn, split, onSublist)
import Types (
  ContractName,
  Expr (..),
  FuncDef (..),
  FuncName,
  FuncNamePair,
  Literal (..),
  Stmt (..),
  funcDefDeps, Identifier,
 )
import Utils (replaceMany, strip)
import qualified Data.Bifunctor

-- | Transform e.g. `@src 18:5006:5080  "a.g(..."` -> `a.g.(...`.
--
-- i.e. Drop everything until the first `"`, and then unwrap the quoted a thing.
unquote :: String -> String
unquote = reverse . dropWhile (== '"') . reverse . dropWhile (== '"') . dropWhile (/= '"')

-- | Parse contract name and function name from delegatecall comment.
parseDelegateCallNames :: String -> (ContractName, FuncName)
parseDelegateCallNames comment =
  case SP.splitOn "." . takeWhile (/= '(') . unquote $ comment of
    [contract, fname] -> (contract, fname)
    _ -> error $ "Bad delegatecall comment: " ++ comment

-- | Substitute all delegate calls in a *reversed* block with normal calls.
subDelegateCalls :: [Stmt] -> [Stmt]
subDelegateCalls [] = []
subDelegateCalls
  ( LetInit vars (Call "delegatecall" _)
      : LetInit _ (Call _ args)
      : InlineComment comment
      : stmts
    ) = call' : subDelegateCalls stmts
    where
      (contract, fname) = parseDelegateCallNames comment
      call' = LetInit vars (CrossContractCall fname contract (drop 1 args))
subDelegateCalls (stmt : stmts) = stmt : subDelegateCalls stmts

subLinkerSymbol :: Stmt -> Stmt
subLinkerSymbol (LetInit name (Call "linkersymbol" _)) = LetInit name (Lit (Number 1))
subLinkerSymbol stmt = stmt

-- | Map a function over all blocks in a function definition, recursively.
transformDef :: ([Stmt] -> [Stmt]) -> FuncDef -> FuncDef
transformDef f (FuncDef name contract args rets body) = FuncDef name contract args rets (mapStmts f body)

-- | Map a function over all blocks contained in a statement, recursively.
transform :: ([Stmt] -> [Stmt]) -> Stmt -> Stmt
transform f (Block xs) = Block (mapStmts f xs)
transform f (Switch e cases stmts) = Switch e (map (second (mapStmts f)) cases) (mapStmts f stmts)
transform f (For init cond body post) = For (mapStmts f init) cond (mapStmts f body) (mapStmts f post)
transform f (If cond body) = If cond (mapStmts f body)
transform _ stmt = stmt

-- | Map a function over all blocks in a block, recursively.
mapStmts :: ([Stmt] -> [Stmt]) -> [Stmt] -> [Stmt]
mapStmts f = f . map (transform f)

linkStmts :: [Stmt] -> [Stmt]
linkStmts = reverse . subDelegateCalls . reverse . map subLinkerSymbol

lookup' :: (Show a, Ord a) => Map a b -> a -> b
lookup' m k = fromMaybe (error $ "Not found: " ++ show k) (M.lookup k m)

-- | Get names of all functions reachable from `fname` (recursively).
getAllCalled :: Map FuncNamePair FuncDef -> FuncNamePair -> [FuncNamePair]
getAllCalled funcMap = recurse . funcDefDeps . lookup' funcMap
  where
    recurse xs = xs ++ concatMap (getAllCalled funcMap) xs

mapDefs :: [FuncDef] -> Map FuncNamePair FuncDef
mapDefs = M.fromList . map (\f@(FuncDef fname c _ _ _) -> ((c, fname), f))

-- | Get all functions reachable from a list of entry points across all contracts.
reach :: [FuncDef] -> [FuncNamePair] -> [FuncNamePair]
reach fs = concatMap (getAllCalled (mapDefs fs))

-- | Is `f` reachable from the entrypoints?
isCalled :: [FuncNamePair] -> [FuncDef] -> FuncDef -> Bool
isCalled entrypoints defs f = namePair f `elem` (entrypoints ++ reach defs entrypoints)

-- | Filter-out functions in each contract not reachable from `entrypoints`.
filterDefs :: [FuncNamePair] -> [FuncDef] -> [FuncDef]
filterDefs entrypoints defs = filter (isCalled entrypoints defs) defs

-- | Given a map of contracts and the `:`-separated parts of an entry point
-- argument, return all (contractName, functionName) pairs specified by this
-- entry point argument.
getEntryPoint :: Map ContractName [FuncDef] -> [String] -> [FuncNamePair]
getEntryPoint _ [c, f] = [(c, f)]
getEntryPoint m [c] = map ((c,) . fdName) . lookup' m $ c
getEntryPoint _ parts = error $ "Malformed entrypoint: '" ++ intercalate ":" parts ++ "'"

contractOrdering :: FuncDef -> FuncDef -> Ordering
contractOrdering f g = compare (fdContract f) (fdContract g)

data Contract = Contract ContractName [FuncDef]

instance Semigroup Contract where
  (Contract c fs) <> (Contract d gs)
    | c == d = Contract c (fs ++ gs)
    | otherwise = error $ "Contract grouping failed: " ++ show c ++ ", " ++ show d

mkContract :: FuncDef -> Contract
mkContract f = Contract (fdName f) [f]

unContract :: Contract -> (ContractName, [FuncDef])
unContract (Contract name fs) = (name, fs)

mapContracts :: [FuncDef] -> Map ContractName [FuncDef]
mapContracts = M.fromList . agg' . groupBy' . sort'
  where
    agg' = map (unContract . foldMap1 mkContract)
    sort' = sortBy contractOrdering
    groupBy' = NE.groupBy (\f g -> fdContract f == fdContract g)

getEntryPoints :: [String] -> [FuncDef] -> [FuncNamePair]
getEntryPoints args fs = concatMap (getEntryPoint (mapContracts fs) . SP.splitOn ":") args

namePair :: FuncDef -> FuncNamePair
namePair (FuncDef name c _ _ _) = (c, name)

-- | A star is a center vertex and directed edges to each called function.
mkStar :: Map FuncNamePair FuncDef -> FuncDef -> (FuncDef, [FuncDef])
mkStar m f = (f, map (lookup' m) (getAllCalled m (namePair f)))

mkStars :: [FuncDef] -> [(FuncDef, [FuncDef])]
mkStars fs = map (mkStar (mapDefs fs)) fs

-- | Do a topological sort on functions in a contract (so we process dependencies first).
sortDefs :: [FuncDef] -> [FuncDef]
sortDefs = either (\fs -> error $ "Call cycle:" ++ show fs) reverse . topSort . stars . mkStars

-- | Replace linkersymbols with constants and delegate calls with normal calls.
link :: [FuncDef] -> [FuncDef]
link = map (transformDef (mapStmts linkStmts))

-- | Only filter if entrypoints are specified.
preprocess :: [String] -> [FuncDef] -> [FuncDef]
preprocess [] fs = sortDefs . link $ fs
preprocess args fs = sortDefs . filterDefs (getEntryPoints args fs) . link $ fs

-- TODO(very ugly, refactor -- also quite slow performance wise, oh well)
preprocessFile :: String -> String
preprocessFile = sansAssignedLiterals . sansInlineComment . sansComments . replaceMany [("Optimized IR:", "")]
  where sansComments = unlines . map (\line -> if "//" `isPrefixOf` strip line then "" else line) . lines

        commentBegin = "/**"
        commentEnd = "*/"
        sansInlineComment = fst . foldl' go ("", False)
                                . concatMap (SP.split (SP.onSublist commentEnd)) . SP.split (SP.onSublist commentBegin)
          where go (res, inComment) chunk =
                  (res ++ if inComment || chunk == commentEnd || chunk == commentBegin
                          then ""
                          else chunk, -- only append chunks that are not delimiters themselves or between them
                   (chunk /= commentEnd) && (chunk == commentBegin)) -- enter/exit the inComment state

        -- TODO(this is a hack inherited from the old version)
        sansAssignedLiterals = unlines . map (\line -> case findString ":= \"" line of
                                                         Nothing -> line
                                                         Just idx -> take idx line ++ ":= 0"
                                                       ) . lines
          where findString needle heystack = findIndex (isPrefixOf needle) (tails heystack)

-- TOOD(some of these are hacks, as per the initial design actually)
preprocessDefs :: [FuncDef] -> [FuncDef]
preprocessDefs = rejectExternals . map (delegateCallHack . expressionSplitterFix . (\fd ->
  fd {
    fdArgs    = map sanitiseVariableName (fdArgs fd),
    fdReturns = map sanitiseVariableName (fdReturns fd),
    fdBody    = map sanitiseVariableNames (fdBody fd)
  }))
  where leanKeywords = ["end"] -- TODO(Do this properly, there's a good chance some variables will collide.)

        sanitiseVariableName :: Identifier -> Identifier
        sanitiseVariableName var = if var `elem` leanKeywords then var ++ "_clear_sanitised_hrafn" else var

        sanitiseExpr :: Expr -> Expr
        sanitiseExpr (Var var) = Var (sanitiseVariableName var)
        sanitiseExpr (Call f args) = Call f (map sanitiseExpr args)
        sanitiseExpr expr      = expr

        sanitiseVariableNames :: Stmt -> Stmt
        sanitiseVariableNames (ExpressionStmt e)    = ExpressionStmt (sanitiseExpr e)
        sanitiseVariableNames (LetInit idents e)    = LetInit (NE.map sanitiseVariableName idents) (sanitiseExpr e)
        sanitiseVariableNames (Assignment idents e) = Assignment (NE.map sanitiseVariableName idents) (sanitiseExpr e)
        sanitiseVariableNames (Declaration idents)  = Declaration (NE.map sanitiseVariableName idents)
        sanitiseVariableNames (Switch c legs dflt)  = Switch (sanitiseExpr c)
                                                             (map (Data.Bifunctor.second (map sanitiseVariableNames)) legs)
                                                             (map sanitiseVariableNames dflt)
        sanitiseVariableNames (For pre c post body) = For (map sanitiseVariableNames pre)
                                                          (sanitiseExpr c)
                                                          (map sanitiseVariableNames post)
                                                          (map sanitiseVariableNames body)
        sanitiseVariableNames (If c body)           = If (sanitiseExpr c) (map sanitiseVariableNames body)
        sanitiseVariableNames stmt                  = stmt

        rejectExternals :: [FuncDef] -> [FuncDef]
        rejectExternals = filter rejectExternal
          where rejectExternal = not . isPrefixOf "external_" . fdName

        delegateCallHack :: FuncDef -> FuncDef
        delegateCallHack (FuncDef a b c d body) = FuncDef a b c d $ map go body
          where
            go :: Stmt -> Stmt
            go (LetInit idents (Call "linkersymbol" _)) = LetInit idents (Lit (Number 42))
            go s = s

        expressionSplitterFix :: FuncDef -> FuncDef
        expressionSplitterFix (FuncDef a b c d body) =
          FuncDef a b c d . foldl' (\acc stmt ->
              case splitPop stmt of
                Nothing -> acc ++ [stmt] -- your antipatterns can't stop me
                Just (pop, expr) -> acc ++ [LetInit (NE.fromList ["cheat"]) expr, pop]
            ) [] $ body
          where splitPop :: Stmt -> Maybe (Stmt, Expr)
                splitPop (ExpressionStmt (Call "pop" [arg])) =
                  Just (ExpressionStmt (Call "pop" [Var "cheat"]), arg)
                splitPop _ = Nothing
