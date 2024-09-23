{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Control.Monad (forM_, when, unless)
import Parser (calc, lexer)
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.Environment (getArgs)
import System.FilePath
    ( (<.>), (</>), takeBaseName, splitPath, dropExtension )
import qualified Data.HashSet as HashSet

import Types (
  FuncDef (..),
  Stmt (..),
  getContracts,
  mkDefs,
  Expr(..), Formattable (src), Segment (..), nameOfNode, Import, ContractName, FileName, Imports, Code
 )
import Data.List (isPrefixOf, foldl', intercalate)
import ProofGenerator
import PrimOps (yulPrimOps)
import Control.Monad.State (State, modify, get, runState)
import Preprocessor (preprocessFile, preprocessDefs)
import Utils (replaceMany, traverseDir, wordsWhen)
import Relude (ordNub)
import Data.List.Extra (replace)

readFuncDefs :: FilePath -> IO [FuncDef]
readFuncDefs = fmap (preprocessDefs . concatMap mkDefs . getContracts . reverse . calc . lexer . preprocessFile) . readFile

bodyOfNode :: Stmt -> [Stmt]
bodyOfNode (For pre c post body) = body ++ pre ++ [ExpressionStmt c] ++ post
bodyOfNode (If c body)           = body ++ [ExpressionStmt c]
bodyOfNode (Block body)          = body
bodyOfNode (Switch c legs dflt)  = ExpressionStmt c : concatMap snd legs ++ dflt
bodyOfNode _                     = []

superStructureOfAsts :: [FuncDef] -> [Segment]
superStructureOfAsts asts = snd $ foldl' produceSegment (HashSet.empty, []) asts
  where
    produceSegment (cache, segs) f@(FuncDef name contract _ _ body) =
      let abstractionsOfBody :: Bool -> (Import, Stmt) -> State (HashSet.HashSet String) [Segment]
          abstractionsOfBody isTopLevel ((name, _), body) = do
            blacklist <- get
            let abstractions = abstractionsOfBlock contract . bodyOfNode $ body
                primarySegment = Segment name (map fst abstractions) body $ if isTopLevel then (f, (contract, True)) else (f, (contract, False))
            subsegments <- concat <$> mapM (abstractionsOfBody False)
                                           (filter (not . alreadyExists blacklist . fst . fst) abstractions)
            let result = primarySegment : subsegments
            modify (flip (foldr (HashSet.insert . qualifiedName)) result)
            pure result
          (segs', cache') = runState (abstractionsOfBody True ((name, (contract, True)), Block body)) cache in
      (cache', segs ++ segs')

    alreadyExists :: HashSet.HashSet String -> String -> Bool
    alreadyExists blacklist name =
      case templateOfName name of
        TemplateFunction -> True
        _                -> name `HashSet.member` blacklist

    qualifiedName :: Segment -> String
    qualifiedName (Segment name _ _ (_, (contract, _))) = contract ++ "_" ++ name

    -- Do not analyse the body, we only want top--level abstractions at each state.
    -- TODO(later): Rewrite this in terms of general tree traversal.
    abstractionIdentifierOfNode :: ContractName -> Stmt -> [(Import, Stmt)]
    abstractionIdentifierOfNode contract node =
      case node of
        (Block block)                  -> abstractionsOfBlock' block
        (For pre c post body)          -> let preAbstrs  = abstractionsOfBlock' pre
                                              cAbstrs    = abstractionIdentifierOfNode' (ExpressionStmt c)
                                              postAbstrs = abstractionsOfBlock' post
                                              bodyAbstrs = abstractionsOfBlock' body
                                              thisNode   = ((nameOfNode node, (contract, False)), node) in
                                              thisNode : abstractedImports (concat [preAbstrs, cAbstrs, postAbstrs, bodyAbstrs])
        (If c body)                    -> let cAbstrs    = abstractionIdentifierOfNode' (ExpressionStmt c)
                                              bodyAbstrs = abstractionsOfBlock' body
                                              thisNode   = ((nameOfNode node, (contract, False)), node) in
                                              thisNode : abstractedImports (cAbstrs ++ bodyAbstrs)
        (ExpressionStmt (Call f args))
          | isPrimOp f                 -> []
          | otherwise                  -> let argsAbstrs = abstractionsOfBlock' (map ExpressionStmt args)
                                              thisNode   = ((f, (contract, True)), ExpressionStmt (Call f args)) in
                                              thisNode : abstractedImports argsAbstrs
        (Assignment _ rhs)             -> abstractedImports $ abstractionIdentifierOfNode' (ExpressionStmt rhs)
        (LetInit _ rhs)                -> abstractedImports $ abstractionIdentifierOfNode' (ExpressionStmt rhs)
        (Switch c legs dflt)           -> let cAbstrs     = abstractionIdentifierOfNode' (ExpressionStmt c)
                                              legsAbstrs  = concatMap (abstractionsOfBlock' . snd) legs
                                              dfltAbsrtrs = abstractionsOfBlock' dflt
                                              thisNode    = ((nameOfNode node, (contract, False)), node) in
                                              thisNode : abstractedImports (concat [cAbstrs, legsAbstrs, dfltAbsrtrs])
        _                              -> []
      where
        isPrimOp name = name `elem` yulPrimOps
        abstractionsOfBlock' = abstractionsOfBlock contract
        abstractionIdentifierOfNode' = abstractionIdentifierOfNode contract
        isControlFlow (name, _) = any (`isPrefixOf` name) ["for_", "if_", "switch_"]
        abstractedImports = filter (not . isControlFlow . fst)

    abstractionsOfBlock :: ContractName -> [Stmt] -> [(Import, Stmt)]
    abstractionsOfBlock = (=<<) . abstractionIdentifierOfNode

generatedDir :: String
generatedDir = "Generated"

generatedSubdirName :: String -> String
generatedSubdirName = (generatedDir </>)

commonSubdirName :: String
commonSubdirName = "Common"

templatesSubdirName :: String
templatesSubdirName = "Templates"

templateSuffixGen :: String
templateSuffixGen = "_gen"

templateSuffixUser :: String
templateSuffixUser = "_user"

templateSuffixGlue :: String
templateSuffixGlue = ""

leanExt :: String
leanExt = "lean"

subdir :: FilePath -> FilePath -> FilePath
subdir = (</>) . (".." </>) . generatedSubdirName

data Template = TemplateFor | TemplateFunction | TemplateStmt | TemplateSwitch

data TemplateType = TTGen | TTUser | TTGlue

templateOfName :: String -> Template
templateOfName name
  | "for_" `isPrefixOf` name = TemplateFor
  | "if_" `isPrefixOf` name = TemplateStmt
  | "switch_" `isPrefixOf` name = TemplateSwitch
  | otherwise = TemplateFunction

suffixOfTemplateType :: TemplateType -> String
suffixOfTemplateType TTGen = templateSuffixGen
suffixOfTemplateType TTUser = templateSuffixUser
suffixOfTemplateType TTGlue = templateSuffixGlue

pathOfTemplate :: TemplateType -> Template -> FilePath
pathOfTemplate ttype template =
  templatesSubdirName </>
    case template of
      TemplateFor      -> suffix "for"
      TemplateFunction -> suffix "function"
      TemplateStmt     -> suffix "stmt"
      TemplateSwitch   -> suffix "stmt"
  where suffix template = template ++ suffixOfTemplateType ttype

importPrefixOfContract :: String -> Import -> String
importPrefixOfContract topLevelContract (s, (contract, isTopLevel)) =
  leanImportOfFile $ generatedSubdirName topLevelContract </> contract </> if isTopLevel then s else commonSubdirName </> s
  -- "import " ++ generatedSubdirName topLevelContract ++ "." ++ contract ++ (if isTopLevel then "" else "." ++ commonSubdirName) ++ "." ++ s

opensOfImports :: ContractName -> Imports -> String
opensOfImports topLevelContract imports =
  commonNamespace ++ userFNamespaces
  where
        commonNamespace = if not (all (snd . snd) imports) then let (_, (x, _)) = head imports in x ++ ".Common " else ""
        userFNamespaces = let res = ordNub . map (\(_, (contract, _)) -> contract) . filter (\(_, (_, hasContract)) -> hasContract) $ imports in
                          if null res then "" else unwords (leanFormatOfFilePath (generatedSubdirName topLevelContract) : res)

internalImports :: ContractName -> ContractName -> FileName -> TemplateType -> String
internalImports topLevelContract contract file ttype =
  case ttype of
    TTGen -> ""
    TTUser -> unlines [importWithSuffix templateSuffixGen]
    TTGlue -> unlines [importWithSuffix templateSuffixGen, importWithSuffix templateSuffixUser]
    where importWithSuffix suffix =
            "\n" ++ importPrefixOfContract topLevelContract (file ++ suffix, (contract, True))

generateGuarded :: Bool -> String -> String
generateGuarded c str = if c then "" else str

fillInStatement :: ContractName -> ContractName -> FileName -> Imports -> Code -> String -> String -> String -> (String, String, String)
fillInStatement topLevelContract contract file imports code gen user glue =
  (
    replaceIn TTGen gen,
    replaceIn TTUser user,
    replaceIn TTGlue glue
  )
  where leanImports = unlines . map (importPrefixOfContract topLevelContract) . ordNub $ imports
        astCode     = src code
        tactics     = tacticsOfStmt code
        opens       = opensOfImports topLevelContract imports

        replaceIn ttype =
          replaceMany [
            ("\\<statement_name>", file),
            ("\\<contract>",       contract),
            ("\\<imports>",        leanImports ++ internalImports topLevelContract contract file ttype),
            ("\\<code>",           astCode),
            ("\\<tacs>",           tactics),
            ("\\<opens>",          opens)
          ]

fillInFor :: ContractName -> ContractName -> FileName -> Imports -> Code -> String -> String -> String -> (String, String, String)
fillInFor topLevelContract contract file imports stmt@(For _ c post body) gen user glue =
  (
    replaceIn TTGen gen,
    replaceIn TTUser user,
    replaceIn TTGlue glue
  )
  where leanImports = unlines . map (importPrefixOfContract topLevelContract) . ordNub $ imports
        astCode     = src (For [] c post body) -- The prefix of For has already been handled. Drop it.
        astCond     = src c
        astPost     = src (Block post)
        astBody     = src (Block body)
        tacsPost    = tacticsOfStmt (Block post)
        tacsBody    = tacticsOfStmt (Block body)
        tactics     = tacticsOfStmt stmt
        opens       = opensOfImports topLevelContract imports

        replaceIn ttype =
          replaceMany [
            ("\\<statement_name>", file),
            ("\\<contract>",       contract),
            ("\\<imports>",        leanImports ++ internalImports topLevelContract contract file ttype),
            ("\\<code>",           astCode),
            ("\\<code_cond>",      astCond),
            ("\\<code_post>",      astPost),
            ("\\<code_body>",      astBody),
            ("\\<tacs_post>",      tacsPost),
            ("\\<tacs_body>",      tacsBody),
            ("\\<tacs>",           tactics),
            ("\\<opens>",          opens)
          ]

fillInFor _ _ _ _ stmt _ _ _ = (
  "FillInFor called with stmt: " ++ show stmt,
  "FillInFor called with stmt: " ++ show stmt,
  "FillInFor called with stmt: " ++ show stmt
  )

fillInFunction :: ContractName -> FileName -> Imports -> FuncDef -> String -> String -> String -> (String, String, String)
fillInFunction topLevelContract file imports (FuncDef _ contract fargs ret body) gen user glue =
  (
    replaceIn TTGen gen,
    replaceIn TTUser user,
    replaceIn TTGlue glue
  )
  where leanImports  = unlines . map (importPrefixOfContract topLevelContract) . ordNub $ imports
        argsSepComma = intercalate ", " fargs
        argsSepSpace = unwords fargs
        modifiers    = " -> "
        return       = intercalate ", " ret
        returnSpace  = unwords ret
        fbody        = src (Block body)
        underscores  = generateGuarded (null (ret ++ fargs)) $ (intercalate " → " . map (const "_") $ ret ++ fargs) ++ " → "
        code         = unlines . map ("  " ++) . lines $ tacticsOfStmt' False (Block body) ++ finish
        namespace    = leanFormatOfFilePath $ generatedSubdirName topLevelContract </> contract
        funcArgs     = generateGuarded (null fargs) $ "(" ++ unwords fargs ++ " : Literal)"
        opens        = opensOfImports topLevelContract imports
        retVals      = generateGuarded (null ret) $ "(" ++ unwords ret ++ " : Identifier)"
        rValsAndArgs = generateGuarded (null (ret ++ fargs)) $ "{" ++ unwords ret ++ " " ++ argsSepSpace ++ "}"
        replaceIn ttype =
          replaceMany [
            ("\\<imports>",                       leanImports ++ internalImports topLevelContract contract file ttype),
            ("\\<statement_name>",                file),
            ("\\<args_sep_comma>",                argsSepComma),
            ("\\<args_sep_space>",                argsSepSpace),
            ("\\<return_modifiers>",              modifiers),
            ("\\<return_value>",                  return),
            ("\\<func_body>",                     fbody),
            ("\\<underscores_return_value_args>", underscores),
            ("\\<func_tactics>",                  code),
            ("\\<namespace>",                     namespace),
            ("\\<fargs>",                         funcArgs),
            ("\\<opens>",                         opens),
            ("\\<ret_vals>",                      retVals),
            ("\\<ret_vals_and_args>",             rValsAndArgs),
            ("\\<return_value_space>",            returnSpace)
          ]

writeSegment :: ContractName -> Segment -> IO ()
writeSegment topLevelContract (Segment name abstractions stmt (f, (contract, isTopLevel))) = do
  (gen, user, glue) <- template
  let (genFile, userFile, glueFile) = leanFiles
  writeFile genFile gen

  -- TODO(feature): Add the option to force override specific files.
  -- Do not overwrite the user file, as we risk overwriting user-defined proofs.
  userFileExists <- doesFileExist userFile
  unless userFileExists $ writeFile userFile user

  -- Do not overwrite the glue file, it does not change as the lemmas therein can be deduced
  -- purely from the superstructure of proofs.
  glueFileExists <- doesFileExist glueFile
  unless glueFileExists $ writeFile glueFile glue
  where
    leanFiles = (leanFileOfAbstr TTGen, leanFileOfAbstr TTUser, leanFileOfAbstr TTGlue)
      where tlContract               = subdir topLevelContract contract
            controlFlowOrAbstraction = if isTopLevel then "" else commonSubdirName
            fileName ttype           = name ++ suffixOfTemplateType ttype
            leanFileOfAbstr ttype    = tlContract </> controlFlowOrAbstraction </> fileName ttype <.> leanExt
    fileName = contract ++ if isTopLevel then "" else "." ++ commonSubdirName
    readTemplates template = do
      genFile <- readFile (pathOfTemplate TTGen template)
      userFile <- readFile (pathOfTemplate TTUser template)
      glueFile <- readFile (pathOfTemplate TTGlue template)
      pure (genFile, userFile, glueFile)
    template = case templateOfName name of
                 TemplateStmt     -> do (genFile, userFile, glueFile) <- readTemplates TemplateStmt
                                        pure $ fillInStatement topLevelContract fileName name abstractions stmt genFile userFile glueFile
                 TemplateFor      -> do (genFile, userFile, glueFile) <- readTemplates TemplateFor
                                        pure $ fillInFor topLevelContract fileName name abstractions stmt genFile userFile glueFile
                 TemplateFunction -> do (genFile, userFile, glueFile) <- readTemplates TemplateFunction
                                        pure $ fillInFunction topLevelContract name abstractions f genFile userFile glueFile
                 TemplateSwitch   -> do (genFile, userFile, glueFile) <- readTemplates TemplateStmt
                                        pure $ fillInStatement topLevelContract fileName name abstractions stmt (switchOfStmt genFile) (switchOfStmt userFile) (switchOfStmt glueFile)
    switchOfStmt = unlines . map (replace "If _ _" "Switch _ _ _" . replace "rw [If']" "rw [Switch']") . lines

writeSegments :: ContractName -> [Segment] -> IO ()
writeSegments topLevelContract segments = do
  createDirectoryIfMissing False $ ".." </> generatedSubdirName topLevelContract
  forM_ segments $ \seg@(Segment _ _ _ (_, (contract, isTopLevel))) -> do
    when isTopLevel $ createDirectoryIfMissing True $ subdir topLevelContract contract </> commonSubdirName
    writeSegment topLevelContract seg

-- | Run verification generator (given raw cmdline args).
vc :: [String] -> IO ()
vc [] = error "usage: vc <yul_file>"
vc (yulFile : _) = do
  asts <- readFuncDefs yulFile
  writeSegments topLevel $ superStructureOfAsts asts
  generatedFiles <- getAllImports
  writeFile "../All.lean" . unlines . map (leanImportOfFile . concat . tail . splitPath) $ generatedFiles
  where topLevel = takeBaseName yulFile

getAllImports :: IO [String]
getAllImports = traverseDir (\acc f -> pure (acc ++ [f])) [] $ ".." </> generatedDir

leanFormatOfFilePath :: FilePath -> String
leanFormatOfFilePath = intercalate "." . wordsWhen (`elem` ['/']) . dropExtension

leanImportOfFile :: FilePath -> String
leanImportOfFile = ("import " ++) . leanFormatOfFilePath

-- | Clear (and create, if necessary) the target directory for generated files.
clear :: IO ()
clear = createDirectoryIfMissing False $ ".." </> generatedDir

main :: IO ()
main = vc =<< getArgs <* clear
