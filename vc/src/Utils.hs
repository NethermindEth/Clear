module Utils (
  exec,
  rm,
  rmr,
  capitalize,
  injectSecond,
  splitAtLast,
  takeWhile',
  replaceFile,
  replaceMany,
  traverseDir,
  wordsWhen,
  strip
) where

import Control.Monad (join, foldM)
import Data.Char (toUpper, isSpace)
import System.Process (callCommand)
import Data.Foldable (foldl')
import System.Directory (listDirectory, doesDirectoryExist)
import System.FilePath ((</>))
import Control.Monad.Extra (partitionM)
import Data.List.Extra (replace)

-- | Print a shell command and then run it.
exec :: String -> IO ()
exec cmd = putStrLn cmd >> callCommand cmd

rm :: FilePath -> IO ()
rm path = exec $ "rm -f " ++ path

rmr :: FilePath -> IO ()
rmr path = exec $ "rm -rf " ++ path

replaceFile :: FilePath -> FilePath -> IO ()
replaceFile dst src = exec $ "mv " ++ src ++ " " ++ dst

injectSecond :: [a] -> a -> [a]
injectSecond [] x = [x]
injectSecond (y : ys) x = y : x : ys

splitAtLast :: [a] -> ([a], [a])
splitAtLast l = splitAt (length l - 1) l

takeWhile' :: (b -> Bool) -> [b] -> [b]
takeWhile' = ((map snd . takeWhile fst) .) . join . ((zip . (True :)) .) . map -- Ad eundum quo nemo ante iit

capitalize :: String -> String
capitalize [] = []
capitalize (hd : tl) = toUpper hd : tl

replaceMany :: [(String, String)] -> String -> String
replaceMany = flip $ foldl' ((flip . uncurry) replace)

traverseDir :: (b -> FilePath -> IO b) -> b -> FilePath -> IO b
traverseDir f = go
    where go state dir =
             do (dirPaths, filePaths) <- listDirectory dir >>= partitionM doesDirectoryExist . map (dir </>)
                state' <- foldM f state filePaths
                foldM go state' dirPaths

-- Based on 'Prelude.words'.
wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s =
  case dropWhile p s of
         "" -> []
         s' -> w : wordsWhen p s''
               where (w, s'') = break p s'

strip :: String -> String
strip = reverse . dropWhile isSpace . reverse . dropWhile isSpace

