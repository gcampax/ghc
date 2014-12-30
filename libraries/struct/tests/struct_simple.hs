module Main where

import Control.Exception
import System.Mem

import Data.Struct

assertFail :: String -> IO ()
assertFail msg = throwIO $ AssertionFailed msg

assertEquals :: (Eq a, Show a) => a -> a -> IO ()
assertEquals expected actual =
  if expected == actual then return ()
  else assertFail $ "expected " ++ (show expected)
       ++ ", got " ++ (show actual)

main = do
  let val = ("hello", 1, 42, 42, Just 42) :: (String, Int, Int, Integer, Maybe Int)
  maybeStr <- structNew 4096 val
  case maybeStr of
    Nothing -> assertFail "failed to create the struct"
    Just str -> do
      -- check that val is still good
      assertEquals ("hello", 1, 42, 42, Just 42) val
      -- check the value in the struct
      assertEquals ("hello", 1, 42, 42, Just 42) (structGetRoot str)
      performMajorGC
      -- check again val
      assertEquals ("hello", 1, 42, 42, Just 42) val
      -- check again the value in the struct
      assertEquals ("hello", 1, 42, 42, Just 42) (structGetRoot str)

