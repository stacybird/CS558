-- Homework 1  Stacy Watts   swatts@pdx.edu
module Main where

-- This import is for getting command line arguments
import System.Environment(getArgs)

hi w = putStrLn ("Hello " ++ reverse(w) ++ "!\n")


{- support invocation from the command line           -}

main =
  do { args <- System.Environment.getArgs 
     ; case args of
        (x :xs) -> (hi x)
        [] -> error "No command line argument specifying input string"
     }

