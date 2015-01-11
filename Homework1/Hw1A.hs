-- Homework 1  Stacy Watts   swatts@pdx.edu
module Main where

-- This is a comment that runs from the "--" to the end of the line
{- This is also a comment which begins with "{-" and ends with "-}" -}

-- This import is for getting command line arguments
import System.Environment(getArgs)

hi w = putStrLn ("Hello " ++ w ++ "!\n")


{- support invocation from the command line           -}

main =
  do { args <- System.Environment.getArgs 
     ; case args of
        (x :xs) -> (hi x)
        [] -> error "No command line argument specifying input string"
     }

{- To run this file one can use several mechanisms.

1) Start the interpretor from the command line using "ghci" and
   call the function "hi"

code> ghci Hw1a.hs
GHCi, version 7.4.1: http://www.haskell.org/ghc/  :? for help
Loading package ghc-prim ... linking ... done.
Loading package integer-gmp ... linking ... done.
Loading package base ... linking ... done.
Ok, modules loaded: Main.
Prelude Main> hi "Bill"
Hello Bill!

2) Use runhaskell on the command line, 
   the second argument is used as the input to "hi"

code> runhaskell Hw1a.hs Tommy
Hello Tommy!

3) Compile and run the executable
   The first command line argument given to the compiled program
   is used as the input to "hi"

On Linux

code> ghc --make Hw1a.hs
Linking Hw1a ...
code> ./Hw1a Mary
Hello Mary!

On Windows (we need the extension ".exe" and don't need the "./"
code>ghc --make Hw1A.hs
Linking Hw1A.exe ...
code>Hw1A.exe Jane
Hello Jane!

-}
    
