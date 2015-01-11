-- Homework 1  Stacy Watts   swatts@pdx.edu
module Hw1b where 

-- This is a comment that runs from the "--" to the end of the line
{- This is also a comment which begins with "{-" and ends with "-}" -}

-- These imports are for defining parsers
import Text.Parsec hiding (State,Column)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import Text.Parsec.Prim(getInput)
import Text.Parsec.Token hiding (natural)
import Data.Functor.Identity(Identity(..))
import Data.Char(digitToInt,isUpper)
import qualified Control.Exception

import Data.List

-- This import is for getting command line arguments
import System.Environment(getArgs)

--------------------------------------------------------------------------
-- This file implements an interpretor for a simple expresion language
-- It has several parts
--  1) Abstract Syntax for Expressions, Instructions, and Programs
--  2) A small implementation of an abstract datatype for stacks
--  3) Some auxillary functions for printing these things
--  4) A parser that reads a file and produces a program in abstract syntax
--  5) A translator for expressions into stack machine programs
--  6) An interpretor for stack machines
--  7) A top level that coordinates and ties together all these parts

------------------------------------------------------------------
-- Abstract Syntax for Expressions, Instructions, and Programs
-- Constructors like "Int" "Add" "Plus" etc.  must start with a capital letters!
-- To add a new operator, you need to add a line like 
--  "| Add (Exp,Exp)"

data Exp                   -- Exp has 5 constructors
  = Int Int
  | Add (Exp,Exp)
  | Sub (Exp,Exp )
  | Mul (Exp,Exp)
  | Div (Exp,Exp) 

data Instr                 -- Instr has 7 constructors
     = Const Int | Plus | Times | Negate | Divrem | Pop | Swap

type Prog = [Instr]

---------------------------------------------------------------
-- A small implementation of an abstract datatype for stacks

data Stack a = St [a]

empty = St []
is_empty (St x) = null x
push (St xs,x) = St(x:xs)
pop (St (x:xs)) = (x,St xs)
pop (St []) = error "pop of empty stack"

----------------------------------------------------------
-- Some auxillary functions for printing these things

{- Turn an Exp into a string -}
exp_to_string (exp) =  
    case exp of
      -- Note all cases must begin in the same column
      -- To write a long line over multiple line indent extra lines more deeply.      Int i) =  show i
      Add(e1,e2) -> "(+ " ++ (exp_to_string e1) ++ " " ++ (exp_to_string e2) ++ ")"
      Sub(e1,e2) ->  "(- " ++ (exp_to_string e1) ++ " " ++ (exp_to_string e2) ++ ")"
      Mul(e1,e2) ->  "{- " ++ (exp_to_string e1) ++ " " ++ (exp_to_string e2) ++ ")"
      Div(e1,e2) ->  "(/ " ++ (exp_to_string e1) ++ " " ++ (exp_to_string e2) ++ ")"
      Int n -> show n

{- Turn a Stack into a string, given a function that turns stack elements into strings -}

to_string f (St xs) = show(map f xs)

{- Turn an instruction into a String -}
instr_to_string instr =
    case instr of
      Const i ->  "Const " ++ (show i) 
      Plus ->   "Plus"
      Times ->  "Times"
      Negate -> "Negate"
      Divrem -> "Divrem"
      Pop ->    "Pop"
      Swap ->   "Swap"

{- Turn a program into a String -}
prog_to_string instrs =
    case instrs of
     [] ->  ""
     (instr:instrs) ->  (instr_to_string instr) ++ "\n" ++ (prog_to_string instrs) 

instance Show Exp where
  show = exp_to_string
instance Show Instr where
  show = instr_to_string

------------------------------------------------------------
-- An interpretor for stack machines

{- Execute a single stack machine instruction -}
step:: Stack Int ->  Instr -> Stack Int
step stk instr = 
    case  instr of
      Const v ->  push (stk,v) 
      Plus ->  
         let (v2,stk1) = pop stk
             (v1,stk2) = pop stk1
         in  push(stk2,v1 + v2)
      Times ->  
         let (v2,stk1) = pop stk
             (v1,stk2) = pop stk1
         in push(stk2,v1 * v2)
      Negate ->  
         let (v,stk1) = pop stk
         in push(stk1,negate v)
      Divrem ->  
         let (v2,stk1) = pop stk 
             (v1,stk2) = pop stk1 
             d = v1 `div` v2
             r = v1 `mod` v2 
         in push (push (stk2, d),r)
      Pop ->  
         let (_,stk1) = pop stk
         in stk1
      Swap ->  
         let (v2,stk1) = pop stk 
             (v1,stk2) = pop stk1
         in push (push(stk2,v2),v1)


{- Execute a sequence of stack machine instructions. -}      
exec :: Prog ->  IO Int
exec instrs =
    let steps stk instrs =
          case instrs of
            [] ->  let (result,_) = pop stk
                   in return (result)
            (instr:instrs) ->  
                do { let stk' = step stk instr
                   ; putStrLn ("*" ++ (instr_to_string instr) ++ " : " ++ 
                              (to_string show stk') ++ "\n")
                   ; steps stk' instrs }
   in steps empty instrs

-----------------------------------------------------------
-- A translator for expressions into stack machine programs

compile (Int i) = [Const i]
compile (Add(e1,e2)) =  (compile e1) ++ (compile e2) ++ [Plus]
compile (Sub(e1,e2)) =  (compile e1) ++ (compile e2) ++ [Negate,Plus]
compile (Mul(e1,e2)) =  (compile e1) ++ (compile e2) ++ [Times]
compile (Div(e1,e2)) =  (compile e1) ++ (compile e2) ++ [Divrem,Pop]

--------------------------------------------------------------------------
-- A parser that reads a file and produces a program in abstract syntax
-- Most of this section is boilerplate
-- The interesting functions are "operatorP" and "expP"

 
-- This function parses a string, but returns a function with type: (Exp,Exp) -> Exp
-- note that this is the type of the operation constructors of Exp
-- There are 4 cases, one for each of the legal operators: "+",  "-",  "*",  or "/".
-- To add a new operation you need to do two things. 1) define it in the
-- "where" clause (e.g. like: "plus   = do { symbol xxx "+"; return Add}" )
-- and then add it to the definition (e.g. like   "<|> divide"  ). 

operatorP = plus <|> times <|> minus <|> divide
  where plus   = do { symbol xxx "+"; return Add}
        times  = do { symbol xxx "*"; return Mul}
        minus  = do { symbol xxx "-"; return Sub}
        divide = do { symbol xxx "/"; return Div}

-- An expression is either a constant or a Lisp like parenthesized operation
expP = constant <|> operation
  where constant = 
           do { n <- lexemE(number 10 digit)
              ; return (Int n)}
        operation = 
           (do { symbol xxx "("
               ; constructorFun <- operatorP; 
               ; x <- expP
               ; y <- expP
               ; symbol xxx ")"
               ; return(constructorFun (x,y))})

-- Boilerplate below here        
       
type MParser a = ParsecT
                    String                -- The input is a sequence of Char
                    ()                    -- The internal state
                    Identity              -- The underlying monad
                    a                     -- the type of the object being parsed
      
xxxStyle = LanguageDef
                { commentStart   = "{-"
                , commentEnd     = "-}"
                , commentLine    = ""
                , nestedComments = True
                , identStart     = lower
                , identLetter    = alphaNum <|> char '_' 
                , opStart        = oneOf "+*-/"
                , opLetter       = oneOf "+*-/"
                , caseSensitive  = True
                , reservedOpNames = []
                , reservedNames  = []
                }                    

xxx = makeTokenParser xxxStyle
lexemE p    = lexeme xxx p
natural     = lexeme xxx (number 10 digit)
parenS p    = between (symbol xxx "(") (symbol xxx ")") p

number ::  Int -> MParser Char -> MParser Int
number base baseDigit
    = do{ digits <- many1 baseDigit
        ; let n = foldl (\x d -> base*x + (digitToInt d)) 0 digits
        ; seq n (return n)
        }

-- Running parsers

runMParser parser name tokens =
  runIdentity (runParserT parser () name tokens) 

parse1 file x s = runMParser (whiteSpace xxx >> x) file s 

parseWithName file x s =
  case parse1 file x s of
   Right(ans) -> ans
   Left message -> error (show message)
   
parse2 x s = parseWithName "keyboard input" x s  

parseString x s =
  case parse1 s x s of
   Right(ans) -> return ans
   Left message -> fail (show message)   

parseFile parser file =
    do possible <- Control.Exception.try (readFile file)
                   -- System.IO.Error.tryIOError (readFile file)
       case possible of
         Right contents -> 
            case parse1 file parser contents of
              Right ans -> return ans
              Left message -> error(show message)
         Left err -> error(show (err::IOError))
         


-------------------------------------------------------------------
-- A top level that coordinates and ties together all these parts

interp filename = 
  do { source <- parseFile expP filename
     ; putStrLn ("Expression: " ++ exp_to_string source)
     ; let prog = compile source
     ; putStrLn ("Compiles to:\n" ++ prog_to_string prog)
     ; result <- exec prog
     ; putStrLn ("\nEvaluates to: " ++ show result)
     ; return ()
     }
     
main =
  do { args <- System.Environment.getArgs 
     ; case args of
        (x :xs) -> interp x
        [] -> error "No command line argument specifying input file"
     }     
         
-----------------------------------------------

-- Some tests

test1 = parseFile expP "Hw1Test1.e1"
test2 = parse1 "input" expP "(+ {- a test -} 33 (* 5 2))"
test3 = interp  "Hw1Test1.e1"


 
