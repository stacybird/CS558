-- Homework 2  your name  your email
module Main where


{- Interpreter for simple imperative language. -}

-- These imports are for defining parsers
import Text.Parsec hiding (State,Column)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import Text.Parsec.Prim(getInput)
import Text.Parsec.Pos(SourcePos)
import Text.Parsec.Token hiding (natural)
import Data.Functor.Identity(Identity(..))
import Data.Char(digitToInt,isUpper)
import qualified Control.Exception

-- These are used for tracing the stack machine
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO.Unsafe(unsafePerformIO)

-- This import is for getting command line arguments
import System.Environment(getArgs)

-- This import is for indenting pretty printing
import qualified Text.PrettyPrint.HughesPJ as PP

-------------------------------------------------------------------
{- Abstract Syntax for expressions. -}

type Vname = String

data Exp 
  = Var  Vname
  | Int  Int
  | Asgn  (Vname , Exp)
  | While  (Exp , Exp)
  | If  (Exp , Exp , Exp)
  | Write Exp
  | Block [Exp]
  | Add  (Exp , Exp)
  | Sub  (Exp , Exp)
  | Mul  (Exp , Exp)
  | Div  (Exp , Exp)
  | Leq  (Exp , Exp)

---------------------------------------------------------------
-- A small implementation of an abstract datatype for stacks

data Stack a = St [a]

empty = St []
is_empty (St x) = null x
push (St xs,x) = St(x:xs)
pop (St (x:xs)) = (x,St xs)
pop (St []) = error "pop of empty stack"

---------------------------------------------------------------
-- Operations on Environments 

type Env a = [(String,a)]
emptyE = []
extend env (k,v) = (k,v):env

lookUp:: Env a -> String -> Either String a
lookUp ((k0,v0):rest) k = if k==k0 then Right v0 else lookUp rest k
lookUp [] k = Left k

update:: Env a -> (String,a) -> Either String (Env a)
update ((k0,v0):rest) (k,v) = 
   if k == k0 then Right((k,v):rest)
              else do { pairs <- update rest (k,v)
                      ; return((k0,v0):pairs)}
update [] (k,v) = Left k   
 
---------------------------------------------------------------------
{- Stack Machine -}

type Var = String
type Label = Int
data Instr = Const Int | Plus | Times | Negate | Divrem | Lessequ 
           | Pop | Dup | Swap | Load Var | Store Var | Print
           | Label Label | Branch Label | Branchz Label
type Prog = [Instr]

exec:: [Instr] -> IO Int
exec instrs = steps emptyE empty instrs where
      find_label l = f instrs where  
          f [] = error ("Missing Label ")
          f (instrs@(Label l2 : rest)) 
            | l == l2 = instrs 
            | otherwise =  f rest 
          f (r : rest) = f rest
      step:: Env Int -> Stack Int -> Instr -> [Instr] -> IO (Env Int,Stack Int,[Instr])
      step env stk instr instrs =
        case instr of
         Const v -> return (env,push (stk,v),instrs)
         Plus ->
           let (v2,stk1) = pop stk 
               (v1,stk2) = pop stk1
           in return (env,push(stk2,v1 + v2),instrs)
         Times ->
           let (v2,stk1) = pop stk  
               (v1,stk2) = pop stk1  
           in return (env,push(stk2,v1 * v2),instrs)
         Negate ->
           let (v,stk1) = pop stk
           in return (env,push(stk1,- v),instrs) 
         Divrem ->
           let (v2,stk1) = pop stk 
               (v1,stk2) = pop stk1 
               d = v1 `div` v2 
               r = v1 `mod` v2 
           in return (env,push(push (stk2,d),r),instrs)
         Lessequ -> 
           let (v2,stk1) = pop stk 
               (v1,stk2) = pop stk1
           in return (env,push(stk2,if v1 <= v2 then 1 else 0),instrs)
         Pop ->
           let (_,stk1) = pop stk 
           in return (env,stk1,instrs)
         Dup -> 
           let (v,stk1) = pop stk 
           in return (env,push(push(stk1,v),v),instrs)
         Swap ->
           let (v1,stk1) = pop stk 
               (v2,stk2) = pop stk1 
           in return (env,push(push(stk2,v1),v2),instrs)           
         Load x -> 
           let (v,env2) = case (lookUp env x) of
                            Left x -> (0,extend env (x,0))
                            Right v -> (v,env) 
           in return (env2,push(stk,v),instrs)
         Store x -> 
           let (v,stk1) = pop stk 
               env2 = case update env (x,v) of
                       Left x -> extend env (x,v)
                       Right env3 -> env3
           in return (env2,stk1,instrs)
         Print ->
           let (v,stk1) = pop stk 
           in do { putStrLn (show v)
                 ; return (env,stk1,instrs) }
         Label l -> return (env,stk,instrs)
         Branch l -> return (env,stk,find_label l) 
         Branchz l -> 
           let (v,stk2) = pop stk 
           in if v == 0 
                 then {- take branch -}
                      return (env,stk2,find_label l)
                 else {- fall through -}
                      return (env,stk2,instrs) 
      steps:: Env Int -> Stack Int -> [Instr] -> IO Int
      steps env stk [] = return result
        where(result,_) = pop stk
      steps env stk (instr: instrs) = 
        do { bool <- readIORef trace_on
           ; if bool then putStrLn ("*" ++ (instr_to_string instr) ++ " with stack " ++ 
                                    (stack_to_string stk) ++ " with Env "++ showEnv env)
                     else return ()
           ; (env1,stk1,instrs2) <- step env stk instr instrs
           ; steps env1 stk1 instrs2 }
                        
 
{- Compilation -}  

compile:: IORef Label -> Exp -> IO Prog
compile next_label exp = do { initLabel; comp exp}      
  where initLabel = writeIORef next_label 0
        new_label = 
          do { label <- readIORef next_label
             ; writeIORef next_label (label+1)
             ; return label}
        comp (Var v) = return [Load v]
        comp ( Int i ) = return [Const i]
        comp ( Asgn (v,e)) = 
           do { cs <- (comp e)
              ; return (cs ++ [Dup, Store v])}  {- v is value of expression -}
        comp ( While (e1,e2)) =
           do { top_lab <- new_label
              ; bottom_lab <- new_label
              ; cs1 <-  comp e1
              ; cs2 <- comp e2
              ; return([Label top_lab] ++ cs1 ++   
                       [Branchz bottom_lab] ++ cs2 ++ [Pop] ++         {- throw away value of body -}
                       [Branch top_lab, Label bottom_lab, Const 0])}   {- overall expression evalutes to 0 -}
        comp (If (e1,e2,e3)) =  
          do false_lab <- new_label
             join_lab <- new_label
             cs1 <- comp e1
             cs2 <- comp e2
             cs3 <- comp e3
             return(cs1 ++ [Branchz false_lab] ++ cs2 ++
                    [Branch join_lab,Label false_lab] ++ cs3 ++ [Label join_lab])
                    
        comp (Write e) = do cs <- (comp e)
                            return(cs ++ [Dup,Print])
        comp (Block es) =  
          do { let c [] = return [Const 0]  {- empty blocks evaluate to 0 -}
                   c [e] = comp e           {- value of overall block is value of last expression -}
                   c (e:es) = 
                     do xs <- comp e
                        ys <- c es
                        return( xs ++ [Pop] ++ ys) {- throw away values of other expressions -}
             ; c es}
        comp (Add(e1,e2)) = 
          do cs2 <- (comp e2)
             cs1 <- (comp e1)
             return(cs2++ cs1++[Plus])
        comp (Sub(e1,e2)) = 
          do cs2 <- comp e2
             cs1 <- comp e1
             return(cs2 ++ [Negate]  ++ cs1 ++ [Plus])
        comp (Mul(e1,e2)) = 
          do cs2 <- (comp e2)
             cs1 <- (comp e1)
             return(cs2++ cs1++[Times])
        comp (Div(e1,e2)) = 
          do cs2 <- (comp e2)
             cs1 <- (comp e1)
             return(cs2++ cs1++[Swap,Divrem,Pop])
        comp (Leq(e1,e2)) = 
          do cs2 <- (comp e2)
             cs1 <- (comp e1)
             return(cs2++ cs1++[Swap,Lessequ])           
                       
--------------------------------------------------------------------------
-- A parser that reads a file and produces a program in abstract syntax
-- Most of this section is boilerplate
-- The interesting functions are "operatorP" and "expP"

-- lower case constructors.
-- The constructors of Exp are lifted to take a position (for error reporting)
-- and list of arguments. Thus every "lowercase" constructor has type: 
--  SourcePos -> [ Exp ] -> Exp
-- If one is given the wrong number of arguments an error is raised,
-- otherwise a well formed Exp is constructed.

-- if too many, or too few arguments, report the error.
report:: SourcePos -> Int -> Int -> String -> a
report pos actual expected message 
  | actual < expected = error ("Near "++show pos++"\noperator '"++message++"' is given too few arguments.")
  | otherwise = error ("Near "++show pos++"\noperator '"++message++"' is given too many arguments.")  
  
ifkey pos [x,y,z] = If(x,y,z)
ifkey pos args = report pos (length args) 3 "if"

write pos [x] = Write x
write pos args = report pos (length args) 1 "write"

while pos [x,y] = While(x,y)
while pos args = report pos (length args) 2 "while"

add pos [x,y] = Add(x,y)
add pos args = report pos (length args) 2 "+"

sub pos [x,y] = Sub(x,y)
sub pos args = report pos (length args) 2 "-"

mul pos [x,y] = Mul(x,y)
mul pos args = report pos (length args) 2 "*"

divide pos [x,y] = Div(x,y)
divide pos args = report pos (length args) 2 "/"

leq pos [x,y] = Leq(x,y)
leq pos args = report pos (length args) 2 "<="

assign pos [Var x,y] = Asgn(x,y)
assign pos [x,y] = error ("Near "++show pos++"\nfirst argument to ':=' is not a variable.")
assign pos args = report pos (length args) 2 ":="

 
-- This function parses a string, but returns a function with type: 
-- SourePos -> [Exp] -> Exp  See "lowercase" constructors above.
-- There are 10 cases, one for each of the legal operators.

operatorP = plus <|> times <|> minus <|> divid <|> ltheq <|> asg <|>
            blck <|> writ <|> iff <|> whil
  where plus   = do { symbol xxx "+";  return add}
        times  = do { symbol xxx "*";  return mul}
        minus  = do { symbol xxx "-";  return sub}
        divid  = do { symbol xxx "/";  return divide}
        ltheq  = do { symbol xxx "<="; return leq}
        asg    = do { symbol xxx ":="; return assign}
        blck   = do { try(symbol xxx "block"); return (\ pos es -> Block es)} 
        writ   = do { try(symbol xxx "write"); return write}
        iff    = do { try(symbol xxx "if"); return ifkey}
        whil   = do { try(symbol xxx "while"); return while}
        
-- An expression is either an atom or a Lisp like parenthesized operation
expP = try atom <|> sexpr
  where atom = constant <|> var
        var = 
          do { s <- identifier xxx; return(Var s)}
        constant = 
           do { n <- lexemE(number 10 digit)
              ; return (Int n)}
        sexpr  = 
           do { symbol xxx "(" 
              ; pos <- getPosition
              ; constrByList <- operatorP
              ; args <- many expP
              ; symbol xxx ")"
              ; return(constrByList pos args)}
              
         
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
                , identStart     = lower <|> upper
                , identLetter    = lower <|> upper -- alphaNum <|> char '_' 
                , opStart        = oneOf "+*-/"
                , opLetter       = oneOf "+*-/"
                , caseSensitive  = True
                , reservedOpNames = []
                , reservedNames  = []
                }                    

xxx = makeTokenParser xxxStyle
lexemE p    = lexeme xxx p
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

-----------------------------------------------
-- Turning things into String

txt = PP.text

-- This is an indenting pretty printer.
ppExp :: Exp -> PP.Doc
ppExp (Var v) = txt v
ppExp (Int n) = txt (show n)
ppExp (Asgn (v,e))= txt "(:= " PP.<> PP.nest 3 (PP.sep [txt v , ppExp e PP.<> txt ")"])
ppExp (While (x,y))= txt "(while " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (If (x,y,z))= txt "(if " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y,ppExp z PP.<> txt ")"])
ppExp (Write x)= txt "(write " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Block es) = txt "(block " PP.<> PP.nest 3 (PP.sep ((map ppExp es)++ [txt ")"]))
ppExp (Add (x,y))  = txt "(+ " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Sub (x,y))  = txt "(- " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Mul (x,y)) = txt "(* " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Div (x,y))  = txt "(/ " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Leq (x,y)) = txt "(<= " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])


plistf :: (a -> String) -> String -> [a] -> String -> String -> String
plistf f open xs sep close = open ++ help xs ++ close
  where help [] = ""
        help [x] = f x
        help (x:xs) = f x ++ sep ++ help xs    

plist = plistf id

-- Non indenting 
exp_to_string exp =
   case exp of
      Var v -> v
      Int i -> show i
      Asgn (v,e) -> "(:= " ++ v ++ " " ++ (exp_to_string e) ++ ")"
      While (e1,e2) -> "(while " ++ (exp_to_string e1) ++ " " ++ (exp_to_string e2) ++ ")"
      If (e1,e2,e3) -> "(if " ++ (exp_to_string e1) ++ " " ++ (exp_to_string e2) ++ " " ++ (exp_to_string e3) ++ ")"
      Write e -> "(write " ++ (exp_to_string e) ++ ")"
      Block es -> plist "(block " (map exp_to_string es) " " ")"
      Add(e1,e2) -> "(+ " ++ (exp_to_string e1) ++ " " ++ (exp_to_string e2) ++ ")"
      Sub(e1,e2) -> "(- " ++ (exp_to_string e1) ++ " " ++ (exp_to_string e2) ++ ")"
      Mul(e1,e2) -> "{- " ++ (exp_to_string e1) ++ " " ++ (exp_to_string e2) ++ ")"
      Div(e1,e2) -> "(/ " ++ (exp_to_string e1) ++ " " ++ (exp_to_string e2) ++ ")"
      Leq(e1,e2) -> "(<= " ++ (exp_to_string e1) ++ " " ++ (exp_to_string e2) ++ ")"

instr_to_string (Const i) = "Const " ++ (show i) 
instr_to_string (Plus) = "Plus"
instr_to_string (Times) = "Times"
instr_to_string (Negate) = "Negate"
instr_to_string (Divrem) = "Divrem"
instr_to_string (Lessequ) = "Leq"
instr_to_string (Pop) = "Pop"
instr_to_string (Dup) = "Dup"
instr_to_string (Swap) = "Swap"
instr_to_string (Load v) = "Load " ++ v
instr_to_string (Store v) = "Store " ++ v
instr_to_string (Print) = "Print"
instr_to_string (Label l) = "Label " ++ (show l) ++ ":"
instr_to_string (Branch l) = "Branch " ++ (show l)
instr_to_string (Branchz l) = "Branchz " ++ (show l)

prog_to_string instrs = showList instrs ""

stack_to_string:: Stack Int -> String
stack_to_string (St xs) = plistf show "" xs ", " " "

showEnv env = plistf f "" env ", " " "
  where f (name,value) = name++"="++show value
 
instance Show Instr where
  show = instr_to_string
  showList xs str = str ++ PP.render(PP.brackets (PP.fsep (PP.punctuate (txt ",") (map (txt . show) xs))))

instance Show Exp where
  show x = PP.render(ppExp x)
           
-------------------------------------------------------------
-- The top level read-eval-print function


interp filename = 
  do { source <- parseFile expP filename  -- this is a *.e2 file
     ; putStrLn ("Expression:\n" ++ PP.render(ppExp source))
     ; nextLabel <- newIORef 0
     ; prog <- compile nextLabel source
     ; putStrLn ("Compiles to:\n" ++ prog_to_string prog)
     ; putStrLn ("Executing:\n")
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

-- Boolean flag for tracing.
trace_on = unsafePerformIO (newIORef False)

-- typing "trace" at the GHCI prompt flips the tracing flag
trace = do { b <- readIORef trace_on
           ; writeIORef trace_on (not b)
           ; let f True = "on"
                 f False = "off"
           ; putStrLn ("\nTracing is "++f (not b)++".")}
              
--------------------------------------------
-- Some very simple tests, requires file 
-- "primes.e2" in the current directory

-- Does the parser work
test1 = parseFile expP "primes.e2"
test3 = parseFile expP "count.e2"

-- does the top level work
test2 = interp "primes.e2"
test4 = interp "count.e2"

test5 = parse2 expP "(for i i (block (:= i (+ i 2)) 10) (block (write i) (:= i (+ i 3))))"