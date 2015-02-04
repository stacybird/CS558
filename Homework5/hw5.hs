{-#LANGUAGE    FlexibleInstances   #-}
module Main where

-- enriched, superior Hw5.hs, use this next time
-- Simple functional language where everything is allocated on the heap
-- slight changes (from hw5.hs) to function introduction (lambda)
-- and introduces Decl's inside (Let pos Decls Exp)
-- This file is the starting point for hw9.hs

{- Interpreter for simple imperative language. -}

-- These imports are for defining parsers
import Text.Parsec hiding (State,Column)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import Text.Parsec.Prim(getInput)
import Text.Parsec.Pos(SourcePos,sourceName,sourceLine,sourceColumn,newPos)
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

type Vname = String  -- Names of variables
type Fname = String  -- Names of functions
type Addr = Int      -- Address of a location in the Heap

data Exp 
  = Var SourcePos Vname
  | Int SourcePos Int
  | Char SourcePos Char
  | If Exp Exp Exp
  | Let SourcePos [Decl] Exp  
  
  | Lambda SourcePos [Vname] Exp
  | At Exp SourcePos [Exp]    
  | Add  Exp Exp
  | Sub  Exp Exp
  | Mul  Exp Exp
  | Div  Exp Exp
  | Leq  Exp Exp
  | Ceq  Exp Exp
  | Pair Exp Exp
  | Fst Exp
  | Snd Exp
  | Ispair Exp
  | Ischar Exp
  | Isint Exp

data Decl 
   = ValDecl SourcePos Vname Exp
   | FunDecl SourcePos Fname [Vname] Exp
             
----------------------------------------------------
-- Values are what the interpreter returns. The IntV
-- part is interpreted as a Bool much as in C. Some
-- operators are defined only on the IntV or PairV
-- types of Value and we need to return errors otherwise.
-- This is done by "numeric" and "test" and "pairLike"

data Value 
  = IntV Int 
  | CharV Char 
  | PairV Value Value 
  | FunV Vname (Env Addr) [Vname] Exp  -- A function closure

type Heap = [Value]

-- numeric operators are only defined if both inputs are integers.
numeric :: String -> (Int -> Int -> Int) -> Value -> Value -> Value
numeric name fun (IntV x) (IntV y) = IntV(fun x y)
numeric name fun v (IntV _) = error ("First arg of "++name++" is not an Int. "++show v)
numeric name fun (IntV _) v = error ("Second arg of "++name++" is not an Int. "++ show v)
numeric name fun u v = error ("neither arg of "++name++" is an int: "++show u++" "++show v)

-- Interpret 0 as False, and non-zero as True
boolToInt False = 0
boolToInt True = 1

-- A sort of "if" over Values, raises an error 
-- if the Value can't be interpreted as a Bool
test :: String -> Value -> t -> t -> t
test name (IntV 0) truth falsehood = falsehood
test name (IntV _) truth falsehood = truth
test name _ t f = error ("Non Int as argument to "++name++" test.")

-- Some operations expect pairs
pairLike name fun (PairV v1 v2) = fun v1 v2
pairLike name fun v = 
  error ("function "++name++" is not passed a pair."++ show v)

charLike name fun (CharV c) = fun c
charLike name fun v = 
  error ("function "++name++" is not passed a char."++ show v)

--------------------------------------------------------------
-- functions on SourcePos


noPos:: SourcePos
noPos = newPos "unknown location" 0 0 

none p = (sourceName p)=="unknown location" &&
         (sourceLine p)==0 &&
         (sourceColumn p)==0

lineCol p = (sourceLine p,sourceColumn p)


---------------------------------------------------------------
-- Tables and Association lists

-- A table maps keys to values
data Table key value = Tab [(key,value)]

-- When searching one returns a Result
data Result a = Found a | NotFound 

search :: Eq key => key -> [(key, a)] -> Result a
search x [] = NotFound
search x ((k,v):rest) = if x==k then Found v else search x rest

-- Search a Table
lookUp :: Eq key => Table key a -> key -> Result a
lookUp (Tab xs) k = search k xs

-- update an association list at a given key.
update n u ((m,v):rest) | n==m = (m,u):rest
update n u (r:rest) = r : update n u rest
update n u [] = error ("Unknown address: "++show n++" in update")

--------------------------------------------------------------
-- Environments

type Env a = Table String a  -- where the key is a String

emptyE = Tab []
extend key value (Tab xs) = Tab ((key,value):xs)

---------------------------------------------------------------
-- The State of the Machine consists of a Stack and a Heap
-- The machine also uses two Tables mapping names to their bindings.

-- State contains a Stack and a Heap and a stack of Exception handlers
data State = State Heap 

state0 = State []

-- Operations on State

heap(State hp) = hp
 
delta g (State hp) = State (g hp)
deltaHeap g state = delta g state

-- Search the State for the Value at a given Address
find n state = if n>(m-1) then NotFound else Found( hp !! n )
   where hp = (heap  state) 
         m = length hp

-- Allocate a new location in the heap.
-- return its Address and a new state.
alloc :: Value -> State -> (Addr,State)
alloc v state = (addr,deltaHeap f state)
   where addr = length (heap state)
         f heap = heap ++ [(v)] 

-- Update the State at a given Adress
stateStore a u state = deltaHeap (updateH a) state
  where updateH 0 (x:xs) = (u:xs)
        updateH n (x:xs) = x : updateH (n-1) xs
        updateH n [] = error ("Address "++show a++" too large for heap.")



   
heap0 = h4
  where h1 = state0
        (_,h2) = alloc (IntV 3) h1
        (_,h3) = alloc (IntV 6) h2
        (_,h4) = alloc (IntV 1) h3
        

instance Show State where
  show state = plistf show "" (heap state) " " " ."
    where f (x,y) = show x++"="++show y
  
------------------------------------------------------------------
-- An interpretor for Exp
-- We store functions and variables in two different name spaces
-- functions in an   Env (Env Value,[Vname],Exp)
-- variables in an   Env Value

-- interpret a single exp
-- An intepretation might compute a new environment for variables
-- because an assignment might take place.
 
run x = interpE emptyE state0 x

interpE :: Env Addr                 -- the variable name space
        -> State                    -- the stack and heap
        -> Exp                      -- exp to interpret
        -> IO(Value,State)          -- (result,new_heap)


interpE vars state exp = traceG run state exp where
   run state (Var pos v) = 
     case lookUp vars v of
       Found addr -> case find addr state of
                       Found v -> return(v,state)
                       NotFound -> error (show pos++"Unknown address: "++show addr++" in heap.")
       NotFound -> error ("Unknown variable: "++v++" in lookup.")
   run state (Int pos n) = return(IntV n,state)
   run state (Char pos  c) = return(CharV c,state)

   run state (term@(At f pos args)) = 
     do { (fv,state2) <- interpE vars state f 
        ; (actuals,state3) <- interpList vars state2 args 
        ; let apply state4 (FunV name env (f:fs) body) (v:vs) =
                do { let (addr,state5) = alloc v state4
                   ; apply state5 (FunV name (extend f addr env) fs body) vs }
              apply state4 (FunV name env [] body) [] = interpE env state4 body
              apply state4 (fun@(FunV _ _ (f:fs) _)) [] = return(fun,state4)
              apply state4 (FunV name env [] body) (v:vs) = 
                do { (fun,state5) <- interpE env state4 body 
                   ; apply state5 fun (v:vs) }
              apply state4 v vs = error("Non function\n   "++show v++"\nin application\n   "++show term)
        ; apply state3 fv actuals
        }
   run state (If x y z) = 
     do { (v,state2) <- interpE vars state x
        ; test "if" v (interpE vars state2 y) (interpE vars state2 z) }  
   run state (Add  x y) = 
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; return(numeric "+" (+) v1 v2,state2) }
   run state (Sub  x y) =
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; return(numeric "-" (-) v1 v2,state2) }      
   run state (Mul  x y) = 
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; return(numeric "*" (*) v1 v2,state2) }   
   run state (Div  x y) = 
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; return(numeric "/" (div) v1 v2,state2) }   
   run state (Leq  x y) = 
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; return(numeric "<=" (\ x y -> boolToInt(x <= y)) v1 v2,state2) } 
   run state (Ceq  x y) = 
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; case (v1,v2) of 
            (CharV x,CharV y) -> return(IntV(boolToInt(x==y)),state2)
            (x,CharV _) -> error ("first arg to 'chareq' is not Char: "++show x) 
            (CharV _,x) -> error ("second arg to 'chareq' is not Char: "++show x) 
            other -> error ("neither arg to 'chareq' is a Char: "++show other)}         
   run state (Pair x y) = 
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; return(PairV v1 v2,state2)}
   run state (Fst x)    = 
     do { (v1,state1) <- interpE vars state x
        ; return(pairLike "fst" (\ x y -> x) v1,state1)}
   run state (Snd x)    = 
     do { (v1,state1) <- interpE vars state x
        ; return(pairLike "snd" (\ x y -> y) v1,state1)}   
   run state (Ispair x) = 
     do { (v1,state1) <- interpE vars state x
        ; case v1 of
            (PairV _ _) -> return(IntV(boolToInt True),state1)
            other -> return(IntV(boolToInt False),state1)}
   run state (Ischar x) = 
     do { (v1,state1) <- interpE vars state x
        ; case v1 of
            (CharV _) -> return(IntV(boolToInt True),state1)
            other -> return(IntV(boolToInt False),state1)}   
   run state (Isint x) = 
     do { (v1,state1) <- interpE vars state x
        ; case v1 of
            (IntV _) -> return(IntV(boolToInt True),state1)
            other -> return(IntV(boolToInt False),state1)}               
   
   run state (Let pos ds body) =      
     do { (vars1,state1) <- foldM (elab False) (vars,state) ds
        ; interpE vars1 state1 body }


   run state (term@(Lambda p vs e)) = 
     return(FunV ("\\"++show (lineCol p)) vars vs e,state)

-- interpret a list from left to right. Be sure the
-- state is updated for each element in the list.

interpList vars state [] = return([],state)
interpList vars state (e:es) = 
  do { (v,state1) <- interpE vars state e
     ; (vs,state2) <- interpList vars state1 es
     ; return(v:vs,state2)}
     
-- The function "elab" is used only in the read-eval-print loop
-- It is very similar to the interpE cases for Let and LetFun
-- In fact, changes made to the interpE cases will also need
-- to be made here. It is needed to compute the environment and state
-- to run the read-eval-print loop. Note outer Let and LeFun should
-- be defined before we run the "main" program, which is the Exp
-- most deeply nested in Let and LetFun.


elab noisy (ValDecl pos nm body) (vars,state) = 
  do { (v,state2) <- interpE vars state body
     ; when noisy (putStrLn (nm ++ " "))
     ; let (addr,state3) = alloc v state2
     ; return(extend nm addr vars,state3)}
elab noisy (FunDecl pos f var e) (vars,state) =
     do { let (addr,state2) = alloc closure state
              vars2 = extend f addr vars
              closure = (FunV f vars2 var e)
        ; when noisy (putStr(f ++ " "))              
        ; return (vars2,state2)}    
when True x = x
when False x = return ()
     
--------------------------------------------------------------------------
-- A parser that reads a file and produces a program in abstract syntax
-- Most of this section is boilerplate
-- The interesting functions are "operatorP" and "expP"


-- if too many, or too few arguments, report the error.
report:: SourcePos -> Int -> Int -> String -> a
report pos actual expected message 
  | actual < expected = error ("Near "++show pos++"\noperator '"++message++"' is given too few arguments.")
  | otherwise = error ("Near "++show pos++"\noperator '"++message++"' is given too many arguments.")  

-- There is one lower case constructors for each Exp constructor
-- The constructors of Exp are lifted to take a position (for error reporting)
-- and a list of arguments. Thus every "lowercase" constructor has type: 
--     SourcePos -> [ Exp ] -> Exp
-- If one is given the wrong number of arguments an error is raised,
-- otherwise a well formed Exp is constructed.

  
ifkey pos [x,y,z] = If x y z
ifkey pos args = report pos (length args) 3 "if"

add pos [x,y] = Add x y
add pos args = report pos (length args) 2 "+"

sub pos [x,y] = Sub x y
sub pos args = report pos (length args) 2 "-"

mul pos [x,y] = Mul x y
mul pos args = report pos (length args) 2 "*"

divide pos [x,y] = Div x y
divide pos args = report pos (length args) 2 "/"

leq pos [x,y] = Leq x y
leq pos args = report pos (length args) 2 "<="

ceq pos [x,y] = Ceq x y
ceq pos args = report pos (length args) 2 "="

atSign pos (x:ys) = At x pos ys
atSign pos args = report pos (length args) 2 "@"

pair pos [x,y] = Pair x y
pair pos args = report pos (length args) 2 "pair"

fstC pos [x] = Fst x
fstC pos args = report pos (length args) 1 "fst"

sndC pos [x] = Snd x
sndC pos args = report pos (length args) 1 "snd"

ispair pos [x] = Ispair x
ispair pos args = report pos (length args) 1 "ispair"

ischar pos [x] = Ischar x
ischar pos args = report pos (length args) 1 "ischar"

isint pos [x] = Isint x
isint pos args = report pos (length args) 1 "isint"

-- letv and letfun are special because some of their arguments must be a variables!!
letv pos [e] = Let pos e
letv pos args = report pos (length args) 3 "let"


-- Lambda SourcePos [Vname] Exp
letfun ds pos [e] = Let pos ds e
letfun ds pos args = report pos (length args) 4 "letfun"

lambda vs pos [x] = Lambda pos vs x
lambda vs pos args = report pos (length args) 1 "\\"

 
-- This function parses a string, but returns a function with type: 
-- SourcePos -> [Exp] -> Exp    See "lowercase" constructors above.
-- There are many cases, one for each of the legal constructors to Exp.
-- To add to the parser, write a new function "f" then add " <|> f "
-- to the definition of "operatorP"

operatorP = plus <|> times <|> minus <|> divid <|> ltheq <|> chareq <|> atP <|>
            iff <|> pairP <|> fstP <|> sndP <|> ispairP <|> ischarP <|> isintP
            <|> lambdaP <|> letP
  where plus   = do { symbol xxx "+";  return add}
        times  = do { symbol xxx "*";  return mul}
        minus  = do { symbol xxx "-";  return sub}
        divid  = do { symbol xxx "/";  return divide}
        ltheq  = do { symbol xxx "<="; return leq}
        chareq = do { symbol xxx "="; return ceq}
        atP    = do { symbol xxx "@"; return atSign}
        iff    = do { try(symbol xxx "if"); return ifkey}
        pairP  = do { try(symbol xxx "pair"); return pair}
        fstP   = do { try(symbol xxx "fst"); return fstC}
        sndP   = do { try(symbol xxx "snd"); return sndC}
        ispairP= do { try(symbol xxx "ispair"); return ispair}
        ischarP= do { try(symbol xxx "ischar"); return ischar}  
        isintP = do { try(symbol xxx "isint"); return isint} 
        -- letfunP  = do { try(symbol xxx "letfun"); return letfun}        
        letP   = do { try(symbol xxx "let")
                    ; ds <- many declP
                    ; symbol xxx "in"
                    ; return (letfun ds)}
        lambdaP = do {try(symbol xxx "lambda")
                     ; vs <- parenS(many (identifier xxx))
                     ; let name (Var pos s) = s
                     ; return(lambda vs)}        
        
        
      
                    
        
        
        
-- An expression is either an atom or a Lisp like parenthesized operation
expP = try atom <|> sexpr
  where atom = constant <|> charP <|> var
        var = 
          do { pos <- getPosition; s <- identifier xxx; return(Var pos s)}
        constant = 
           do { pos <- getPosition;
              ; n <- lexemE(number 10 digit)
              ; return (Int pos n)}
        sexpr  = 
           do { symbol xxx "(" 
              ; pos <- getPosition
              ; constrByList <- operatorP  -- Parse a string, get a lowercase constructor
              ; args <- many expP
              ; symbol xxx ")"
              ; return(constrByList pos args)}
        charP = do { pos <- getPosition; c <- charLiteral xxx; return(Char pos c)}

declP = parenS(valP <|> funP) <?> "<decl>"
  where  funP =
          do { pos <- getPosition
             ; try(symbol xxx "fun")
             ; name <- identifier xxx
             ; vs <- parenS(many (identifier xxx)) <?> "<fun param list>"
             ; body <- expP
             ; return(FunDecl pos name vs body)} 
         valP =
          do { pos <- getPosition
             ; try(symbol xxx "val")
             ; name <- identifier xxx
             ; body <- expP <?> "<val body>"
             ; return(ValDecl pos name body)}             
             
             
progP = 
  do { ds <- many (try declP)
     ; symbol xxx "in"
     ; main <- expP
     ; return(ds,main)}
     
-- Boilerplate below here        
       
type MParser a = ParsecT
                    String                -- The input is a sequence of Char
                    ()                    -- The internal state
                    Identity              -- The underlying monad
                    a                     -- the type of the object being parsed
      
xxxStyle = LanguageDef
                { commentStart   = "{"
                , commentEnd     = "}"
                , commentLine    = ""
                , nestedComments = True
                , identStart     = lower <|> upper
                , identLetter    = lower <|> upper <|> digit
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
manyPP [] = [txt ")"]
manyPP [x] = [ppExp x PP.<> txt ")"]
manyPP (x:xs) = ppExp x : manyPP xs
                    
copies n x | n <= 0 = []
copies n x = x : (copies (n-1) x)

-- This is an indenting pretty printer.
ppExp :: Exp -> PP.Doc
ppExp (Var pos v) = txt v
ppExp (Int pos n) = txt (show n)
ppExp (Char pos c) = txt (show c)
ppExp (If x y z)= txt "(if " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y,ppExp z PP.<> txt ")"])
ppExp (Let pos ds exp) = 
   PP.parens(PP.sep [txt "let",PP.nest 4 (PP.vcat (map ppDecl ds)),ppExp exp])

ppExp (Lambda p vars e) = txt "(\\ " PP.<> PP.nest 3 (PP.sep [vs, ppExp e PP.<> txt ")"])
  where vs = PP.parens(PP.sep(map txt vars))
ppExp (At f p args)= txt "(@ " PP.<> PP.nest 3 (PP.sep (ppExp f : ppMany args))
ppExp (Add  x y)  = txt "(+ " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Sub  x y)  = txt "(- " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Mul  x y) = txt "(* " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Div  x y)  = txt "(/ " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Leq  x y) = txt "(<= " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Ceq  x y) = txt "(= " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Pair x y) = txt "(pair " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Fst x) = txt "(fst " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Snd x) = txt "(snd " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Ispair x) = txt "(ispair " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Ischar x) = txt "(ischar " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Isint x) = txt "(isint " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
   

ppDecl (FunDecl pos nm vs e) = 
  PP.parens(PP.sep [ txt "fun", txt nm, PP.parens(PP.sep(map txt vs)), ppExp e])
ppDecl (ValDecl pos nm e) = 
  PP.parens(PP.sep [ txt "val", txt nm, ppExp e])
  
ppMany [] = [txt ")"]
ppMany [x] = [ppExp x PP.<> txt ")"]
ppMany (x:xs) = ppExp x : ppMany xs

ppProg (ds,exp) = 
   PP.sep [txt "let",PP.nest 4 (PP.vcat (map ppDecl ds)),ppExp exp]


plistf :: (a -> String) -> String -> [a] -> String -> String -> String
plistf f open xs sep close = open ++ help xs ++ close
  where help [] = ""
        help [x] = f x
        help (x:xs) = f x ++ sep ++ help xs    

plist = plistf id


isList (IntV 0) = Just []
isList (PairV x xs) = do { ys <- isList xs; return(x:ys)}
isList other = Nothing

isString (IntV 0) = Just []
isString (PairV (CharV x) xs) = do { ys <- isString xs; return(x:ys)}
isString other = Nothing



instance Show Value where
  show (x@(PairV _ _)) | Just str <- isString x = show str
  show (x@(PairV _ _)) | Just ys <- isList x = plist "[" (map show ys) "," "]"    
  show (IntV n) = show n
  show (CharV c) = show c
  show (PairV x y) = "("++show x++"."++show y++")"
  show (FunV f env args body) = "<"++f++" "++show(length args)++">"

showEnv env = plistf f "" env ", " " "
  where f (name,value) = show name++"="++show value

instance (Show key,Show value) => Show (Table key value) where
  show (Tab xs) = showEnv xs
  
instance Show Exp where
  show x = PP.render(ppExp x)

instance Show Decl where
  show x = PP.render(ppDecl x)
------------------------------------------------------- 
-- Functions for indenting pretty printing. Needed for the tracer.

class Pretty x where
  pp:: x -> PP.Doc

instance Pretty Exp where
   pp = ppExp

instance (Pretty key,Pretty value) => Pretty (Table key value) where
  pp (Tab xs) = PP.sep(map f xs)
    where f (x,y) = pp x PP.<> txt ("=") PP.<> pp y
    
instance (Pretty a, Pretty b) => Pretty (a,b) where
  pp (x,y) = PP.parens (PP.sep [pp x, txt ",", pp y])
  
instance Pretty Value where
   pp v = txt(show v)
   
instance Pretty [Char] where
  pp str = txt str

instance Pretty Int where
  pp x = txt(show x)
  
instance Pretty State where
  pp x = txt(show x)
  

ppStack [] = PP.empty
ppStack xs = txt "Heap  " PP.<> txt(plistf f "" xs " " "")
    where f (x,y) = show x++"="++show y
    
ppHeap [] = PP.empty
ppHeap xs = txt "Stack " PP.<> txt(plistf f "" (zip [0..] xs) " " "")
    where f (x,y) = show x++"@"++show y    


------------------------------------------------------------
-- This is for tracing the interpreter

-- Boolean flag for tracing.
trace_on = unsafePerformIO (newIORef False)

-- typing "trace" at the GHCI prompt flips the tracing flag
trace = do { b <- readIORef trace_on
           ; writeIORef trace_on (not b)
           ; let f True = "on"
                 f False = "off"
           ; putStrLn ("\nTracing is "++f (not b)++".")}

-- Keeps track of the indentation of the tracer
traceIndent = unsafePerformIO (newIORef 0)

type InterpType = State -> Exp -> IO (Value,State)

traceF :: InterpType -> InterpType 
traceF f state exp =
  do { n <- readIORef traceIndent
     ; let indent x = txt(concat(replicate n " |")++x)
     ; putStrLn(PP.render(indent "> " PP.<> (PP.vcat[pp exp
                                                    ,ppHeap (heap state)])))
     ; writeIORef traceIndent (n+1)
     ; ans <- f state exp
     ; writeIORef traceIndent n
     ; putStrLn(PP.render(indent "< " PP.<> ppAns ans))
     ; return ans }

ppAns (v,state) = pp v

-- Like traceF if tracing is on, like f if not.
traceG :: InterpType -> InterpType 
traceG f vars exp = 
  do {  b <- readIORef trace_on
     ; if b then traceF f vars exp else f vars exp }

-------------------------------------------------------------
-- The top level functions
-- Runs

-- Runs an expression of type (IO a), and catches calls to error with "bad"
guard command bad =
  do possible <- Control.Exception.try command
     case possible of
       Right ans -> return ans
       Left err -> (bad (err::(Control.Exception.ErrorCall)))

foldM acc state [] = return state
foldM acc state (x:xs) =  do { state2 <- acc x state; foldM acc state2 xs}
 

              
runFile filename = 
  do { putStrLn "\n********** PARSING ******************"
     --; source <- parseFile expP filename  -- this is a *.e5 file
     ; (ds,main) <- parseFile progP filename 
     ; putStrLn ("Program:\n" ++ PP.render(ppProg(ds,main)))
     
     ; putStrLn "\n******** LOADING DEFS **************"
     ; (vars,state) <- foldM (elab True) (emptyE,state0) ds
     
     ; putStrLn "\n\n********** EXECUTING BODY **********"
     ; (v,state2) <- interpE vars state main
     ; putStrLn(show v)
     ; putStrLn "\n*********** ENTERING READ EVAL PRINT ***************"    
     ; putStrLn "type ':q' to exit, type 'trace' to flip tracer state\n"
     ; let loop state = 
              do { putStrLn "enter Exp>"
                 ; str <- getLine
                 ; case str of
                     ":q" -> (error "Quitting")
                     "trace" -> do { trace; loop state}
                     other -> case parse1 ("keyboard input\n"++str) expP str of
                                Left message -> do { putStrLn(show message); loop state}
                                Right exp -> guard
                                  (do { (v,state2) <- interpE vars state exp
                                      ; putStrLn(show v)
                                      ; loop state2})
                                  (\ s -> do { putStrLn(show s); loop state})}               
     ; loop (state2)
     }
     
 
     
main =
  do { args <- System.Environment.getArgs 
     ; case args of
        (x :xs) -> runFile x
        [] -> error "No command line argument specifying input file"
     }     

----------------------------------------------------------------------
-- Some very simple tests, requires some files 

-- Does the parser work
test1 = parseFile progP "static.e5"
test2 = parseFile progP "compose.e5"
test3 = parseFile progP "map.e5"        

-- does the top level work

test4 = runFile "static.e5"
test5 = runFile "compose.e5"
test6 = runFile "map.e5"        
