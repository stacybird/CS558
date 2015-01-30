{-#LANGUAGE    FlexibleInstances   #-}
module Main where

-- There are two kinds of addresses, on the stack and on the heap


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

type Vname = String  -- Names of variables
type Fname = String  -- Names of functions
type Addr = Int      -- Address of a location in the Heap

data Exp 
  = Var  Vname
  | Int  Int
  | Char Char
  | Asgn  Vname Exp
  | While Exp Exp
  | If Exp Exp Exp
  | Write Exp
  | Block [Exp]
  | At Fname [Exp]
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
  | Try Exp [(Fname,[Vname],Exp)]
  | Raise Fname [Exp]
  | Tag String Exp
  | Local [Exp] Exp
  
data Def 
  = GlobalDef Vname Exp
  | FunDef Fname [Vname] Exp
  | Except Fname Int

data Program = Prog [Def] Exp  

defName (GlobalDef v e) = v
defName (FunDef f vs e) = f
defName (Except f n) = f

----------------------------------------------------
-- Values are what the interpreter returns. The IntV
-- part is interpreted as a Bool much as in C. Some
-- operators are defined only on the IntV or PairV
-- types of Value and we need to return errors otherwise.
-- This is done by "numeric" and "test" and "pairLike"

data Value = IntV Int | CharV Char | PairV Value Value | Bad

type Stack = [(Vname,Value)]
type Heap = [Value]

-- An address either points into the Stack or the Heap
data Address = SAddr Vname | HAddr Addr
  deriving Show


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
push vs (Tab xs) = Tab (map f vs ++ xs) where f x = (x,SAddr x)

---------------------------------------------------------------
-- The State of the Machine consists of a Stack and a Heap
-- The machine also uses two Tables mapping names to their bindings.

-- State contains a Stack and a Heap and a stack of Exception handlers
data State  
  = State Stack Heap 
  | Exception State Fname [Value]

state0 = State [] []

-- Operations on State

exceptional (Exception _ _ _) = True
exceptional (State _ _) = False

stack(State st hp) = st
stack(Exception st f vs) = stack st

heap(State st hp) = hp
heap(Exception st f vs) = heap st

subState (Exception st f vs) = st

delta f g (State st hp) = State (f st) (g hp)
delta f g (Exception st fname vs) = Exception st fname vs

deltaStack f state = delta f id state 
deltaHeap g state = delta id g state

-- Search the State for the Value at a given Address
find addr state | exceptional state = find addr (subState state)
find (SAddr nm) state = search nm (stack state)
find (HAddr n) state = if n>(m-1) then NotFound else Found( hp !! n )
   where hp = (heap  state) 
         m = length hp

-- Allocate a new location in the heap.
-- return its Address and a new state.
alloc :: Value -> State -> (Address,State)
alloc v state | exceptional state = (error "Exception State in alloc",state)
alloc v state = (HAddr addr,deltaHeap f state)
   where addr = length (heap state)
         f heap = heap ++ [(v)] 

-- Add many Stack items to the State
bind names objects state = deltaStack f state
  where f stack = (zip names objects)++stack

-- Update the State at a given Adress
stateStore (SAddr n) u state = deltaStack (update n u) state
stateStore (HAddr a) u state = deltaHeap (updateH a) state
  where updateH 0 (x:xs) = (u:xs)
        updateH n (x:xs) = x : updateH (n-1) xs
        updateH n [] = error ("Address "++show a++" too large for heap.")



   
heap0 = h4
  where h1 = state0
        (_,h2) = alloc (IntV 3) h1
        (_,h3) = alloc (IntV 6) h2
        (_,h4) = alloc (IntV 1) h3
        

instance Show State where
  show state | exceptional state = "EXCEPTION"
  show state = plistf f "" (stack state) " " " | " ++ plistf show "" (heap state) " " " ."
    where f (x,y) = show x++"="++show y
  
------------------------------------------------------------------
-- An interpretor for Exp
-- We store functions and variables in two different name spaces
-- functions in an   Env (Env Value,[Vname],Exp)
-- variables in an   Env Value

-- interpret a single exp
-- An intepretation might compute a new environment for variables
-- because an assignment might take place.
 
run x = interpE emptyE emptyE state0 x

interpE :: Env (Stack,[Vname],Exp)  -- The function name space
        -> Env Address              -- the variable name space
        -> State                    -- the stack and heap
        -> Exp                      -- exp to interpret
        -> IO(Value,State)          -- (result,new_heap)


interpE funs vars state exp = traceG run state exp where
   run state exp | exceptional state = return(Bad,state)
   run state (Var v) = 
     case lookUp vars v of
       Found addr -> case find addr state of
                       Found v -> return(v,state)
                       NotFound -> error ("Unknown address: "++show addr++" in heap.")
       NotFound -> error ("Unknown variable: "++v++" in lookup.")
   run state (Int n) = return(IntV n,state)
   run state (Char c) = return(CharV c,state)
   run state (Asgn v e ) = 
     do { (val,state2) <- interpE funs vars state e
        ; case lookUp vars v of
            Found addr -> return(val,stateStore addr val state2)
            NotFound -> -- error ("Unknown variable: "++v++" in assignment.") }
              do { let (addr,state3) = alloc val state2
                 ; return(val,state3)} }              
  
   run state (term@(At f args)) = 
     case lookUp funs f of
        NotFound -> error ("Unknown function: "++f++" in function call "++show term++".")
        Found (locals,formals,body) -> 
          do { when (length args /= length formals)
                    (error ("Wrong number of args to: "++f++" in: "++show term))
             ; (vs,st2) <- interpList funs vars state args
             ; let st3 = delta (\ _ -> locals) (\ _ -> heap st2) state
             ; (v,st4) <- interpE funs (push formals vars) (bind formals vs st3) body
             ; return(v,deltaStack (\ _ -> stack st2) st4)}

   run state (While tst body)= while state
     where while state = 
             do { (v,state2) <- interpE funs vars state tst
                ; test "while" v
                       (do { (_,state3) <- interpE funs vars state2 body
                           ; while state3})
                       (return(IntV 0,state2))}   
   run state (If x y z) = 
     do { (v,state2) <- interpE funs vars state x
        ; test "if" v (interpE funs vars state2 y) (interpE funs vars state2 z) }  
   run state (Write x)  = 
     do { (v1,state1) <- interpE funs vars state x
        ; putStrLn (show v1)
        ; return(v1,state1)}
   run state (Block es) = 
     do { let last [] = IntV 0  -- empty block returns 0
              last [x] = x
              last (x:xs) = last xs
        ; (vs,state2) <- interpList funs vars state es
        ; return(last vs,state2)}
   run state (Add  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric "+" (+) v1 v2,state2) }
   run state (Sub  x y) =
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric "-" (-) v1 v2,state2) }      
   run state (Mul  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric "*" (*) v1 v2,state2) }   
   run state (Div  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric "/" (div) v1 v2,state2) }   
   run state (Leq  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric "<=" (\ x y -> boolToInt(x <= y)) v1 v2,state2) } 
   run state (Ceq  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; case (v1,v2) of 
            (CharV x,CharV y) -> return(IntV(boolToInt(x==y)),state2)
            (x,CharV _) -> error ("first arg to 'chareq' is not Char: "++show x) 
            (CharV _,x) -> error ("second arg to 'chareq' is not Char: "++show x) 
            other -> error ("neither arg to 'chareq' is a Char: "++show other)}         
   run state (Pair x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(PairV v1 v2,state2)}
   run state (Fst x)    = 
     do { (v1,state1) <- interpE funs vars state x
        ; return(pairLike "fst" (\ x y -> x) v1,state1)}
   run state (Snd x)    = 
     do { (v1,state1) <- interpE funs vars state x
        ; return(pairLike "snd" (\ x y -> y) v1,state1)}   
   run state (Ispair x) = 
     do { (v1,state1) <- interpE funs vars state x
        ; case v1 of
            (PairV _ _) -> return(IntV(boolToInt True),state1)
            other -> return(IntV(boolToInt False),state1)}
   run state (Ischar x) = 
     do { (v1,state1) <- interpE funs vars state x
        ; case v1 of
            (CharV _) -> return(IntV(boolToInt True),state1)
            other -> return(IntV(boolToInt False),state1)}            
   run state (Try e handlers) = 
     do { (v,st2) <- interpE funs vars state e
        ; case st2 of
            (State _ _) -> return(v,st2)
            (Exception st3 f vs) ->
               let tryAll [] = return(v,st2) -- pass exception on, no handler matched
                   tryAll ((g,fs,body):xs) 
                     | f==g 
                     = do { when (length fs /= length vs)
                                 (error ("Matching handle: "++ g++", does not have correct number of parameters"))
                          ; (v,st4) <- interpE funs (push fs vars) 
                                       (bind fs vs (deltaHeap (\ _ -> heap st3) state))
                                       (Tag ("handle "++f) body)
                          ; return(v,deltaStack (\ _ -> stack state) st4)}                     
                     | otherwise = tryAll xs
               in tryAll handlers}
   run state (Raise f es) = 
     do { (vs,st2) <- interpList funs vars state es
        ; return(Bad,Exception st2 f vs)}
   run state (Tag s e) = interpE funs vars state e 
   run state (Local pairs body) = 
     do { let split (Var v : e : zs) (vs,es) = split zs (vs++[v],es++[e])
              split _ (vs,es) = (vs,es)
              (formals,es) = split pairs ([],[])
        ; (vs,st2) <- interpList funs vars state es
        ; let st3 = delta id (\ _ -> heap st2) state
        ; (v,st4) <- interpE funs (push formals vars) (bind formals vs st3) body
        ; return(v,deltaStack (\ _ -> stack st2) st4)}
 

-- interpret a list from left to right. Be sure the
-- state is updated for each element in the list.

interpList funs vars state es | exceptional state = return ([],state)
interpList funs vars state [] = return([],state)
interpList funs vars state (e:es) = 
  do { (v,state1) <- interpE funs vars state e
     ; (vs,state2) <- interpList funs vars state1 es
     ; return(v:vs,state2)}
 
elab:: Def -> (Env (Stack,[Vname],Exp),Env Address,State) -> IO (Env (Stack,[Vname],Exp),Env Address,State)
elab ef (fs,xs,state) | exceptional state = error ("Uncaught exception" ++ show state)
elab (FunDef f vs e) (Tab fs,Tab xs,state) =
  return (Tab ((f,(stack state,vs,e)):fs),Tab xs,state)
elab (GlobalDef v e) (funs,vars,state) =
  do { (value,state2) <- interpE funs vars state e
     ; let (addr,state3) = alloc value state2
     ; return(funs, extend v addr vars,state3)}

when True x = x
when False x = return ()

elaborate loud [] ts = return ts
elaborate loud (d:ds) ts = 
  do { when loud (putStr (defName d++" "))
     ; ts1 <- elab d ts
     ; elaborate loud ds ts1}
                
     
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

write pos [x] = Write x
write pos args = report pos (length args) 1 "write"

while pos [x,y] = While x y
while pos args = report pos (length args) 2 "while"

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

atSign pos (Var x:args) = At x args
atSign pos args = error ("Near "++show pos++"\nfirst argument to '@' is not a function name.")

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

-- Asgn is special because its first argument must be a variable!!
assign pos [Var x,y] = Asgn x y
assign pos [x,y] = error ("Near "++show pos++"\nfirst argument to ':=' is not a variable.")
assign pos args = report pos (length args) 2 ":="

local vs pos [x] = Local vs x  
local vs pos args = report pos (length args) 1 "local"

tryf pos args = Try x (map triple handlers)
  where (x:handlers) = args
        triple (At exname zs) = excall zs []
           where excall [e] xs = (exname,xs,e)
                 excall [] xs = error ("Near "++show pos++"\nHandler without body")
                 excall (Var x : es) xs = excall es (xs++[x])
                 excall (e:es) xs = error ("Near "++show pos++"\nNon var in handler arg list: "++show e)
                           
-- Raise is special because its first argument must be a variable!!
raise pos (Var x: ys) = Raise x ys
raise pos (x:xs) = error ("Near "++show pos++"\nfirst argument to 'raise' is not an exception name.")


 
-- This function parses a string, but returns a function with type: 
-- SourcePos -> [Exp] -> Exp    See "lowercase" constructors above.
-- There are many cases, one for each of the legal constructors to Exp.
-- To add to the parser, write a new function "f" then add " <|> f "
-- to the definition of "operatorP"

operatorP = plus <|> times <|> minus <|> divid <|> ltheq <|> chareq <|> asg <|> atP <|>
            blck <|> writ <|> iff <|> whil <|> localP <|>
            pairP <|> fstP <|> sndP <|> ispairP <|> ischarP <|> raiseP <|> tryP
  where plus   = do { symbol xxx "+";  return add}
        times  = do { symbol xxx "*";  return mul}
        minus  = do { symbol xxx "-";  return sub}
        divid  = do { symbol xxx "/";  return divide}
        ltheq  = do { symbol xxx "<="; return leq}
        chareq = do { symbol xxx "="; return ceq}
        asg    = do { symbol xxx ":="; return assign}
        atP    = do { symbol xxx "@"; return atSign}
        blck   = do { try(symbol xxx "block"); return (\ pos es -> Block es)} 
        writ   = do { try(symbol xxx "write"); return write}
        iff    = do { try(symbol xxx "if"); return ifkey}
        whil   = do { try(symbol xxx "while"); return while}
        pairP  = do { try(symbol xxx "pair"); return pair}
        fstP   = do { try(symbol xxx "fst"); return fstC}
        sndP   = do { try(symbol xxx "snd"); return sndC}
        ispairP= do { try(symbol xxx "ispair"); return ispair}
        ischarP= do { try(symbol xxx "ischar"); return ischar}        
        raiseP = do { try(symbol xxx "raise"); return raise}        
        tryP   = do { try(symbol xxx "try"); return tryf}
        localP = do { try(symbol xxx "local")
                    ; let pair = do { s <- identifier xxx <?> "'local variable'"
                                    ; e <- expP
                                    ; return[Var s,e]}
                    ; vs <- parenS(do { ps <- many pair; return(concat ps)}) <?> "'local var-value list'"
                    ; return (local vs)}
        
                    
        
        
        
-- An expression is either an atom or a Lisp like parenthesized operation
expP = try atom <|> sexpr
  where atom = constant <|> charP <|> var
        var = 
          do { s <- identifier xxx; return(Var s)}
        constant = 
           do { n <- lexemE(number 10 digit)
              ; return (Int n)}
        sexpr  = 
           do { symbol xxx "(" 
              ; pos <- getPosition
              ; constrByList <- operatorP  -- Parse a string, get a lowercase constructor
              ; args <- many expP
              ; symbol xxx ")"
              ; return(constrByList pos args)}
        charP = do { c <- charLiteral xxx; return(Char c)}

defP = parenS ( global <|> local )
  where global =
           do { symbol xxx "global"
              ; v <- identifier xxx
              ; e <- expP
              ; return(GlobalDef v e)}
        local = 
           do { symbol xxx "fun"
              ; f <- identifier xxx
              ; vs <- parenS(many (identifier xxx))
              ; body <- expP
              ; return(FunDef f vs body)}
              
progP = do { ds <- parenS (many defP)
           ; e <- expP
           ; return(Prog ds e)}
         
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
        
-- This is an indenting pretty printer.
ppExp :: Exp -> PP.Doc
ppExp (Var v) = txt v
ppExp (Int n) = txt (show n)
ppExp (Char c) = txt (show c)
ppExp (Asgn v e )= txt "(:= " PP.<> PP.nest 3 (PP.sep [txt v , ppExp e PP.<> txt ")"])
ppExp (At f args)= txt "(@ " PP.<> PP.nest 3 (PP.sep (txt f : manyPP args))     
ppExp (While x y)= txt "(while " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (If x y z)= txt "(if " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y,ppExp z PP.<> txt ")"])
ppExp (Write x)= txt "(write " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Block es) = txt "(block " PP.<> PP.nest 3 (PP.sep ((map ppExp es)++ [txt ")"]))
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
ppExp (Try x hs) = txt "(try " PP.<> PP.nest 3 (PP.vcat (ppExp x : zap hs))
  where f (name,vs,body) = PP.parens(PP.sep (txt name : map txt vs ++ [ppExp body]))
        zap [] = [txt ")"]
        zap [x] = [f x PP.<> txt ")"]
        zap (x: xs) = f x : zap xs
ppExp (Raise f args)= txt "(raise " PP.<> PP.nest 3 (PP.sep (txt f : manyPP args))
ppExp (Tag s x) = PP.parens (txt s PP.<+> ppExp x)
ppExp (Local vs e) = txt "(local " PP.<> PP.nest 3 ( vars PP.$$ ppExp e PP.<> txt ")")
  where pairs = f vs
        f (x:y:zs) = (x,y): f zs
        f _ = []
        vars :: PP.Doc
        vars = PP.parens(PP.sep (map h pairs))
        h (x,y) = PP.sep [ppExp x,ppExp y]
        

ppDef (GlobalDef v e) = txt "(global " PP.<> PP.nest 3 (PP.sep [txt v, ppExp e PP.<> txt ")"])
ppDef (FunDef f args body) = 
  txt "(fun " PP.<> PP.nest 3 (PP.sep [txt f, PP.sep (map txt args),ppExp body PP.<> txt ")"])
  
ppProgram (Prog ds e) = 
  ( PP.parens (PP.vcat (map ppDef ds)))
  PP.$$
  (ppExp e)
    
plistf :: (a -> String) -> String -> [a] -> String -> String -> String
plistf f open xs sep close = open ++ help xs ++ close
  where help [] = ""
        help [x] = f x
        help (x:xs) = f x ++ sep ++ help xs    

plist = plistf id


prog_to_string instrs = showList instrs ""


isList (IntV 0) = Just []
isList (PairV x xs) = do { ys <- isList xs; return(x:ys)}
isList other = Nothing

instance Show Value where
  -- show (x@(PairV _ _)) | Just ys <- isList x = plist "[" (map show ys) "," "]"
  show (IntV n) = show n
  show (CharV c) = show c
  show (PairV x y) = "("++show x++"."++show y++")"
  show (Bad) = "<Bad>"

showEnv env = plistf f "" env ", " " "
  where f (name,value) = show name++"="++show value

instance (Show key,Show value) => Show (Table key value) where
  show (Tab xs) = showEnv xs
  
instance Show Exp where
  show x = PP.render(ppExp x)
           
instance Show Def where
  show x = PP.render(ppDef x)
  showList xs str = PP.render(txt str PP.$$ PP.vcat (map ppDef xs))

instance Show Program where
  show p = PP.render(ppProgram p)

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
                                                    ,ppStack (stack state)
                                                    ,ppHeap (heap state)])))
     ; writeIORef traceIndent (n+1)
     ; ans <- f state exp
     ; writeIORef traceIndent n
     ; putStrLn(PP.render(indent "< " PP.<> ppAns ans))
     ; return ans }

ppAns (Bad,Exception state f vs) = txt ("Exception "++f++plistf show " " vs " " "")
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

              
runFile filename = 
  do { putStrLn "\n********** PARSING ******************"
     ; (source@(Prog ds exp)) <- parseFile progP filename  -- this is a *.e3 file
     ; putStrLn ("Program:\n" ++ show source)
     ; putStrLn "\n******** LOADING DEFS **************"
     ; (funs,vars,state) <- elaborate True ds (emptyE,emptyE,state0)
     ; putStrLn "\n\n********** EXECUTING BODY **********"
     ; (v,state2) <- interpE funs vars state exp
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
                                  (do { pair <- interpE funs vars state exp
                                      ; state3 <- 
                                          case pair of
                                           (Bad,Exception s f vs) ->
                                              do { putStrLn("Uncaught exception: "++f++ plistf show " " vs " " "")
                                                 ; return s }
                                           (v,state2) -> do { putStrLn(show v); return state2}
                                      ; loop state3})
                                  (\ s -> do { putStrLn(show s); loop state})}               
     ; loop (ok state2) }
     
ok (State y z) = State y z
ok (Exception a b c) = a
     
main =
  do { args <- System.Environment.getArgs 
     ; case args of
        (x :xs) -> runFile x
        [] -> error "No command line argument specifying input file"
     }     

----------------------------------------------------------------------
-- Some very simple tests, requires some files 
-- like "primes.e2" "count.e2" and "lists.e3" in 
-- the current directory

-- Does the parser work
test1 = parseFile expP "../hw2/primes.e2"
test2 = do { x <- test1
           ; interpE emptyE 
                     (Tab [("n",HAddr 0),("p",HAddr 1),("d",HAddr 2),("m",HAddr 3)]) 
                     (deltaHeap (\ _ ->  [IntV 5,IntV 0,IntV 0,IntV 0]) state0)
                      x}
                      
test3 = parseFile expP "../hw2/count.e2"
test4 = do { prog <- test3
           ; interpE emptyE 
                     (Tab [("n",HAddr 0)])
                     (deltaHeap (\ _ ->  [(IntV 5)]) state0)
                     prog }
                     
test6 = runFile "lists.e3"



-- does the top level work

-- test4 = interp "count.e2"

test5 = parse2 expP "(for i i (block (:= i (+ i 2)) 10) (block (write i) (:= i (+ i 3))))"

test8 = run (parse2 expP "(+ (try (* 4 (raise f 99)) (@ f n 33)) 2)")
test9 = runFile "HW4Variants/sol4B.e4"

test10 = runFile "simpleExcept.e4"