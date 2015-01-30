{-#LANGUAGE    FlexibleInstances   #-}
module Main where

-- This files try various forms of parameter passing mechanisms
-- on heap based addresses.

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
  | Pair Exp Exp
  | Fst Exp
  | Snd Exp
  | Ispair Exp
  | Local [Exp] Exp
  
data Def 
  = GlobalDef Vname Exp
  | FunDef Fname [Vname] Exp

data Program = Prog [Def] Exp  

defName (GlobalDef v e) = v
defName (FunDef f vs e) = f

----------------------------------------------------
-- A Value is either an Int, or an Pair which is a 
-- an Addr which points at consectutive addresses
-- that store the Fst and Snd. (PairV 34) means the Fst
-- is at 34 in the heap, and the Snd is at 35 in the heap.

data Value 
     = IntV Int       -- An Int
     | PairV Addr     -- Or a pointer into the heap 
  deriving Show     

-- numeric operators are only defined if both inputs are integers.
numeric :: State -> String -> (Int -> Int -> Int) -> Value -> Value -> Value
numeric st name fun (IntV x) (IntV y) = IntV(fun x y)
numeric st name fun (v@(PairV _)) _ = error ("First arg of "++name++" is not an Int. "++showV (v,st))
numeric st name fun _ (v@(PairV _)) = error ("Second arg of "++name++" is not an Int. "++ showV (v,st))

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
pairLike name fun (PairV addr) = fun addr
pairLike name fun (IntV n) = 
  error ("function "++name++" is not passed a pair: "++ show n++".")


---------------------------------------------------------------
-- The State of the Machine consists of a Heap
-- The machine also uses two Tables mapping names to their bindings.

-- A table maps keys to values
data Table key object = Tab [(key,object)]
type Env a = Table String a  -- A Table where the key is a String

-- Operations on Env
emptyE = Tab []
extend key value (Tab xs) = Tab ((key,value):xs)
push pairs (Tab xs) = Tab(pairs ++ xs)

-- When searching an Env one returns a Result
data Result a = Found a | NotFound 

search :: Eq key => key -> [(key, a)] -> Result a
search x [] = NotFound
search x ((k,v):rest) = if x==k then Found v else search x rest

-- Search a Table
lookUp :: Eq key => Table key a -> key -> Result a
lookUp (Tab xs) k = search k xs

-- update a Table at a given key.
update n u ((m,v):rest) | n==m = (m,u):rest
update n u (r:rest) = r : update n u rest
update n u [] = error ("Unknown address: "++show n++" in update")

---------------------------------------
-- States and Heaps

type Heap = [Value]

-- State contains just a Heap
data State = State Heap 

-- Access the State for the Value at a given Address
access n (State heap) = heap !! n

-- Allocate a new location in the heap. Intitialize it
-- with a value, and return its Address and a new heap.
alloc :: Value -> State -> (Addr,State)
alloc value (State heap) = (addr,State (heap ++ [value]))
   where addr = length heap
                
-- Update the State at a given Adress
stateStore addr u (State heap) = State (update addr heap)
  where update 0 (x:xs) = (u:xs)
        update n (x:xs) = x : update (n-1) xs
        update n [] = error ("Address "++show addr++" too large for heap.")

-- A small heap as a test.

heap = h4
  where h1 = State []
        (_,h2) = alloc (IntV 3) h1
        (_,h3) = alloc (IntV 6) h2
        (_,h4) = alloc (IntV 1) h3
        
when True x = x
when False x = return ()

------------------------------------------------------------------
-- An interpretor for Exp
-- We store functions and variables in two different name spaces
-- functions in an   Env (Env Addr,[Vname],Exp)
-- variables in an   Env Addr
-- The values of variables are stored in the heap.

-- Interpret a single Exp
-- An intepretation might compute a new State (heap)
-- because a new variable might be allocated, or an
-- assignment might change what is stored at an address.

run x = interpE emptyE emptyE (State []) x

interpE :: Env (Env Addr,[Vname],Exp)  -- The function name space
        -> Env Addr                    -- the variable name space
        -> State                       -- the machine state, which is a heap
        -> Exp                         -- the Exp to interpret
        -> IO(Value,State)             -- (result,new_state)
interpE funs vars state exp = (traceG vars) -- this term: "(traceG vars)" enables tracing
                                            -- comment it out to get rid of tracing.
                              run state exp where
   run state (Var v) = 
     case lookUp vars v of
       Found addr -> return(access addr state,state)
       NotFound -> error ("Unknown variable: "++v++" in lookup.")
   
   run state (Int n) = return(IntV n,state)

   run state (Asgn v e ) = 
     do { (val,state2) <- interpE funs vars state e
        ; case lookUp vars v of
            Found addr -> return(val,stateStore addr val state2)
            NotFound -> error ("Unknown variable: "++v++" in assignment.") }             
   
   -- Call By Reference             
   run state (term@(At f args)) = 
     case lookUp funs f of
        NotFound -> error ("Unknown function: "++f++" in function call.")
        Found (vars2,formals,body) -> 
          do { when (length args /= length formals)
                    (error ("Wrong number of args to: "++f++" in: "++show term))
             ; let callByRef [] [] (env,state)  = return (env,state)
                   -- special case when arg is a variable
                   callByRef (n:ns) (Var x : es) (env,state) =
                     case lookUp vars x of
                       NotFound -> error ("Unknown variable "++x)
                       Found addr -> 
                         do { (env3,state3) <- callByRef ns es (env,state)
                            ; return(extend n addr env3,state3) }
                   -- special case when arg is a (fst e)
                   {- callByRef (n:ns) (Fst e:es) (env,state) = ... -}
                   -- special case when arg is a (snd e)                   
                   {- callByRef (n:ns) (Snd e:es) (env,state) = ...  -}
                   -- case when arg is not a var, we must
                   -- create an address by allocating on the heap
                   callByRef (n:ns) (e:es) (env,state) =
                     do { (v,state2) <- interpE funs vars state e
                        ; let (adr,state3) = alloc v state2
                        ; (env4,state4) <- callByRef ns es (env,state3)
                        ; return(extend n adr env4,state4)}
             ; (vars3,state3) <- callByRef formals args (vars2,state)
             ; interpE funs vars3 state3 body}
                                      
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
        ; putStrLn (showV (v1,state1))
        ; return(v1,state1)}

   run state (Block es) = 
     do { let last [] = (IntV 0)  -- empty block returns 0
              last [x] = x
              last (x:xs) = last xs
        ; (vs,state2) <- interpList funs vars state es
        ; return(last vs,state2)}

   run state (Add  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric state2 "+" (+) v1 v2,state2) }

   run state (Sub  x y) =
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric state2 "-" (-) v1 v2,state2) }      

   run state (Mul  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric state2 "*" (*) v1 v2,state2) }   

   run state (Div  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric state2 "/" (div) v1 v2,state2) }   

   run state (Leq  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric state2 "<=" (\ x y -> boolToInt(x <= y)) v1 v2,state2) }        

   run state (Pair x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; let (a1,state3) = alloc v1 state2  -- Allocate consequtive locations
              (a2,state4) = alloc v2 state3  -- for v1 and v2
        ; return(PairV a1,state4)}           -- return the PairV of the first address

   run state (Fst x)    = 
     do { (v1,state1@(State xs)) <- interpE funs vars state x
        ; let getfirst addr = xs !! addr
        ; return(pairLike "fst" getfirst v1,state1)}

   run state (Snd x)    = 
     do { (v1,state1@(State xs)) <- interpE funs vars state x
        ; let getsnd addr = xs !! (addr+1)
        ; return(pairLike "snd" getsnd v1,state1)}   

   run state (Ispair x) = 
     do { (v1,state1) <- interpE funs vars state x
        ; case v1 of
            (PairV _) -> return(IntV(boolToInt True),state1)
            other -> return(IntV(boolToInt False),state1)}

   run state (Local pairs body) = 
     do { let split (Var v : e : zs) (vs,es) = split zs (vs++[v],es++[e])
              split _ (vs,es) = (vs,es)
              (vs,es) = split pairs ([],[])
        ; (vals,state2) <- interpList funs vars state es 
        ; let (pairs,state3) = bind vs vals state2  
        ; interpE funs (push pairs vars) state3 body }
         

bind:: [String] -> [Value] -> State -> ([(Vname,Addr)],State)
bind names objects state = loop (zip names objects) state
  where loop [] state = ([],state)
        loop ((nm,v):more) state = ((nm,ad):xs,state3)
          where (ad,state2) = alloc v state
                (xs,state3) = loop more state2
                
-- interpret a list from left to right. Be sure the
-- state is updated for each element in the list.

interpList funs vars state [] = return([],state)
interpList funs vars state (e:es) = 
  do { (v,state1) <- interpE funs vars state e
     ; (vs,state2) <- interpList funs vars state1 es
     ; return(v:vs,state2)}

-- elab:: Def -> (Env (Stack,[Vname],Exp),Env Address,State) -> IO (Env (Stack,[Vname],Exp),Env Address,State)
elab (FunDef f vs e) (funs,vars,state) =
  return ( extend f (vars,vs,e) funs, vars, state )
elab (GlobalDef v e) (funs,vars,state) =
  do { (value,state2) <- interpE funs vars state e
     ; let (addr,state3) = alloc value state2
     ; return(funs, extend v addr vars,state3)}

elaborate loud [] ts = return ts
elaborate loud (d:ds) ts = 
  do { when loud (putStr (defName d++" "))
     ; ts1 <- elab d ts
     ; elaborate loud ds ts1}
                                     
--------------------------------------------------------------------------
-- A parser that reads a file and produces a program in abstract syntax
-- Most of this section is boilerplate
-- The interesting functions are "operatorP" and "expP"

-- A Exp is either a an Atom or a listlike thing like: (tag x1 x2 ... xn)
-- Depending upon the "tag" a different number of xi are expected.
-- We parse tag to a LOWER CASE CONSTRUCTOR (see below) by using "operatorP",
-- and then apply it to a list [p1 p2 ... pn] where the pi
-- are the result of parsing the xi with "expP". When parsing if too many, 
-- or too few arguments, are parsed then "report" an error.

report:: SourcePos -> Int -> Int -> String -> a
report pos actual expected message 
  | actual < expected = error ("Near "++show pos++"\noperator '"++message++"' is given too few arguments.")
  | otherwise = error ("Near "++show pos++"\noperator '"++message++"' is given too many arguments.")  

-- There is one LOWER CASE CONSTRUCTORS for each Exp constructor (Var, Int, Asgn, etc).
-- The constructors of Exp are lifted to take a position (for error reporting)
-- and a list of arguments. Thus every "lowercase" constructor has type: 
--     SourcePos -> [ Exp ] -> Exp
-- If one is given the wrong number of arguments an error is "report"ed,
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

-- Asgn is special because its first argument must be a variable!!
assign pos [Var x,y] = Asgn x y
assign pos [x,y] = error ("Near "++show pos++"\nfirst argument to ':=' is not a variable.")
assign pos args = report pos (length args) 2 ":="

local vs pos [x] = Local vs x
local vs pos args = report pos (length args) 1 "local"

setfst pos [x,y] = error "\nYou need to define setfst"
setfst pos args = report pos (length args) 2 "setfst"

setsnd pos [x,y] = error "\nYou need to define setsnd"
setsnd pos args = report pos (length args) 2 "setsnd"

  
-- This function parses a string, but returns a function with type: 
-- SourcePos -> [Exp] -> Exp    See "lowercase" constructors above.
-- There are many cases, one for each of the legal constructors to Exp.
-- To add to the parser, write a new function "f" then add " <|> f "
-- to the definition of "operatorP"

operatorP = plus <|> times <|> minus <|> divid <|> ltheq <|> asg <|> atP <|>
            blck <|> writ <|> iff <|> whil <|>
            pairP <|> fstP <|> sndP <|> ispairP <|>
            localP <|> setsndP <|> setfstP
  where plus   = do { symbol xxx "+";  return add}
        times  = do { symbol xxx "*";  return mul}
        minus  = do { symbol xxx "-";  return sub}
        divid  = do { symbol xxx "/";  return divide}
        ltheq  = do { symbol xxx "<="; return leq}
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
        setfstP= do { try(symbol xxx "setfst"); return setfst}
        setsndP= do { try(symbol xxx "setsnd"); return setsnd}
        localP = do { try(symbol xxx "local")
                    ; let pair = do { s <- identifier xxx <?> "'local variable'"
                                    ; e <- expP
                                    ; return[Var s,e]}
                    ; vs <- parenS(do { ps <- many pair; return(concat ps)}) <?> "'local var-value list'"
                    ; return (local vs)}
        
        
-- An expression is either an atom or a Lisp like parenthesized operation or a local.
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
              ; constrByList <- operatorP  -- Parse a string, get a lowercase constructor
              ; args <- many expP
              ; symbol xxx ")"
              ; return(constrByList pos args)}
     

-- Parse a Def
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

-- Parse a Prog              
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

-- This is an indenting pretty printer.
ppExp :: Exp -> PP.Doc
ppExp (Var v) = txt v
ppExp (Int n) = txt (show n)
ppExp (Asgn v e )= txt "(:= " PP.<> PP.nest 3 (PP.sep [txt v , ppExp e PP.<> txt ")"])
ppExp (At f args)= txt "(@ " PP.<> PP.nest 3 (PP.sep (txt f : many args))
  where many [] = [txt ")"]
        many [x] = [ppExp x PP.<> txt ")"]
        many (x:xs) = ppExp x : many xs
ppExp (While x y)= txt "(while " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (If x y z)= txt "(if " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y,ppExp z PP.<> txt ")"])
ppExp (Write x)= txt "(write " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Block es) = txt "(block " PP.<> PP.nest 3 (PP.sep ((map ppExp es)++ [txt ")"]))
ppExp (Add  x y)  = txt "(+ " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Sub  x y)  = txt "(- " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Mul  x y) = txt "(* " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Div  x y)  = txt "(/ " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Leq  x y) = txt "(<= " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Pair x y) = txt "(pair " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Fst x) = txt "(fst " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Snd x) = txt "(snd " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Ispair x) = txt "(ispair " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])

ppExp (Local vs e) = txt "(local " PP.<> PP.nest 3 ( vars PP.$$ ppExp e PP.<> txt ")")
  where pairs = f vs
        f (x:y:zs) = (x,y): f zs
        f _ = []
        vars :: PP.Doc
        vars = PP.parens(PP.sep (map h pairs))
        h (x,y) = PP.sep [ppExp x,ppExp y]


ppDef (GlobalDef v e) = txt "(global " PP.<> PP.nest 3 (PP.sep [txt v, ppExp e PP.<> txt ")"])
ppDef (FunDef f args body) = 
  txt "(fun " PP.<> PP.nest 3 (PP.sep [txt f, PP.parens(PP.sep (map txt args)),ppExp body PP.<> txt ")"])
  
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

instance Show State where
  show (s@(State hp)) =  plistf f "" hp " " " ."
    where f x = showV (x,s)
    
prog_to_string instrs = showList instrs ""

instance Show Exp where
  show x = PP.render(ppExp x)
           
instance Show Def where
  show x = PP.render(ppDef x)
  showList xs str = PP.render(txt str PP.$$ PP.vcat (map ppDef xs))

instance Show Program where
  show p = PP.render(ppProgram p)

showV:: (Value,State) -> String
showV (IntV n,state) = show n
showV (PairV addr,state) = "("++showV(get addr,state)++"."++showV(get (addr+1),state)++")@"++show addr
  where get n = xs !! n where (State xs) = state

showEnv:: Env Addr -> State -> [PP.Doc]
showEnv (Tab env) (state@(State xs)) = loop env
  where loop [] = [txt " "]
        loop [x] = [txt (f x),txt " "]
        loop (x:xs) = (txt (f x)): (txt " "): loop xs
        f (name,addr) = name++"@"++show addr++"="++showV(xs !! addr,state)


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

instance Pretty [Char] where
  pp str = txt str

instance Pretty Int where
  pp x = txt(show x)
  
instance Pretty State where
  pp x = txt(show x)


------------------------------------------------------------
-- This is for tracing the interpreter

-- Boolean flag for tracing.
trace_on = unsafePerformIO (newIORef False)

-- typing "trace" at the GHCI prompt or within the READ EVAL PRINT
-- loop flips the tracing flag.
trace = do { b <- readIORef trace_on
           ; writeIORef trace_on (not b)
           ; let f True = "on"
                 f False = "off"
           ; putStrLn ("\nTracing is "++f (not b)++".")}

-- Keeps track of the indentation of the tracer
traceIndent = unsafePerformIO (newIORef 0)

type InterpType = State -> Exp -> IO (Value,State)

traceF :: Env Addr -> InterpType -> InterpType 
traceF env f state exp =
  do { n <- readIORef traceIndent
     ; let indent x = txt(concat(replicate n " |")++x)
     ; putStrLn(PP.render(indent "> " PP.<> PP.fsep (pp exp : showEnv env state)))
     ; writeIORef traceIndent (n+1)
     ; ans <- f state exp
     ; writeIORef traceIndent n
     ; putStrLn(PP.render(indent "< " PP.<> txt(showV ans)))
     ; return ans }

-- Like traceF if tracing is on, like f if not.
traceG :: Env Addr -> InterpType -> InterpType 
traceG env f vars exp = 
  do {  b <- readIORef trace_on
     ; if b then traceF env f vars exp else f vars exp }

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
     ; (funs,vars,state) <- elaborate True ds (emptyE,emptyE,State [])
     ; putStrLn "\n\n********** EXECUTING BODY **********"
     ; (v,state2) <- interpE funs vars state exp
     ; putStrLn(showV (v,state2))
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
                                  (do { (v,state2) <- interpE funs vars state exp
                                      ; putStrLn(showV (v,state2))
                                      ; loop state2 })
                                  (\ s -> do { putStrLn(show s); loop state})}               
     ; loop state2 }
     
     
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
test3 = parseFile expP "../hw2/count.e2"
test6 = parseFile progP "lists.e3"

test7 = do { x <- test3 ; interpE emptyE (Tab [("n",0)]) (State [(IntV 5)]) x }
test8 = do { x <- test1 
           ; interpE emptyE 
                     (Tab [("n",0),("p",1),("d",2),("m",3)]) 
                     (State [(IntV 0),(IntV 0),(IntV 0),(IntV 0)])
                     x }

test9 = runFile "lists.e3"

test10 = runFile "../hw3/test.e3"

test11 = runFile "../hw3/solutions/sol3A.e3"


