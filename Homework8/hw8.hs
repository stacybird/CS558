{-#LANGUAGE    FlexibleInstances   #-}
module Main where

-- These imports are for defining parsers
import Text.Parsec hiding (State,Column)
import Text.Parsec.Expr(Operator(..),buildExpressionParser) 
import Text.Parsec.Prim(getInput)
import Text.Parsec.Token hiding (natural)
import Text.Parsec.Pos(SourcePos,sourceName,sourceLine,sourceColumn,newPos)
import Data.Functor.Identity(Identity(..))
import Data.Char(digitToInt,isUpper)
import qualified Control.Exception
import Control.Monad(when)

-- These are used for tracing the stack machine
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO.Unsafe(unsafePerformIO)
import System.IO(fixIO)
import Data.List(union,(\\))


-- This import is for getting command line arguments
import System.Environment(getArgs)

-- This import is for indenting pretty printing
import qualified Text.PrettyPrint.HughesPJ as PP

----------------------------------------------------------------------------
-- An Object oriented language

-- Type synonyms
type Name = String
type Addr = Int   -- Address of a location in the Heap

--------- Syntax

data Exp 
  = Var SourcePos Name       
  
  | Bool SourcePos Bool    -- Literal objects
  | Int  SourcePos Int
  | String SourcePos String
  
  | While Exp Exp          -- Control structures
  | Write String Exp
  | Block [Exp]
  | If Exp Exp Exp         -- (if x y z) --> (x.ifTrueFalse y z)
  | Asgn Exp Exp           -- Only to Var not Def.
  
  | Apply Exp [Exp]        -- (Apply x y z) ---> (Request x "apply" y z)
  | Lam [Name] Exp         -- (\ ( a b c) e)   this object has one method: apply

  | Local              [Decl] Exp 
  | ObjLit (Maybe Exp) [Decl] (Maybe Exp)
  | Request Exp Name [Exp] -- (exp.field e1 e2 e3) set a handler for field.

  | Return String Exp      -- (return f x) return from the enclosing method f

  | Self SourcePos
  | Done SourcePos
  | EmptyObj SourcePos
  | Super SourcePos
  | Op String [Exp]        -- (+ 4 5 6 7) --> (((4.+ 5).+ 6).+ 7)


data Assoc = L | R | Non

data Decl
  = MethodDecl Name [Name] Exp
  | DefDecl Name Exp
  | VarDecl Name (Maybe Exp)
  | DataDecl SourcePos Name [String] [(Name,[Name])]  
  | AssocDecl Name Assoc

-------------------------------------------------------------
-- Environments

data Env = Env { self:: Object, vars::[(Name,Binding)], assoc:: [(String,Assoc)]}

data Binding = Val Object | Ref Addr | Action Code | Ass Assoc

data Code 
  = Prim ([Object] -> State -> IO(Object,State))
  | Closure Name (Maybe Object) Env [Name] Exp
  
--------------------------------------------------
-- Semantic objects

data Value = DoneV | BoolV Bool | IntV Int | StringV String | ExceptV Name
     deriving (Eq,Ord)

data Object = Obj{ value::(Maybe Value)
                 , fields::[(Name,Binding)]
                 , super:: (Maybe Object)}
            | Thunk Name (State -> IO(Object,State))

--------------------------------------------------------------
-- Free variables and minimizing bindings in closures.

unionL xs = foldr union [] xs  
varsOf (Var p x) = [x]
varsOf (Int p n) = []
varsOf (Bool p b) = []
varsOf (String p s) = []
varsOf (While y z) = unionL[varsOf y,varsOf z]
varsOf (Local [] e ) = varsOf e
varsOf (Local ds e) = ((union (varsOf e) (varsDecl ds)) \\ introduced)
  where introduced = namesDecl ds

varsOf (Write s e) = varsOf e
varsOf (Block xs) = unionL (map varsOf xs)
varsOf (If x y z) = unionL[varsOf x,varsOf y,varsOf z]
varsOf (Asgn y z) = unionL[varsOf y,varsOf z]
varsOf (Apply x xs) = unionL (map varsOf (x:xs))
varsOf (Lam vs exp) = varsOf exp \\ vs
varsOf (ObjLit Nothing ds Nothing) = varsDecl ds
varsOf (ObjLit (Just i) ds Nothing) = union (varsOf i) (varsDecl ds)
varsOf (ObjLit Nothing ds (Just i)) = union (varsDecl ds) (varsOf i)
varsOf (ObjLit (Just x) ds (Just y)) = unionL[varsOf x,varsDecl ds, varsOf y]

varsOf (Request x field xs) = unionL (map varsOf (x:xs))
varsOf (Return s e) = varsOf e
varsOf (Self p) = [] 
varsOf (Done p) = [] 
varsOf (EmptyObj p) = [] 
varsOf (Super p) = [] 
varsOf (Op s xs) = unionL (map varsOf xs)

dname (MethodDecl nm vs body) = [nm]
dname (DefDecl nm exp) = [nm]
dname (VarDecl nm mexp) = [nm]
dname (AssocDecl nm a) = []

addD (MethodDecl nm vs body) = varsOf body \\ vs
addD (DefDecl nm exp) = varsOf exp
addD (VarDecl nm Nothing) = []
addD (VarDecl nm (Just exp)) = varsOf exp
addD (AssocDecl _ _) = []

namesDecl ds = (foldr (\ x ans -> union (dname x) ans) [] ds)
varsDecl ds = (foldr (\ x ans -> union (addD x) ans) [] ds)

ext :: Env -> [(Name,Binding)] -> Env
ext env [] = env
ext env ((nm,Ass x):more) = ext (env{assoc=(nm,x):(assoc env)}) more
ext env (x:more) = env2{vars= x:(vars env2)} where env2 = ext env more

squash e env = (env{vars=(used vs (vars env))})
  where vs = varsOf e
        used vs [] = []
        used vs ((p@(nm,_)):more) | elem nm vs = p : used (vs \\ [nm]) more
        used vs (m : more) = used vs more
        
----------------------------------------------------



            
except name = Obj (Just(ExceptV name)) [] Nothing            
  
-- State is a Heap or an Exception handler (for Return)
data State = State{ depth:: Int, heap:: Heap }
           | Exception State Name Object

type Heap = [Object]

---------------------------------------
-- Thunks to implement recursive bindings

-- Trace through Thunks until a non-thunk is found    
pull :: (Object,State) -> IO(Object,State)
pull (Thunk nm f,state1) = do { (v,state2) <- f state1; pull (v,state2)}
pull (v,state) = return(v,state)

-- Create a lazy thunk
memoize:: (State -> IO(Object,State)) -> IO (State -> IO(Object,State))
memoize f = do { ref <- newIORef Nothing; return(g ref)}
  where g ref s = 
          do { mv <- readIORef ref
             ; case mv of 
                Nothing -> do { (v,s2) <- f s; writeIORef ref (Just v); return(v,s2)}
                Just v -> return(v,s)}
                
-- Trace deeply, pulling on the shallowest thunks
zonk :: Object -> State -> IO(Object,State)
zonk (Thunk nm f) state = do { pair <- f state; pull pair } -- (obj,st2) <- pull pair; zonk obj st2 }
zonk (Obj prim ms (Just super)) s0 =
  do { (super1,s1) <- zonk super s0
     ; (ms2,st2) <- thread acc ms s1
     ;return(Obj prim ms2 (Just super1),st2)}
zonk (Obj prim ms Nothing) state =
  do { (ms2,st2) <- thread acc ms state
     ;return(Obj prim ms2 Nothing,st2)}

     
acc (name,Val x) st = 
  do { (x2,s2) <- zonk x st
     ; return((name,Val x2),s2)}
acc (name,Ref addr) st = 
  do { (x2,s2) <- zonk (access addr st) st
     ; return((name,Val x2),updateSt addr x2 s2)}     
acc x st = return(x,st)     
                     

initialize :: State -> [(Name,Binding)] -> IO([(Name,Binding)],State)
initialize state env = thread acc env state 
  where acc (nm,Val obj) st = 
          do { (v,st1) <- pull (obj,st); return((nm,Val v),st1)}
        acc (nm,Ref addr) st = 
          do { (v,st1) <- pull(access addr st,st); return((nm,Ref addr),st1)}
        acc (nm,Ass x) st = return((nm,Ass x),st)
        acc (nm,Action(Closure t Nothing env fs exp)) st
          = return((nm,Action(Closure t Nothing (squash exp env) fs exp)),st)
         
        acc (nm,Action code) st = return((nm,Action code),st)

-------------------------------------------------------------
-- evaluate a list of (Name,Binding) pairs.

evalRec
  :: Maybe Object
     -> ([(Name, Binding)] -> Env)
     -> [Decl]
     -> ([(Name, Binding)], State)
     -> ([(Name, Binding)], State)
     -> IO ([(Name, Binding)], State)
evalRec selfstub extendenv [] (bs,st0) loop = return (reverse bs,st0)
evalRec selfStub extendenv (MethodDecl name formals body : more) (bs,s0) (loop@(~(allBs,zzz)))  = 
    evalRec selfStub extendenv more 
           ((name,Action(Closure name selfStub (squash body (extendenv allBs)) formals body)):bs,s0)
           loop
evalRec selfStub extendenv (d@(DefDecl name body: more)) (bs,s0) (loop@(~(allBs,zzz))) = 
    do { comp <- memoize (eval (squash body (extendenv allBs)) body)
       ; evalRec selfStub extendenv more ((name,Val(Thunk name comp)):bs,s0) loop }
evalRec selfStub extendenv (VarDecl name mexp:more) (bs,s0) (loop@(~(allBs,zzz))) = 
   do { thunk <- case mexp of
                   Nothing -> return done
                   Just exp -> do { comp <- (memoize(eval (squash exp (extendenv allBs)) exp))
                                  ; return(Thunk name comp)}
      ; let (addr2,s1) = allocate [thunk] s0
      ; evalRec selfStub extendenv more ((name,Ref addr2):bs,s1) loop }
evalRec selfStub extendenv (AssocDecl nm x:more) (bs,s0) loop = 
   evalRec selfStub extendenv more ((nm,Ass x):bs,s0) loop
evalRec selfStub extendenv ((d@(DataDecl p tn args cls)): more) (bs,s0) loop =
  evalRec selfStub extendenv (dataToObject d : more) (bs,s0) loop   
  

---------------------------------------------------
-- expanding a DataDecl to an object

dataToObject (DataDecl pos tn args cls) = 
      (DefDecl tn (ObjLit Nothing (map choosedecl cls) Nothing))
  where choosedecl (cname,[]) = (DefDecl cname (ObjLit Nothing (preds cname) Nothing))
        choosedecl (cname,fields) =
           (MethodDecl cname (take (length fields) names) 
                             (ObjLit Nothing (zipWith g fields [0..] ++ preds cname) Nothing))
        preds cname = [MethodDecl "?" ["x"] (Request (Var pos "x") "=" [String pos cname])]
        g nm i = (DefDecl nm (Var pos (names !! i)))

names = map (:[]) "abcdefghijklmnopqrstuvwxyz"

---------------------------------------
-- Operations on States and Heaps

state0 = (State 2 [])

exceptional (Exception _ _ _) = True
exceptional _ = False

setDepth:: (Int -> Int) -> State -> State
setDepth f st = st{depth = f (depth st)}

-- Access the State for the Value at a given Address
access n st = (heap st) !! n 
   -- if n < length heap then heap !! n else error("Heap address too large: "++show n)

updateSt :: Addr -> Object -> State -> State
updateSt addr u st = st{heap = (update addr (heap st))}
  where update 0 (x:xs) = (u:xs)
        update n (x:xs) = x : update (n-1) xs
        update n [] = error ("Address "++show addr++" too large for heap.")

-- Allocate "n" new locations in the heap. Intitialize it
-- with the list of values "v", and return the first of
-- "n" consecutive addresses, and new heap.   
allocate :: [Object] -> State -> (Addr,State)
allocate [] st = 
  (error "pull on address of nullary constructor",st)
allocate vs st = (addr,st{heap = (heap st)++ vs})
   where addr = length (heap st)

extract (State depth y) = State depth y
extract (Exception a b c) = extract a

------------------------
-- Operations on environments

assoc0 = [("+",L),("-",L),("*",L),("/",L),("++",R)]

associativity s env = 
  case lookup s (assoc env) of
    Just t -> t
    Nothing -> Non
    
associateToThe L xs s = foldl1 (\ e1 e2 -> Request e1 s [e2]) xs
associateToThe R xs s = foldr1 (\ e1 e2 -> Request e2 s [e1]) xs
associateToThe Non [x,y] s = (Request x s [y])
associateToThe Non xs s = 
   error(show (locL loc xs)++
         "\nNon associative operator: "++s++
         "\ndoesn't have exactly two operands.")
         
t6 = associateToThe R [Int noPos 4,Int noPos 7,Int noPos 9] "++"         

-- This defines the derived forms

derive env (Lam formals body) = 
  Local [MethodDecl "lam" formals body] (Var (loc body) "lam")
derive env (If b x y) = (Request b "ifTrueFalse" [derive env (Lam [] x),derive env(Lam [] y)])
derive env (While tst body) =
  let p = posAdd (loc tst) (loc body)
  in Local [MethodDecl "loop" [] 
              (derive env 
                  (If tst 
                      (Block [body,derive env (Apply (Var p "loop") [])])
                      (Done p)))] 
           (derive env (Apply (Var p "loop")[]))
derive env (Op s es) = associateToThe (associativity s env) es s    
derive env (Apply e1 es) = (Request e1 "apply" es)
derive env (EmptyObj p) = ObjLit Nothing [] Nothing
derive env x = error("\nThe expression\n   "++show x++"\nhas no derived form.")

   
-------------------------------------------------------
-- Primitive Semantic Objects

showArgs depth args = plistf (showObj state0) "" args ", " ""

-- these functions build methods

eqMethod :: Value -> (String, Binding)
eqMethod x = ("=",Action(Prim(\ xs st -> return(makeBool(primEq x xs),st))))
  where primEq x ((Obj (Just y) _ super):more) = x==y
        primEq x obs = False
        
leMethod :: Value -> (String, Binding)
leMethod x = ("<=",Action(Prim(\ xs st -> return(makeBool(primLE x xs),st))))
  where primLE x ((Obj (Just y) _ super):more) = x <= y
        primLE x obs = False        

asString :: String -> (String,Binding)
asString result = ("asString",Action(Prim f))
  where f [] s = return(makeString(result),s)
        f xs s = error("Illegal args to 'asString'\n   "++showArgs 2 xs)

intOp n name oper unit = (name,lift n name oper unit)
        
-- Build a left associative method
-- (+ 3 4 5 6) --> (+ 7 5 6) --> (+ 11 6) --> (+ 17) -> 17
lift:: Int -> String -> (Int -> Int -> Int) -> Int -> Binding
lift n nm f unit = Action(Prim (g n))
   where g n [] s = return(makeInt (f n unit),s)
         g n [Obj (Just (IntV m)) ms sup] s = return(makeInt (f n m),s)
         g n (Obj (Just (IntV m)) ms sup : more) s = g (f n m) more s
         g n (t@(Thunk _ _): more) s =
           do { (v,s1) <- pull (t,s); g n (v:more) s1}
         g n xs s0 = error("Illegal args to method '"++nm++"'\n  "++showArgs 0 xs)

----------------------------
-- Creating primitive objects

makeInt :: Int -> Object
makeInt n = Obj (Just (IntV n)) 
                [intOp n "+" (+) 0,intOp n "*" (*) 1,
                 intOp n "-" (-) 0,intOp n "/"  div 1,
                 asString (show n),eqMethod (IntV n),leMethod (IntV n)]
               Nothing
  where f name (oper,unit) = (name,lift n name oper unit)
  
makeString:: String -> Object
makeString x = self
  where self = Obj (Just(StringV x)) fields Nothing
        fields = [("sub",sub),("at",at),("++",app),("len",len)
                 ,eqMethod (StringV x),asString x,leMethod (StringV x)]
        sub = Action(Prim f)
            where f [Obj (Just (IntV i)) ms _,Obj (Just (IntV j)) ns _] st0 = 
                      return(makeString (take (j-i) (drop i x)),st0)
                  f xs s0 = error("Illegal args to method 'substring'\n  "++showArgs 0 xs)
        at = Action(Prim f)
            where f [Obj (Just (IntV i)) ms _] s0 = return(makeString (take 1 (drop i x)),s0)
                  f xs s0 = error("Illegal args to method 'at'\n  "++showArgs 0 xs)
        -- right assoc (++) (++ a b c) = (++ a (++ b c))
        app = Action(Prim (\ xs st -> return(makeString(f x xs),st)))
            where f x [] = x
                  f x [Obj (Just (StringV i)) ms _] = i ++ x
                 -- f x (Obj (Just (StringV i)) ms: ys) = (f i ys) ++ x
                  f x xs = error("Illegal args to method '++'\n  "++showArgs 0 xs)   
        len = Action(Prim (\ xs st -> return(makeInt (length x),st)))
              
done = (Obj (Just DoneV) [(asString "done")]) Nothing
  
trueObj = Obj (Just(BoolV True)) 
              [("ifTrueFalse",ifTF),(asString "False"),eqMethod (BoolV True)]
              Nothing
  where ifTF = Action(Prim f)
           where f [obj1,obj2] st = request obj1 "apply" [] st
                 f xs st = error("Illegal args to method 'ifTrueFalse'\n  "++showArgs 0 xs)
                 
falseObj = Obj (Just(BoolV False)) 
               [("ifTrueFalse",ifTF),(asString "False"),eqMethod (BoolV False)]
               Nothing
  where ifTF = Action(Prim f)
           where f [obj1,obj2] st = request obj2 "apply" [] st
                 f xs st = error("Illegal args to method 'ifTrueFalse'\n  "++showArgs 0 xs)   

makeBool b = if b then trueObj else falseObj                 

hasAsString (Obj _ fields super) = 
  case lookup "asString" fields of { Nothing -> False; (Just _) -> True}
hasAsString _ = False

-------------------------------------------------------
-- The evaluator

passOn (state@(Exception st n obj)) = return(except n,state)
      
eval:: Env -> Exp -> State -> IO(Object,State)
eval env exp state | exceptional state  = passOn state
eval env exp state = (traceG env) run exp state where
   run (Var pos v) state = 
      case lookup v (vars env) of
        Nothing -> error("Unknown variable: "++v)
        Just (Ref addr) -> return(access addr state,state)
        Just (Val obj) -> return(obj,state)
        Just (Action code) -> 
             return(Obj Nothing [("apply",Action code)] Nothing,state)
   run (Bool pos b) state = return(if b then trueObj else falseObj, state)
   run (Int pos n) state = return(makeInt n,state)
   run (String pos n) state = return(makeString n,state)
   run (While tst body) state = eval env (derive env (While tst body)) state        
         
   run (Write message exp) state = 
      do { (obj,st1) <- eval env exp state
         ; putStrLn (message++showObj state0 obj)
         ; return(done,st1)}
   run (Block []) state = return(done,state)
   run (Block exps) state = 
     do { (objL,st1) <- thread (eval env) exps state
        ; return(last objL,st1)}               
   run (Asgn e1 e2) state = 
      do { (addr,st1) <- lvalue env e1 state
         ; (obj,st2) <- eval env e2 st1
         ; return(obj,updateSt addr obj st1)} 

   run (Local ds body) state =
      do { (bindings,state1) <- fixIO (evalRec (Just (self env))
                                               (ext env)
                                               ds ([],state))
         ; (bindings2,state2) <- initialize state1 bindings
         ; eval (ext env bindings2) body state2}

   run (ObjLit parent ms init) state = 
     do { (val,inheritedms,super,st0) <- 
             case parent of
               Nothing -> return(Nothing,[],Nothing,state)
               Just p -> do { (super,st0) <- eval env p state >>= pull
                            ; return(value super,fields super,Just super,st0)}

        ; let extend allBs = env{self=(Obj val (allBs ++ inheritedms) super)}
        ; (allBs,st1) <- fixIO (evalRec Nothing extend ms ([],st0))
        ; let selfObj = Obj val (allBs ++ inheritedms) super

        ; (_,st2) <- 
              case init of
                Just x -> eval (env{self=selfObj}) x st1
                Nothing -> return(done,st1)
        ; return(selfObj,st2)}   
   run (Request exp mname args) state =
      do { (obj,state2) <- eval env exp state
         ; (obList,state3) <- thread (eval env) args state2
         ; request obj mname obList state3 }
   run (Return s exp) state = 
      do { (obj,st1) <- eval env exp state
         ; return(except s,Exception st1 s obj)}
   run (Self pos) state = return(self env,state)
   run (Done pos) state = return(done,state)  
   run (Super pos) state = 
      case super(self env) of 
        Just obj -> return(obj,state)
        Nothing -> error(show pos++"\nThe current object (self) has no super class.")
      
   run (Lam formals body) state = eval env (derive env (Lam formals body)) state
   run (Apply e1 es) state = eval env (derive env (Apply e1 es)) state 
   run (Op s es) state = eval env (derive env (Op s es)) state
   run (If b x y) state = eval env (derive env (If b x y)) state   
   run (EmptyObj pos) state = eval env (derive env (EmptyObj pos)) state
--   run x state = error("NOT YET IN RUN "++show x)   
                           
-------------------------------------------
-- evaluation helper functions

thread:: (a -> State -> IO(b,State)) -> [a] -> State -> IO([b],State)
thread f xs state | exceptional state = return([],state)
thread f [] state = return([],state)
thread f (x:xs) state = 
  do { (y,st1) <- f x state
     ; (ys,st2) <- thread f xs st1
     ; return(y:ys,st2)}                       

lvalue :: Env -> Exp -> State -> IO (Addr, State) 
lvalue env exp state | exceptional state = return(0,state)
lvalue env (Var pos v) state =
   case lookup v (vars env) of
     Just (Ref addr) -> return(addr,state) 
     Just (Val obj) -> error ("Val (rather than Ref) as l-value in assignment: "++v)
     Nothing -> error ("Unknown variable as l-value in assignment: "++v)
     
lvalue env (Request e1 name []) state =
   do { pair <- eval env e1 state >>= pull
      ; let test (_,st) | exceptional st = return(0,st)
            test (Obj _ methods sup,st0) =
              case lookup name methods of
                  Nothing -> error ("Unknown method in assignment: "++name)
                  Just (Ref addr) -> return(addr,st0)
                  Just (Val _) -> error("Attempt to assign to definition: "++name)
                  Just (Action _ ) -> error("Attempt to assign to method: "++name)
      ; test pair} 
lvalue env e1 state = error("Assignment to non-lvalue\n   "++show e1)      

request:: Object -> Name -> [Object] -> State -> IO (Object, State)
request self mname args s0 | exceptional s0 = passOn s0
request (x@(Thunk _ _)) mname args s0 = do { (y,s1) <- pull (x,s0); request y mname args s1 }
request (self@(Obj _ methods sup)) mname args s0 =
 case (lookup mname methods) of
             (Nothing) -> error ("Message not understood: "++mname++"\n   "++showObj s0 self)
             (Just field) -> requestObjField mname field self args s0

          
requestObjField:: Name -> Binding -> Object -> [Object] -> State -> IO(Object,State)                        
requestObjField name d self args st | exceptional st = passOn st
requestObjField name (Val x) self [] state = return(x,state)
requestObjField name (Action (Prim f)) selfV args state = f args state
requestObjField name (Action (Closure yyy static env [] body)) selfV [] state =
    do { let env3 = env{self = case static of {Nothing -> selfV; Just x-> x} }
       ; pair <- eval env3 body state
       ; case pair of
          (_,Exception state2 nm obj) | yyy==nm -> return(obj,state2)
          _ -> return pair }
requestObjField name (Action (c@(Closure yyy static env formals body))) selfV [] state =
    return(Obj Nothing [("apply",Action c)] Nothing,state)
requestObjField name (Action (c@(Closure yyy static env (f:fs) body))) selfV (v:vs) state =
    requestObjField name (Action (Closure yyy static (env{vars=((f,Val v):(vars env))}) fs body)) selfV vs state
requestObjField name (Action (Closure yyy static env [] body)) selfV args state 
  = do { let env3 = env{self = case static of {Nothing -> selfV; Just x-> x} }
       ; pair <- eval env3 body state
       ; case pair of
          (_,Exception state2 nm obj) | yyy==nm -> return(obj,state2)
          (Obj Nothing [("apply",Action c)] Nothing,state2) ->
              do { 
                 ; requestObjField name (Action c) selfV args state2 }
          other -> error ("Too many args to field request: "++name) }
       
requestObjField name (Ref addr) self args state = return(access addr state,state)
requestObjField name field self args state = 
   error("The number of args does not match method: "++name++
         "\n   self = "++showObj state self++"\n   args = "++showArgs state args)
         
                                         
-------------------------------------------------
-- parsing
-------------------------------------------------

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

write pos [String p s,x] = Write s x
write pos [x,y] = error ("\nNear "++show pos++"\nthe first arg to write must be a literal string\n   "++show x)
write pos args = report pos (length args) 2 "write"

while pos [x,y] = While x y
while pos args = report pos (length args) 2 "while"

assign pos [x,y] = Asgn x y
assign pos args = report pos (length args) 2 ":="

app pos (x:ys) = Apply x ys
app pos [] = error("Near "++show pos++"\nApplication with no function, like '(@)'")

local vs pos [x] = Local vs x  
local vs pos args = report pos (length args) 1 "local"

lambda vs pos [x] = Lam vs x
lambda vs pos args = report pos (length args) 1 "\\"

   
-- Raise is special because its first argument must be a variable!!
returnF pos [Var p s, x] = Return s x 
returnF pos [x,y] = error ("\nFirst arg to return must be a variable: "++show x)
returnF pos args = report pos (length args) 2 "return"

object parent ds init pos [] = ObjLit parent ds init
object parent ds init pos args = report pos (length args) 0 "object"

oper name pos vs = Op name vs

-- Parsing expression has two parts: atoms, and s-exps

atom = num <|> string <|> trueP <|> falseP <|> self <|> super <|> done <|> unit <|> var
  where var = do {  p <- getPosition; s <- identifier xxx; return(Var p s)}
        num = do { p <- getPosition;
                 ; n <- lexemE(number 10 digit)
                 ; return (Int p n)} <?> "<number>"
        string = do { p <- getPosition; c <- stringLiteral xxx; return(String p c)} <?> "<string literal>"
        trueP = try(do { p<- getPosition; symbol xxx "True"; return(Bool p True)}) 
        falseP = try(do { p<- getPosition; symbol xxx "False"; return(Bool p False)})               
        self = try(do { p<- getPosition; symbol xxx "self"; return(Self p)}) 
        super = try(do { p<- getPosition; symbol xxx "super"; return(Super p)}) 
        done = try(do { p<- getPosition; symbol xxx "done"; return(Done p)})  
        unit = try(do {p <- getPosition; symbol xxx "[]"; return(EmptyObj p)})

-- This function parses a string, but returns a function with type: 
-- SourcePos -> [Exp] -> Exp    See "lowercase" constructors above.
-- There are many cases, one for each of the legal constructors to Exp.
-- To add to the parser, write a new function "f" then add " <|> f "
-- to the definition of "operatorP"
objectTags = ("method","def","var")
localTags = ("fun","val","ref")

operatorP = asg <|>  apply <|> blck <|> writ <|> iff <|> whil <|> returnP <|> opP <|> 
            localP <|> lamP <|> objP <|> requestP
  where 
        asg    = do { try(symbol xxx ":="); return assign}
        apply    = do { try(symbol xxx "@"); return app}
        blck   = do { try(symbol xxx "block"); return (\ pos es -> Block es)} 
        writ   = do { try(symbol xxx "write"); return write}
        iff    = do { try(symbol xxx "if"); return ifkey}
        whil   = do { try(symbol xxx "while"); return while}  
        returnP = do { try(symbol xxx "return"); return returnF} 
        opP    = do { s <- try(operator xxx); return(oper s)}
        lamP = do { try(symbol xxx "lambda")
                     ; vs <- parenS(many (identifier xxx))
                     ; return(lambda vs)}  
        objP = do { try(symbol xxx "object")
                  ; parent <- inherits
                  ; ds <- many (declP objectTags )
                  ; init <- initializer
                  ; return (object (Just parent) ds (Just init))}
        localP = do { try(symbol xxx "local")
                    ; ds <- many (try (declP localTags))
                    ; return (local ds)}     




inherits = try here <|> nothere
  where here = (do { symbol xxx "inherits"; expP}) <?> "<inherits keyword>"
        nothere = do { p <- getPosition; return(EmptyObj p)}
        
initializer = try here <|> nothere
  where here = (do { symbol xxx "init"; expP}) <?> "<init keyword>"
        nothere = do { p <- getPosition; return(Done p)}
                   
requestP = do { e <- expP; symbol xxx "."; zs <- chain; return(apply e zs)}
  where apply e [(nm,args)] pos vs = Request e nm (args ++ vs)
        apply e ((nm,args):more) pos vs = apply (Request e nm args) more pos vs
chain = sepBy1 (field <|> args) (symbol xxx ".")
  where field = do { x <- name; return(x,[])}
        args = parenS(do { x <- name;  vs <- many1 expP; return(x,vs)})

                    
-- Lam ObjLit Request Op                    
        
-- An expression is either an atom or a Lisp like parenthesized operation
expP = try atom <|> sexpr
  where sexpr  = 
           do { symbol xxx "(" 
              ; pos <- getPosition
              ; constrByList <- operatorP  -- Parse a string, get a lowercase constructor
              ; args <- many expP
              ; symbol xxx ")"
              ; return(constrByList pos args)}


declOrExp = try(fmap Left (declP localTags))  <|> fmap Right expP

-- A method can be an operator like (+) or (++) etc.
name = identifier xxx <|> operator xxx  
               
declP (fun,val,ref) = parenS(method <|> var <|> def <|> dataP <|> assoc) <?> "<decl>"
  where method =
           do { try(symbol xxx fun) -- "method" or "fun"
              ; nm <- name 
              ; vs <- parenS(many (identifier xxx))
              ; body <- expP
              ;return(MethodDecl nm vs body)} <?> ("<"++fun++" decl>")
        var = 
           do { try(symbol xxx ref)  -- "var" or "ref"
              ; nm <- identifier xxx
              ; arg <- (fmap Just expP) <|> (return Nothing)
              ; return(VarDecl nm arg)} <?> ("<"++ref++" decl>")
        def = 
           do { try(symbol xxx val)  -- "def" or "val"
              ; nm <- identifier xxx
              ; arg <- expP
              ; return(DefDecl nm arg)} <?> ("<"++val++" decl>")
        assoc = do { symbol xxx "assoc"
                   ; nm <- operator xxx
                   ; val <- assocP           
                   ; return(AssocDecl nm val)}
        dataP = 
          (do { try(symbol xxx "data")
              ; pos <- getPosition
              ; let args = (many (do { c <- lexemE lower;return[c]})) <|> (return [])
              ; (c,vs) <- parenS (do { c <- identifier xxx; vs <- args; return (c,vs)}) <|>
                          (do { c <- identifier xxx; return(c,[])})
              ; let clause = do { lexemE (char '#')
                                ; c <- identifier xxx
                                ; ts <- many (identifier xxx)
                                ; return(c,ts)}
              ; clauses <- many(parenS clause)
              ; return(DataDecl pos c vs clauses)}) <?> ("<data decl>")
     

assocP = (f "left" L) <|> (f "right" R) <|> (f "non" Non) <?> "<associativity>"
 where f name value = (try (symbol xxx name) >> return value)

progP =
  do { ds <- many (declP localTags)
     ; (symbol xxx "init") <?> "<init keyword>"
     ; body <- expP
     ; return (Local ds body)}

-----------------------------------
-- Parser Boilerplate below here        
       
type MParser a = ParsecT
                    String                -- The input is a sequence of Char
                    ()                    -- The internal state
                    Identity              -- The underlying monad
                    a                     -- the type of the object being parsed
      
xxxStyle = LanguageDef
                { commentStart   = "{-"
                , commentEnd     = "-}"
                , commentLine    = "--"
                , nestedComments = True
                , identStart     = lower <|> upper
                , identLetter    = lower <|> upper <|> digit
                , opStart        = oneOf "+*-/!@#$%^&~=?<>:"
                , opLetter       = oneOf "+*-/!@#$%^&~=?<>:"
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


-----------------------------------------------------
-- operations on SourcePos
-----------------------------------------------------

noPos:: SourcePos
noPos = newPos "unknown location" 0 0 

none p = (sourceName p)=="unknown location" &&
         (sourceLine p)==0 &&
         (sourceColumn p)==0

lineCol p = (sourceLine p,sourceColumn p)

posAdd :: SourcePos -> SourcePos -> SourcePos
posAdd p q | none p = q
posAdd p _ = p

loc2 x y = posAdd (loc x) (loc y)
locL f [] = noPos
locL f (x:xs) = posAdd (f x) (locL f xs)
locM f Nothing = noPos
locM f (Just x) = f x

-- Compute the SourcePos of a term 
loc (Var p s) = p
loc (Bool p b) = p
loc (Int p n) = p
loc (String p s) = p
loc (While x y) = posAdd (loc x) (loc y)
loc (Local es e) = (loc e)
loc (Write message e) = loc e
loc (Block es) = locL loc es
loc (If x y z) = posAdd (posAdd (loc x) (loc y)) (loc z)
loc (Asgn x y) = posAdd (loc x) (loc y)
loc (Apply x ys) = posAdd (loc x) (locL loc ys)
loc (Lam vs e) = loc e
loc (ObjLit parent ds e) = posAdd (locM loc  parent) (posAdd (locL locD ds) (locM loc e))
loc (Request e nm es) = posAdd (loc e) (locL loc es)
loc (Return s e) = loc e
loc (Op s es) = locL loc es
loc (Self p) = p
loc (Super p) = p
loc (Done p) = p

locD (DefDecl nm e) = loc e
locD (VarDecl nm (Just e)) = loc e
locD (MethodDecl n vs e) = loc e
locD _ = noPos

------------------------------------------------------------
-- Showing and indenting printing
------------------------------------------------------------

instance Show Value where
  show (IntV n) = show n
  show (StringV s) = show s
  show (BoolV b) = show b
  show (ExceptV s)= ("Exception "++s)
  show DoneV = "done"
  
instance Show Object where
  show (Obj (Just n) xs sup) = show n ++ plistf fst ("[") xs "," "]"
  show (Obj Nothing xs sup) = plistf fst ("[") xs "," "]"
  show (Thunk name _) = "<thunk "++name++">"
  
instance Show Exp where
  show x = PP.render(ppExp x)

instance Show Decl where
  show x = PP.render(ppDecl objectTags x)


plistf :: (a -> String) -> String -> [a] -> String -> String -> String
plistf f open xs sep close = open ++ help xs ++ close
  where help [] = ""
        help [x] = f x
        help (x:xs) = f x ++ sep ++ help xs    

plist = plistf id

txt = PP.text
punc comma ds = PP.punctuate (txt comma) ds
(<>) = (PP.<>)
(<+>) = (PP.<+>)

manyPP [] = [txt ")"]
manyPP [x] = [ppExp x <> txt ")"]
manyPP (x:xs) = ppExp x : manyPP xs
        
-- This is an indenting pretty printer for syntactic elements 
ppM f Nothing = PP.empty
ppM f (Just x) = f x

ppExp :: Exp -> PP.Doc
ppExp (Var p v) = txt v
ppExp (Bool p b) = txt(show b)
ppExp (Int p n) = txt (show n)
ppExp (String p c) = txt (show c)
ppExp (While x y)= txt "(while " <> PP.nest 3 (PP.sep [ppExp x , ppExp y <> txt ")"])
ppExp (Local ds e) = PP.parens(PP.sep [txt "local",PP.sep(map (ppDecl localTags) ds),ppExp e])

ppExp (Write s x)= txt "(write " <> PP.nest 3 (PP.sep [txt(show s),ppExp x <> txt ")"])
ppExp (Block es) = txt "(block " <> PP.nest 3 (PP.sep ((map ppExp es)++ [txt ")"]))
ppExp (If x y z)= txt "(if " <> PP.nest 3 (PP.sep [ppExp x , ppExp y,ppExp z <> txt ")"])        
ppExp (Asgn v e )= txt "(:= " <> PP.nest 3 (PP.sep [ppExp v , ppExp e <> txt ")"])
ppExp (Apply e es)= PP.parens(PP.sep (txt "@" : ppExp e : map ppExp es))
ppExp (ObjLit Nothing ds e) = 
   PP.parens(PP.sep [ txt "object"
                    , PP.sep(map (ppDecl objectTags) ds)
                    , ppM(\ e -> txt "init"<+> ppExp e) e])
ppExp (ObjLit (Just parent) ds e) = 
   PP.parens(PP.sep [ txt "object"
                    , ppExp parent,PP.sep(map (ppDecl objectTags) ds)
                    , ppM(\ e -> txt "init" <+> ppExp e) e])   
ppExp (Request e field es) =  -- Choose one of the two ways to print
   -- PP.parens(PP.sep(txt "req" : (PP.hcat [ppExp e,txt ".", txt field]) : map ppExp es))
      PP.parens(PP.sep( PP.hcat[ppExp e,txt ".",txt field] : map ppExp es))
ppExp (Return f arg)=  PP.parens (PP.sep [txt "return",txt f,ppExp arg])    
ppExp (Op s args) = PP.parens(PP.sep (txt s : map ppExp args))
ppExp (Self p) = txt "self"
ppExp (Super p) = txt "super"
ppExp (Done p) = txt "done"
ppExp (EmptyObj p) = txt "[]"
ppExp (Lam vars e) = txt "(\\ " <> PP.nest 3 (PP.sep [vs, ppExp e <> txt ")"])
  where vs = PP.parens(PP.sep(map txt vars))

ppDecl (method,def,var) (MethodDecl nm vs body) = PP.parens(PP.sep[txt method <+> txt nm <+> parenL txt vs,ppExp body])
ppDecl (method,def,var) (DefDecl nm body) = PP.parens(PP.sep [txt def <+> txt nm,ppExp body])
ppDecl (method,def,var) (VarDecl nm Nothing) = PP.parens(PP.sep [txt var, txt nm])
ppDecl (method,def,var) (VarDecl nm (Just body)) = PP.parens(PP.sep [txt var <+> txt nm,ppExp body])
ppDecl _ (AssocDecl nm x) = PP.parens(PP.sep[txt (show x), txt nm])
ppDecl _ (DataDecl pos c vs cls) = PP.parens
          (PP.sep[PP.sep [txt "data",PP.parens(PP.sep (txt c: (map txt vs)))]
                 ,PP.nest 3 (PP.vcat (map f cls))])
  where f (c,ts) = PP.parens(PP.sep (txt ("#"++c) : map txt ts))



ppEnv n state env = parenL help (take n (vars env))
  where help (nm,Val x) = PP.sep[txt nm, txt "=",ppObject2 state (10,2) x]
        help (nm,Ref x) = txt (nm++" = Ref")
        help (nm,Action code) = PP.sep [txt nm, txt "=",ppCode code]

showEnv n state x = PP.render(ppEnv n state x)

instance Show Assoc where
  show L = "left"
  show R = "right"
  show Non = "non"

-- Indenting run-time objects
-- 0  just values or {...}
-- 1 values and just names
-- 2 values and just var or def with result
-- 3 vales and just var or def with result, and method names
-- 4 everything

f2:: State -> Int -> (Name,Binding) -> PP.Doc
f2 st d (nm,Val v) = txt nm<>txt " "<> ppObject2 st (d-1,2) v
f2 st d (nm,Ref x) = txt nm<>txt "@"<> ppObject2 st (d-1,2) (access x st)
f2 st d _ = PP.empty

f3 st d (nm,Val v) = txt nm<>txt " "<> ppObject2 st (d-1,3) v
f3 st d (nm,Ref x) = txt nm<>txt "@"<> ppObject2 st (d-1,3) (access x st)
f3 st d (nm,_) = txt nm

f4 st d (nm,Val v) = txt nm<>txt " "<>ppObject2 st (d-1,4) v
f4 st d (nm,Ref x) = txt nm<>txt "@"<> ppObject2 st (d-1,4) (access x st)
f4 st d (nm,Action code) = txt nm <> txt " " <> ppCode code

get i xs = filter (p i) xs
  where p 1 xs = False
        p 2 (nm,Val x) = True
        p 2 (nm,Ref x) = True
        p 2 (nm,_) = False
        p _ _ = True

zap [] = txt "[]"
zap xs = PP.brackets(PP.sep (punc "," xs))

select st (Just v) ms (0,_) = txt(show v)
select st Nothing  ms (0,_) = txt "[...]"
select st (Just v) ms (d,0) = txt(show v)
select st Nothing  ms (d,0) = txt "[...]"
select st (Just v) ms (d,1) = txt(show v) <+> txt(plistf fst "[" ms "," "]")
select st Nothing  ms (d,1) = txt(plistf fst "[" ms "," "]")
select st (Just v) ms (d,2) = txt(show v)<> zap (map (f2 st d) (get 2 ms))
select st Nothing  ms (d,2) = zap (map (f2 st d) (get 2 ms))
select st (Just v) ms (d,3) = txt(show v)<> zap (map (f3 st d) (get 3 ms))
select st Nothing  ms (d,3) = zap (map (f3 st d) (get 3 ms))
select st (Just v) ms (d,n) = txt(show v)<> zap (map (f4 st d) (get 4 ms))
select st Nothing  ms (d,n) = zap(map (f4 st d) (get 4 ms))
  
ppObject2:: State -> (Int,Int) -> Object -> PP.Doc
ppObject2 st (d,m) (Thunk nm f) = txt("<thunk "++nm++">")
ppObject2 st (d,m) (Obj v ms sup) = select st v ms (d,m)

showObj:: State -> Object -> String
showObj state x = PP.render(ppObject2 state (10,depth state) x)

ppCode (Prim f) = txt "<prim>"
ppCode (Closure nm static env ns exp) = 
    -- if (nm/="")
    --   then txt (left++nm++">") else
        -- PP.sep[txt (left++nm),parenL txt ns,ppExp exp,txt ">"]
        PP.sep[txt (left) <> txt(plistf fst "(" (vars env) "," ")"),parenL txt ns,ppExp exp <> txt ">"]
  where left = case static of { Nothing -> "<" ; Just _ -> "<*"}

parenL f xs = PP.parens (PP.sep (map f xs))

test =
  do { let s1 = (State 2 [])
     ; (o,st) <- eval (Env (makeInt 3) [] assoc0) (Request (Int noPos 4) "+" [(Int noPos 6)]) s1
     ; putStrLn (showObj st o)
     }
         
------------------------------------------------------------
-- The top-level Loop
------------------------------------------------------------

---------------------------------------
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
indent n x = txt(concat(replicate n " |")++x)

type InterpType = Exp -> State -> IO (Object,State)

traceF :: Env -> InterpType -> InterpType 
traceF env f exp state =
  do { n <- readIORef traceIndent 
     ; putStrLn(PP.render(indent n "> " PP.<+> (ppExp exp) <+> txt " self = " <+>
                 ppObject2 state (10,1) (self env)))
     ; writeIORef traceIndent (n+1)
     ; ans <- f exp state
     ; writeIORef traceIndent n
     ; putStrLn(PP.render(indent n "< " PP.<> ppObject2 state (10,depth state) (fst ans)))
     ; return ans }

-- Like traceF if tracing is on, like f if not.
traceG :: Env -> InterpType -> InterpType 
traceG env f vars exp = 
  do {  b <- readIORef trace_on
     ; if b then traceF env f vars exp else f vars exp }

---------------------------------------
-- Catching exceptions 

-- Runs an expression of type (IO a), and catches calls to error with "bad"
guard command bad =
  do possible <- Control.Exception.try command
     case possible of
       Right ans -> return ans
       Left err -> (bad (err::(Control.Exception.ErrorCall)))

deriveQuestion env string = 
  do { thing <- parseString declOrExp string
     ; let (str,result) = 
             case thing of
               Left decl -> (show decl,show(dataToObject decl))
               Right exp -> (show exp,show(derive env exp))
     ; putStrLn(str++"\n   --> \n\n"++result) }
 
   
-------------------------------------
-- run a file, then go into interactive loop
              
runFile filename = 
  do { putStrLn "\n********** PARSING ******************"
     ; (source@(Local ds init)) <- parseFile progP filename  -- this is a *.e8 file
     ; putStrLn ("Program:\n" ++ show source)
     ; putStrLn "\n********** Loading Decls ******************"
     ; let initEnv = (Env (makeInt 0) [] assoc0)
           initState = state0
    -- ; (env1,state1) <- tieLocalKnot ds initEnv initState
     ; (bs0,state0) <- fixIO (evalRec (Just (self initEnv))
                                       (ext initEnv)
                                       ds ([],initState))
     ; (bs1,state1) <- initialize state0 bs0
     ; let env1 = ext initEnv bs1     
     -- ; let env1 = initEnv{vars = map bind methods ++ (vars initEnv)}
     ; putStrLn "\n\n********** EXECUTING BODY **********"
     ; (obj,state2) <- eval env1 source state1
     ; putStrLn(show obj)
     ; putStrLn "\n*********** ENTERING READ EVAL PRINT ***************"    
     ; putStrLn "type ':q' to exit, type 'trace' to flip tracer state\n"
     ; let loop state = 
              do { putStrLn "enter Exp>"
                 ; str <- getLine
                 ; case str of
                     "" -> loop state
                     ":q" -> (putStrLn "Quitting")
                     (':' : 'm' : more) -> do { guard (deriveQuestion env1 more)
                                                  (\ s -> do { putStrLn(show s); loop state})
                                              ; loop state }
                     "trace" -> do { trace; loop state}
                     (':' : 'd' : more) -> loop(setDepth (const (read more)) state)
                     other -> case parse1 ("keyboard input\n"++str) expP str of
                                Left message -> do { putStrLn(show message); loop state}
                                Right exp -> guard
                                  (do { pair <- eval env1 exp state >>= pull 
                                      ; state3 <- 
                                          case pair of
                                           (_,Exception s f vs) ->
                                              do { putStrLn("Uncaught exception: "++f++" "++show vs)
                                                 ; return s }
                                           (v,state2) ->   
                                              (if False -- (hasAsString v) -- thunks cause infinite loops
                                                  then do { (Obj (Just(StringV s)) fs sup,state3) <- request v "asString" [] state2
                                                          ; putStrLn s ; return state3}
                                                  else do { (v2,state3) <- zonk v state2
                                                          ; putStrLn(showObj state3 v2); return state3})
                                      ; loop state3})
                                  (\ s -> do { putStrLn(show s); loop state})}               
     ; loop (extract state2) }
     


--------------------------------------------
-- run from the command line

main =
  do { args <- System.Environment.getArgs 
     ; case args of
        (x :xs) -> runFile x
        [] -> error "No command line argument specifying input file"
     }     


------------------------------------------------------------------------
-- Tests and comments
------------------------------------------------------------------------

test1 = runFile "test1.e8"
test2 = runFile "solutions/sol8A.e8"
test3 = runFile "solutions/sol8B.e8"
test4 = runFile "work.e8"
test5 =runFile "bad.e8"


{-  

What to do next?
Dictionaries
Trees
Lists
Pairs 

Add (data (T a b) (#Nil) (#Cons a (T a b))) as an expansion
into a class definition.
-}

           
                               
                       
  
  

  
  