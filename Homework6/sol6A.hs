{-#LANGUAGE    FlexibleInstances, ScopedTypeVariables  #-}
-- Homework 6  Stacy Watts   swatts@pdx.edu
module Main where

-- Interpreter for simple TYPED imperative language. 
-- This version uses indirection, where all values are
-- stored on the heap. Each value is tagged. A Pair
-- takes up two heap locations.

-- These imports are for defining parsers
import Text.Parsec hiding (State,Column)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import Text.Parsec.Prim(getInput)
import Text.Parsec.Pos(SourcePos,sourceName,sourceLine,sourceColumn,newPos)
import Text.Parsec.Token hiding (natural)
import Data.Functor.Identity(Identity(..))
import Data.Char(digitToInt,isUpper)
import Data.List(union,unionBy,any,(\\),partition)

-- These are used for tracing the stack machine
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO.Unsafe(unsafePerformIO)

-- This import is for getting command line arguments
import System.Environment(getArgs)

-- This import is for indenting pretty printing
import qualified Text.PrettyPrint.HughesPJ as PP

import qualified Control.Exception as E

-- import Types

-------------------------------------------------------------------
{- Abstract Syntax for expressions. -}

type Vname = String  -- Names of variables
type Fname = String  -- Names of functions
type Addr = Int      -- Address of a location in the Heap

data Exp 
  = Var Vname SourcePos
  | Local [Exp] Exp
  | Asgn Exp Exp  
  | Write Exp
  | Block [Exp]
  | At Fname SourcePos [Exp]

  | Bool Bool
  | While Exp Exp
  | If Exp Exp Exp

  | Int  Int
  | Add  Exp Exp
  | Sub  Exp Exp
  | Mul  Exp Exp
  | Div  Exp Exp
  | Leq  Exp Exp
    
  | Char Char
  | Ceq Exp Exp

  | Pair Exp Exp
  | Fst Exp
  | Snd Exp

  | Cons Exp Exp
  | Nil 
  | Head Exp
  | Tail Exp
  | Null Exp
  
  
data Def 
  = GlobalDef Vname Exp
  | FunDef Fname Typ [(Vname,Typ)] Exp

data Program = Prog [Def] Exp  

defName (GlobalDef v e) = v
defName (FunDef f t vs e) = f

----------------------------------------------------
-- A Value is either an Int, or an Pair which is a 
-- an Addr which points at consectutive addresses
-- that store the Fst and Snd. (PairV 34) means the Fst
-- is at 34 in the heap, and the Snd is at 35 in the heap.

data Value 
     = IntV Int       -- An Int
     | PairV Addr     -- A pointer into the heap 
     | CharV Char     -- A Char
     | BoolV Bool     -- A Bool
     | ConsV Addr     -- A pointer into the heap
     | NilV           -- The end of a list
  deriving Show     

-- numeric operators are only defined if both inputs are integers.
numeric :: State -> String -> (Int -> Int -> Value) -> Value -> Value -> Value
numeric st name fun (IntV x) (IntV y) = (fun x y)
numeric st name fun v (IntV _) = error ("First arg of "++name++" is not an Int. "++showV (v,st))
numeric st name fun (IntV _) v = error ("Second arg of "++name++" is not an Int. "++ showV (v,st))
numeric st name fun u v = error ("neither arg of "++name++" is not an Int. "++ showV (v,st) ++ ", "++showV (u,st))


-- A sort of "if" over Values, raises an error 
-- if the Value can't be interpreted as a Bool
test :: State -> String -> Value -> t -> t -> t
test st name (BoolV False) truth falsehood = falsehood
test st name (BoolV True) truth falsehood = truth
test st name v t f = error ("Non Bool as argument to "++name++" test: "++showV(v,st))

-- Some operations expect pairs
pairLike name fun (PairV addr) = fun addr
pairLike name fun v = 
  error ("function "++name++" is not passed a pair."++ show v)

---------------------------------------------------------------
-- Code for Types and their operations
---------------------------------------------------------------
type Pointer t = IORef (Maybe t)
type Uniq = Integer

data Typ 
   = TyVar String
   | TyPair Typ Typ
   | TyFun [Typ] Typ
   | TyList Typ
   | TyCon String  -- Things like:  Int, Bool, Char
   | TyFresh (Uniq,Pointer Typ)

data Scheme = Sch [String] Typ

-----------------------------------------------
-- pretty printing Types

ppTyp :: Typ -> PP.Doc
ppTyp (TyVar s) = txt s
ppTyp (TyPair x y) = PP.parens (PP.sep [ppTyp x, txt "." ,ppTyp y])
ppTyp (TyFun ds rng) = 
   PP.parens(PP.sep (PP.punctuate (txt "->") (map ppTyp (ds++[rng]))))
-- ppTyp (TyArrow x y) = PP.parens (PP.sep [ppTyp x, txt "->" ,ppTyp y])
ppTyp (TyList x) = PP.brackets (ppTyp x)
ppTyp (TyCon c) = txt c
ppTyp (TyFresh (uniq,ptr)) = txt("t"++show uniq)


ppScheme :: Scheme -> PP.Doc
ppScheme (Sch vs t) = PP.sep [txt "forall", PP.sep (ppAllArgs vs) PP.<+> txt ".", ppTyp t]

ppAllArgs [s] = [txt s]  
ppAllArgs ((s):xs) = txt s :(ppAllArgs xs)
ppAllArgs [] = [PP.empty]

instance Show Typ where
  show t = PP.render(ppTyp t)
instance Show Scheme where
  show t = PP.render(ppScheme t)

-----------------------------------------------
-- monadic operations and fresh names

lift1 f comp = do { x <- comp;return(f x)}    
lift2 f c1 c2 = do { x <- c1; y <- c2; return(f x y)}  

counter :: IORef Integer
counter = unsafePerformIO(newIORef 0)

nextInteger = do { n <- readIORef counter; writeIORef counter (n+1); return n }
resetNext m = writeIORef counter m

fresh = unique "_x"
unique s = do { n <- nextInteger; return (s++show n)}

freshType = 
  do { n <- (nextInteger)
     ; p <- (newIORef Nothing)
     ; return(TyFresh (n,p)) }

freshScheme = do { r <- freshType; return(Sch [] r)}
 
----------------------------------------------
-- operations on Typ

getTyVars:: Typ -> [(String)] 
getTyVars (TyVar n) = [(n)]
getTyVars (TyCon s) = []
getTyVars (TyPair x y) = unionBy (==) (getTyVars x) (getTyVars y)
-- getTyVars (TyArrow x y) = unionBy (==) (getTyVars x) (getTyVars y) 
getTyVars (TyList x) = getTyVars x
getTyVars (TyFresh (uniq,ptr)) = [] 
getTyVars (TyFun ds rng) = foldr acc (getTyVars rng) ds
  where acc t ans = unionBy (==) (getTyVars t) ans 


get_tvs:: Typ -> IO ([(Pointer Typ)],[String])
get_tvs t = do { x <- prune t; f x }
  where f (TyVar n) = return ([],[n])
        f (TyCon s) = return ([],[])
        {-
        f (TyArrow x y) =
          do { (ts,vs) <- get_tvs x 
             ; (ss,us) <- get_tvs y
             ; return(unionBy (==) ts ss,union vs us)}
        -}
        f (TyPair x y) =
          do { (ts,vs) <- get_tvs x 
             ; (ss,us) <- get_tvs y
             ; return(unionBy (==) ts ss,union vs us)}
        f (TyList x) = get_tvs x
        f (TyFresh (uniq,ptr)) = return([(ptr)],[])
        f (TyFun ds rng) = 
          do { pairs <- mapM get_tvs (rng:ds)
             ; let (vs,us) = unzip pairs
             ; let acc x ans = unionBy (==) x ans
             ; return(foldr acc [] vs,foldr union [] us)}        

unify ::  Typ -> Typ -> SourcePos -> [String] -> IO ()
unify expected computed loc message = do { x1 <- prune expected; y1 <- prune computed; f x1 y1 }
  where f (t1@(TyVar n)) (t2@(TyVar n1)) | n==n1 = return ()
        f (TyPair x y) (TyPair a b) = 
            do { unify x a loc message; unify y b loc message}
        -- f (TyArrow x y) (TyArrow a b) = 
        --     do { unify x a loc message; unify y b loc message} 
        f (TyFun ds1 r1) (TyFun ds2 r2) =
            do { unify r1 r2 loc message
               ; unifyL ds1 ds2 loc message }
        f (TyList x) (TyList y) = unify x y loc message
        f (x@(TyCon s)) (y@(TyCon t)) =
           if s==t then return () else matchErr loc ((s++ " =/= " ++t++" (Different type constuctors)") : message) x y         
        f (TyFresh (u1,r1)) (TyFresh (u2,r2)) | r1==r2 = return ()
        f (TyFresh x) t = unifyVar loc message x t
        f t (TyFresh x) = unifyVar loc message x t 
        f s t = matchErr loc ((show s++ " =/= " ++show t++" (Different types)") : message)  s t

unifyL [] [] loc m = return()
unifyL (x:xs) (y:ys) loc m = unify x y loc m >> unifyL xs ys loc m 
unifyL [] (y:ys) loc m = matchErr loc ("too many arguments in function call ":m) y y
unifyL (y:ys) [] loc m = matchErr loc ("too few arguments in function call ":m) y y


unifyVar loc message (x@(u1,r1)) t =
  do { (vs,_) <- get_tvs t
     ; if (any (\(r0) -> r0==r1) vs) 
          then (matchErr loc ("\nOccurs check" : message)  (TyFresh x) t)
          else return ()
     ; (writeIORef r1 (Just t))
     ; return ()
     }

matchErr loc messages t1 t2 = fail ("\n*** Error, near "++show loc++"\n"++(concat messages))

-----------------------------------------------------
-- Monadic substitution on Types

look x xs def =
  case lookup x xs of
    Nothing -> def
    Just t -> t

tySub :: loc -> ([(Pointer Typ,Typ)],[(String,Typ)],[(String,Typ)]) -> Typ -> IO Typ
tySub loc (env@(xs,ys,zs)) x = do { a <- prune x; f a }
  where f (typ@(TyVar s)) = return(look s ys typ)
        f (typ@(TyCon c)) = return(look c zs typ)
        f (typ@(TyFresh (uniq,ptr))) = return(look ptr xs typ)  
        f (TyPair g x) = lift2 TyPair (tySub loc env g) (tySub loc env x)
        -- f (TyArrow g x) = lift2 TyArrow (tySub loc env g) (tySub loc env x)
        f (TyFun ds rng) = lift2 TyFun (mapM (tySub loc env) ds) (tySub loc env rng)
        f (TyList x) = do { y <- tySub loc env x; return(TyList y)}

             
schemeSub loc (xs,ys,zs) (Sch vs t) = 
   do { let f (v) = do { u <- fresh; return(v,TyVar u)}
            g (v,TyVar u) = (u)
      ; newys <- mapM f vs
      ; t' <- tySub loc (xs,newys++ys,zs) t
      ; return(Sch (map g newys) t')}

-----------------------------------------------------
-- Zonking follows all mutable variable chains and eliminates them
-- use this when ever you return a type that might have 
-- fresh variables inside.
     
prune :: Typ -> IO Typ
prune (typ @ (TyFresh (uniq,ref))) =
  do { maybet <- (readIORef ref)
     ; case maybet of
         Nothing -> return typ
         Just t -> do{t2 <- prune t; (writeIORef ref (Just t2)); return t2}}
prune t = return t


zonk :: Typ -> IO Typ
zonk t = do { x <- prune t; f x}
  where f (TyVar s) = return(TyVar s)
        f (TyPair f x) = lift2 TyPair (zonk f) (zonk x) 
        -- f (TyArrow f x) = lift2 TyArrow (zonk f) (zonk x) 
        f (TyFun ds rng) = lift2 TyFun (mapM zonk ds) (zonk rng)
        f (TyList x) = lift1 TyList (zonk x)        
        f (TyCon c) = return(TyCon c)
        f (TyFresh (uniq,ptr)) =  return(TyFresh(uniq,ptr))
      
zonkScheme :: Scheme -> IO Scheme
zonkScheme (Sch vs r) =
  do { b <- zonk r
     ; return(Sch vs b)}

------------------------------------------
-- Turn a scheme into a Typ , with fresh mutable
-- variables for the universally quantified ones.

instantiate:: Scheme -> IO Typ 
instantiate (Sch xs r) = do { env <- freshen xs; tySub noPos ([],env,[]) r }
  where freshen xs = mapM g xs
        g (name) = do { t <- freshType; return(name,t) }

noPos:: SourcePos
noPos = newPos "unknown location" 0 0 

none p = (sourceName p)=="unknown location" &&
         (sourceLine p)==0 &&
         (sourceColumn p)==0

-------------------------------------------
-- Create a scheme

generalize:: [Pointer Typ] -> Typ -> IO Scheme
generalize us t = generalizeRho us t
     
generalizeRho:: [Pointer Typ] -> Typ -> IO Scheme
generalizeRho us t = 
  do { (vs,bad) <- get_tvs t
     ; let ok (p) = not(elem p us)
           free = filter ok vs
           argKind (_,TyVar nam) = (nam)
     ; let subst = goodNames bad free names
     ; body <- tySub noPos (subst,[],[]) t
     ; return (Sch (map argKind subst) body)}     

 
names = (map (:[]) "abcdefghijklmnpqrstuvwxyz") ++ map f names
  where f s = s++"1"

goodNames bad [] names = []
goodNames bad ((p):more) (n:names) =
   if elem n bad then goodNames bad ((p):more) names
                 else (p,TyVar n):goodNames bad more names

-- some simple types
intT = TyCon "Int"
charT = TyCon "Char"
boolT = TyCon "Bool"
stringT = TyList charT
   
ta = TyVar "a" 
tb = TyVar "b" 
tc = TyVar "c" 

-- We use types to infer and check that an Exp
-- is used consistently. We make some effort to report
-- errors in a useful way.

-- check that an Exp has a certain type. Report an error if it doesn't

check:: [(String, Scheme)] -> [(String, Scheme)]
        -> Exp -> Typ -> String -> IO ()
check fs vs exp typ1 message =
  do { typ2 <- infer fs vs exp
     ; unify typ1 typ2 (loc exp) 
          ["\nChecking "++message
          ,"\nWhile infering the type of\n   "++show exp
          ,"\nExpected type: "++show typ1
          ,"\nComputed type: "++show typ2
          ]}

-- A type inference function for Exp

notYet pos = 
  do { putStrLn (pos++" typechecking failed: unimplemented")
     ; freshType }
     
sh (Int n) = show n
sh (Char c) = show c
sh (Bool b) = show b
sh x = show(loc x)
     
infer:: [(String,Scheme)] -> [(String,Scheme)] -> Exp -> IO Typ
infer fs vs (term@(Var s pos)) = 
  case lookup s vs of
    Just sch -> instantiate sch
    Nothing -> error ("\nNear "++show pos++"\nUnknown var in type inference: "++ s)
infer fs vs (term@(Int n)) = return intT 
infer fs vs (term@(Char c)) = return charT  -- now returns a charT
infer fs vs (term@(Bool b)) = return boolT 
infer fs vs (term@(Local es body)) =
  do { let split [] = return vs
           split (Var x p : e : more) = 
             do { t <- infer fs vs e
                ; zs <- split more
                ; return((x,Sch [] t):zs)}
     ; vs2 <- split es
     ; infer fs vs2 body }
infer fs vs (term@(Asgn e1 e2)) =   -- type e1 to be type eval e2
  do { t1 <- infer fs vs e2  -- get type of e2
     ; t2 <- infer fs vs e1
     ; unify t1 t2 (loc term)
         ["\nWhile infering the term\n   "++show term
         ,"\nThe var and exp have different types" ]
     ; return t2}  -- 

infer fs vs (term@(Write e)) = infer fs vs e  -- type eval e
infer fs vs (term@(Block es)) =
  do { ts <- mapM (infer fs vs) es
     ; return (last ts)}
infer fs vs (term@(At f pos es)) = 
  case lookup f fs of
    Nothing -> error ("\nNear "++show pos++"\nUnknown function in type inference: "++ f)
    Just sch -> 
      do { expected <- instantiate sch 
         ; rng <- freshType
         ; ds <- mapM (infer fs vs) es
         ; unify expected (TyFun ds rng) (loc term) [show term]
         ; zonk rng }
infer fs vs (term@(If x y z)) =
  do { check fs vs x boolT "if statement test"
     ; t1 <- infer fs vs y
     ; t2 <- infer fs vs z
     ; unify t2 t1 (loc term) 
         ["\nWhile infering the term\n   "++show term
         ,"\nThe two branches have different types" ]
     ; return t1}
infer fs vs (term@(Add x y)) =
  do { check fs vs x intT "(+)"
     ; check fs vs y intT "(+)"
     ; return intT}
infer fs vs (term@(Sub x y)) =
  do { check fs vs x intT "(-)"
     ; check fs vs y intT "(-)"
     ; return intT}
infer fs vs (term@(Mul x y)) =
  do { check fs vs x intT "(*)"
     ; check fs vs y intT "(*)"
     ; return intT}
infer fs vs (term@(Div x y)) =
  do { check fs vs x intT "(/)"
     ; check fs vs y intT "(/)"
     ; return intT}
infer fs vs (term@(Leq x y)) = notYet (sh term) 
infer fs vs (term@(Ceq x y)) =
  do { check fs vs x charT "(=)"
     ; check fs vs y charT "(=)"
     ; return boolT}
infer fs vs (term@(Pair x y)) = notYet (sh term)
infer fs vs (term@(Fst p)) = 
  do { t1 <- infer fs vs p
     ; a <- freshType; b <- freshType
     ; unify (TyPair a b) t1 (loc p) 
         ["\nWhile infering type of\n   "++show term
         ,"\nThe term\n   "++show p
         ,"\nis not a pair\n   "++show  t1 ] 
     ; zonk a}
infer fs vs (term@(Snd p)) = notYet (sh term)
infer fs vs (term@(Cons x y)) = 
  do { t1 <- infer fs vs x
     ; check fs vs y (TyList t1) "2nd arg to cons"
     ; return(TyList t1)}
infer fs vs (term@(Head p)) = 
  do { t1 <- infer fs vs p
     ; a <- freshType;
     ; unify (TyList a) t1 (loc p)
         ["\nWhile infering type of\n   "++show term
         ,"\nThe term\n   "++show p
         ,"\nis not a list\n   "++show  t1 ] 
     ; zonk a}
infer fs vs (term@(Tail p)) = 
  do { t1 <- infer fs vs p
     ; a <- freshType; 
     ; unify (TyList a) t1 (loc p) 
         ["\nWhile infering type of\n   "++show term
         ,"\nThe term\n   "++show p
         ,"\nis not a list\n   "++show  t1 ] 
     ; zonk(TyList a)} 
infer fs vs (term@(Null e)) =
  do { t1 <- infer fs vs e
     ; a <- freshType; 
     ; unify (TyList a) t1 (loc e) 
        ["\nWhile infering type of\n   "++show term
        ,"\nThe term\n   "++show e
        ,"\nis not a list\n   "++show  t1 ] 
     ; return boolT } 
infer fs vs (term@Nil) =  -- placeholder for now, I think there's a better way.
  do { a <- freshType; 
     ; return (TyList a)}
infer fs vs (term@(While tst body)) = notYet (sh term)
  

-- Check that GlobalDef and FunDef are used consistently with their
-- declared type information.
                     
checkDefs:: [Def] -> IO([(String, Scheme)],[(String, Scheme)])
checkDefs ds = 
  do { (fs,vs) <- foldr defScheme (return ([],[])) ds
     -- compute type schemes for each FunDef and GlobalDef
     ; let checkD (GlobalDef v e) =
             do { t <- findtype vs v; check fs vs e t "global def"}
           checkD (FunDef f rng args body) =
             do { let acc (v,t) ans = (v,Sch [] t):ans
                      vs2 = foldr acc vs args
                ; check fs vs2 body rng "body of fundef"}
     ; mapM checkD ds -- check that each Def is used consistently
     ; vs2 <- mapM crush vs -- remove residual fresh type variables.
     ; fs2 <- mapM crush fs
     ; return (vs2,fs2) }

crush (v,sch) = do { sch2 <- zonkScheme sch; return(v,sch2)}

findtype xs v =
  case lookup v xs of
    Just sch -> instantiate sch
    Nothing -> freshType

-- Compute a type scheme for each GlobalDef and FunDef. Later
-- we will check if these types schemes are used consistently.

defScheme (GlobalDef v exp) m = 
  do { sch <- freshScheme; (fs,vs) <- m; return(fs,(v,sch):vs)}
defScheme (FunDef f rng args body) m = do { (fs,vs) <- m; return((f,Sch us typ):fs,vs)}
  where typ = TyFun (map snd args) rng
        us = getTyVars typ  

---------------------------------------------------------------
-- The State of the Machine consists of a Heap
-- The machine also uses two Tables mapping names to their bindings.
--------------------------------------------------------------------

-- A table maps keys to objects
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

-- For each Name and associated value, allocate the value on the heap,
-- and pair its name with the address it was allocated to.
-- For example:    bind [a,b,c] 
--                      [IntV 3,IntV 7,IntV 1] 
--                      (State [IntV 17])  ---> 
-- returns the pair
-- ( [(a,1),(b,2),(c,3)]    -- names paired with Addr 
-- , (State [IntV 17,IntV 3,IntV 7,IntV 1]) -- The new heap
-- )


bind:: [String] -> [Value] -> State -> ([(Vname,Addr)],State)
bind names objects state = loop (zip names objects) state
  where loop [] state = ([],state)
        loop ((nm,v):more) state = ((nm,ad):xs,state3)
          where (ad,state2) = alloc v state
                (xs,state3) = loop more state2
                
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
   run state (Var v pos) = 
     case lookUp vars v of
       Found addr -> return(access addr state,state)
       NotFound -> error ("Unknown variable: "++v++" in lookup.")
   
   run state (Int n) = return(IntV n,state)
   run state (Bool b) = return(BoolV b,state)
   run state (Char c) = return(CharV c, state)

   run state (Asgn e1 e2 ) = 
     do { (val,state2) <- interpE funs vars state e2
        ; (addr,state3) <- addressOf funs vars state2 e1
        ; return(val,stateStore addr val state3)}
   
   run state (term@(At f pos args)) = 
     case lookUp funs f of
        NotFound -> error ("\nUnknown function: "++f++" in function call.")
        Found (vars2,formals,body) -> 
          do { when (length args /= length formals)
                    (error ("\nWrong number of args to: "++f++" in: "++show term))
               -- Eval all the arguments
             ; (vs,state2) <- interpList funs vars state args 
               -- bind names to addresses, and allocate them on the heap             
             ; let (pairs,state3) = bind formals vs state2  
               -- run the body in new environment
             ; (v,state4) <- interpE funs (push pairs vars2) state3 body 
             ; return(v,state4) }

   run state (While tst body)= while state
     where while state = 
             do { (v,state2) <- interpE funs vars state tst
                ; test state2 "while" v
                       (do { (_,state3) <- interpE funs vars state2 body
                           ; while state3})
                       (return(IntV 0,state2))}   
                       
   run state (If x y z) = 
     do { (v,state2) <- interpE funs vars state x
        ; test state2 "if" v (interpE funs vars state2 y) (interpE funs vars state2 z) }  
   
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
        ; return(numeric state2 "+" (\ x y -> IntV(x+y)) v1 v2,state2) }

   run state (Sub  x y) =
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric state2 "-" (\ x y -> IntV(x-y)) v1 v2,state2) }      

   run state (Mul  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric state2 "*" (\ x y -> IntV(x*y)) v1 v2,state2) }   

   run state (Div  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric state2 "/" (\ x y -> IntV(div x y)) v1 v2,state2) }   

   run state (Leq  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; return(numeric state2 "<=" (\ x y -> BoolV(x <= y)) v1 v2,state2) }        

   run state (Ceq  x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; case (v1,v2) of 
            (CharV x,CharV y) -> return(BoolV(x==y),state2)
            (x,CharV _) -> error ("first arg to 'chareq' is not Char: "++show x) 
            (CharV _,x) -> error ("second arg to 'chareq' is not Char: "++show x) 
            other -> error ("neither arg to 'chareq' is a Char: "++show other)}         

   run state (Pair x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; let (a1,state3) = alloc v1 state2  -- Allocate consequtive locations
              (a2,state4) = alloc v2 state3  -- for v1 and v2
        ; return(PairV a1,state4)}           -- return the PairV of the first address

   run state (Fst x)    = 
     do { (v1,state1@(State xs)) <- interpE funs vars state x
        {- ; case v1 of
           PairV addr -> xs !! addr  -}
        ; let getfirst addr = xs !! addr
        ; return(pairLike "fst" getfirst v1,state1)}

   run state (Snd x)    = 
     do { (v1,state1@(State xs)) <- interpE funs vars state x
        ; let getsnd addr = xs !! (addr+1)
        ; return(pairLike "snd" getsnd v1,state1)}   

   run state (Cons x y) = 
     do { (v1,state1) <- interpE funs vars state x
        ; (v2,state2) <- interpE funs vars state1 y
        ; let (a1,state3) = alloc v1 state2  -- Allocate consequtive locations
              (a2,state4) = alloc v2 state3  -- for v1 and v2
        ; return(ConsV a1,state4)}           -- return the ConsV of the first address
        
   run state Nil = return(NilV,state)  
   run state (Head x) = 
     do { (v,state2@(State xs)) <- interpE funs vars state x
        ; case v of
            ConsV addr -> return(xs !! addr,state2)
            other -> error ("Non 'cons' cell in head: "++showV(other,state2))}

   run state (Tail x) = 
     do { (v,state2@(State xs)) <- interpE funs vars state x
        ; case v of
            ConsV addr -> return(xs !! (addr+1),state2)
            other -> error ("Non 'cons' cell in head: "++showV(other,state2))}


   run state (Null x) = 
     do { (v1,state1) <- interpE funs vars state x
        ; case v1 of            
            (NilV) -> return(BoolV True,state1)
            other -> return(BoolV False,state1) }
            
   run state (Local pairs body) = 
     do { let split (Var v p : e : zs) (vs,es) = split zs (vs++[v],es++[e])
              split _ (vs,es) = (vs,es)
              (vs,es) = split pairs ([],[])
        ; (vals,state2) <- interpList funs vars state es 
        ; let (pairs,state3) = bind vs vals state2  
        ; interpE funs (push pairs vars) state3 body }
            

-- Compute the l-value of an expression. Used in assignment

addressOf funs vars state (Var v pos) =
   case lookUp vars v of
     Found addr -> return (addr,state)
     NotFound -> error ("\nUnknown variable: "++v++" in assignment.") 
addressOf funs vars state (Fst e) = 
  do { (v,st) <- interpE funs vars state e
     ; case v of
         PairV addr -> return (addr,st)
         other -> error ("\nNon pair as argument to Fst: "++showV(other,st)++" in assignment.") }
addressOf funs vars state (Snd e) = 
  do { (v,st) <- interpE funs vars state e
     ; case v of
         PairV addr -> return (addr+1,st)
         other -> error ("\nNon pair as argument to Snd: "++showV(other,st)++" in assignment.") }
addressOf funs vars state (Head e) = 
  do { (v,st) <- interpE funs vars state e
     ; case v of
         ConsV addr -> return (addr,st)
         other -> error ("\nNon cons-list as argument to Head: "++showV(other,st)++" in assignment.") }
addressOf funs vars state (Tail e) = 
  do { (v,st) <- interpE funs vars state e
     ; case v of
         ConsV addr -> return (addr+1,st)
         other -> error ("\nNon cons-list as argument to Tail: "++showV(other,st)++" in assignment.") }
addressOf funs vars state e =
  error ("Exp with no l-value in assignment: "++show e)
     

-- interpret a list from left to right. Be sure the
-- state is updated for each element in the list.

interpList funs vars state [] = return([],state)
interpList funs vars state (e:es) = 
  do { (v,state1) <- interpE funs vars state e
     ; (vs,state2) <- interpList funs vars state1 es
     ; return(v:vs,state2)}

-- elab:: Def -> (Env (Stack,[Vname],Exp),Env Address,State) -> IO (Env (Stack,[Vname],Exp),Env Address,State)
elab (FunDef f t vs e) (funs,vars,state) =
  return ( extend f (vars,map fst vs,e) funs, vars, state )
elab (GlobalDef v e) (funs,vars,state) =
  do { (value,state2) <- interpE funs vars state e
     ; let (addr,state3) = alloc value state2
     ; return(funs, extend v addr vars,state3)}

elaborate loud [] ts = return ts
elaborate loud (d:ds) ts = 
  do { when loud (putStr (defName d++" "))
     ; ts1 <- elab d ts
     ; elaborate loud ds ts1}
                                     
---------------------------------------------------------
-- Computing with SourcePos, essentially the location
-- of a term in a file (line and column information).

posAdd p q | none p = q
posAdd p _ = p

loc2 x y = posAdd (loc x) (loc y)
locL [] = noPos
locL (x:xs) = posAdd (loc x) (locL xs)

-- Compute the SourcePOs of a term 
loc (Var s p) = p
loc (Local es e) = posAdd (locL es) (loc e)
loc (Asgn x y) = posAdd (loc x) (loc y)
loc (Write e) = loc e
loc (Block es) = locL es
loc (At f p es) = p
loc (Bool b) = noPos
loc (While x y) = posAdd (loc x) (loc y)
loc (If x y z) = posAdd (posAdd (loc x) (loc y)) (loc z)
loc (Int n) = noPos
loc (Add x y) = posAdd (loc x) (loc y)
loc (Sub x y) = posAdd (loc x) (loc y)
loc (Mul x y) = posAdd (loc x) (loc y)
loc (Div x y) = posAdd (loc x) (loc y)
loc (Leq x y) = posAdd (loc x) (loc y)
loc (Ceq x y) = posAdd (loc x) (loc y)
loc (Char c) = noPos
loc (Pair x y) = posAdd (loc x) (loc y)
loc (Fst e) = loc e
loc (Snd e) = loc e
loc (Cons x y) = posAdd (loc x) (loc y)
loc (Head e) = loc e
loc (Tail e) = loc e
loc (Null e) = loc e
loc Nil = noPos

                                     
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

ceq pos [x,y] = Ceq x y
ceq pos args = report pos (length args) 2 "="

atSign pos (Var x p:args) = At x p args
atSign pos args = error ("Near "++show pos++"\nfirst argument to '@' is not a function name.")

pair pos [x,y] = Pair x y
pair pos args = report pos (length args) 2 "pair"

cons pos [x,y] = Cons x y
cons pos args = report pos (length args) 2 "cons"

fstC pos [x] = Fst x
fstC pos args = report pos (length args) 1 "fst"

sndC pos [x] = Snd x
sndC pos args = report pos (length args) 1 "snd"

headC pos [x] = Head x
headC pos args = report pos (length args) 1 "head"

tailC pos [x] = Tail x
tailC pos args = report pos (length args) 1 "tail"

nullC pos [x] = Null x
nullC pos args = report pos (length args) 1 "null"

local vs pos [x] = Local vs x
local vs pos args = report pos (length args) 1 "local"

assign pos [x,y] = Asgn x y
assign pos args = report pos (length args) 2 ":="

setfst pos [x,y] = error "\nYou need to define setfst"
setfst pos args = report pos (length args) 2 "setfst"

setsnd pos [x,y] = error "\nYou need to define setsnd"
setsnd pos args = report pos (length args) 2 "setsnd"
  
-- This function parses a string, but returns a function with type: 
-- SourcePos -> [Exp] -> Exp    See "lowercase" constructors above.
-- There are many cases, one for each of the legal constructors to Exp.
-- To add to the parser, write a new function "f" then add " <|> f "
-- to the definition of "operatorP"

operatorP = plus <|> times <|> minus <|> divid <|> ltheq <|> ceqP <|> asg <|> atP <|>
            blck <|> writ <|> iff <|> whil <|>
            pairP <|> fstP <|> sndP <|> consP <|> headP <|> tailP <|>
            nullP <|>
            localP <|> setfstP <|> setsndP
  where plus   = do { symbol xxx "+";  return add}
        times  = do { symbol xxx "*";  return mul}
        minus  = do { symbol xxx "-";  return sub}
        divid  = do { symbol xxx "/";  return divide}
        ltheq  = do { symbol xxx "<="; return leq}
        ceqP   = do { symbol xxx "="; return ceq}
        asg    = do { symbol xxx ":="; return assign}
        atP    = do { symbol xxx "@"; return atSign}
        blck   = do { try(symbol xxx "block"); return (\ pos es -> Block es)} 
        writ   = do { try(symbol xxx "write"); return write}
        iff    = do { try(symbol xxx "if"); return ifkey}
        whil   = do { try(symbol xxx "while"); return while}
        pairP  = do { try(symbol xxx "pair"); return pair}
        fstP   = do { try(symbol xxx "fst"); return fstC}
        sndP   = do { try(symbol xxx "snd"); return sndC}
        headP   = do { try(symbol xxx "head"); return headC}
        tailP   = do { try(symbol xxx "tail"); return tailC}        
        nullP= do { try(symbol xxx "null"); return nullC}     
        setfstP= do { try(symbol xxx "setfst"); return setfst}
        setsndP= do { try(symbol xxx "setsnd"); return setsnd}
        consP = do { try(symbol xxx "cons"); return cons}
        
        localP = do { try(symbol xxx "local")
                    ; let pair = do { pos <- getPosition
                                    ; s <- identifier xxx <?> "'local variable'"
                                    ; e <- expP
                                    ; return[Var s pos,e]}
                    ; vs <- parenS(do { ps <- many pair; return(concat ps)}) <?> "'local var-value list'"
                    ; return (local vs)}
        
        
        
-- An expression is either an atom or a Lisp like parenthesized operation
expP = try atom <|> sexpr
  where atom = constant <|> charP <|> trueP <|> falseP <|> nilP <|> var
        var = 
          do { pos <- getPosition; s <- identifier xxx; return(Var s pos)}
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
        trueP = try(do { symbol xxx "True"; return(Bool True)}) 
        falseP = try(do { symbol xxx "False"; return(Bool False)}) 
        nilP = try(do { symbol xxx "nil"; return(Nil)})         


-- Parse a Def
defP = parenS ( global <|> function )
  where global =
           do { symbol xxx "global"
              ; v <- identifier xxx
              ; e <- expP
              ; return(GlobalDef v e)}
        
function = 
           do { symbol xxx "fun"
              ; f <- identifier xxx
              ; rng <- typP
              ; let arg = do { x <- identifier xxx; t <- typP; return(x,t)}
              ; vs <- parenS(many arg)
              ; body <- expP
              ; return(FunDef f rng vs body)}

typP = intP <|> boolP <|> charP <|> stringP <|> varP <|> pairP <|> listP
  where intP = lift1 TyCon (symbol xxx "Int")
        boolP = lift1 TyCon (symbol xxx "Bool")
        charP = lift1 TyCon (symbol xxx "Char")
        pairP = parens xxx 
                 (do { x <- typP
                     ; symbol xxx "."
                     ; y <- typP
                     ; return(TyPair x y)})
        listP = brackets xxx (lift1 TyList typP)
        stringP = do { symbol xxx "String"; return stringT}
        varP = lift1 (\ x -> TyVar [x]) (lexemE lower)
       

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
    do possible <- E.try (readFile file)
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
ppExp (Var v p) = txt v
ppExp (Asgn v e )= txt "(:= " PP.<> PP.nest 3 (PP.sep [ppExp v , ppExp e PP.<> txt ")"])
ppExp (Write x)= txt "(write " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Block es) = txt "(block " PP.<> PP.nest 3 (PP.sep ((map ppExp es)++ [txt ")"]))
ppExp (At f p args)= txt "(@ " PP.<> PP.nest 3 (PP.sep (txt f : many args))
  where many [] = [txt ")"]
        many [x] = [ppExp x PP.<> txt ")"]
        many (x:xs) = ppExp x : many xs

ppExp (Bool b) = txt (show b)
ppExp (While x y)= txt "(while " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (If x y z)= txt "(if " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y,ppExp z PP.<> txt ")"])

ppExp (Int n) = txt (show n)
ppExp (Add  x y)  = txt "(+ " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Sub  x y)  = txt "(- " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Mul  x y) = txt "(* " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Div  x y)  = txt "(/ " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Leq  x y) = txt "(<= " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])

ppExp (Char c) = txt (show c)
ppExp (Ceq x y) = txt "(= " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])

ppExp (Pair x y) = txt "(pair " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Fst x) = txt "(fst " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Snd x) = txt "(snd " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])

ppExp (Cons x y) = txt "(cons " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp Nil = txt "nil"
ppExp (Head x) = txt "(head " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Tail x) = txt "(tail " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Null x) = txt "(null " PP.<> PP.nest 3 (PP.sep [ppExp x PP.<> txt ")"])
ppExp (Local vs e) = txt "(local " PP.<> PP.nest 3 ( vars PP.$$ ppExp e PP.<> txt ")")
  where pairs = f vs
        f (x:y:zs) = (x,y): f zs
        f _ = []
        vars :: PP.Doc
        vars = PP.parens(PP.sep (map h pairs))
        h (x,y) = PP.sep [ppExp x,ppExp y]




{-
ppExp (Local vs e) = txt "(local " PP.<> PP.nest 3 ( vars PP.$$ ppExp e PP.<> txt ")")
  where pairs = f vs
        f (x:y:zs) = (x,y): f zs
        f _ = []
        vars :: PP.Doc
        vars = PP.parens(PP.sep (map h pairs))
        h (x,y) = PP.sep [ppExp x,ppExp y]
-}        


ppDef (GlobalDef v e) = txt "(global " PP.<> PP.nest 3 (PP.sep [txt v, ppExp e PP.<> txt ")"])
ppDef (FunDef f t args body) = 
    txt "(fun " PP.<> PP.nest 3 (PP.sep [txt f PP.<+> ppTyp t, PP.parens (PP.sep (map g args)),ppExp body PP.<> txt ")"])
  where g (x,t) = txt x PP.<+> ppTyp t
  
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
showV (BoolV b,state) = show b
showV (CharV c,state) = show c
showV (NilV,state) = "[]"
showV (v,state) | Just xs <- isString (v,state) = show xs
showV (v,state) | Just xs <- isList (v,state) = plistf f "[" xs "," "]"
  where f x = showV(x,state)
showV (v,state) = 
    case v of
      PairV addr -> "("++showV(get addr,state)++"."++showV(get (addr+1),state)++")"
  where get n = xs !! n where (State xs) = state

isList :: (Value,State) -> Maybe [Value]
isList (NilV,state) = Just []
isList (ConsV addr,state) = do { ys <- isList (xs,state); return(y:ys)}
  where y = get addr
        xs = get (addr+1)
        get n = xs !! n where (State xs) = state
isList other = Nothing

isString :: (Value,State) -> Maybe String
isString (NilV,state) = Just ""
isString (ConsV addr,state) = 
    case (get addr, get (addr+1)) of
      (CharV c, tail) -> do { cs <- isString (tail,state); return(c:cs)}
      other -> Nothing
  where get n = xs !! n where (State xs) = state
isString other = Nothing


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

-- Runs an expression of type (IO a), and catches calls to error with continue
guard2 :: IO b -> IO b -> IO b
guard2 comp continue = E.catch comp handler
  where handler (err:: E.SomeException) = putStrLn(show err) >> continue 
 

shD (v,Sch vs t) = putStrLn (v++"::"++show t)
              
runFile filename = 
  do { putStrLn "\n********** PARSING ******************"
     ; (source@(Prog ds exp)) <- parseFile progP filename  -- this is a *.e3 file
     ; putStrLn ("Program:\n" ++ show source)
     ; putStrLn "\n********** Type Checking *************"
     ; (tyvars,tyfuns) <- checkDefs ds
     ; mapM shD tyfuns
     ; putStrLn ""
     ; mapM shD tyvars
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
                                Left message -> do { putStrLn("\n"++show message); loop state}
                                Right exp -> guard2
                                  (do { typ <-infer tyfuns tyvars exp
                                      ; (v,state2) <- interpE funs vars state exp
                                      -- ; putStrLn(show exp++":: "++show typ)
                                      ; putStrLn(showV (v,state2)++":: "++show typ)
                                      ; loop state2 })
                                  (loop state)}               
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

test1 = runFile "typedlists.e6"
test2 = runFile "badprog.e6"
test3 = runFile "simple.e6"
