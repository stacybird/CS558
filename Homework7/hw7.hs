{-#LANGUAGE    FlexibleInstances, ScopedTypeVariables  #-}
module Main where
-- This version uses indirection, where all values are
-- stored on the heap. Each value is tagged. Constructors
-- are allocated in consecutive heap locations.

{- Interpreter for simple typed imperative language with first class functions and data. -}

-- These imports are for defining parsers
import Text.Parsec hiding (State,Column)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import Text.Parsec.Prim(getInput)
import Text.Parsec.Pos(SourcePos,sourceName,sourceLine,sourceColumn,newPos)
import Text.Parsec.Token hiding (natural)
import Data.Functor.Identity(Identity(..))
import Data.Char(digitToInt,isUpper)
import Data.List(union,unionBy,any,(\\),partition,intersectBy,unionBy)

-- These are used for tracing the stack machine
import Data.IORef(newIORef,readIORef,writeIORef,IORef)
import System.IO(fixIO)
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
type Cname = String  -- Names of Constructors (Cons, Nil, Pair, ...)
type Addr = Int      -- Address of a location in the Heap

data Exp 
  = Var Vname SourcePos
  | Local [Exp] Exp
  | Asgn Exp Exp  
  | Write Exp
  | Block [Exp]
  | While Exp Exp
  
  | Bool SourcePos Bool
  | If Exp Exp Exp

  | Int SourcePos Int
  | Add  Exp Exp
  | Sub  Exp Exp
  | Mul  Exp Exp
  | Div  Exp Exp
  | Leq  Exp Exp

  | Char SourcePos Char
  | String SourcePos String    
  | Ceq Exp Exp

  | At Exp SourcePos [Exp]
  | Lambda SourcePos [Vname] Exp
  
  | Construction SourcePos Cname [Exp]
  | Selection SourcePos Cname Int Exp
  | Predicate SourcePos Cname Exp

data Def 
  = GlobalDef SourcePos Vname Typ Exp 
  | FunDef SourcePos Fname Typ [(Vname,Typ)] Exp
  | DataDef SourcePos Cname [String] [(Cname,[Typ])]
  | AdtDef SourcePos Cname [String] Typ [Def]
  | ImportDef SourcePos String SigExp (Maybe Program)

data SigItem
  = ValItem SourcePos Vname Typ
  | DataItem SourcePos Cname [String] [(Cname,[Typ])]
  | TypItem SourcePos Cname [String]

data SigExp
  = NameExp String
  | PreludeExp
  | AllExp
  | ExplicitExp [SigItem]  
  | HideExp SigExp [String]
  | UnionExp [SigExp]
--   | FileExp SourcePos String
  
data Signature = Sig SourcePos Cname String     
data Module = Mod SourcePos Cname SigExp SigExp
 
data Program = Prog [Signature] Module [Def] Exp  

defName :: Def -> [String]
defName (GlobalDef pos v mt e) = [v]
defName (FunDef pos f t vs e) = [f]
defName (DataDef pos c vs xs) = (c:(map fst xs))
defName (AdtDef pos c vs t ds) = c : concat(map defName ds)
-- defName (SigDef pos c ss) = [c]
-- defName (FileDef pos s) = []
defName (ImportDef pos path sig mprog) = []

----------------------------------------------------
-- A Value is either a primitive (Int, Char, or Bool), 
-- or a closure (or function) or a heap allocated 
-- object with an Addr which points at consecutive 
-- addresses. For example (ConV "pair" 2 34) means the Fst
-- is at 34 in the heap, and the Snd is at 35 in the heap.
-- We also use Thunks, but only in one place to defined
-- recursive functions and objects

-- A table maps keys to objects
data Table key object = Tab [(key,object)]
type Env a = Table String a  -- A Table where the key is a String

data Value 
       -- Primitive types
     = IntV Int       -- An Int   
     | CharV Char     -- A Char
     | BoolV Bool     -- A Bool
       -- Function objects     
     | FunV Fname (Env Addr) [Vname] Exp -- Closures (\ (x y) -> (+ x y))
       -- Heap Allocated Data
     | ConV Cname Int Addr  -- A constructor with with N arguments, starting at Addr in Heap
     | Thunk Vname (State -> IO(Value,State))

-- Trace through Thunks until a non-thunk is found    
pull :: (Value,State) -> IO(Value,State)
pull (Thunk nm f,state1) = 
    do { -- putStrLn("Pulling "++nm); 
         (v,state2) <- f state1
       ; pull (v,state2)}
pull (v,state) = return(v,state)

memoize:: (State -> IO(Value,State)) -> IO (State -> IO(Value,State))
memoize f = do { ref <- newIORef Nothing; return(g ref)}
  where g ref s = 
          do { mv <- readIORef ref
             ; case mv of 
                Nothing -> do { (v,s2) <- f s; writeIORef ref (Just v); return(v,s2)}
                Just v -> return(v,s)}

initialize :: State -> Env Addr -> IO State
initialize state (Tab []) = return state
initialize state (Tab ((k,addr):more)) 
  = do { (_,state2) <- pull (access addr state,state); initialize state2 (Tab more) }

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


---------------------------------------------------------------
-- Code for Types and their operations
---------------------------------------------------------------
type Pointer t = IORef (Maybe t)
type Uniq = Integer

data Typ 
   = TyVar String
   | TyFun [Typ] Typ
   | TyCon SourcePos String [Typ]  -- Things like:  Int, Bool, Char
   | TyFresh (Uniq,Pointer Typ)

instance Eq Typ where
 (TyVar x) == (TyVar y) = x==y
 (TyFun ds rng) == (TyFun cs z) = ds==cs && rng==z
 (TyCon _ nm ts)==(TyCon _ name ss) = nm==name && ts==ss
 (TyFresh (u,_)) == (TyFresh(v,_)) = u==v
 x == y = False

data Scheme = Sch [String] Typ deriving Eq


-- some simple types
intT = TyCon noPos "Int" []
charT = TyCon noPos "Char" []
boolT = TyCon noPos "Bool" []
stringT pos = tylist pos charT
typair pos x y = TyCon pos "Pair" [x,y]
tylist pos x = TyCon pos "List" [x]

arity0 = [("Bool",0),("Int",0),("Char",0),("List",1),("Pair",2)]
   
ta = TyVar "a" 
tb = TyVar "b" 
tc = TyVar "c" 

constructors0 = [nilSch,consSch,pairSch]
  where p = newPos "prelude" 0 0
        a = "a"
        b = "b"
        lista = tylist p (TyVar a)
        nilSch = ("nil",Sch [a] lista)
        consSch = ("cons",Sch [a] (TyFun [TyVar a,lista] lista) )
        pairSch = ("pair",Sch [a,b] (TyFun [TyVar a, TyVar b] (typair p (TyVar a) (TyVar b))))


-----------------------------------------------
-- pretty printing Types

ppTyp :: Typ -> PP.Doc
ppTyp (TyVar s) = txt s

ppTyp (TyFun ds rng) = 
   PP.parens(PP.sep (PP.punctuate (txt "->") (map ppTyp (ds++[rng]))))
ppTyp (TyCon pos "List" [x]) = PP.brackets (ppTyp x)
ppTyp (TyCon p "Pair" [x,y]) = PP.parens (PP.sep [ppTyp x, txt "." ,ppTyp y])
ppTyp (TyCon p c []) = txt c
ppTyp (TyCon p c ts) = PP.parens(PP.sep (txt c: map ppTyp ts))
ppTyp (TyFresh (uniq,ptr)) = txt("t"++show uniq)


ppScheme :: Scheme -> PP.Doc
ppScheme (Sch [] t) = ppTyp t
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
getTyVars (TyCon pos s ts) = foldr acc [] ts
   where acc t ans = unionBy (==) (getTyVars t) ans 
getTyVars (TyFresh (uniq,ptr)) = [] 
getTyVars (TyFun ds rng) = foldr acc (getTyVars rng) ds
  where acc t ans = unionBy (==) (getTyVars t) ans 

get_tvsL ts = 
  do { pairs <- mapM get_tvs ts
     ; let (vs,us) = unzip pairs
     ; let acc x ans = unionBy (==) x ans
     ; return(foldr acc [] vs,foldr union [] us)} 
             
             
get_tvs:: Typ -> IO ([(Pointer Typ)],[String])
get_tvs t = do { x <- prune t; f x }
  where f (TyVar n) = return ([],[n])
        f (TyCon pos s ts) = get_tvsL ts
        f (TyFresh (uniq,ptr)) = return([(ptr)],[])
        f (TyFun ds rng) = get_tvsL (rng:ds)

          
unify ::  Typ -> Typ -> SourcePos -> [String] -> IO ()
unify expected computed loc message = do { x1 <- prune expected; y1 <- prune computed; f x1 y1 }
  where f (t1@(TyVar n)) (t2@(TyVar n1)) | n==n1 = return ()
        f (TyFun ds1 r1) (TyFun ds2 r2) = unifyFun r1 r2 ds1 ds2 loc message               

        f (x@(TyCon _ s [])) (y@(TyCon _ t [])) =
           if s==t then return () else matchErr loc ((s++ " =/= " ++t++" (Different type constuctors)") : message) x y         
        f (x@(TyCon _ s ss)) (y@(TyCon _ t ts)) 
          | s==t && (length ss == length ts) 
          = let uni x y = unify x y loc message
            in sequence_(zipWith uni ss ts)
        f (TyFresh (u1,r1)) (TyFresh (u2,r2)) | r1==r2 = return ()
        f (TyFresh x) t = unifyVar loc message x t
        f t (TyFresh x) = unifyVar loc message x t 
        f s t = matchErr loc ((show s++ " =/= " ++show t++" (Different types)") : message)  s t

unifyFun rng1 rng2 [] [] loc m = unify rng1 rng2 loc m
unifyFun rng1 rng2 (x:xs) (y:ys) loc m =
  do { unify x y loc m; unifyFun rng1 rng2 xs ys loc m}
unifyFun rng1 rng2 (t:ts) [] loc m = 
  unify (TyFun (t:ts) rng1) rng2 loc ("\ntoo few arguments in function call ":m)
unifyFun rng1 rng2 [] (t:ts) loc m = 
  unify rng1 (TyFun (t:ts) rng2) loc ("\ntoo many arguments in function call ":m)  

unifyVar loc message (x@(u1,r1)) t =
  do { (vs,_) <- get_tvs t
     ; if (any (\(r0) -> r0==r1) vs) 
          then (matchErr loc ("\nOccurs check" : message)  (TyFresh x) t)
          else return ()
     ; (writeIORef r1 (Just t))
     ; return ()
     }

matchErr loc messages t1 t2 = fail ("\n*** Error, near "++show loc++"\n"++(concat messages))

-- This is used for arity checking and to transform abstract types into their
-- representation

checkType:: SourcePos -> [(String,Int)] -> (SourcePos -> String -> [Typ] -> IO Typ) -> Typ -> IO Typ
checkType pos arities subfun t = check t
  where check t = do { typ <- prune t; help typ}
        help (TyVar s) = return(TyVar s)
        help (TyFun ds rng) = do { ds2 <- mapM check ds; r2 <- check rng; return(TyFun ds2 r2)}
        help (t@(TyFresh _)) = return t
        help (typ@(TyCon pos1 c ts)) =
          case lookup c arities of
            Nothing -> error (show pos1 ++ "\nUnknown type constructor: "++c++
                              (if preludeP c then "\nPerhaps you forgot to include the prelude in the module 'in' set?" else ""))
            Just n -> do { when (not(n == length ts))
                                (error (show pos1++
                                        "\nWrong number of arguments in type\n   "++show typ++
                                        " (there should be exactly "++show n++")."))
                         ; us <- mapM check ts
                         ; subfun pos c us }

checkArity pos arities t = 
   checkType pos arities (\ p c ts -> return(TyCon p c ts)) t  >> return ()

-----------------------------------------------------
-- Monadic substitution on Types

look x xs def =
  case lookup x xs of
    Nothing -> def
    Just t -> t

tySub :: loc -> ([(Pointer Typ,Typ)],[(String,Typ)],[(String,Typ)]) -> Typ -> IO Typ
tySub loc (env@(xs,ys,zs)) x = do { a <- prune x; f a }
  where f (typ@(TyVar s)) = return(look s ys typ)
        f (typ@(TyCon p c [])) = return(look c zs typ)  
        f (typ@(TyCon p c ts)) = lift1 (TyCon p c) (mapM (tySub loc env) ts)      
        f (typ@(TyFresh (uniq,ptr))) = return(look ptr xs typ)       
        f (TyFun ds rng) = lift2 TyFun (mapM (tySub loc env) ds) (tySub loc env rng)
          
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
        f (TyFun ds rng) = lift2 TyFun (mapM zonk ds) (zonk rng)              
        f (TyCon p c ts) = lift1 (TyCon p c) (mapM zonk ts)
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

lineCol p = (sourceLine p,sourceColumn p)

-------------------------------------------
-- Create a scheme

generalize:: String -> [Pointer Typ] -> Typ -> IO Scheme
generalize name us t = generalizeRho us t
     
generalizeRho:: [Pointer Typ] -> Typ -> IO Scheme
generalizeRho us t = 
  do { (vs,bad) <- get_tvs t
     ; let ok (p) = not(elem p us)
           free = filter ok vs
           argKind (_,TyVar nam) = (nam)
     ; let subst = goodNames bad free names
     ; body <- tySub noPos (subst,[],[]) t
     ; let vars = (getTyVars body)
           f var name = (var,TyVar name)
           new = take (length vars) names
     ; return(Sch new (subT (zipWith f vars new) body)) }
      
 
names = (map (:[]) "abcdefghijklmnpqrstuvwxyz") ++ map f names
  where f s = s++"1"

goodNames bad [] names = []
goodNames bad ((p):more) (n:names) =
   if elem n bad then goodNames bad ((p):more) names
                 else (p,TyVar n):goodNames bad more names

subT:: [(String,Typ)] -> Typ -> Typ
subT env (typ@(TyVar s)) = (look s env typ)
subT env (typ@(TyCon p c ts)) = TyCon p c (map (subT env) ts)      
subT env (typ@(TyFresh (uniq,ptr))) = typ       
subT env (TyFun ds rng) = TyFun (map (subT env) ds) (subT env rng)

-- Turns a type into a Scheme in normal form

normTyp t = generalizeRho [] t

-- normSch (Sch [] t) = normTyp t
normSch (Sch vars t) =
  do { t2 <- zonk t
     ; let f var name = (var,TyVar name)
           new = take (length vars) names
     ; return(Sch new (subT (zipWith f vars new) t2)) }
   
-----------------------------------------------------------------
-- The Static environment tracks things like

data ItemInfo = 
     Item { arities  :: [(String,Int)]     -- The arity of user defined types.
          , constrs :: [(String,Scheme)]   -- The type of constructors
          , vars    :: [(String,Scheme)]   -- The type of variables
          }
          
preludeItems = (Item arity0 constructors0 [])          
emptyItems = (Item [] [] [])
preludeNames = map fst arity0 ++ map fst constructors0
preludeP x = elem x preludeNames

data Static = 
  Static { items :: ItemInfo
         , sigs    :: [(String,ItemInfo)]   -- The Signatures loaded first
         , imported :: [(String,Static -> (Env Addr,State) -> IO(Env Addr,State))] }

-- Just the predefined types
static0 = Static (Item arity0 [] []) [] []

-- the predefined types and the constructors of Pair and List.
preludeSig = Static preludeItems [] []
emptySig = Static emptyItems [] []

data Tagged 
   = A (String,Int,Int) 
   | C (String,Typ,Typ) 
   | V (String,Typ,Typ) 
   | Missing String String  deriving Show

-- legalSubset x y, those things in x, not in y with matching types.
legalSubset:: ItemInfo -> ItemInfo -> IO [Tagged]
legalSubset demanded supplied =  
    do { as <- test "type" same2 (arities demanded) (arities supplied) []
       ; cs <- test "#" (same1 C) (constrs demanded) (constrs supplied) []
       ; vs <- test "value" (same1 V) (vars demanded) (vars supplied) []
       ; return(vs++cs++as)}
  where test:: String -> ((String,a) -> a -> IO(Maybe Tagged)) -> [(String,a)] -> [(String,a)] -> [Tagged] -> IO[Tagged]
        test tg same [] supplied ans = return ans
        test tg same ((s,x):more) supplied ans =
          case lookup s supplied of
            Nothing -> test tg same more supplied (Missing tg s : ans)
            Just y -> do { mt <- same (s,x) y
                         ; case mt of
                             Nothing -> test tg same more supplied ans
                             Just trip -> test tg same more supplied (trip:ans)}
        same2 (name,s1) s2 =  if (s1==s2) then return Nothing else return (Just(A(name,s1,s2)))
        same1 inject (name,s1) s2 =  
           do { t1 <- instantiate s1
              ; t2 <- instantiate s2
              ; guard2 (unify t1 t2 noPos [] >> return Nothing) 
                       (return(Just (inject (name,t1,t2))))}


sufficient pos tag demanded supplied =  
    do { test same2 (arities demanded) (arities supplied)
       ; test (same1 "#constructor") (constrs demanded) (constrs supplied)
       ; test (same1 "value") (vars demanded) (vars supplied) }
  where test:: ((String,a)->a->IO()) -> [(String,a)] -> [(String,a)] -> IO ()
        test same [] supplied = return ()
        test same ((s,x):more) supplied =
          case lookup s supplied of
            Nothing -> error(show pos ++ "\nMissing "++tag++" object in import context: "++s)
            Just y -> do { same (s,x) y; test same more supplied}
        same2 (name,s1) s2 = 
          if s1==s2 
             then return ()
             else error (show pos++"\n"++tag++" Type: "++name++
                         " has mismatched arity in import context." ++
                         "\nexpecting\n   "++show s1++"\nfound\n   "++show s2)
        same1 obj (name,s1) s2 =
          do { t1 <- instantiate s1
             ; t2 <- instantiate s2
             ; unify t1 t2 pos 
               ["\n "++tag++" "++obj++": "++name++" has type mismatched in import context."
               ,"\nexpecting\n   "++show s1++"\nfound\n   "++show s2]}
            
  
-- Add a new pair to one of the lists in a Static env.
-- Raise an error if it is a duplicate and the "dup" flag is set True
-- Sometimes, things, such as function parameters shadow, so
-- the dup flag will be False. But in the top-level of file or a
-- signature, only one copy of each thing is allowed.

addArity dup pos c env | any (\ (v,_)-> (fst c)==v) (arities env) && dup
                   = error (show pos++"\nduplicate Type: "++(fst c))
addArity dup pos c env = env{arities = c:(arities env)}  


addCon dup pos cs env | any (\ (v,_)-> any (\ (c,_) -> v==c) cs) (constrs env) && dup
                   = error (show pos++"\nOne of the #constructors: "++show(map fst cs)++" is a duplicate.")
addCon dup pos cs env = env{constrs = cs++(constrs env)}  


addVar dup pos c env | any (\ (v,_)-> (fst c)==v) (vars env) && dup
                   = error (show pos++"\nduplicate value: "++(fst c))
addVar dup pos c env = env{vars = c:(vars env)} 

addSig dup pos c env | any (\ (v,_)-> (fst c)==v) (sigs env) && dup
                   = error (show pos++"\nduplicate signature: "++(fst c))
addSig dup pos c env = env{sigs = c:(sigs env)} 

addVarS dup pos pair x = x{items= addVar dup pos pair (items x)}
addArityS dup pos pair x = x{items= addArity dup pos pair (items x)}
addConS dup pos ys x = x{items=addCon dup pos ys (items x)}


--------------------------------------------------------------------
-- Set semantics where the snd part of the pair is irrelevant
-- These versions are left-biased, as elements in the left argument
-- are preferred over those in the right argument.

unionS message (Item as1 cs1 vs1) (Item as2 cs2 vs2) =
       (Item (as1\/as2) (cs1\/cs2) (vs1\/vs2))
  where (\/) xs ys = unionBy testf xs ys
        testf (a,b) (c,d) 
          | a==c &&  not(b == d)
          = error("In 'union' the item "++show a++" has inconsistent attributes "++show b++" =/= "++show d++"\n"++message)
        testf (a,b) (c,d) = a==c
       
    
intersectS message (Item as1 cs1 vs1) (Item as2 cs2 vs2) =
   return(Item (as1/\as2) (cs1/\cs2) (vs1/\vs2))
 where (/\) xs ys = intersectBy testf xs ys
       testf (a,b) (c,d)
         | a==c && b /= d 
         = error("In 'intersect' the item "++show a++" has inconsistent attributes "++show b++" =/= "++show d++"\n"++message)
       testf (a,b) (c,d) = a==c
       

diffS (Item as cs vs) nms = 
      (Item (rem as nms) (rem cs nms) (rem vs nms))
 where rem pairs [] = pairs
       rem pairs (x:xs) = rem (removeFirst pairs x) xs
       removeFirst [] x = []
       removeFirst ((y,v):ys) x | x==y = ys
       removeFirst (p:ys) x = p :(removeFirst ys x)

tree = DataDef noPos "Tree" ["a"] [("Tip", [TyVar "a"])
                            ,("Fork", [TyCon noPos "Tree" [TyVar "a"],TyCon noPos "Tree" [TyVar "a"]])]
                            
-------------------------------------------------------------------------         
-- Check that GlobalDef and FunDef are used consistently with their
-- declared type information.

-- transform:: String -> [String] -> Typ -> Def -> IO Def
-- Replaces abstract type with concrete type, everywhere.

transform pos c vs typ arities d =
    case d of
     (FunDef pos f rng args body) -> lift2 (\ r as ->FunDef pos f r as body) 
                                       (checkT rng) (mapM checkP args)
     (GlobalDef pos nm t exp) -> lift1 (\ t -> GlobalDef pos nm t exp) (checkT t)
     d -> return d
  where subfun p name ts | name==c = tySub pos ([],zip vs ts,[]) typ
                         | otherwise = return(TyCon p name ts)
        checkP (s,t) = do { t2 <- checkT t; return(s,t2)}
        checkT t = checkType pos arities subfun t
                      

tell (Missing tg s) = "to define "++tg++" '"++s++"', but is missing"
tell (V(s,t1,t2)) = "to define value '"++s++"'::"++show t1++", but it has type "++show t2++" instead"
tell (C(s,t1,t2)) = "to define constructor #"++s++"::"++show t1++", but it has type "++show t2++" instead"
tell (A(s,n,m)) = "to define type '"++s++"' with arity "++show n++", but it has arity "++show m++" instead"

tell2 (Missing tg s) = "the "++tg++" '"++s++"' is missing"
tell2 (V(s,t1,t2)) = "the value '"++s++"'::"++show t1++", but it should have type "++show t2++" instead"
tell2 (C(s,t1,t2)) = "the constructor #"++s++"::"++show t1++", but it should have type "++show t2++" instead"
tell2 (A(s,n,m)) = "the type '"++s++"' has arity "++show n++", but it should have arity "++show m++" instead"
-----------------------------------------------------------------      
-- We use types to infer and check that an Exp
-- is used consistently. We make some effort to report
-- errors in a useful way. Our language is polymorphic
                   
-- compute fresh versions of a type for a variable bound in an env

findAndFresh message pos env v =
  case lookup v env of
    Just sch -> instantiate sch
    Nothing -> error (show pos ++ "\nUnknown "++message++" name in type inference: "++v)

findConAndFresh p c cs = do { t <- findAndFresh "constructor" p cs c; return(select t) }
  where select (TyFun doms rng) = (doms,rng)
        select rng = ([],rng)

-- check that an Exp has a certain type. Report an error if it doesn't

check:: Static -> Exp -> Typ -> String -> IO ()
check vs exp typ1 message =
  do { typ2 <- infer vs exp
     ; unify typ1 typ2 (loc exp) 
          ["\nChecking "++message
          ,"\nWhile inferring the type of\n   "++show exp
          ,"\nExpected type: "++show typ1
          ,"\nComputed type: "++show typ2
          ]}
    
-- A type inference function for Exp. Infer a type
-- for every syntactic form of Exp.
    
infer:: Static -> Exp -> IO Typ
infer vs term = trace1 compute vs term where
  compute vs (term@(Var s pos)) = findAndFresh "variable" pos (vars (items vs)) s
  compute vs (term@(Int pos n)) = return intT 
  compute vs (term@(Char pos c)) = return charT
  compute vs (term@(String pos s)) = return(stringT pos)
  compute vs (term@(Bool pos b)) = return boolT 
  compute vs (term@(Local es body)) =
   do { let split [] = return vs
            split (Var x p : e : more) = 
              do { t <- infer vs e
                 ; env <- split more
                 ; return(addVarS False (loc body) (x,Sch [] t) env)}
                 -- ; return(env{vars=(x,Sch [] t):(vars env)})}
      ; vs2 <- split es
      ; infer vs2 body }
  compute vs (term@(Lambda p formals e)) = 
    do { let fresh v = do { sch <- freshScheme; return(v,sch)}
             typesOf (v,Sch [] t) = prune t
       ; delta <- mapM fresh formals
       ; rng <- infer (foldr (addVarS False p) vs delta) e
                -- infer (vs{vars=delta++(vars vs)}) e
       ; doms <- mapM typesOf delta
       ; return(TyFun doms rng)}
 
  compute vs (term@(Asgn e1 e2)) =
   do { t1 <- infer vs e1
      ; t2 <- infer vs e2
      ; unify t1 t2 (loc2 e1 e2) 
         ["\nWhile inferring the term\n   "++show term
         ,"\nThe l-value and the r-value have different types"]           
      ; return t2}      
  compute vs (term@(Write e)) =
   do { t1 <- infer vs e
      ; return intT} 
  compute vs (term@(Block es)) =
   do { ts <- mapM (infer vs) es
      ; return (last ts)}
  compute vs (term@(At f pos es)) = 
   do { expected <- infer vs f -- findAndFresh "function" pos (snd vs) f  
      ; rng <- freshType
      ; ds <- mapM (infer vs) es
      ; unify expected (TyFun ds rng) (loc term) [show term]
      ; zonk rng }
  compute vs (term@(If x y z)) =
   do { check vs x boolT "if statement test"
      ; t1 <- infer vs y
      ; t2 <- infer vs z
      ; unify t2 t1 (loc term)
          ["\nWhile inferring the term\n   "++show term
          ,"\nThe two branches have different types" ]
      ; return t1}
  compute vs (term@(Add x y)) =
   do { check vs x intT "(+)"
      ; check vs y intT "(+)"
      ; return intT}
  compute vs (term@(Sub x y)) =
   do { check vs x intT "(-)"
      ; check vs y intT "(-)"
      ; return intT}
  compute vs (term@(Mul x y)) =
   do { check vs x intT "(*)"
      ; check vs y intT "(*)"
      ; return intT}
  compute vs (term@(Div x y)) =
   do { check vs x intT "(/)"
      ; check vs y intT "(/)"
      ; return intT}
  compute vs (term@(Leq x y)) =
   do { check vs x intT "(<=)"
      ; check vs y intT "(<=)"
      ; return boolT}  
  compute vs (term@(Ceq x y)) =
   do { check vs x charT "(=)"
      ; check vs y charT "(=)"
      ; return boolT}

  compute vs (term@(While tst body)) =
   do { check vs tst boolT "while test"
      ; x <- infer vs body
      ; return intT }
  compute vs (term@(Construction p c es)) = 
    do { (doms,rng) <- findConAndFresh p c (constrs (items vs))
       ; let validate [] [] = return ()
             validate (e:es) (t:ts) = 
               do { check vs e t ("construction arg "++show e); validate es ts}
             validate [] (t:ts) = error("Too few args in construction\n  "++show term)
             validate (e:es) [] = error("Too many args in construction\n  "++show term)
       ; validate es doms
       ; zonk rng}
  compute vs (term@(Selection p c n e)) =
    do { (doms,rng) <- findConAndFresh p c (constrs (items vs))
       ; when (length doms == 0) (error ("Selection out of bounds\n   "++show term++"\n"++c++" is nullary, it has no fields."))
       ; when (n >= length doms)
              (error ("Selection out of bounds\n   "++show term++"\nindex should be less than "++show(length doms)))
       ; check vs e rng ("selection !"++c++" "++show n++" arg")
       ; zonk(doms !! n)}
  compute vs (term@(Predicate p c e)) =
    do { (doms,rng) <- findConAndFresh p c (constrs (items vs))
       ; check vs e rng ("predicate ?"++c++" arg")
       ; return boolT }

--------------------------------------------------------
-- Not implemented features, and tracing the
-- type checker.

notYet pos = 
  do { putStrLn (pos++" typechecking failed: unimplemented")
     ; freshType }
     
sh (Int pos n) = show n
sh (Char pos c) = show c
sh (Bool pos b) = show b
sh (String pos s) = show s
sh x = show(loc x)

traceIndent1 = unsafePerformIO (newIORef 0)
trace1 compute vs term = 
  do { indent <- readIORef traceIndent1
     ; writeIORef traceIndent1 (indent+1)
     ; ans <- compute vs term
     ; typ <- zonk ans
     -- ; putStrLn(PP.render(jline indent vs term typ))
     ; writeIORef traceIndent1 indent
     ; return typ
     }


jline n vs term typ = PP.hcat [indent n " ",pp term,txt ": ",ppTyp typ]
 
---------------------------------------------------------------
-- The State of the Machine consists of a Heap
-- The machine also uses two Tables mapping names to their bindings.
--------------------------------------------------------------------


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

-- Access n consectutive values in the heap
accessN n addr (State heap) = take n (drop addr heap)


-- Allocate a new location in the heap. Intitialize it
-- with a value, and return its Address and a new heap.
alloc :: Value -> State -> (Addr,State)
alloc value (State heap) = (addr,State (heap ++ [value]))
   where addr = length heap

-- Allocate "n" new location sin the heap. Intitialize it
-- with the list of values "v", and return the first of
-- "n" consecutive addresses, and new heap.   
allocate :: Int -> [Value] -> State -> (Addr,State)
allocate n vs state | (n /= (length vs)) = error ("allocate with bad length: "++show n)
allocate 0 vs (State heap) = (error "pull on address of nullary constructor",State heap)
allocate n vs (State heap) = (addr,State(heap ++ vs))
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

foldM acc state [] = return state
foldM acc state (x:xs) =  do { state2 <- acc x state; foldM acc state2 xs}
 

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

stringToValue:: State -> String -> (Value,State)
stringToValue state xs = foldr cons (ConV "nil" 0 0,state) xs
  where cons x (tail,state) = (ConV "cons" 2 addr,state2)
           where (addr,state2) = allocate 2 [CharV x,tail] state
                 
unTab (Tab x) = x                 

run x = interpE emptyE (State []) x

interpE :: Env Addr                    -- the variable name space
        -> State                       -- the machine state, which is a heap
        -> Exp                         -- the Exp to interpret
        -> IO(Value,State)             -- (result,new_state)
interpE vars state exp = (traceG vars) -- this term: "(traceG vars)" enables tracing
                                       -- comment it out to get rid of tracing.
                         run state exp where
   run state (Var v pos) = 
     case lookUp vars v of
       Found addr -> pull(access addr state,state)  -- might be a global thunk, so pull on it
       NotFound -> error ("Unknown variable: "++v++" in runtime lookup.")
   
   run state (Int pos n) = return(IntV n,state)
   run state (Bool pos b) = return(BoolV b,state)
   run state (Char pos c) = return(CharV c, state)
   run state (String ps s) = return(stringToValue state s)

   run state (Asgn e1 e2 ) = 
     do { (val,state2) <- interpE vars state e2
        ; (addr,state3) <- addressOf vars state2 e1
        ; return(val,stateStore addr val state3)}
   run state (term@(At f pos args)) = 
     do { (fv,state2) <- interpE vars state f >>= pull
        ;(actuals,state3) <- interpList vars state2 args 
        ; let apply state4 (FunV name env (f:fs) body) (v:vs) =
                do { let (addr,state5) = alloc v state4
                   ; apply state5 (FunV name (extend f addr env) fs body) vs }
              apply state4 (FunV name (env@(Tab pairs)) [] body) [] = 
                  interpE env state4 body
              apply state4 (fun@(FunV _ _ (f:fs) _)) [] = return(fun,state4)
              apply state4 (FunV name env [] body) (v:vs) = 
                do { (fun,state5) <- interpE env state4 body >>= pull
                   ; apply state5 fun (v:vs) }
              apply state4 v vs = error("Non function\n   "++show v++"\nin application\n   "++show term)
        ; apply state3 fv actuals
        }
         
   run state (term@(Lambda p vs e)) = return(FunV ("\\"++show (lineCol p)) vars vs e,state)

   run state (While tst body)= while state
     where while state = 
             do { (v,state2) <- interpE vars state tst
                ; test state2 "while" v
                       (do { (_,state3) <- interpE vars state2 body
                           ; while state3})
                       (return(IntV 0,state2))}   
                       
   run state (If x y z) = 
     do { (v,state2) <- interpE vars state x
        ; test state2 "if" v (interpE vars state2 y) (interpE vars state2 z) }  
   
   run state (Write x)  = 
     do { (v1,state1) <- interpE vars state x
        ; putStrLn (showV (v1,state1))
        ; return(v1,state1)}

   run state (Block es) = 
     do { let last [] = (IntV 0)  -- empty block returns 0
              last [x] = x
              last (x:xs) = last xs
        ; (vs,state2) <- interpList vars state es
        ; return(last vs,state2)}

   run state (Add  x y) = 
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; return(numeric state2 "+" (\ x y -> IntV(x+y)) v1 v2,state2) }

   run state (Sub  x y) =
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; return(numeric state2 "-" (\ x y -> IntV(x-y)) v1 v2,state2) }      

   run state (Mul  x y) = 
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; return(numeric state2 "*" (\ x y -> IntV(x*y)) v1 v2,state2) }   

   run state (Div  x y) = 
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; return(numeric state2 "/" (\ x y -> IntV(div x y)) v1 v2,state2) }   

   run state (Leq  x y) = 
     do { (v1,state1) <- interpE vars state x
        ; (v2,state2) <- interpE vars state1 y
        ; return(numeric state2 "<=" (\ x y -> BoolV(x <= y)) v1 v2,state2) }        

   run state (Ceq  x y) = 
     do { (v1,state1) <- interpE vars state x >>= pull
        ; (v2,state2) <- interpE vars state1 y >>= pull
        ; case (v1,v2) of 
            (CharV x,CharV y) -> return(BoolV(x==y),state2)
            (x,CharV _) -> error ("first arg to 'chareq' is not Char: "++show x) 
            (CharV _,x) -> error ("second arg to 'chareq' is not Char: "++show x) 
            other -> error ("neither arg to 'chareq' is a Char: "++show other)}         

   run state (Local pairs body) = 
     do { let split (Var v p : e : zs) (vs,es) = split zs (vs++[v],es++[e])
              split _ (vs,es) = (vs,es)
              (vs,es) = split pairs ([],[])
        ; (vals,state2) <- interpList vars state es 
        ; let (pairs,state3) = bind vs vals state2  
        ; interpE (push pairs vars) state3 body }
        
   run state (Construction p c es) = 
     do { (vals,state2) <- interpList vars state es
        ; let count = length es
              (addr,state3) = allocate count vals state2
        ; return(ConV c count addr,state3)}
        
   run state (term@(Selection p c n e)) = 
     do { (v,state2) <- interpE vars state e >>= pull
        ; case v of
            (ConV d m addr) | c==d && n<m -> return(access (addr+n) state2,state2)
            (ConV d m addr) | not(c==d) -> error ("Construction\n   "++showV(v,state2)++"\ndoesn't match in Selection\n   "++show term)
            (ConV d m addr) | not(n<m)  -> error ("Selection out of bounds\n   "++show term++"\nout of bounds\n   "++showV(v,state2))            
            other -> error ("Non Construction\n   "++showV(v,state2)++"\n in Selection\n   "++show term)}        
            
   run state (term@(Predicate p c e)) = 
     do { (v,state2) <- interpE vars state e >>= pull
        ; case v of
            (ConV d m addr) | c==d -> return(BoolV True,state2)
            (ConV d m addr) -> return(BoolV False,state2)
            other -> error ("Non Construction\n   "++showV(v,state2)++"\n in Predicate\n   "++show term)}        
            

-- Compute the l-value of an expression. Used in assignment.
-- Only variables and Selection calls indicate addresses.

addressOf vars state (Var v pos) =
   case lookUp vars v of
     Found addr -> return (addr,state)
     NotFound -> error ("\nUnknown variable: "++v++" in assignment.") 
addressOf vars state (term@(Selection pos c n e)) =
  do { (v,st) <- interpE vars state e >>= pull 
     ; case v of
         (ConV d m addr) | c==d && n<m -> return (addr,st)
         other -> error ("\nNon match\n   "++showV(other,st)++
                         "\nas argument to selection\n   "++show term++
                         "\nin assignment.") }
addressOf vars state e =
  error ("Exp with no l-value in assignment: "++show e)
     

-- interpret a list from left to right. Be sure the
-- state is updated for each element in the list.

interpList vars state [] = return([],state)
interpList vars state (e:es) = 
  do { (v,state1) <- interpE vars state e
     ; (vs,state2) <- interpList vars state1 es
     ; return(v:vs,state2)}

elab
  :: Bool
     -> Static
     -> Def
     -> (Env Addr, t)
     -> (Env Addr, State)
     -> IO (Env Addr, State)
     
elab loud static (FunDef pos f t vs e) loop (vars,state) =
  let closure = FunV f finalvars (map fst vs) e
      (addr,state2) = alloc closure state
      (finalvars,_) = loop     
  in return (extend f addr vars, state2)
elab loud static (GlobalDef pos v mt e) (loop@(~(finalvars,_))) (vars@(Tab pairs),state) =
  do { -- we create a thunk for the value, since the evaluation of 'e'
       -- might involve a function call, where the env of its closure (fst loop)
       -- hasn't been completed yet. Without thunks the cyclic nature of the env
       -- of the closure could cause an infinite loop.
     ; f <- memoize (\ s -> interpE finalvars s e)
     ; let value = Thunk v f
     ; let (addr,state3) = alloc value state
     ; return(extend v addr vars,state3)}     
elab loud static (DataDef pos c vs cls) loop (vars,state) = return(vars,state)
elab loud static (AdtDef pos c vs ts ds) loop ts1 = elaborate loud static ds ts1 loop
elab loud static (ImportDef os path sig mprog) loop (vars,state) = 
  case lookup path (imported static) of
    Nothing -> error("Missing import info: "++show path)
    Just(loadfun) -> loadfun static (vars,state)
            
elaborate loud static [] ts loop = return ts
elaborate loud static (d:ds) ts loop = 
  do { when loud (putStr (plistf id "" (defName d) " " " "))
     ; ts1 <- elab loud static d loop ts
     ; elaborate loud static ds ts1 loop}




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
loc (Lambda p vs e) = p
loc (Asgn x y) = posAdd (loc x) (loc y)
loc (Write e) = loc e
loc (Block es) = locL es
loc (At f p es) = p
loc (Bool p b) = p
loc (While x y) = posAdd (loc x) (loc y)
loc (If x y z) = posAdd (posAdd (loc x) (loc y)) (loc z)
loc (Int p n) = p
loc (Add x y) = posAdd (loc x) (loc y)
loc (Sub x y) = posAdd (loc x) (loc y)
loc (Mul x y) = posAdd (loc x) (loc y)
loc (Div x y) = posAdd (loc x) (loc y)
loc (Leq x y) = posAdd (loc x) (loc y)
loc (Ceq x y) = posAdd (loc x) (loc y)
loc (Char p c) = p
loc (String p s) = p

loc (Construction p x es) = p
loc (Selection p c n x) = p
loc (Predicate p c x) = p

                                     
--------------------------------------------------------------------------
-- A parser that reads a file and produces a program in abstract syntax
-- Most of this section is boilerplate
-- The interesting functions are "operatorP" and "expP"

-- A Exp is either a an Atom or a list like thing: (tag x1 x2 ... xn)
-- Depending upon the "tag" a different number (and type) of xi are expected.
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

atSign pos (f:args) = At f pos args
atSign pos [] = error ("Near "++show pos++" ill formed function call.")

local vs pos [x] = Local vs x
local vs pos args = report pos (length args) 1 "local"

lambda vs pos [x] = Lambda pos vs x
lambda vs pos args = report pos (length args) 1 "\\"

assign pos [x,y] = Asgn x y
assign pos args = report pos (length args) 2 ":="

construction pos (Var c p: xs) = Construction p c xs
construction pos args = error ("Near "++show pos++"\nfirst argument to '#' is not a constructor name.")

selection pos [Var c p,Int _ n,x] = Selection p c n x
selection pos args | length args /= 3 = report pos (length args) 3 "!"
selection pos [e,Int p n,x] = error ("Near "++show pos++"\nfirst argument to '!' is not a constructor name: "++show e)
selection pos [Var _ _,e,x] = error ("Near "++show pos++"\nsecond argument to '!' is not a literal integer: "++show e)

predicate pos [Var c p,x] = Predicate p c x
predicate pos args | length args /= 2 = report pos (length args) 2 "?"
predicate pos args = error ("Near "++show pos++"\nfirst argument to '?' is not a constructor name.")

-- This function parses a string, but returns a function with type: 
-- SourcePos -> [Exp] -> Exp .  See "lowercase" constructors above.
-- There are many cases, one for each of the legal constructors to Exp.
-- To add to the parser, write a new function "f" then add " <|> f "
-- to the definition of "operatorP"

operatorP = plus <|> times <|> minus <|> divid <|> ltheq <|> ceqP <|>
            asg <|> atP <|> blck <|> writ <|> iff <|> whil <|>
            localP <|> lambdaP <|> con <|> sel <|> pred
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
        con    = do { symbol xxx "#"; return construction}
        sel    = do { symbol xxx "!"; return selection}
        pred   = do { symbol xxx "?"; return predicate}
        lambdaP = do { try(symbol xxx "lambda")
                     ; vs <- parenS(many var)
                     ; let name (Var s pos) = s
                     ; return(lambda (map name vs))}
        localP = do { try(symbol xxx "local")
                    ; let pair = do { v <- var; e <- expP; return[v,e]}
                    ; vs <- parenS(do { ps <- many pair; return(concat ps)}) <?> "'local var-value list'"
                    ; return (local vs)}
        

--------------------------------------------
-- Parse variable like things

var = (do { pos <- getPosition
          ; s <- smallId 
          ; return(Var s pos)}) <?> "<var (starts with lower case)>"

-- An identifer that starts with a lower case letter
smallId = identifier xxx          
-- An identifier that starts with a Capital letter
capId = lexemE(do { cap <- upper
                 ; post <- many (lower <|> upper <|> digit)
                 ; return(cap:post)})  <?> "<Type name (starts with a capital letter)>"          

--------------------------------------------------------------------------        
-- Parse n expression.  Either an atom or a Lisp like parenthesized list.

expP = try atom <|> sexpr
  where atom = constant <|> charP <|> stringP <|> trueP <|> falseP <|> var
        constant = 
           do { p <- getPosition
              ; n <- lexemE(number 10 digit)
              ; return (Int p n)}
        charP = do { p <- getPosition; c <- charLiteral xxx; return(Char p c)}
        stringP = do { p <- getPosition; c <- stringLiteral xxx; return(String p c)}        
        trueP = try(do { p<- getPosition; symbol xxx "True"; return(Bool p True)}) 
        falseP = try(do { p<- getPosition; symbol xxx "False"; return(Bool p False)})               
        sexpr  = 
           do { symbol xxx "(" 
              ; pos <- getPosition
              ; constrByList <- operatorP  -- Parse a string, get a lowercase constructor
              ; args <- many expP
              ; symbol xxx ")"
              ; return(constrByList pos args)}
        

---------------------------------------------------        
-- Parse a Def 

defP = parenS ( global <|> function <|> (dataP "def" DataDef) <|> adt <|> importP )

global =
   (do { symbol xxx "global"
       ; v <- smallId
       ; pos <- getPosition
       ; mt <- typP
       ; e <- expP
       ; return(GlobalDef pos v mt e)}) <?> "<global def>"
             
function = 
 (do { symbol xxx "fun"
     ; f <- smallId
     ; pos <- getPosition
     ; rng <- typP
     ; let arg = do { x <- smallId; t <- typP; return(x,t)}
     ; vs <- parenS(many arg)
     ; body <- expP
     ; return(FunDef pos f rng vs body)}) <?> "<fun def>"

dataP key datacon = 
  (do { symbol xxx "data"
      ; pos <- getPosition
      ; let args = (many (do { c <- lexemE lower;return[c]})) <|> (return [])
      ; (c,vs) <- parenS (do { c <- capId; vs <- args; return (c,vs)})    
      ; let clause = do { lexemE (char '#')
                        ; c <- smallId
                        ; ts <- many typP
                        ; return(c,ts)}
      ; clauses <- many(parenS clause)
      ; return(datacon pos c vs clauses)}) <?> ("<data "++key++">")
     
adt = 
  (do { symbol xxx "adt"
      ; pos <- getPosition
      ; let args = (many (do { c <- lexemE lower;return[c]})) <|> (return [])
      ; (c,vs) <- parenS (do { c <- capId; vs <- args; return (c,vs)})   
      ; body <- typP
      -- Only values can appear in and abstract data definition.
      ; methods <- many(parenS ( global <|> function ))
      ; return(AdtDef pos c vs body methods)}) <?> "<adt def>"

importP =
  (do { symbol xxx "import"
      ; pos <- getPosition
      ; path <- stringLiteral xxx
      ; symbol xxx "implementing"
      ; s <- sigExpP
      ; return(ImportDef pos path s Nothing)}) <?> "<import def>"
  
---------------------------------------------
-- Parse a Sig item

sigP = parenS(valueSig <|> typeSig  <|> (dataP "item" DataItem))

valueSig =
  (do { symbol xxx "val"
      ; v <- (smallId) 
      ; pos <- getPosition
      ; ty <- typP
      ; return(ValItem pos v ty)}) <?> "<val item>"
              
typeSig =  
  (do { symbol xxx "type"
      ; pos <- getPosition
      ; (v,args) <- parenS(do { v <- capId
                              ; args <- many smallId
                              ; return (v,args)})
      ; return(TypItem pos v args)}) <?> "<type item>"
      
  
              
-------------------------------------------------------
-- Parse a Typ
   
typP = (try stringP <|> namedP <|> varP <|> parensP <|> listP) <?> "<typ>"
  where listP = do { pos <- getPosition; brackets xxx (lift1 (tylist pos) typP)}
        stringP = do {  pos <- getPosition; symbol xxx "String"; return (stringT pos)}
        namedP = do { pos <- getPosition; c <- capId; return(TyCon pos c [])}
        varP = lift1 (\ x -> TyVar [x]) (lexemE lower)

parensP = parens xxx ( try(do { t <- typP; postfix t}) )   

postfix x = case x of
             (TyCon p c []) -> pairPost <|> arrPost <|> (args c) <|> (return x)
             other -> pairPost <|> arrPost <|> (return x)
  where args c = do { p <- getPosition; ts <- many1 typP; return(TyCon p c ts)}
        pairPost = do { p <- getPosition; symbol xxx ".";  y <- typP; return(typair p x y)}
        arrPost = do { symbol xxx "->"
                     ; ts <- sepBy1 typP (symbol xxx "->")
                     ; let make [t] = t
                           make ts = TyFun (take n ts) (last ts) where  n = length ts - 1
                     ; return(make (x:ts))}

--------------------------------------------------------
-- Parse a SigExp

sigExpP = ( try prelude <|> try everything  <|> name <|> parenS core) <?> "<sigExp>"
  where name = fmap NameExp capId
        prelude = do { symbol xxx "prelude"; return PreludeExp} <?> "<prelude exp>"
        everything = do { symbol xxx "everything"; return AllExp} <?> "<everything exp>"        
        core = sig <|> union <|> hide --  <|> file
        sig =  do { symbol xxx "sig"
                   ; ss <- many sigP
                   ; return(ExplicitExp ss)} <?> "<explicit sig exp>"
        union = do { symbol xxx "union"
                   ; ss <- many sigExpP
                   ; return(UnionExp ss)} <?> "<union exp>" 
        hide = do { symbol xxx "hide"
                  ; x <- sigExpP
                  ; ss <- (many (capId <|> smallId))
                  ; return(HideExp x ss)} <?> "<hide exp>"  
                
                  
signatureP = parenS(sig)
  where sig = do { pos <- getPosition
                 ; try (symbol xxx "signature")
                 ; name <- capId
                 ; file <- stringLiteral xxx
                 ; return(Sig pos name file)}
                 
--------------------------------------------------------
-- Parse a module introduction

modP = parenS (do { symbol xxx  "module"; n <- capId
                  ; p <- getPosition
                  ; s1 <- inP
                  ; s2 <- outP
                 -- ; (s1,s2) <- sigs
                  ; return(Mod p n s1 s2)}) <?> "<module>"
  where sigs = inout <|> out 
        out = (do { symbol xxx "out"; s <- sigExpP; return(PreludeExp,s)})
              <|> (return(PreludeExp,AllExp))
        inout = do { symbol xxx "in"; s1 <- sigExpP; (_,s2) <- out; return(s1,s2)}

importPred = (implements <|> hiding) <?> "<import predicate>"

inP = (do { symbol xxx "in"; s1 <- sigExpP; return(s1)}) <|> 
      (return(PreludeExp)) <?> "<optional 'in' pred>"
outP = (do { symbol xxx "out"; s1 <- sigExpP; return(s1)}) <|> 
       (return(AllExp)) <?> "<optional 'out' pred>"
implements = 
  (do { symbol xxx "implements"; s1 <- sigExpP; return(s1)}) <?> "<implements pred>"
hiding = 
  (do {symbol xxx "hiding"
      ;ss <- parenS (many (capId <|> smallId))
      ; return((HideExp AllExp ss))}) <?> "<hiding pred>"
        
     
                           
------------------------------------------------------------
-- Parse things we expect to take up a whole file.
      
sigFile2 = 
  (do { ss <- many (try signatureP)
      ; (pos,c,e) <- parenS
                      (do { symbol xxx "defsig"
                          ; pos <- getPosition
                          ; c <- capId
                          ; e <- sigExpP
                          ; return(pos,c,e)})
      ; return(pos,ss,c,e)}) <?> "<signature def>" 
            
-- Parse a Prog              
progP = do { ss <- many (try signatureP)
           ; m <- modP
           ; p <- getPosition
           ; ds <- many defP
           ; symbol xxx "main"
           ; e <- expP
           ; return(Prog ss m ds e)}


------------------------------------------------------------------
-- Parsing Boilerplate below here        
------------------------------------------------------------------
       
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
ppExp (At f p args)= txt "(@ " PP.<> PP.nest 3 (PP.sep (ppExp f : ppMany args))
ppExp (Bool p b) = txt (show b)
ppExp (While x y)= txt "(while " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (If x y z)= txt "(if " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y,ppExp z PP.<> txt ")"])

ppExp (Int p n) = txt (show n)
ppExp (Add  x y)  = txt "(+ " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Sub  x y)  = txt "(- " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Mul  x y) = txt "(* " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Div  x y)  = txt "(/ " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Leq  x y) = txt "(<= " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])

ppExp (Char p c) = txt (show c)
ppExp (String p s) = txt(show s)
ppExp (Ceq x y) = txt "(= " PP.<> PP.nest 3 (PP.sep [ppExp x , ppExp y PP.<> txt ")"])
ppExp (Local vs e) = txt "(local " PP.<> PP.nest 3 ( vars PP.$$ ppExp e PP.<> txt ")")
  where pairs = f vs
        f (x:y:zs) = (x,y): f zs
        f _ = []
        vars :: PP.Doc
        vars = PP.parens(PP.sep (map h pairs))
        h (x,y) = PP.sep [ppExp x,ppExp y]
ppExp (Lambda p vars e) = txt "(\\ " PP.<> PP.nest 3 (PP.sep [vs, ppExp e PP.<> txt ")"])
  where vs = PP.parens(PP.sep(map txt vars))
ppExp (Construction p c args) = 
   txt "(# " PP.<> PP.nest 3 (PP.sep (txt c : ppMany args))
ppExp (Selection p c n arg) = 
   txt "(! " PP.<> PP.nest 3 (PP.sep [txt c,txt (show n),ppExp arg PP.<> txt ")"])   
ppExp (Predicate p c arg) = 
   txt "(? " PP.<> PP.nest 3 (PP.sep [txt c,ppExp arg PP.<> txt ")"])

     

ppMany [] = [txt ")"]
ppMany [x] = [ppExp x PP.<> txt ")"]
ppMany (x:xs) = ppExp x : ppMany xs
   

ppSig (ValItem pos v t) = txt "(val " PP.<> PP.nest 3 (PP.sep [txt v, ppTyp t PP.<> txt ")"])
ppSig (TypItem pos t vs) = PP.parens(PP.sep [txt "type", PP.parens(PP.sep (txt t : (map txt vs)))])
ppSig (DataItem pos c vs cls) = PP.parens
     ((PP.sep [txt "data",txt c,PP.parens(PP.sep (map txt vs))]) PP.$$
      (PP.nest 3 (PP.vcat (map f cls))))
  where f (c,ts) = PP.parens(PP.sep (txt ("#"++c) : map ppTyp ts))

instance Show SigItem where
  show x = PP.render(ppSig x)


ppDef (GlobalDef pos v t e) = txt "(global " PP.<> PP.nest 3 (PP.sep [txt v,ppTyp t, ppExp e PP.<> txt ")"])
ppDef (FunDef pos f t args body) = 
    txt "(fun " PP.<> PP.nest 3 (PP.sep [txt f PP.<+> ppTyp t, PP.parens (PP.sep (map g args)),ppExp body PP.<> txt ")"])
  where g (x,t) = txt x PP.<+> ppTyp t
ppDef (DataDef pos c vs cls) = PP.parens
     ((PP.sep [txt "data",PP.parens(PP.sep (txt c: (map txt vs)))]) PP.$$
      (PP.nest 3 (PP.vcat (map f cls))))
  where f (c,ts) = PP.parens(PP.sep (txt ("#"++c) : map ppTyp ts))
ppDef (AdtDef pos c vs typ ds) = PP.parens
     ((PP.sep [txt "adt",PP.parens(PP.sep (txt c: (map txt vs))),ppTyp typ]) PP.$$
      (PP.nest 3 (PP.vcat (map ppDef ds)))) 
ppDef (ImportDef pos path sig mprog) = PP.parens(PP.sep[txt "import",txt(show path),ppSigExp sig ]) 
-- ppDef (FileDef pos s) = PP.parens(PP.sep [txt "signature ", txt(show s)])

  
  
ppProgram (Prog sigs mod ds e) = 
  PP.vcat ((map ppSignature sigs)++[ppMod mod]++map ppDef ds ++ [txt "\nmain\n",ppExp e])
 
ppSigExp (NameExp s) = txt s
ppSigExp (ExplicitExp ss) =
  PP.parens(PP.sep(txt "sig" : (map ppSig ss)))
ppSigExp PreludeExp = txt "prelude"
ppSigExp AllExp = txt "everything"
ppSigExp (HideExp x cs) = 
  PP.parens(PP.sep([txt "hide",ppSigExp x]++map txt cs))
ppSigExp (UnionExp xs) =
  (PP.parens(PP.sep(txt "union" : map ppSigExp xs)))
-- ppSigExp (FileExp pos s) = PP.parens(PP.sep [txt "file ", txt(show s)])  

ppSigPred key x = txt key PP.<+> ppSigExp x


ppSignature (Sig pos c ss) = 
  PP.parens(txt "signature" PP.<+> txt c PP.<+> txt(show ss))

instance Show Signature where
  show x = PP.render(ppSignature x)

ppMod (Mod pos name s1 s2) =
  PP.parens(PP.sep [txt "module", txt name, ppSigExp s1,ppSigExp s2])

instance Show Module where
  show x = PP.render(ppMod x)
instance Show SigExp where
  show x = PP.render(ppSigExp x)  
    
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
showV (ConV "nil" 0 _,state) = "[]"
showV (ConV c 0 _,state) = c
showV (ConV "pair" 2 addr,state) = "("++(showV (access addr state,state))++
                                   " . "++(showV (access (addr + 1) state,state))++")"
showV (v,state) | Just xs <- isString (v,state) = show xs  
showV (v,state) | Just xs <- isList (v,state) = plistf f "[" xs "," "]"
  where f x = showV(x,state)
showV (ConV c n addr,state) = plistf f ("("++c++" ") (accessN n addr state) " " ")" 
  where f x = showV(x,state)
showV (v,_) = show v  
 
isList :: (Value,State) -> Maybe [Value]
isList (ConV "nil" 0 addr,state) = Just []
isList (ConV "cons" 2 addr,state) = do { ys <- isList (xs,state); return(y:ys)}
  where y = get addr
        xs = get (addr+1)
        get n = xs !! n where (State xs) = state        
isList other = Nothing

isString :: (Value,State) -> Maybe String
isString (ConV "nil" 0 addr,state) = Just ""
isString (ConV "cons" 2 addr,state) = 
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

instance Show Value where
  show (IntV n) = show n
  show (CharV c) = show c
  show (BoolV b) = show b
  show (FunV f env args body) = "<"++f++" "++show(length args)++">"
  show (ConV nm 0 _) = nm++"@nullary"
  show (ConV nm n addr) = nm++"@"++show addr
  show (Thunk nm f) = "<thunk "++nm++">" 
--   show x = "<value>"


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
indent n x = txt(concat(replicate n " |")++x)

type InterpType = State -> Exp -> IO (Value,State)

traceF :: Env Addr -> InterpType -> InterpType 
traceF env f state exp =
  do { n <- readIORef traceIndent 
     ; putStrLn(PP.render(indent n "> " PP.<> PP.fsep (pp exp : showEnv env state)))
     ; writeIORef traceIndent (n+1)
     ; ans <- f state exp
     ; writeIORef traceIndent n
     ; putStrLn(PP.render(indent n "< " PP.<> txt(showV ans)))
     ; return ans }

-- Like traceF if tracing is on, like f if not.
traceG :: Env Addr -> InterpType -> InterpType 
traceG env f vars exp = 
  do {  b <- readIORef trace_on
     ; if b then traceF env f vars exp else f vars exp }

--------------------------------------------------------------------

printSigSet :: String -> Static -> IO String
printSigSet s static = 
     do { set <- setSemantics noPos ("evaluating sigSet "++show sigExp) 
                     static sigExp
        ; return(show set)}
  where sigExp = parse2 sigExpP (dropWhile (==' ') s)  
   
instance Show Static where
  show x = plistf (shD "") "" (vars (items x)) ", " "" ++
           plistf (shD "#") "\n" (constrs (items x)) ", " "" ++  
           plistf shA "\n" (arities (items x)) ", " "" ++
           plistf shS "\n" (sigs x) "," ""
           
instance Show ItemInfo where
  show x = plistf shA "\n*** Types\n" (arities x) ", " "\n" ++
           plistf (shD "") "*** Vars\n" (vars x) "\n" "\n" ++
           plistf (shD "#") "*** Constructors\n" (constrs x) "\n" ""  
                  

shD tag (v,Sch vs t) = (tag++v++"::"++show t)  
shA (v,n) = plistf id ("("++v++" ") (take n names) " " ")"
shS (v,s) = "sig "++v

-------------------------------------------
-- Sematics of SigExp. In essence a set of
-- all the names and their uses, captured as a ItemInfo

setSemantics :: SourcePos -> String -> Static -> SigExp -> IO ItemInfo
setSemantics pos message env pred =
  case pred of
    PreludeExp -> return preludeItems
    ExplicitExp ss -> foldM (addSigItem True) emptyItems ss
    AllExp -> return(items env)
          -- error ("'everything' SigExp makes no sense in 'in' clause of module")
    HideExp x names -> 
       do { static <- setSemantics pos message env x
          ; return(diffS static names)}
    UnionExp xs -> 
       let acc x ans = do { y <- setSemantics pos message env x
                          ; return(unionS message y ans)}
       in foldM acc emptyItems xs
    NameExp s -> case lookup s (sigs env) of
                   Nothing -> error (show pos++" Unknown signature: "++s++"\n"++message)
                   Just x -> return x

-- every item in the sig, must be mentioned in the Static.                   
filterSemantics :: SourcePos -> String -> Static -> SigExp -> IO ItemInfo
filterSemantics pos message static sigExp = 
  do { exports <- setSemantics pos message static sigExp
     ; checkSubSet exports (items static)
     ; return exports }

checkSubSet (Item xs ys zs) (Item as bs cs) = undefined

{-
filterSemantics pos message env sig =
  case sig of
    -- assume every set supports the prelude
    -- so the intersection is just the prelude, the smallest legal Static object
    PreludeExp -> return preludeItems  
    -- the intersection of x with itself is just x
    AllExp -> return (items env)
    HideExp AllExp names -> return(diffS (items env) names)
    HideExp x names -> 
       do { set1 <- filterSemantics pos message env x
          ; return(diffS set1 names)}
    ExplicitExp ss -> 
       do { set <- foldM (addSigItem True) preludeItems ss
          ; intersectS message (items env) set}
    -- under the assumption that 
    -- (intersect A (union B C)) = (union (intersect A B) (intersect A C))
    UnionExp xs -> 
       do { let acc x ans = do { y <- filterSemantics pos message env x
                               ; return(unionS message y ans)}
          ; foldM acc preludeItems xs }
    NameExp s -> case lookup s (sigs env) of
                   Nothing -> error (show pos++" Unknown signature: "++s)
                   Just x -> intersectS message (items env) x
-}

-------------------------------------------------------------------------
-- Collecting involves collecting type arity information, and type
-- information from Defs, to be used in a later stage for checking.

collectSignatures:: [Signature] -> IO([(String,ItemInfo)])
collectSignatures xs = getSignatures [] [] xs

collectSigExp :: SigExp -> ItemInfo -> IO ItemInfo
collectSigExp (NameExp nm) info = return info
collectSigExp (ExplicitExp sigItems) info = foldM (addSigItem True) info sigItems
collectSigExp (HideExp ss cs) info = collectSigExp ss info
collectSigExp (UnionExp ss) info = foldM collectSigExp info ss
collectSigExp PreludeExp info = return info
collectSigExp AllExp info = return info

getSignatures history items ss =
  foldM (\ (Sig pos name2 path2) -> getSig (name2,path2) history) items ss

getSig :: (String,String) -> [(String,String)] -> [(String,ItemInfo)] -> IO [(String,ItemInfo)]
getSig (name,path) history items  = case lookup name history of
  Nothing -> 
    case lookup name items of
      Nothing -> 
        do { (pos,sigs,t,exp) <- parseFile sigFile2 path
           ; when (not (name==t)) 
                  (error (show pos++". Signature name "++name++" doesn't match defsig name "++t++"."))
           ; items2 <- getSignatures ((name,path):history) items sigs
           ; env <- collectSigExp exp preludeItems
           ; checkSigExp pos env exp
           ; info <- setSemantics pos 
                         (show pos++" (defsig "++name++" "++show exp++")")
                         (Static emptyItems items2 []) exp
           ; return((name,info):items2)
           }
      Just info -> return items                       
  Just p -> error(plistf (\ (nm,f) -> nm ++" "++show f)
                      "Cycle in signature files\n   " 
                      (reverse history ++ [(name,path)])
                      " calls\n   " "\n")
 
 
 -- This parses all the imports directly after parsing the main file.         
parseProg loud path =
  do { when loud (putStrLn ("******** PARSING "++path++" ******************"))
     ; (Prog sigs mod ds exp) <- parseFile progP path
     ; let acc [] = return []
           acc (ImportDef pos nm sig Nothing : ds) =
              do { prog <- parseProg loud nm
                 ; ds2 <- acc ds
                 ; return(ImportDef pos nm sig (Just prog) : ds2)}
           acc (d:ds) = do { ds2 <- acc ds; return(d:ds2)}
     -- ; ds2 <- acc ds
     -- ; return(Prog sigs mod ds2 exp)
     ; return (Prog sigs mod ds exp)}         

----------------------------------------------------------------------
-- Checking involves looking at things a seeing that they are used
-- consitently with their intorductions. For types in SigItems and other
-- things this means that arities are consistent. A simple Kind-check

checkSigItem:: SourcePos -> ItemInfo -> SigItem -> IO ()     
checkSigItem pos env (ValItem p v t) = checkArity pos (arities env) t
checkSigItem pos env (TypItem p t args) = checkArity pos (arities env) (TyCon pos t (map TyVar args))
checkSigItem pos env (DataItem pos2 c vs cls) = checkD env (DataDef pos2 c vs cls)
   where checkD env (DataDef pos c vs cls) = mapM_ checkCl cls
             where checkCl (c,ts) = mapM_ (checkArity pos (arities env)) ts

checkSigExp :: SourcePos -> ItemInfo -> SigExp -> IO ()
checkSigExp pos env (NameExp nm) = return ()
checkSigExp pos env (ExplicitExp ss) = mapM_ (checkSigItem pos env) ss 
checkSigExp pos env (HideExp ss cs) = checkSigExp pos env ss
checkSigExp pos env (UnionExp ss) = mapM_ (checkSigExp pos env) ss         
checkSigExp pos env other = return ()             


-- Checking Declarations involves arity checking on types, and
-- type checking expressions in Declarations.

checkD :: Static -> Def -> IO ()
checkD env (GlobalDef pos v t e) =
  do { checkArity pos (arities (items env)) t
     ; t <- findAndFresh "global" noPos (vars (items env)) v
     ; check env e t ("global def: "++v)}
checkD env (FunDef pos f rng args body) =
  do { let acc (v,t) env = 
             do { checkArity pos (arities env) t
                ; sch <- normTyp t
                 -- here duplicates hide earlier names
                ; return(env{vars=(v,sch):(vars env)})}
     ; env2 <- foldM acc (items env) args
     ; checkArity (loc body) (arities env2) rng
     ; check (env{items=env2}) body rng ("body of fundef: "++f)}
checkD env (DataDef pos c vs cls) = mapM_ checkCl cls
   where checkCl (c,ts) = mapM_ (checkArity pos (arities (items env))) ts   
checkD env (AdtDef pos c vs typ ds) = 
  do { checkArity pos (arities (items env)) typ
     ; ds2 <- mapM (transform pos c vs typ (arities (items env))) ds
     ; env2 <- foldM (addDef False) env ds2
     ; mapM_ (checkD env2) ds2}         
checkD env (ImportDef pos path pred mprog) = checkSigExp pos (items env) pred

------------------------------------------------------------------------------
-- Add static info for each introduction, i.e. Def or Sig element.
-- Later we will check if this information is used consistently using "checks"
-- addX adds information for an X-object to a Static environment.

-- Add a list of Defs in the context of some signatures and module def.

touch message (Item as cs vs) =
  case (length as + length cs + length vs < 0 ) of
    False -> putStrLn(message)

addModule:: [(String,ItemInfo)] -> Module -> [Def] -> Exp -> IO (ItemInfo,ItemInfo,Static)
addModule sigPairs (Mod pos name inSigExp outSigExp) ds exp = 
  do { checkSigExp pos preludeItems inSigExp
     ; let message = ("module "++name++" 'in' "++show inSigExp)
     ; imports <- setSemantics pos message
                     (Static preludeItems sigPairs []) inSigExp
     ; touch ("Checking "++name++" 'in' "++show inSigExp) imports
     -- add types of each Def, to be checked later
     ; static1@(Static env pairs imps) <- foldM (addDef True) (Static imports sigPairs []) ds
     -- Now check that each Def is consistent with its type            
     ; mapM (checkD static1) ds      
     ; expTyp <- infer static1 exp  -- check the body too!
     -- remove any residual fresh type variables.
     ; let crush (v,sch) = do { sch2 <- normSch sch; return(v,sch2)}
     ; vs2 <- mapM crush (vars env) 
     ; let static2 = static1{ items=(env{vars=vs2}) }
           message = "Near :"++show pos++"\nthe inferred item is inconsistent with the same item from the 'out' sig\n   "++show outSigExp
     -- compute what should be exported, filter out the rest
     ; checkSigExp pos env outSigExp     
     ; exports <- setSemantics pos message static2 outSigExp 
     ; touch ("Checking "++name++" 'out' "++show outSigExp) exports
     ; bad2 <- legalSubset exports (items static2)
     ; when (not (null bad2)) 
            (error (show pos++"\nwhile compiling the module "++name++
                    "\nThe 'out' predicate\n   "++show outSigExp++
                    "\nexpects the module to"++
                    plistf tell "\n   " bad2 ",\n   " "."))     
     ; return (imports,exports,static2{items=exports})}

-- add a single Def
addDef :: Bool -> Def -> Static -> IO Static        
addDef dup (GlobalDef pos v t exp) env =
  do { sch <- normTyp t
     ; return(addVarS dup pos (v,sch) env) }
addDef dup (FunDef pos f rng args body) env = 
  do { let typ = TyFun (map snd args) rng
     ; sch <- normTyp typ
     ; return(addVarS dup pos (f,sch) env) } 
addDef dup (d@(DataDef pos c args clauses)) env =    
  do { let process (c,ts) = do { sch <- normSch (Sch args (fun ts))
                               ; return(c,sch)}
           fun [] = TyCon pos c (map TyVar args)
           fun ds = TyFun ds (TyCon pos c (map TyVar args))
     ; cs2 <- mapM process clauses
     ; return(addConS dup pos cs2 (addArityS dup pos (c,length args) env)) }
addDef dup (AdtDef pos c args typ ds) env = 
  foldM (addDef dup) (addArityS dup pos (c,length args) env) ds

addDef dup (ImportDef pos path (pred@sig) Nothing) env1 =
  do { prog <- parseProg True path
     ; addDef dup (ImportDef pos path pred (Just prog)) env1 }
addDef dup (ImportDef pos path (pred@sig) 
             (Just (prog@(Prog ss (Mod pos2 t inp outp) defs exp))))
           env1 = 
  case lookup path (imported env1) of
    Just _ -> return env1 -- The file has already been loaded
    Nothing -> do { (demanded,exported,stat) <- staticProg True path prog
                  ; bad <- legalSubset demanded (items env1)
                  ; when (not (null bad)) 
                         (error (show pos++"\nwhile importing "++show path++
                                 "\nThe 'in' predicate\n   "++show inp++
                                 "\nin the imported file "++show pos2++
                                 "\nexpects the importing context to supply certain things, but"++
                                 plistf tell2 "\n   " bad ",\n   " "."))
                  ; expected <- setSemantics pos2 (show pos2++"\nimport implementing "++show sig)
                                     (preludeSig{sigs=sigs env1}) sig
                  ; bad2 <- legalSubset expected exported
                  ; when (not (null bad2)) 
                         (error (show pos++"\nwhile importing "++show path++
                                 "\nThe predicate\n   "++show pred++
                                 "\nexpects the imported file to"++
                                 plistf tell "\n   " bad2 ",\n   " "."))                  
                  ; let compile env pair = dynamicFile path True env defs exp pair                               
                        imps = (path,compile):(imported env1)
                        mess = "adding exports from import "++path++" to static environment"
                        env4 = env1{items=unionS mess exported (items env1),imported=imps}
                  ; return env4}
                  
addSigItem :: Bool -> SigItem -> ItemInfo -> IO ItemInfo
addSigItem dup (ValItem pos v t) env =
  do { sch <- normTyp t; return(addVar dup pos (v,sch) env)}
addSigItem dup (DataItem pos c args cls) env = addData dup (DataDef pos c args cls) env  
addSigItem dup (TypItem pos t args) env = return(addArity dup pos (t,length args) env)

addData :: Bool -> Def -> ItemInfo -> IO ItemInfo
addData dup (DataDef pos c args clauses) env = 
  do { let process (c,ts) = do { sch <- normSch (Sch args (fun ts))
                               ; return(c,sch)}
           fun [] = TyCon pos c (map TyVar args)
           fun ds = TyFun ds (TyCon pos c (map TyVar args))
     ; cs2 <- mapM process clauses
     ; return(addCon dup pos cs2 (addArity dup pos (c,length args) env)) }

            

-------------------------------------------------------------
-- The top level functions
-- Runs

-- Runs an expression of type (IO a), and catches calls to error with continue
guard2 :: IO b -> IO b -> IO b
guard2 comp continue = E.catch comp handler
  where handler (err:: E.SomeException) = putStrLn("\n"++show err) >> continue 

staticProg loud path (source@(Prog sigs (mod@(Mod pos t inp outp)) ds exp)) =
  do { when loud (putStrLn (show source))
     ; let f (Sig p nm path) = nm
     ; when (loud  && (not (null sigs)))
            (putStrLn("\n***** Loading signatures: "++plistf f "" sigs ", " " ******"))
     ; sigPairs <- collectSignatures sigs 
     ; when loud (putStrLn ("\n******** TYPING "++path++" *************"))
     ; (demanded,exported,static) <- addModule sigPairs mod ds exp
     ; when loud (putStrLn ("\n\n"))
     ; let shD (v,Sch vs t) = putStrLn (v++"::"++show t)
     ; when loud (mapM_ shD (vars exported))
     ; return (demanded,exported,static) }

dynamicFile path loud imports defs exp (env,state) = 
  do { when loud ( putStrLn ("\n******** LOADING DEFS "++path++" **************"))
     ; (vars,state2) <- fixIO(elaborate loud imports defs (env,state))
     ; when loud (putStrLn "\n")
     ; when loud (putStrLn ("\n\n********** EXECUTING BODY "++path++" **********"))
     ; (v,state4) <- interpE vars state2 exp
     ; when loud (putStrLn(showV (v,state4)))
     ; return(vars,state4)}
              
runFile filename = 
  do { prog@(Prog sigs (Mod pos t inp outp) ds exp) <- parseProg True filename
     ; (demanded,exported,static) <- staticProg True filename prog
     ; (vars,state2) <- dynamicFile filename True static ds exp (emptyE ,State []) 
     ; bad <- legalSubset demanded preludeItems
     ; when (not (null bad)) 
            (putStrLn ("\nwhile compiling "++show filename++
                    "\nThe 'in' predicate\n   "++show inp++
                    "\nnear "++show pos++
                    "\nexpects the importing context to supply certain things, but"++
                                 plistf tell2 "\n   " bad ",\n   " "."++
                    "\nExpect certain values in the read-type-eval-print loop to be missing."))     
     ; putStrLn "\n*********** ENTERING READ EVAL PRINT ***************"    
     ; putStrLn "type ':q' to exit, type 'trace' to flip tracer state\n"
     ; let loop state = 
              do { putStrLn "enter Exp>"
                 ; str <- getLine
                 ; case str of
                     "" -> loop state
                     ":q" -> (putStrLn "Quitting") 
                     (':' : 'i' : more) -> 
                         guard2 (do { putStrLn(PP.render (pp vars)); (loop state)}) (loop state)
                     (':' : 's' : more) -> 
                         guard2 (do { s <- (printSigSet more static); putStrLn s; loop state})
                                (loop state)
                     "trace" -> do { trace; loop state}
                     other -> case parse1 ("keyboard input\n"++str) expP str of
                                Left message -> do { putStrLn("\n"++show message); loop state}
                                Right exp -> guard2
                                  (do { typ <-infer static exp
                                      ; (v,state2) <- interpE vars state exp
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
-- Some very simple tests, requires some files in current directory

test1 = runFile "typedlists.e7"
test2 = runFile "simple.e7"
test3 = runFile "types.e7"
test4 = runFile "solutions/sol7A.e7"
test5 = runFile "solutions/sol7B.e7"
test6 = runFile "bad.e7"
test7 = runFile "work.e7"
