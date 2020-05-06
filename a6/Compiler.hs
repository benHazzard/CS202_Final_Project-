{-# LANGUAGE Strict, ScopedTypeVariables #-}
module Compiler where

import Data.List
import Data.Maybe
import qualified Data.Bits as Bits

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Ord

import Text.Pretty.Simple (pPrint, pPrintNoColor, pShowNoColor)

import qualified Data.Text.Lazy as T

import Graph
import Gensym
import CFG
import AST

-- a Type Alias for variables
-- Variables are represented by Strings
type Variable = String

------------------------------------------------------------
-- global constant definitions
------------------------------------------------------------

-- r11 and r15 are reserved for vector operations
callerSavedRegisters = ["rdx", "rcx", "rsi", "rdi", "r8", "r9", "r10"]
calleeSavedRegisters = ["rbx", "r12", "r13", "r14"]
allRegisters = callerSavedRegisters ++ calleeSavedRegisters

argRegisters = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]

-- size of the root stack and heap
rootStackSize = 2^14
heapSize = 2^4

------------------------------------------------------------
-- typecheck
------------------------------------------------------------

type TEnv = [(Variable, Type)]

-- Typechecker for R5 Expressions
-- Inputs:
--  - e: an R5 expression
--  - env: a type environment mapping variables to their types
-- Output: a pair
--  - the type of e, if it is well-typed
--  - a *typed* R5 expression
-- Throws a run-time error if e is not well-typed
tcExpr :: R5Expr -> TEnv -> (Type, TypedR5Expr)
tcExpr e env = case e of
  VarE x ->
    let t = fromJust (lookup x env)
    in (t, VarTE x t)
  IntE i -> (IntT, IntTE i)

  TrueE -> (BoolT, TrueTE)
  FalseE -> (BoolT, FalseTE)

  IfE e1 e2 e3 ->
    case (tcExpr e1 env, tcExpr e2 env, tcExpr e3 env) of
      ((BoolT, e1'), (t1, e2'), (t2, e3')) | t1 == t2 ->
                                             (t1, IfTE e1' e2' e3' t1)
      ((BoolT, _), (t1, _), (t2, _)) ->
        error ("Type error in " ++ (show e) ++ ":\n branch 1 has type " ++ (show t1)
               ++ " and branch 2 has type " ++ (show t2))
      (tTest, _, _) ->
        error ("Type error in " ++ (show e) ++ ":\n test has non-boolean type "
               ++ (show tTest))

  PlusE e1 e2 ->
    case (tcExpr e1 env, tcExpr e2 env) of
      ((IntT, e1'), (IntT, e2')) -> (IntT, PlusTE e1' e2')
      _ -> error ("Type error in " ++ (show e))

  CmpE CmpEqual e1 e2 ->
    case (tcExpr e1 env, tcExpr e2 env) of
      ((IntT, e1'), (IntT, e2')) -> (BoolT, CmpTE CmpEqual e1' e2')
      ((BoolT, e1'), (BoolT, e2')) -> (BoolT, CmpTE CmpEqual e1' e2')
      _ -> error ("Type error in " ++ (show e))

  CmpE c e1 e2 ->
    case (tcExpr e1 env, tcExpr e2 env) of
      ((IntT, e1'), (IntT, e2')) -> (BoolT, CmpTE c e1' e2')
      _ -> error ("Type error in " ++ (show e))

  OrE e1 e2 ->
    case (tcExpr e1 env, tcExpr e2 env) of
      ((BoolT, e1'), (BoolT, e2')) -> (BoolT, OrTE e1' e2')
      _ -> error ("Type error in " ++ (show e))

  AndE e1 e2 ->
    case (tcExpr e1 env, tcExpr e2 env) of
      ((BoolT, e1'), (BoolT, e2')) -> (BoolT, AndTE e1' e2')
      _ -> error ("Type error in " ++ (show e))

  NotE e1 ->
    case (tcExpr e1 env) of
      (BoolT, e1') -> (BoolT, NotTE e1')
      _ -> error ("Type error in " ++ (show e))

  LetE x e1 e2 ->
    let (t1, e1') = tcExpr e1 env
        env'      = (x, t1) : env
        (t2, e2') = tcExpr e2 env'
    in (t2, LetTE x e1' e2')

  VectorE args ->
    let pairs = map (\e -> tcExpr e env) args
        types = map fst pairs
        args' = map snd pairs
        t     = VectorT types
    in (t, VectorTE args' t)

  VectorRefE e1 idx ->
    let (VectorT argTs, e1') = tcExpr e1 env
        t = argTs !! idx
    in (t, VectorRefTE e1' idx t)

  VectorSetE e1 idx e2 ->
    let (VectorT argTs, e1') = tcExpr e1 env
        (t2, e2')            = tcExpr e2 env
    in case (argTs !! idx == t2) of
      True -> (VoidT, VectorSetTE e1' idx e2')
      False -> error ("Type error in " ++ (show e))

  VoidE -> (VoidT, VoidTE)
  FunCallE f args ->
    let (FunT argTs outT, f') = tcExpr f env
        argPs = map (\e -> tcExpr e env) args
        argTs2 = map fst argPs
        args' = map snd argPs
        _ = map (\(t1, t2) -> case t1 == t2 of
                    True -> ()
                    False -> error $ "Mismatched argument types: " ++ (show (t1, t2)))
               (zip argTs argTs2)
    in (outT, FunCallTE f' args' argTs outT)

    --let ls = cons(1, cons(2, nil))
    --in car(cdr(ls))

  -- think similar to additon
  -- recurvely arguement first

  -- appending item to a list
  ConsE i1 i2->  --list constructer
      let (type1, ex1) = tcExpr i1 env
          (type2, ex2) = tcExpr i2 env
      in case (type2) of
        ListT tyL -> case (type1 == tyL) of
          True ->
            let x = gensym "Box"
                newEnv = Mapinsert x tyL env
            in (ListT tyl, ConsTE ex1 ex2)
          False -> error $ "1st arg type mismatch 2nd list type"
        _ -> error $ "There is no list Type to match with"
        -- Type2 to be a listT of the same type of first arg

  -- gets head of list (first item of list)
  CarE h ->
    let (typeH, exH) = tcExpr l env
    in case typeH of --Hope its a listT
        ListT t -> (t, CarTE exH)
        _ -> error $ "Not a ListT, so no head can be made. "
--        TrueE -> (BoolT, TrueTE)
  --      FalseE -> (BoolT, FalseTE)
    --    InT i -> (IntT, IntTE i)


  -- get tail of a list  (gets all other items)
  CdrE l ->  --almost same as CarE, takes list and return list
    let (typeL, exL) = tcExpr l env -- fromJust (lookup i1 env)
      in case typel of
        ListT i -> (ListT i, CdrTE exL)
        _ -> error $"Not a list, so not needed" --so just 1 is error,
        --BoolT i -> (ListT BaoolT, CdrTE l)

  -- empty list
  NilE u -> (ListT u, NilTE u) -- be able to match with any list
-- What type of Nil, like NillInt or NillBool
-- Change to NilE -> NilE Type
--think  cons(1, nil[Int])

-- Get the name and type of a definition
getDefnType :: R5Definition -> (Variable, Type)
getDefnType (Defn name args outputType body) =
  (name, FunT (map snd args) outputType)

-- Typechecker for R5 definitions
tcDefn :: TEnv -> R5Definition -> TypedR5Definition
tcDefn env (Defn name args outputT body) =
  let env'           = args ++ env
      (bodyT, body') = tcExpr body env'
  in case bodyT == outputT of
    True -> DefnT name args outputT body'
    False -> error ("Type error in definition: output type " ++ (show outputT) ++
                    " does not match body type " ++ (show bodyT))

-- Typechecker for R5 programs
typecheck :: R5Program -> TypedR5Program
typecheck (defns, e) =
  let defTypeEnv = map getDefnType defns
      defns' = map (tcDefn defTypeEnv) defns
      (t, e') = tcExpr e defTypeEnv
  in trace ("Type: " ++ (show t)) (defns', e')


------------------------------------------------------------
-- shrink
------------------------------------------------------------

-- Shrink, for R5 expressions
-- Input: e, an R5 expression
-- Output: an R5 expression
-- Removes "and", "or", ">=", ">", ">="
shrinkExpr :: TypedR5Expr -> TypedR5Expr
shrinkExpr e =  case e of
  IntTE i -> IntTE i
  VarTE x t -> VarTE x t
  PlusTE e1 e2 -> PlusTE (shrinkExpr e1) (shrinkExpr e2)
  LetTE x e1 e2 -> LetTE x (shrinkExpr e1) (shrinkExpr e2)
  TrueTE -> TrueTE
  FalseTE -> FalseTE
  NotTE e1 -> NotTE (shrinkExpr e1)
  IfTE e1 e2 e3 t -> IfTE (shrinkExpr e1) (shrinkExpr e2) (shrinkExpr e3) t
  AndTE e1 e2 -> IfTE (shrinkExpr e1) (shrinkExpr e2) FalseTE BoolT
  OrTE e1 e2 -> IfTE (shrinkExpr e1) TrueTE (shrinkExpr e2) BoolT
  CmpTE CmpLTE e1 e2 -> NotTE (CmpTE CmpLT (shrinkExpr e2) (shrinkExpr e1))
  CmpTE CmpGT e1 e2 -> CmpTE CmpLT (shrinkExpr e2) (shrinkExpr e1)
  CmpTE CmpGTE e1 e2 -> NotTE (CmpTE CmpLT (shrinkExpr e1) (shrinkExpr e2))
  CmpTE c e1 e2 -> CmpTE c (shrinkExpr e1) (shrinkExpr e2)
  VectorTE args t -> VectorTE (map shrinkExpr args) t
  VectorRefTE e1 idx t -> VectorRefTE (shrinkExpr e1) idx t
  VectorSetTE e1 idx e2 -> VectorSetTE (shrinkExpr e1) idx (shrinkExpr e2)
  VoidTE -> VoidTE
  FunCallTE e1 args argTs t -> FunCallTE (shrinkExpr e1) (map shrinkExpr args) argTs t
  ConsTE i1 i2 -> --VectorE e1 e2, append first to second. COuld make the 2nd a list
    let env = Set.empty
        (u, td) = tcExp e env
        e1' = shrinkExpr i1
        e2' = shrinkExpr i2 -- make a list
        nwList = [e2']++e1'
    in VectorTE nwList u
  CdrTE t -> case t of
    VectorTE args ty ->
      let end = last args
          ln = (length args) - 1
      in VectorRefTE (shrink end) ln ty
    _ -> show error $ "No"
  CarTE h -> case h of
    VectorTE args ty ->
      let hD = head arg
      in VectorRefTE (shrink hD) 0 ty
    _ -> show error $ "No"
  NilTE ty ->
    let blk = Set.empty
    in VectorTE blk ty

-- The shrink pass, for an R5 definition
-- Input:  an R5 definition
-- Output: an R5 definition
shrinkDefn :: TypedR5Definition -> TypedR5Definition
shrinkDefn (DefnT name args outputT body) =
  (DefnT name args outputT (shrinkExpr body))

-- The shrink pass, for an R5 program
-- Input:  an R5 program
-- Output: a list of R5 definitions
-- Moves the top-level expression into a "main" definition
shrink :: TypedR5Program -> [TypedR5Definition]
shrink (defns, e) =
  let defns'   = map shrinkDefn defns
      e'       = shrinkExpr e
      mainDefn = DefnT "main" [] IntT e'
  in mainDefn : defns'

------------------------------------------------------------
-- uniquify
------------------------------------------------------------

-- A Variable Environment maps variables to variables
type VEnv = [(Variable, Variable)]

-- The uniquify pass, for an expression
-- Input:
--   - an R5 expression
--   - a variable environment
-- Output: an R5 expression, with variables renamed to be unique
uniquifyExp :: TypedR5Expr -> VEnv -> TypedR5Expr
uniquifyExp e env = case e of
  IntTE _ -> e
  VarTE x t -> case lookup x env of
    Just x' -> VarTE x' t
    Nothing -> error $ "Failed to find variable " ++ (show x) ++ " in environment " ++ (show env)
  PlusTE e1 e2 ->
    PlusTE (uniquifyExp e1 env) (uniquifyExp e2 env)
  LetTE x e1 e2 ->
    let newV = gensym x
        newEnv = (x, newV) : env
    in LetTE newV (uniquifyExp e1 newEnv) (uniquifyExp e2 newEnv)
  TrueTE -> TrueTE
  FalseTE -> FalseTE
  NotTE e1 -> NotTE (uniquifyExp e1 env)
  CmpTE c e1 e2 -> CmpTE c (uniquifyExp e1 env) (uniquifyExp e2 env)
  IfTE e1 e2 e3 t -> IfTE (uniquifyExp e1 env) (uniquifyExp e2 env) (uniquifyExp e3 env) t
  VectorTE args t -> VectorTE (map (\e -> uniquifyExp e env) args) t
  VectorRefTE e1 idx t -> VectorRefTE (uniquifyExp e1 env) idx t
  VectorSetTE e1 idx e2 -> VectorSetTE (uniquifyExp e1 env) idx (uniquifyExp e2 env)
  VoidTE -> VoidTE
  FunCallTE e1 args argTs t ->
    FunCallTE (uniquifyExp e1 env) (map (\e -> uniquifyExp e env) args) argTs t
  ConsTE i1 i2 -> ConsTE (uniquifyExp i1 env) (uniquifyExp i2 env)
  CarTE h -> CarTE (uniquifyExp h env) -- grabbing head
  CdrTE t -> CdrTE (uniquifyExp t env) -- the tail
  NilTE ty -> NilTE ty


-- The uniquify pass, for a single R5 definition
-- Input:  an R5 definition
-- Output: an R5 definition, with variables renamed to be unique
uniquifyDefn :: VEnv -> TypedR5Definition -> TypedR5Definition
uniquifyDefn initEnv (DefnT name args outputT body) =
  let argNames  = map fst args
      argTypes  = map snd args
      argNames' = map gensym argNames
      vEnv      = zip argNames argNames'
      body'     = uniquifyExp body (vEnv ++ initEnv)
  in DefnT name (zip argNames' argTypes) outputT body'

-- The uniquify pass, for a list of R5 definitions
-- Input:  a list of R5 definitions
-- Output: a list of R5 definitions, with variables renamed to be unique
uniquify :: [TypedR5Definition] -> [TypedR5Definition]
uniquify defns =
  let initEnv  = map (\(DefnT name _ _ _) -> (name, name)) defns
  in map (uniquifyDefn initEnv) defns

------------------------------------------------------------
-- reveal-functions
------------------------------------------------------------

-- Reveal-functions, for R5 expressions
-- Input: e, an R5 expression
-- Output: an R5 expression
-- Transforms variables referencing function names with FunRefTE expressions
revealExpr :: TypedR5Expr -> [String] -> TypedR5Expr
revealExpr e funs = case e of
  IntTE i -> IntTE i
  VarTE x t -> case elem x funs of
    True -> FunRefTE x t
    False -> e
  PlusTE e1 e2 -> PlusTE (revealExpr e1 funs) (revealExpr e2 funs)
  LetTE x e1 e2 -> LetTE x (revealExpr e1 funs) (revealExpr e2 funs)
  TrueTE -> TrueTE
  FalseTE -> FalseTE
  NotTE e1 -> NotTE (revealExpr e1 funs)
  IfTE e1 e2 e3 t -> IfTE (revealExpr e1 funs) (revealExpr e2 funs) (revealExpr e3 funs) t
  AndTE e1 e2 -> IfTE (revealExpr e1 funs) (revealExpr e2 funs) FalseTE BoolT
  OrTE e1 e2 -> IfTE (revealExpr e1 funs) TrueTE (revealExpr e2 funs) BoolT

  CmpTE CmpLTE e1 e2 -> NotTE (CmpTE CmpLT (revealExpr e2 funs) (revealExpr e1 funs))
  CmpTE CmpGT e1 e2 -> CmpTE CmpLT (revealExpr e2 funs) (revealExpr e1 funs)
  CmpTE CmpGTE e1 e2 -> NotTE (CmpTE CmpLT (revealExpr e1 funs) (revealExpr e2 funs))
  CmpTE c e1 e2 -> CmpTE c (revealExpr e1 funs) (revealExpr e2 funs)

  VectorTE args t -> VectorTE (map (\a -> revealExpr a funs) args) t
  VectorRefTE e1 idx t -> VectorRefTE (revealExpr e1 funs) idx t
  VectorSetTE e1 idx e2 -> VectorSetTE (revealExpr e1 funs) idx (revealExpr e2 funs)
  VoidTE -> VoidTE
  FunCallTE e1 args argTs t ->
    FunCallTE (revealExpr e1 funs) (map (\a -> revealExpr a funs) args) argTs t

  -- List Exprs
  ConsTE i1 i2 -> ConsTE (revealExpr i1 funs) (revealExpr i2 funs)
  CdrTE t-> CdrTE (revealExpr t funs)
  CarTE h -> CarTE (revealExpr h funs)
  NilTE ty-> NilTE ty

-- Reveal-functions, for R5 expressions
-- Input: e, an R5 expression
-- Output: an R5 expression
-- Transforms variables referencing function names with FunRefTE expressions
revealDefn :: [String] -> TypedR5Definition -> TypedR5Definition
revealDefn funs (DefnT name args outputT body) =
  (DefnT name args outputT (revealExpr body funs))

-- Reveal-functions, for a list of R5 definitions
-- Input: a list of R5 definitions
-- Output: a list of R5 definitions
-- Transforms variables referencing function names with FunRefTE expressions
revealFunctions :: [TypedR5Definition] -> [TypedR5Definition]
revealFunctions defns =
  let funs = map (\(DefnT name _ _ _) -> name) defns
  in map (revealDefn funs) defns


------------------------------------------------------------
-- limit-functions
------------------------------------------------------------

-- An environment mapping variables to expressions
-- For replacing variables with vectorRef expressions in functions with >6 arguments
type EEnv = [(Variable, TypedR5Expr)]

-- Limit-functions, for R5 expressions
-- Input:
--  - e, an R5 expression
--  - env, an environment
-- Output: an R5 expression
-- Moves arguments > 6 into a vector
limitExpr :: TypedR5Expr -> EEnv -> TypedR5Expr
limitExpr e env = case e of
  IntTE i -> IntTE i
  VarTE x t -> case lookup x envs of
    Nothing  -> VarTE x t
    Just e' -> e'
  PlusTE e1 e2 -> PlusTE (limitExpr e1 env) (limitExpr e2 env)
  LetTE x e1 e2 -> LetTE x (limitExpr e1 env) (limitExpr e2 env)
  TrueTE -> TrueTE
  FalseTE -> FalseTE
  NotTE e1 -> NotTE (limitExpr e1 env)
  IfTE e1 e2 e3 t -> IfTE (limitExpr e1 env) (limitExpr e2 env) (limitExpr e3 env) t
  AndTE e1 e2 -> IfTE (limitExpr e1 env) (limitExpr e2 env) FalseTE BoolT
  OrTE e1 e2 -> IfTE (limitExpr e1 env) TrueTE (limitExpr e2 env) BoolT

  CmpTE CmpLTE e1 e2 -> NotTE (CmpTE CmpLT (revealExpr e2 funs) (revealExpr e1 funs))
  CmpTE CmpGT e1 e2 -> CmpTE CmpLT (revealExpr e2 funs) (revealExpr e1 funs)
  CmpTE CmpGTE e1 e2 -> NotTE (CmpTE CmpLT (revealExpr e1 funs) (revealExpr e2 funs))
  CmpTE c e1 e2 -> CmpTE c (revealExpr e1 funs) (revealExpr e2 funs)

  VectorTE args t -> VectorTE (map (\a -> revealExpr a funs) args) t
  VectorRefTE e1 idx t -> VectorRefTE (revealExpr e1 funs) idx t
  VectorSetTE e1 idx e2 -> VectorSetTE (revealExpr e1 funs) idx (revealExpr e2 funs)
  VoidTE -> VoidTE

  ConsTE i1 i2 -> ConsTE (limitExpr i1 env) (limitExpr i2 env)
  CdrTE t-> CdrTE (limitExpr t env)
  CarTE h -> CarTE (limitExpr h env)
  NilTE ty-> NilTE ty

-- Limit-functions, for an R5 definition
-- Input: an R5 definition
-- Output: an R5 definition
-- Moves arguments > 6 into a vector
limitDefn :: TypedR5Definition -> TypedR5Definition
limitDefn (DefnT name args outputT body) =
  case (length args) > 6 of
    True -> let vecArgName = gensym "vecArg"
                vecArgs = drop 5 args
                vecArgTypes = map snd vecArgs
                vecArgType = VectorT vecArgTypes
                vecArgExpr = VarTE vecArgName vecArgType
                newArgs = (take 5 args) ++ [(vecArgName, vecArgType)]
                env = map (\((var, t), i) -> (var, VectorRefTE vecArgExpr i t)) (zip vecArgs [0..])
            in DefnT name newArgs outputT (limitExpr body env)
    False -> DefnT name args outputT (limitExpr body []) -- no change needed

-- Limit-functions, for a list of R5 definitions
-- Input: a list of R5 definitions
-- Output: a list of R5 definitions
-- Moves arguments > 6 into a vector
limitFunctions :: [TypedR5Definition] -> [TypedR5Definition]
limitFunctions defns = map limitDefn defns

------------------------------------------------------------
-- expose-allocation
------------------------------------------------------------

-- a Binding maps a variable to a typed expression
type Binding = (Variable, TypedR5Expr)

-- Make a "LET" expression from a list of bindings and a final "body" expression
mkLet :: [Binding] -> TypedR5Expr -> TypedR5Expr
mkLet [] body = body
mkLet ((x, e) : bs) body = LetTE x e (mkLet bs body)

-- Expose allocation, for an R5 expression
-- Input: an R5 expression
-- Output: an R5 expression, without "VectorTE" expressions
-- This pass compiles "VectorTE" expressions into explicit allocations
eaExp :: TypedR5Expr -> TypedR5Expr
eaExp e = case e of
  IntTE _ -> e
  VarTE _ _ -> e
  PlusTE e1 e2 -> PlusTE (eaExp e1) (eaExp e2)
  LetTE x e1 e2 -> LetTE x (eaExp e1) (eaExp e2)
  TrueTE -> TrueTE
  FalseTE -> FalseTE
  NotTE e1 -> NotTE (eaExp e1)
  CmpTE c e1 e2 -> CmpTE c (eaExp e1) (eaExp e2)
  IfTE e1 e2 e3 t -> IfTE (eaExp e1) (eaExp e2) (eaExp e3) t
  VectorRefTE e1 idx t -> VectorRefTE (eaExp e1) idx t
  VectorSetTE e1 idx e2 -> VectorSetTE (eaExp e1) idx (eaExp e2)
  VoidTE -> VoidTE
  VectorTE args vt ->
    let (VectorT ts) = vt
        varNames = map (\e -> gensym "v") args
        varBindings = zip varNames (map eaExp args)
        len = length args
        bytes = 8 + 8 * len
        collectExpr = (IfTE (CmpTE CmpLT (PlusTE (GlobalValTE "free_ptr")
                                                 (IntTE bytes))
                                         (GlobalValTE "fromspace_end"))
                        VoidTE
                        (CollectTE bytes)
                        VoidT)
        allocateExpr = AllocateTE len vt
        v = gensym "vec"
        idxs = zip3 varNames [0..] ts
        vectorSetBindings = map (\(x, idx, t) -> ("_", VectorSetTE (VarTE v vt) idx (VarTE x t))) idxs
        allBindings =
          varBindings ++
          [("_", collectExpr), (v, allocateExpr)] ++
          vectorSetBindings
    in mkLet allBindings (VarTE v vt)
  FunCallTE name args argTs t -> FunCallTE name (map eaExp args) argTs t
  FunRefTE f t -> FunRefTE f t
  ConsTE i1 i2 -> ConsTE (eaExp i1) (eaExp i2) --VectorRef [e1,e2]
  CdrTE t-> CdrTE (eaExp t) --VectorRefE e1' 1
  CarTE h -> CarTE (eaExpr h) --VectorRefE e1' 0
  NilTE ty-> NilTE ty
  _ -> error $ show e

-- Expose allocation, for an R5 definition
-- Input: an R5 definition
-- Output: an R5 definition, without "VectorTE" expressions
eaDefn :: TypedR5Definition -> TypedR5Definition
eaDefn (DefnT name args outputT body) =
  DefnT name args outputT (eaExp body)

-- Expose allocation, for an R5 expression
-- Input: an R5 expression
-- Output: an R5 expression, without "VectorTE" expressions
exposeAllocation :: [TypedR5Definition] -> [TypedR5Definition]
exposeAllocation defns = map eaDefn defns

------------------------------------------------------------
-- remove-complex-opera
------------------------------------------------------------

-- The remove-complex-operand pass on an expression in TAIL POSITION
-- input:  COMPLEX EXPRESSION
-- output: COMPLEX EXPRESSION in A-Normal Form
rcoExp :: TypedR5Expr -> TypedR5Expr
rcoExp e = case e of
  IntTE i -> IntTE i
  VarTE x t -> VarTE x t
  PlusTE e1 e2 ->
    let (v1, b1) = rcoArg e1
        (v2, b2) = rcoArg e2
    in mkLet (b1 ++ b2) (PlusTE v1 v2)
  LetTE x e1 e2 ->
    LetTE x (rcoExp e1) (rcoExp e2)
  TrueTE -> TrueTE
  FalseTE -> FalseTE
  NotTE e1 ->
    let (v1, b1) = rcoArg e1
    in mkLet b1 (NotTE v1)
  CmpTE c e1 e2 ->
    let (v1, b1) = rcoArg e1
        (v2, b2) = rcoArg e2
    in mkLet (b1 ++ b2) (CmpTE c v1 v2)
  IfTE e1 e2 e3 t -> IfTE (rcoExp e1) (rcoExp e2) (rcoExp e3) t
  VectorRefTE e1 idx t ->
    let (v, b) = rcoArg e1
    in mkLet b (VectorRefTE v idx t)
  VectorSetTE e1 idx e2 ->
    let (v1, b1) = rcoArg e1
        (v2, b2) = rcoArg e2
    in mkLet (b1 ++ b2) (VectorSetTE v1 idx v2)
  VoidTE -> VoidTE
  CollectTE i -> CollectTE i
  AllocateTE i t -> AllocateTE i t
  GlobalValTE s -> GlobalValTE s
  FunRefTE f t-> FunRefTE f t
  FunCallTE e1 args argTs t ->
    let (v1, b1) = rcoArg e1
        ps       = map rcoArg args
        args'    = map fst ps
        bs       = concat (map snd ps)
    in mkLet (b1 ++ bs) (FunCallTE v1 args' argTs t)
  ConsTE i1 i2 -> ConsTE (rcoExp i1) (rcoExp i2)
  CdrTE t-> CdrTE (rcoExp t)
  CarTE h -> CarTE (rcoExpr h)
  NilTE ty-> NilTE ty


-- The remove-complex-operand pass on an expression in ARGUMENT POSITION
-- input:  COMPLEX EXPRESSION
-- output: pair: SIMPLE EXPRESSION and LIST OF BINDINGS
--
-- the LIST OF BINDINGS maps variables to SIMPLE EXPRESSIONS
rcoArg :: TypedR5Expr -> (TypedR5Expr, [Binding])
rcoArg e = case e of
  IntTE i -> (IntTE i, [])
  VarTE x t -> (VarTE x t, [])
  TrueTE -> (TrueTE, [])
  FalseTE -> (FalseTE, [])
  PlusTE e1 e2 ->
    let (v1, b1) = rcoArg e1
        (v2, b2) = rcoArg e2
        newV = gensym "tmp"
        newB = (newV, PlusTE v1 v2)
    in (VarTE newV IntT, (b1 ++ b2 ++ [newB]))
  LetTE x e1 e2 ->
    let e1' = rcoExp e1
        (v2, b2) = rcoArg e2
        newB = (x, e1')
    in (v2, newB : b2)
  NotTE e1 ->
    let (v1, b1) = rcoArg e1
        newV = gensym "tmp"
        newB = (newV, NotTE v1)
    in (VarTE newV BoolT, b1 ++ [newB])
  CmpTE c e1 e2 ->
    let (v1, b1) = rcoArg e1
        (v2, b2) = rcoArg e2
        newV = gensym "tmp"
        newB = (newV, CmpTE c v1 v2)
    in (VarTE newV BoolT, b1 ++ b2 ++ [newB])
  IfTE e1 e2 e3 t ->
    let newV = gensym "tmp"
        newB = (newV, IfTE (rcoExp e1) (rcoExp e2) (rcoExp e3) t)
    in (VarTE newV t, [newB])
  VectorRefTE e1 idx t ->
    let (v, b) = rcoArg e1
        newV = gensym "tmp"
        newB = (newV, VectorRefTE v idx t)
    in (VarTE newV t, b ++ [newB])
  VectorSetTE e1 idx e2 ->
    let (v1, b1) = rcoArg e1
        (v2, b2) = rcoArg e2
        newV = gensym "tmp"
        newB = (newV, VectorSetTE v1 idx v2)
    in (VarTE newV VoidT, (b1 ++ b2 ++ [newB]))
  GlobalValTE s -> (GlobalValTE s, [])
  FunRefTE name t ->
    let newV = gensym ("tmp_fun_" ++ name)
        newB = (newV, FunRefTE name t)
    in (VarTE newV t, [newB])
  FunCallTE e1 args argTs t ->
    let (v1, b1) = rcoArg e1
        ps       = map rcoArg args
        args'    = map fst ps
        bs       = concat (map snd ps)
        newV     = gensym "tmp"
        newB     = (newV, FunCallTE v1 args' argTs t)
    in (VarTE newV t, (b1 ++ bs ++ [newB]))
  ConsTE i1 i2 ->
    let (v1, b1) = rcoArg i1
        (v2, b2) = rcoArg i2
    in (ConsTE v1 v2, (b1++b2))
  CdrTE h ->
    let (v, b) = rcoArg h
    in (CdrTE v, b)
  CarTE h ->
    let (v, b) = rcoArg h
    in (CarTE v, b)
  NilTE u ->  (NilTE u, [])

-- Remove complex operands, for an R5 definition
-- Input: an R5 definition
-- Output: an R5 definition, without complex operands
rcoDefn :: TypedR5Definition -> TypedR5Definition
rcoDefn (DefnT name args outputT body) =
  DefnT name args outputT (rcoExp body)

-- Remove complex operands, for an R5 program
-- Input: an R5 program
-- Output: an R5 program, without complex operands
removeComplexOpera :: [TypedR5Definition] -> [TypedR5Definition]
removeComplexOpera defns = map rcoDefn defns

------------------------------------------------------------
-- explicate-control
------------------------------------------------------------
type Label = String

data C3Arg = IntC3 Int
           | VarC3 Variable Type
           | TrueC3
           | FalseC3
           | VoidC3
           | GlobalValC3 String
  deriving (Eq, Ord, Show)

data C3Cmp = CmpEqC3
           | CmpLTC3
  deriving (Eq, Ord, Show)

data C3Basic = C3ArgE C3Arg
             | C3PlusE C3Arg C3Arg
             | C3NotE C3Arg
             | C3CmpE C3Cmp C3Arg C3Arg
             | C3AllocateE Int Type
             | C3VectorRefE C3Arg Int
             | C3VectorSetE C3Arg Int C3Arg
             | C3FunRefE Label Type
             | C3CallE C3Arg [C3Arg]
  deriving (Eq, Ord, Show)

data C3Stmt = AssignC3 Variable Type C3Basic
            | CollectC3 Int
  deriving (Eq, Ord, Show)

data C3Tail = ReturnC3 C3Basic
            | SeqC3 C3Stmt C3Tail
            | GotoC3 Label
            | IfC3 C3Cmp C3Arg C3Arg Label Label
            | TailCallC3 C3Arg [C3Arg]
  deriving (Eq, Ord, Show)

type C3CFG = CFG C3Tail

data C3Defn = DefnC3 Label [(Variable, Type)] Type C3CFG
  deriving (Eq, Show)

-- Compile a R5 argument (integer or variable) into a C3Arg expression
ecArg :: TypedR5Expr -> C3Arg
ecArg e = case e of
  IntTE i -> IntC3 i
  VarTE x t -> VarC3 x t
  TrueTE -> TrueC3
  FalseTE -> FalseC3
  VoidTE -> VoidC3
  GlobalValTE s -> GlobalValC3 s
  _ -> error $ show e

ecCmp :: Cmp -> C3Cmp
ecCmp c = case c of
  CmpEqual -> CmpEqC3
  CmpLT -> CmpLTC3

-- Compile a BASIC R5 Expression into a C3Basic Expression
ecBasic :: TypedR5Expr -> C3Basic
ecBasic e = case e of
  PlusTE e1 e2 -> C3PlusE (ecArg e1) (ecArg e2)
  NotTE e1 -> C3NotE (ecArg e1)
  CmpTE c e1 e2 -> C3CmpE (ecCmp c) (ecArg e1) (ecArg e2)
  VectorRefTE e1 i t -> C3VectorRefE (ecArg e1) i
  VectorSetTE e1 i e2 -> C3VectorSetE (ecArg e1) i (ecArg e2)
  AllocateTE i t -> C3AllocateE i t
  FunRefTE name t -> C3FunRefE name t
  FunCallTE a1 args argTs t -> C3CallE (ecArg a1) (map ecArg args)
  _ -> C3ArgE (ecArg e)

-- The explicate-control pass on an expression in TAIL POSITION
-- inputs:
--  - e: a COMPLEX EXPRESSION in A-Normal Form
--  - cfg: a C3CFG (control flow graph)
-- output: a C3 Tail expression
-- Sometimes updates 'cfg' with new CFG nodes
ecTail :: TypedR5Expr -> C3CFG -> C3Tail
ecTail e cfg = case e of
  IntTE _ -> ReturnC3 (ecBasic e)
  VarTE _ t -> ReturnC3 (ecBasic e)
  PlusTE e1 e2 -> ReturnC3 (C3PlusE (ecArg e1) (ecArg e2))
  LetTE x e1 e2 ->
    let b = ecTail e2 cfg
    in ecAssign x e1 b cfg
  IfTE e1 e2 e3 t ->
    let b1 = ecTail e2 cfg
        b2 = ecTail e3 cfg
    in ecPred e1 b1 b2 cfg
  TrueTE -> ReturnC3 (ecBasic e)
  FalseTE -> ReturnC3 (ecBasic e)
  NotTE e1 -> ReturnC3 (ecBasic e)
  CmpTE c a1 a2 -> ReturnC3 (ecBasic e)
  VectorRefTE a i t -> ReturnC3 (ecBasic e)
  VectorSetTE a1 i a2 -> ReturnC3 (ecBasic e)
  FunCallTE a1 args argTs t -> TailCallC3 (ecArg a1) (map ecArg args)
  _ -> error (show e)

-- The explicate-control pass on an expression in PREDICATE POSITION
-- inputs:
--  - test: a COMPLEX R5 EXPRESSION
--  - b1: a C3 Tail expression (the "then-block")
--  - b2: a C3 Tail expression (the "else-block")
--  - cfg: a C3CFG (control flow graph)
-- output: a C3 Tail expression
-- Sometimes updates 'cfg' with new CFG nodes
ecPred :: TypedR5Expr -> C3Tail -> C3Tail -> C3CFG -> C3Tail
ecPred test b1 b2 cfg = case test of
  TrueTE -> b1
  FalseTE -> b2
  NotTE e1 -> ecPred e1 b2 b1 cfg
  VarTE x t ->
    let thenLabel = gensym "label"
        elseLabel = gensym "label"
        _ = addCFGNode cfg thenLabel b1
        _ = addCFGNode cfg elseLabel b2
        block = IfC3 CmpEqC3 (VarC3 x t) TrueC3 thenLabel elseLabel
    in block
  LetTE x e1 e2 ->
    let e2Block = ecPred e2 b1 b2 cfg
    in ecAssign x e1 e2Block cfg
  CmpTE c e1 e2 ->
    let thenLabel = gensym "label"
        elseLabel = gensym "label"
        _ = addCFGNode cfg thenLabel b1
        _ = addCFGNode cfg elseLabel b2
        block = IfC3 (ecCmp c) (ecArg e1) (ecArg e2) thenLabel elseLabel
    in block
  IfTE e1 e2 e3 t ->
    let label1 = gensym "label"
        label2 = gensym "label"
        _ = addCFGNode cfg label1 b1
        _ = addCFGNode cfg label2 b2
        newb2 = ecPred e2 (GotoC3 label1) (GotoC3 label2) cfg
        newb3 = ecPred e3 (GotoC3 label1) (GotoC3 label2) cfg
    in ecPred e1 newb2 newb3 cfg
  _ -> error ("unknown expr: " ++ (show test))

-- The explicate-control pass on an expression in ASSIGNMENT POSITION
-- input:
--   - x: the variable being assigned
--   - e: the R5 Expression it is being assigned to
--   - k: a C3 Tail expression describing what should happen *after* the assignment
--   - cfg: a C3CFG (control flow graph)
-- output: a C3 Tail expression
-- Sometimes updates 'cfg' with new CFG nodes
ecAssign :: Variable -> TypedR5Expr -> C3Tail -> C3CFG -> C3Tail
ecAssign x e k cfg = case e of
  IntTE _ -> SeqC3 (AssignC3 x IntT (ecBasic e)) k
  VarTE _ t -> SeqC3 (AssignC3 x t (ecBasic e)) k
  PlusTE e1 e2 -> SeqC3 (AssignC3 x IntT (C3PlusE (ecArg e1) (ecArg e2))) k
  LetTE x' e1 e2 ->
    let b = ecAssign x e2 k cfg
    in ecAssign x' e1 b cfg
  CmpTE c e1 e2 -> SeqC3 (AssignC3 x BoolT (ecBasic e)) k
  IfTE e1 e2 e3 t ->
    let finallyLabel = gensym "label"
        _ = addCFGNode cfg finallyLabel k
        b2 = ecAssign x e2 (GotoC3 finallyLabel) cfg
        b3 = ecAssign x e3 (GotoC3 finallyLabel) cfg
    in ecPred e1 b2 b3 cfg
  TrueTE -> SeqC3 (AssignC3 x BoolT (ecBasic e)) k
  FalseTE -> SeqC3 (AssignC3 x BoolT (ecBasic e)) k
  NotTE _ -> SeqC3 (AssignC3 x BoolT (ecBasic e)) k
  VectorSetTE e1 i e2 -> SeqC3 (AssignC3 x VoidT (ecBasic e)) k
  AllocateTE i t -> SeqC3 (AssignC3 x t (ecBasic e)) k
  VoidTE -> SeqC3 (AssignC3 x VoidT (ecBasic e)) k
  CollectTE bytes -> SeqC3 (CollectC3 bytes) k
  VectorRefTE e1 i t -> SeqC3 (AssignC3 x t (ecBasic e)) k
  FunRefTE name t -> SeqC3 (AssignC3 x t (ecBasic e)) k
  FunCallTE a1 args argsT t -> SeqC3 (AssignC3 x t (ecBasic e)) k
  _ -> error $ show e

ecDefn :: TypedR5Definition -> C3Defn
ecDefn (DefnT name args outputT body) =
  let cfg = emptyCFG ()
      b = case name of
        "main" -> let tmp = gensym "result"
                  in ecAssign tmp body (ReturnC3 (C3ArgE (VarC3 tmp IntT))) cfg
        _ -> ecTail body cfg
      _   = addCFGNode cfg name b
  in DefnC3 name args outputT cfg

-- The explicate control pass
-- input: an R5 expression
-- output: a C3 control flow graph
explicateControl :: [TypedR5Definition] -> [C3Defn]
explicateControl defns = map ecDefn defns


------------------------------------------------------------
-- select-instructions
------------------------------------------------------------

data X86Arg = VarXE Variable Type
            | DerefE String Int
            | RegE String
            | ByteRegE String
            | IntXE Int
            | GlobalValXE String
            | FunRefXE Label
  deriving (Eq, Ord, Show)

data X86CC = CCe
           | CCl
           | CCle
           | CCg
           | CCge
  deriving (Eq, Ord, Show)

data X86Instr = MovqE X86Arg X86Arg
              | AddqE X86Arg X86Arg
              | RetqE
              | XorqE X86Arg X86Arg
              | CmpqE X86Arg X86Arg
              | SetE X86CC X86Arg
              | MovzbqE X86Arg X86Arg
              | JmpE Label
              | JmpIfE X86CC Label
              | CallqE Label
              | IndirectCallqE X86Arg
              | TailJmpE X86Arg
              | LeaqE X86Arg X86Arg
  deriving (Eq, Ord, Show)

type X86CFG = [(Label, [X86Instr])]

data X86Definition = X86Def Label [(Variable, Type)] Type X86CFG
  deriving (Eq, Ord, Show)

-- select instructions for a C3 Arg
-- returns an x86 argument
siArg :: C3Arg -> X86Arg
siArg e = case e of
  IntC3 i -> IntXE i
  VarC3 x t -> VarXE x t
  TrueC3 -> IntXE 1
  FalseC3 -> IntXE 0
  VoidC3 -> IntXE 0
  GlobalValC3 s -> GlobalValXE s

-- select instructions for a C3 comparison
-- returns an x86 comparison code
siCC :: C3Cmp -> X86CC
siCC c = case c of
  CmpEqC3 -> CCe
  CmpLTC3 -> CCl

-- Build a pointer mask for a list of types
-- Reference section 5.2.2 in the textbook
-- Input: a list of types
-- Output: a pointer mask, in decimal representation
mkPointerMask :: [Type] -> Int
mkPointerMask [] = 0
mkPointerMask (VectorT _ : ts) =
  let m = mkPointerMask ts
  in 1 + (Bits.shift m 1)
mkPointerMask (_ : ts) =
  let m = mkPointerMask ts
  in Bits.shift m 1

-- Build a tag for a vector
-- Reference section 5.2.2 in the textbook
-- Input: a list of types
-- Output: a vector tag, in decimal representation
mkTag :: [Type] -> Int
mkTag ts =
  let len = length ts
      pMask = mkPointerMask ts
      pMaskAndLength = (Bits.shift pMask 6) + len
  in (Bits.shift pMaskAndLength 1) + 1

-- The select-instructions pass on a C3Stmt statement
-- input:  a C3Stmt
-- output: a list of pseudo-x86 instructions
siStmt :: C3Stmt -> [X86Instr]
siStmt e = case e of
  AssignC3 x t (C3ArgE a) -> [ MovqE (siArg a) (VarXE x t) ]
  AssignC3 x t (C3PlusE a1 a2) -> [ MovqE (siArg a1) (VarXE x t)
                                  , AddqE (siArg a2) (VarXE x t) ]
  AssignC3 x t (C3CmpE c a1 a2) -> [ CmpqE (siArg a2) (siArg a1)
                                   , SetE (siCC c) (ByteRegE "al")
                                   , MovzbqE (ByteRegE "al") (VarXE x t) ]
  AssignC3 x t (C3NotE a1) -> [ MovqE (siArg a1) (VarXE x t)
                              , XorqE (IntXE 1) (VarXE x t) ]
  AssignC3 x t (C3AllocateE len (VectorT ts)) ->
    let tag = mkTag ts
        bytes = 8 * (len + 1)
    in [ MovqE (GlobalValXE "free_ptr") (VarXE x t)
       , AddqE (IntXE bytes) (GlobalValXE "free_ptr")
       , MovqE (VarXE x t) (RegE "r11")
       , MovqE (IntXE tag) (DerefE "r11" 0) ]
  AssignC3 x t (C3VectorSetE a1 i a2) ->
    let offset = 8 * (i + 1)
    in [ MovqE (siArg a1) (RegE "r11")
       , MovqE (siArg a2) (DerefE "r11" offset)
       , MovqE (IntXE 0) (VarXE x t) ]
  AssignC3 x t (C3VectorRefE a1 i) ->
    let offset = 8 * (i + 1)
    in [ MovqE (siArg a1) (RegE "r11")
       , MovqE (DerefE "r11" offset) (VarXE x t) ]
  CollectC3 bytes ->
    [ MovqE (RegE "r15") (RegE "rdi")
    , MovqE (IntXE bytes) (RegE "rsi")
    , CallqE "collect" ]
  AssignC3 x t (C3FunRefE f _) ->
    [ LeaqE (FunRefXE f) (VarXE x t) ]
  AssignC3 x t (C3CallE a1 args) ->
    let ps        = zip args argRegisters
        argInstrs = map (\(arg, reg) -> MovqE (siArg arg) (RegE reg)) ps
    in argInstrs ++
       [ IndirectCallqE (siArg a1)
       , MovqE (RegE "rax") (VarXE x t)
       ]
  _ -> error (show e)

-- The select-instructions pass on a C3Tail expression
-- input:  a C3 Tail expression
-- output: a list of pseudo-X86 instructions
siTail :: C3Tail -> [X86Instr]
siTail e = case e of
  ReturnC3 a ->
    let newV = gensym "tmp" in
      siStmt (AssignC3 newV IntT a) ++
           [ MovqE (VarXE newV IntT) (RegE "rax")
           , RetqE ]
  SeqC3 s t ->  (siStmt s) ++ (siTail t)
  IfC3 c a1 a2 l1 l2 ->
    [ CmpqE (siArg a2) (siArg a1)
    , JmpIfE (siCC c) l1
    , JmpE l2 ]
  GotoC3 l -> [ JmpE l ]
  TailCallC3 a1 args ->
    let a1'       = siArg a1
        args'     = map siArg args
        argInstrs = map (\(arg, reg) -> MovqE arg reg) (zip args' callingRegs)
    in argInstrs ++ [TailJmpE a1']
  _ -> error $ show e

-- The select-instructions pass, for a basic block
-- Input: a pair
--  - the basic block's label
--  - the basic block's code, as a C3 Tail
-- Output: a pair
--  - the basic block's label
--  - the basic block's code, as a list of pseudo-x86 instructions
siBlock :: (Label, C3Tail) -> (Label, [X86Instr])
siBlock (label, block) = (label, siTail block)

-- registers used for passing inputs to a function
callingRegs = map RegE ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]

-- load an argument from an input register into a function-local variable
loadArg :: ((Variable, Type), X86Arg) -> X86Instr
loadArg ((var, typ), reg) = MovqE reg (VarXE var typ)

-- The select-instructions pass, for a definition
-- Input: a C3 definition
-- Output: an x86 definition
siDefn :: C3Defn -> X86Definition
siDefn (DefnC3 name args outputT cfg) =
  let argInstrs       = map loadArg (zip args callingRegs)
      x86cfg          = map siBlock (toListCFG cfg)
      mainBlockInstrs = fromJust (lookup name x86cfg)
      mainBlock'      = (name ++ "_start", argInstrs ++ mainBlockInstrs)
  in X86Def name args outputT (mainBlock' : (delete (name, mainBlockInstrs) x86cfg))

-- The select-instructions pass
-- Input: a C3 control flow graph
-- Output: an x86 control flow graph
selectInstructions :: [C3Defn] -> [X86Definition]
selectInstructions defns = map siDefn defns

------------------------------------------------------------
-- uncover-live
------------------------------------------------------------

-- Typed variables: a pair of a variable and a type
type TypedVariable = (Variable, Type)
type LivenessResult = [(Label, [Set TypedVariable])]

-- Returns the set of referenced variables in an arg
-- input:  an x86 Arg
-- output: a set of variables mentioned in the arg
varsArg :: X86Arg -> Set TypedVariable
varsArg e = case e of
  VarXE x t -> Set.singleton (x, t)
  DerefE _ _ -> Set.empty
  RegE _ -> Set.empty
  IntXE _ -> Set.empty
  GlobalValXE _ -> Set.empty
  FunRefXE _ -> Set.empty
  _ -> error $ show e

-- Liveness analysis, for an instruction
-- inputs:
--   - e: an instruction
--   - lAfter: the set of live-after variables for *this* instruction (e)
-- output: the set of live-before variables for *this* instruction in the program
--   in other words: the set of live-after variables for the *previous* instruction
ulInstr :: X86Instr -> Set TypedVariable -> Set TypedVariable
ulInstr e lAfter = case e of
  MovqE e1 e2 -> Set.union (Set.difference lAfter (varsArg e2)) (varsArg e1)
  AddqE e1 e2 -> Set.union lAfter (Set.union (varsArg e1) (varsArg e2))
  RetqE -> lAfter
  JmpE _ -> lAfter
  JmpIfE _ _ -> lAfter
  CmpqE e1 e2 -> Set.union lAfter (Set.union (varsArg e1) (varsArg e2))
  MovzbqE (ByteRegE _) e2 -> Set.difference lAfter (varsArg e2)
  SetE c (ByteRegE _) -> lAfter
  XorqE e1 e2 -> Set.union lAfter (Set.union (varsArg e1) (varsArg e2))
  CallqE _ -> lAfter
  TailJmpE e1 -> Set.union lAfter (varsArg e1)
  LeaqE _ e2 -> Set.difference lAfter (varsArg e2)
  IndirectCallqE e1 -> Set.union lAfter (varsArg e1)
  _ -> error (show e)

-- Liveness analysis, for multiple instructions
-- input:  a list of instructions
-- output: a list of live-after sets for each instruction in the program, plus one extra
--  live-after set for the point before the first program instruction
ulInstrs :: Set TypedVariable -> [X86Instr] -> [Set TypedVariable]
ulInstrs lBefore [] = [lBefore]
ulInstrs lBefore (i : is) =
  let prevLafter : lAfters = ulInstrs lBefore is
      nextLafter = ulInstr i prevLafter
  in nextLafter : prevLafter : lAfters

-- Liveness analysis, for a pseudo-x86 control flow graph
-- inputs:
--  - ls: a topological sorted control flow graph
--  - cfg: a pseudo-x86 control flow graph
--  - lBefores: for each label, the live-before set for the associated basic block
-- output: a liveness analysis result
--  represented as a mapping from label to a list of live-after sets
ulBlocks :: [(Label, Set Label)] -> X86CFG -> [(Label, Set TypedVariable)] -> LivenessResult
ulBlocks [] cfg lBefores = []
ulBlocks ((l, adj) : ls) cfg lBefores =
  let lBefore :: Set TypedVariable =
        Set.unions (Set.map (\dest -> fromJust (lookup dest lBefores)) adj)
      (lB : lAS) = ulInstrs lBefore (fromJust (lookup l cfg))
      newLBefores = (l, lB) : lBefores
  in (l, lAS) : ulBlocks ls cfg newLBefores

-- Liveness analysis, for a pseudo-x86 control flow graph
-- input:  a pseudo-x86 control flow graph
-- output: a pair:
--   1. a liveness result (a mapping from labels to lists of live-after sets)
--   2. a pseudo-x86 control flow graph
-- How it works:
--  1. For each label in the CFG, find the adjacent blocks
--  2. Perform a topological sort on the directed graph representing the result in #1
--  3. Sort the CFG according to #2
--  4. Initialize the live-before set for each label to be empty
--  5. Run the liveness analysis on the sorted CFG in order
uncoverLive :: [X86Definition] -> [(LivenessResult, X86Definition)]
uncoverLive defs = map uncoverLiveDef defs

uncoverLiveDef :: X86Definition -> (LivenessResult, X86Definition)
uncoverLiveDef (X86Def name args outputT cfg) =
  let adjacentBlockSets = map adjacentBlocks cfg
      sortedLabels = tsort adjacentBlockSets
      sortedCFG = map (\l -> (l, fromJust (lookup l adjacentBlockSets))) sortedLabels
      initLiveBefores = map (\l -> (l, Set.empty)) sortedLabels
      lAfters = ulBlocks sortedCFG cfg initLiveBefores
  in (lAfters, X86Def name args outputT cfg)

-- topological sort
tsort :: [(Label, Set Label)] -> [Label]
tsort [] = []
tsort ls =
  let p@(l, _) = case find (\(l, s) -> Set.null s) ls of
        Nothing -> error ("tsort failure: \n" ++ (T.unpack $ pShowNoColor ls))
        Just x -> x
      ls2 = delete p ls
      ls3 = map (\(l', s) -> (l', Set.delete l s)) ls2
  in l : tsort ls3

-- Find the blocks adjacent to a block
adjacentBlocks :: (Label, [X86Instr]) -> (Label, Set Label)
adjacentBlocks (label, instrs) =
  (label, Set.unions (map adjacentBlocksInstr instrs))

-- Find the blocks an instruction jumps to
adjacentBlocksInstr :: X86Instr -> Set Label
adjacentBlocksInstr i = case i of
  JmpE l -> Set.singleton l
  JmpIfE _ l -> Set.singleton l
  _ -> Set.empty


------------------------------------------------------------
-- build-interference
------------------------------------------------------------

-- a list of all the registers available to use
registerArgs = map RegE allRegisters
callerSavedArgs = map RegE callerSavedRegisters

-- Add edges between one location (as an X86Arg) and a list of other variables
-- input:
--  - an interference graph (g)
--  - a "destination" (d)
--  - a list of "source" variables
-- output: a new interference graph, with edges between d and each
--  variable in the list of source variables
addEdges :: Graph X86Arg -> X86Arg -> [TypedVariable] -> Graph X86Arg
addEdges g d []             = g
addEdges g d ((v, tv) : vs) =
  let g' = addEdges g d vs
  in addEdge g' d (VarXE v UnknownT)

-- Add edges between a list of locations (as X86Args) and a list of other variables
-- input:
--  - an interference graph (g)
--  - a list of "destinations"
--  - a list of "source" variables
-- output: a new interference graph, with edges between d and each
--  variable in the list of source variables
addRegisterEdges :: Graph X86Arg -> [X86Arg] -> [TypedVariable] -> Graph X86Arg
addRegisterEdges g []       vs  = g
addRegisterEdges g (r : rs) vs  =
  let g' = addRegisterEdges g rs vs
  in addEdges g' r vs

-- Determine if a typed variable is a vector or not
isVecVar :: TypedVariable -> Bool
isVecVar (_, VectorT _) = True
isVecVar _ = False

-- build-interference, for a single instruction
-- input:
--  - a pair, containing an instruction and the live-after set for that instruction
--  - the current interference graph
-- output:
--  - a new interference graph
biInstr :: (X86Instr, Set TypedVariable) -> Graph X86Arg -> Graph X86Arg
biInstr (instr, liveAfter) g = case instr of
  MovqE _ (VarXE x t) -> addEdges g (VarXE x t) (Set.toList liveAfter)
  MovqE _ _ -> g
  AddqE _ (VarXE x t) -> addEdges g (VarXE x t) (Set.toList liveAfter)
  AddqE _ _ -> g
  CmpqE _ (VarXE x t) -> addEdges g (VarXE x t) (Set.toList liveAfter)
  CmpqE _ _ -> g
  JmpIfE _ _ -> g
  JmpE _ -> g
  SetE _ (ByteRegE _) -> g
  MovzbqE (ByteRegE _) (VarXE x t) -> addEdges g (VarXE x t) (Set.toList liveAfter)
  MovzbqE (ByteRegE _) _ -> g
  RetqE -> g
  XorqE _ (VarXE x t) -> addEdges g (VarXE x t) (Set.toList liveAfter)
  XorqE _ _ -> g
  CallqE f ->
    let vecVars = filter isVecVar (Set.toList liveAfter)
        -- add edges from vector-valued variables to *all* registers
        g1      = addRegisterEdges g registerArgs vecVars
        -- add edges from *all* variables to *caller-saved* registers
        g2      = addRegisterEdges g1 callerSavedArgs (Set.toList liveAfter)
    in g2
  LeaqE _ (VarXE x t) -> addEdges g (VarXE x t) (Set.toList liveAfter)
  LeaqE _ _ -> g
  TailJmpE _ -> addRegisterEdges g callerSavedArgs (Set.toList liveAfter)
  IndirectCallqE _ -> addRegisterEdges g callerSavedArgs (Set.toList liveAfter)
  _ -> error (show instr)

-- build-interference, for a list of instructions
-- input:  a list of pairs, each one containing an instruction and live-after set
-- output: a complete interference graph
biInstrs :: [(X86Instr, Set TypedVariable)] -> Graph X86Arg -> Graph X86Arg
biInstrs [] g = g
biInstrs (p : ps) g = biInstrs ps (biInstr p g)

-- build-interference, for a block
-- inputs:
--  - l: the block's label
--  - cfg: the x86 control flow graph
--  - liveness: the liveness analysis results for the cfg
--  - g: the current interference graph
-- output: the updated interference graph
biBlock :: Label -> X86CFG -> LivenessResult -> Graph X86Arg -> Graph X86Arg
biBlock l cfg liveness g =
  let instrs = fromJust $ lookup l cfg
      las = fromJust $ lookup l liveness
  in biInstrs (zip instrs las) g

-- build-interference, for multiple blocks
-- inputs:
--  - ls: the labels of multiple blocks
--  - cfg: the x86 control flow graph
--  - liveness: the liveness analysis results for the cfg
--  - g: the current interference graph
-- output: the updated interference graph
biBlocks :: [Label] -> X86CFG -> LivenessResult -> Graph X86Arg -> Graph X86Arg
biBlocks [] _ _ g = g
biBlocks (l : ls) cfg liveness g = biBlocks ls cfg liveness (biBlock l cfg liveness g)

-- build-interference, for a pseudo-x86 program
-- input:  a pair:
--  - the liveness analysis results for the program
--  - the pseudo-x86 control flow graph for the program
-- output: a pair:
--  - the complete interference graph
--  - the pseudo-x86 control flow graph
buildInterference :: [(LivenessResult, X86Definition)] -> [(Graph X86Arg, X86Definition)]
buildInterference ps = map biDef ps

biDef :: (LivenessResult, X86Definition) -> (Graph X86Arg, X86Definition)
biDef (liveness, X86Def name args outputT cfg) =
  let labels = map fst cfg
      g = biBlocks labels cfg liveness emptyGraph
  in (g, X86Def name args outputT cfg)


------------------------------------------------------------
-- allocate-registers
------------------------------------------------------------

-- Colors are one of:
--  - Register colors
--  - Stack location colors
--  - Root stack location colors
data Color = RegColor String
           | StackColor Int
           | RootStackColor Int
  deriving (Eq, Ord, Show)

-- A "coloring" for a graph is a mapping from variables in the graph to colors
type Coloring = Map Variable Color

-- A "saturation" is the set of colors used by neighboring nodes in the graph
type Saturation = Set Color

-- We pre-assign each register a color
regColors = map RegColor allRegisters
regColorSet = Set.fromList regColors

-- Attempt to pick a register color which does *not* occur in a saturation set
-- Input: a saturation set (sat)
-- Output: (Maybe) a register color
--  If a register color is available, return the first available color
--  If all register colors are present in the saturation set, return Nothing
pickRegColor :: Saturation -> Maybe Color
pickRegColor sat = case Set.toList (Set.difference regColorSet sat) of
  [] -> Nothing
  r : rs -> Just r

-- pick a color that isn't already used by a neighbor
-- inputs:
--  - a saturation set (sat)
--  - the type of the variable being colored (t)
-- output: a color
--  If a register color is available, return that one
--  Otherwise, if the variable type is a vector, return a root stack color
--  Otherwise, pick a regular stack color
pickColor :: Saturation -> Type -> Color
pickColor sat t =
  case pickRegColor sat of
    Just c -> c
    Nothing -> case t of
      VectorT _ -> pickRootStackColor sat 0
      _ -> pickStackColor sat 0

-- find the "smallest" root stack color not in a saturation
-- input:  saturation (sat) and lowest color to consider (c)
-- output: lowest root stack color not present in "sat"
pickRootStackColor :: Saturation -> Int -> Color
pickRootStackColor sat c | Set.member (RootStackColor c) sat = pickRootStackColor sat (c+1)
                         | otherwise = RootStackColor c

-- find the "smallest" stack color not in a saturation
-- input:  saturation (sat) and lowest color to consider (c)
-- output: lowest stack color not present in "sat"
pickStackColor :: Saturation -> Int -> Color
pickStackColor sat c | Set.member (StackColor c) sat = pickStackColor sat (c+1)
                     | otherwise = StackColor c

-- get the colors assigned to a list of variables in the coloring assignment
-- input:
--  - a coloring (cs)
--  - a list of variables
-- output: a set of colors, containing all the colors assigned to variables in the
--  list by the coloring "cs"
getColors :: Coloring -> [X86Arg] -> Set Color
getColors cs [] = Set.empty
getColors cs (RegE r : xs) = Set.insert (RegColor r) (getColors cs xs)
getColors cs (VarXE x t : xs) | Map.member x cs = Set.insert (cs Map.! x) (getColors cs xs)
                              | otherwise       = getColors cs xs

-- get the saturation of a node in the interference graph
-- input:
--  - a variable (x)
--  - a coloring (cs)
--  - an interference graph (g)
-- output: the saturation of x given cs and g
getSaturation :: TypedVariable -> Coloring -> Graph X86Arg -> Saturation
getSaturation (x, t) cs g =
  let ns = Set.toList (neighbors g (VarXE x UnknownT))
  in getColors cs ns

-- helper to return the index of the maximum value in a list
maxi :: (Ord a) => [a] -> (a, Int)
maxi xs = maximumBy (comparing fst) (zip xs [0..])

-- find the maximally saturated variable in a list of variables
-- input:
--  - a list of variables (xs)
--  - the current coloring (cs)
--  - the interference graph (g)
-- output:
--  - the variable from xs with the maximum saturation, given cs and g
maxSat :: [TypedVariable] -> Coloring -> Graph X86Arg -> TypedVariable
maxSat xs cs g =
  let sats   = map (\x -> getSaturation x cs g) xs
      sizes  = map Set.size sats
      (_, i) = maxi sizes
  in xs !! i

-- color the graph
-- input:
--  - a list of variables (xs) to color
--  - the interference graph (g)
--  - the current coloring (cs)
-- output:
--  - the new coloring
colorGraph :: [TypedVariable] -> Graph X86Arg -> Coloring -> Coloring
colorGraph [] g cs = cs
colorGraph xs g cs =
  let (x, t) = maxSat xs cs g                          -- find maximally saturated variable
      xs'    = delete (x, t) xs                        -- remove it from the list
      color  = pickColor (getSaturation (x, t) cs g) t -- pick a color for it
      newCs  = Map.insert x color cs                   -- record its coloring
  in colorGraph xs' g newCs

-- get the variables used in a program
-- input: a list of instructions
-- output: a list of variables
getLocalVars :: [X86Instr] -> [TypedVariable]
getLocalVars instrs = Set.toList (Set.unions (map varsInstr instrs))

varsInstr :: X86Instr -> Set TypedVariable
varsInstr e = case e of
  MovqE a1 a2 -> Set.union (varsArg a1) (varsArg a2)
  AddqE a1 a2 -> Set.union (varsArg a1) (varsArg a2)
  RetqE -> Set.empty
  CmpqE a1 a2 -> Set.union (varsArg a1) (varsArg a2)
  JmpIfE _ _ -> Set.empty
  JmpE _ -> Set.empty
  MovzbqE (ByteRegE _) a2 -> varsArg a2
  SetE _ (ByteRegE _) -> Set.empty
  XorqE a1 a2 -> Set.union (varsArg a1) (varsArg a2)
  CallqE f -> Set.empty
  LeaqE a1 a2 -> Set.union (varsArg a1) (varsArg a2)
  TailJmpE a1 -> varsArg a1
  IndirectCallqE a1 -> varsArg a1
  _ -> error (show e)

-- Given a register (reg) and an offset (i), build a stack location (as an X86Arg)
mkStackLoc :: Int -> String -> X86Arg
mkStackLoc i reg = DerefE reg (-8 * (i + 1))

-- given a coloring, a map from colors to their locations (on the stack or in a register),
-- and a variable, return the assigned location for that variable
-- input:
--  - a coloring (cs)
--  - a variable (x)
-- output: the location for the variable "x"
getHome :: Coloring -> TypedVariable -> (Variable, X86Arg)
getHome cs (x, t) =
  let color = cs Map.! x
      loc   = case color of
                RegColor r -> RegE r
                StackColor i -> mkStackLoc i "rbp"
                RootStackColor i -> mkStackLoc i "r15"
  in (x, loc)

-- When printing out the homes and coloring information, skip printing
-- if the output would be longer than this value (default: 5000 characters).
-- To see the output when information is really long, modify this value
-- to a larger number.
longestOutputAllowed = 5000

-- Print a list in a nicely-formatted way (for homes and coloring)
showL :: (Show a) => [a] -> String
showL xs =
  let str = "[ " ++ intercalate "\n, " (map show xs) ++ " ]"
  in if (length str) > longestOutputAllowed
  then " **** LONG OUTPUT OMITTED, modify 'longestOutputAllowed' to see it ****"
  else str

-- Count the number of variables spilled to both stacks
-- Input: the list of colors assigned during allocation
-- Output: a pair
--  - the number of variables spilled to the stack
--  - the number of variables spilled to the root stack
countSpills :: [Color] -> (Int, Int)
countSpills [] = (0, 0)
countSpills (a : as) =
  let (stackSpills, rootStackSpills) = countSpills as
  in case a of
    RegColor _ -> (stackSpills, rootStackSpills)
    StackColor _ -> (stackSpills + 1, rootStackSpills)
    RootStackColor _ -> (stackSpills, rootStackSpills + 1)

-- the allocate-registers pass
-- input:  a pair, containing an interference graph and list of pseudo-x86 instructions
-- output: a pair, containing a list of x86 instructions and the number of stack locations used
allocateRegisters :: [(Graph X86Arg, X86Definition)] -> [(X86Definition, (Int, Int))]
allocateRegisters ps = map arDef ps

-- the allocate-registers pass, for a definition
-- input:
--  - g: the interference graph for the definition
--  - the definition itself
-- output: a pair, containing a definition and the number of variables spilled
--  to the stack and root stack
arDef :: (Graph X86Arg, X86Definition) -> (X86Definition, (Int, Int))
arDef (g, X86Def name args outputT cfg) =
  let locals    :: [TypedVariable]      = nub (concat (map (getLocalVars . snd) cfg))
      initColoring :: Coloring          = Map.empty
      coloring  :: Coloring             = colorGraph locals g initColoring
      homes :: [(Variable, X86Arg)]     = map (getHome coloring) locals
      cfg'      :: X86CFG               = map (ahBlock homes) cfg
      spills                            = countSpills (map snd (Map.toList coloring))
  in trace ("\nColoring:\n" ++ (showL (Map.toList coloring)) ++
            "\n\nHomes:\n" ++ (showL homes) )
  (X86Def name args outputT cfg', spills)

-- assign-homes for a block
ahBlock :: [(Variable, X86Arg)] -> (Label, [X86Instr]) -> (Label, [X86Instr])
ahBlock homes (l, instrs) = (l, map (ahInstr homes) instrs)

-- copied from assign-homes
ahInstr :: [(Variable, X86Arg)] -> X86Instr -> X86Instr
ahInstr homes e = case e of
  MovqE a1 a2 -> MovqE (ahArg homes a1) (ahArg homes a2)
  AddqE a1 a2 -> AddqE (ahArg homes a1) (ahArg homes a2)
  RetqE -> RetqE
  CmpqE a1 a2 -> CmpqE (ahArg homes a1) (ahArg homes a2)
  JmpIfE c l -> JmpIfE c l
  JmpE l -> JmpE l
  SetE _ (ByteRegE _) -> e
  MovzbqE (ByteRegE r) a2 -> MovzbqE (ByteRegE r) (ahArg homes a2)
  XorqE a1 a2 -> XorqE (ahArg homes a1) (ahArg homes a2)
  CallqE f -> CallqE f
  LeaqE a1 a2 -> LeaqE (ahArg homes a1) (ahArg homes a2)
  TailJmpE a1 -> TailJmpE (ahArg homes a1)
  IndirectCallqE a1 -> IndirectCallqE (ahArg homes a1)
  _ -> error (show e)

ahArg :: [(Variable, X86Arg)] -> X86Arg -> X86Arg
ahArg homes e = case e of
  VarXE s t -> fromJust $ lookup s homes
  RegE _ -> e
  IntXE _ -> e
  GlobalValXE _ -> e
  DerefE _ _ -> e
  FunRefXE _ -> e
  _ -> error (show e)

------------------------------------------------------------
-- patch-instructions
------------------------------------------------------------

-- The patch-instructions pass
-- input: a pair
--   - a list of x86 instructions
--   - the number of stack locations used
-- output: a pair
--   - a list of *patched* x86 instructions
--   - the number of stack locations used
patchInstructions :: [(X86Definition, (Int, Int))] -> [(X86Definition, (Int, Int))]
patchInstructions ps = map piDef ps

piDef :: (X86Definition, (Int, Int)) -> (X86Definition, (Int, Int))
piDef (X86Def name args outputT cfg, numSpills) =
  (X86Def name args outputT (map piBlock cfg), numSpills)

-- The patch-instructions pass, for a basic block
-- input: a pair:
--  - the label of the block
--  - the list of instructions for the block
-- output: a pair:
--  - the label of the block
--  - the list of (updated) instructions for the block
piBlock :: (Label, [X86Instr]) -> (Label, [X86Instr])
piBlock (l, instrs) = (l, concat (map piInstr instrs))

-- The patch-instructions pass, for a single instruction
-- input: a pair
--   - a single x86 instruction
--   - the number of stack locations used
-- output: a pair
--   - a single *patched* x86 instruction
--   - the number of stack locations used
-- Patched instructions contain at most one memory access in each `movq` or `addq` instruction
piInstr :: X86Instr -> [X86Instr]
piInstr e = case e of
  MovqE (DerefE r1 i1) (DerefE r2 i2) -> [ MovqE (DerefE r1 i1) (RegE "rax")
                                         , MovqE (RegE "rax") (DerefE r2 i2) ]
  MovqE _ _ -> [e]
  AddqE (DerefE r1 i1) (DerefE r2 i2) -> [ MovqE (DerefE r1 i1) (RegE "rax")
                                         , AddqE (RegE "rax") (DerefE r2 i2) ]
  AddqE _ _ -> [e]
  RetqE -> [e]
  CmpqE a1 (IntXE i) -> [ MovqE (IntXE i) (RegE "rax")
                        , CmpqE a1 (RegE "rax") ]
  CmpqE _ _ -> [e]
  JmpIfE _ _ -> [e]
  JmpE _ -> [e]
  SetE _ (ByteRegE _) -> [e]
  MovzbqE (ByteRegE r) (DerefE r1 i1) -> [ MovzbqE (ByteRegE r) (RegE "rax")
                                         , MovqE (RegE "rax") (DerefE r1 i1) ]
  MovzbqE _ _ -> [e]
  XorqE (DerefE r1 i1) (DerefE r2 i2) -> [ MovqE (DerefE r1 i1) (RegE "rax")
                                         , XorqE (RegE "rax") (DerefE r2 i2) ]
  XorqE _ _ -> [e]
  CallqE _ -> [e]
  LeaqE (FunRefXE f) (DerefE r o) -> [ LeaqE (FunRefXE f) (RegE "rax")
                                     , MovqE (RegE "rax") (DerefE r o) ]
  LeaqE (FunRefXE _) _ -> [e]
  TailJmpE d -> [ MovqE d (RegE "rax")
                , TailJmpE (RegE "rax") ]
  IndirectCallqE _ -> [e]
  _ -> error (show e)

------------------------------------------------------------
-- print-x86
------------------------------------------------------------

-- Set this to `True` if you're using macos
macos :: Bool
macos = False

-- Print a function or label name
-- Add a _ at the front if we're using macos
printFun :: String -> String
printFun s = case macos of
  True -> "_" ++ s
  False -> s

-- Align the size of the stack frame to `alignment` bytes
-- Input:
--   - n: the number of bytes of stack space used on the current stack frame
--   - alignment: the desired alignment (in bytes) - for x86, usually 16 bytes
-- Output: the size in bytes of the correctly aligned stack frame
align :: Int -> Int -> Int
align n alignment = case n `mod` alignment of
  0 -> n
  _ -> n + (alignment - (n `mod` alignment))

-- The printX86 pass for x86 "args"
printX86Arg :: X86Arg -> String
printX86Arg e = case e of
  VarXE s t -> "%%" ++ s
  RegE r -> "%" ++ r
  IntXE i -> "$" ++ (show i)
  DerefE r i -> (show i) ++ "(%" ++ r ++ ")"
  ByteRegE r -> "%" ++ r
  GlobalValXE s -> (printFun s) ++ "(%rip)"
  FunRefXE f -> (printFun f) ++ "(%rip)"
  _ -> error $ show e

-- The printX86 pass for x86 instructions
printX86Instr :: (Int, Int) -> Label -> X86Instr -> String
printX86Instr (stackSpills, rootStackSpills) name e =  case e of
  MovqE a1 a2 -> " movq " ++ (printX86Arg a1) ++ ", " ++ (printX86Arg a2)
  AddqE a1 a2 -> " addq " ++ (printX86Arg a1) ++ ", " ++ (printX86Arg a2)
  RetqE -> " jmp " ++ (printFun (name ++ "_conclusion"))
  CmpqE a1 a2 -> " cmpq " ++ (printX86Arg a1) ++ ", " ++ (printX86Arg a2)
  JmpIfE CCe l -> " je " ++ (printFun l)
  JmpIfE CCl l -> " jl " ++ (printFun l)
  JmpE l -> " jmp " ++ (printFun l)
  SetE CCe a -> " sete " ++ (printX86Arg a)
  SetE CCl a -> " setl " ++ (printX86Arg a)
  MovzbqE (ByteRegE r) a2 -> " movzbq %" ++ r ++ ", " ++ (printX86Arg a2)
  XorqE a1 a2 -> " xorq " ++ (printX86Arg a1) ++ ", " ++ (printX86Arg a2)
  CallqE f -> " callq " ++ (printFun f)
  LeaqE a1 a2 -> " leaq " ++ (printX86Arg a1) ++ ", " ++ (printX86Arg a2)
  TailJmpE a1 ->
    let popqs = map (\r -> " popq %" ++ r ++ "\n") (reverse calleeSavedRegisters)
        stackSize = align (8 * stackSpills) 16
        rootStackSize = 8 * rootStackSpills
    in " subq $" ++ (show rootStackSize) ++ ", %r15\n" ++
       " addq $" ++ (show stackSize) ++ ", %rsp\n" ++
       (concat popqs) ++
       " popq %rbp\n" ++
       " jmp *" ++ (printX86Arg a1)
  IndirectCallqE a1 -> " callq *" ++ (printX86Arg a1)
  _ -> error $ show e



-- The printX86 pass for a single block
-- Input:
--   - spills: the number of variables spilled to the regular and root stacks
--   - name: the name of the function being printed
--   - (l, instrs): the label and instructions of the block to print
-- Output: x86 assembly, as a string
printX86Block :: (Int, Int) -> Label -> (Label, [X86Instr]) -> String
printX86Block spills name (l, instrs) =
  (printFun l) ++ ":\n" ++
  (intercalate "\n" $ map (printX86Instr spills name) instrs)


-- The printX86 pass for multiple block
-- Input:
--   - spills: the number of variables spilled to the regular and root stacks
--   - name: the name of the function being printed
--   - cfg: the control flow graph for the function being printed
-- Output: x86 assembly, as a string
printX86Blocks :: (Int, Int) -> Label -> [(Label, [X86Instr])] -> String
printX86Blocks spills name cfg =
  (intercalate "\n" $ map (printX86Block spills name) cfg) ++ "\n"

-- The printX86 pass for x86 programs
-- Input: a pair
--   - a list of instructions
--   - the number of stack locations used in the program
-- Output: x86 assembly, as a string
printX86 :: [(X86Definition, (Int, Int))] -> String
printX86 ps =
  " .globl " ++ (printFun "main") ++ "\n" ++
  (concat (map printX86Def ps))


-- Initialize the root stack
-- Input:
--  - name: the name of the function being printed
--  - rootStackSpills: the number of variables spilled to the root stack
-- Output: a string containing instructions for initializing the root stack
rootStackInit :: String -> Int -> String
rootStackInit name rootStackSpills =
  -- for each spilled variable, initialize the stack location for it
  let initInstrs = concat (take rootStackSpills (repeat " movq $0, (%r15)\n addq $8, %r15\n"))
  in case name of
       "main" ->
         -- if we're in main, initialize the root stack itself
         " movq $" ++ (show rootStackSize) ++ ", %rdi\n" ++
         " movq $" ++ (show heapSize) ++ ", %rsi\n" ++
         " callq " ++ (printFun "initialize") ++ "\n" ++
         " movq " ++ (printFun "rootstack_begin") ++ "(%rip), %r15\n" ++
         -- then initialize the root stack locations we'll use
         initInstrs
       _ -> initInstrs  -- otherwise just initialize the root stack locations


printX86Def :: (X86Definition, (Int, Int)) -> String
printX86Def (X86Def name args outputT cfg, (stackSpills, rootStackSpills)) =
  let stackSize = align (8 * stackSpills) 16
      rootStackSize = 8 * rootStackSpills
      pushqs = map (\r -> " pushq %" ++ r ++ "\n") calleeSavedRegisters
      popqs = map (\r -> " popq %" ++ r ++ "\n") (reverse calleeSavedRegisters)
  in
  -- entry point for the function
  (printFun (name)) ++ ":\n" ++
  -- set up the stack
  " pushq %rbp\n" ++
  " movq %rsp, %rbp\n" ++
  -- save callee-saved registers
  (concat pushqs) ++
  -- add space on the stack for stack variables
  " subq $" ++ (show stackSize) ++ ", %rsp\n" ++
  -- initialize the root stack
  (rootStackInit name rootStackSpills) ++
  -- jump to the function body
  " jmp " ++ (printFun (name ++ "_start")) ++ "\n" ++
  -- print the labels and instructions for the blocks of this function
  (printX86Blocks (stackSpills, rootStackSpills) name (reverse cfg)) ++
  -- print the function conclusion
  (printFun (name ++ "_conclusion")) ++ ":\n" ++
  -- if we're in main, call print_int
  (case name of
     "main" ->
       " movq %rax, %rdi\n" ++
       " callq " ++ (printFun "print_int") ++ "\n" ++
       " movq $0, %rax\n"
     _ -> "") ++
  -- shrink the root stack
  " subq $" ++ (show rootStackSize) ++ ", %r15\n" ++
  -- shrink the stack
  " addq $" ++ (show stackSize) ++ ", %rsp\n" ++
  -- restore callee-saved registers
  (concat popqs) ++
  -- restore stack pointer
  " popq %rbp\n" ++
  -- return
  " retq\n"

------------------------------------------------------------
-- compile / main
------------------------------------------------------------

compile :: R5Program -> String
compile = printX86 . patchInstructions . allocateRegisters . buildInterference .
  uncoverLive . selectInstructions . explicateControl . removeComplexOpera . exposeAllocation .
  limitFunctions . revealFunctions . uniquify . shrink . typecheck

logOutput :: Show b => String -> (a -> b) -> (a -> IO b)
logOutput name f = \ x -> do
  putStrLn "--------------------------------------------------"
  putStrLn $ "Output of pass " ++ name ++ ":"
  putStrLn "--------------------------------------------------"
  let result = f x
  putStrLn ""
  pPrintNoColor result
  putStrLn ""
  return result

compileLog :: R5Program -> IO String
compileLog e =
  (logOutput "input" id) e >>=
  (logOutput "typecheck" typecheck) >>=
  (logOutput "shrink" shrink) >>=
  (logOutput "uniquify" uniquify) >>=
  (logOutput "revealFunctions" revealFunctions) >>=
  (logOutput "limitFunctions" limitFunctions) >>=
  (logOutput "exposeAllocation" exposeAllocation) >>=
  (logOutput "removeComplexOpera" removeComplexOpera) >>=
  (logOutput "explicateControl" explicateControl) >>=
  (logOutput "selectInstructions" selectInstructions) >>=
  (logOutput "uncoverLive" uncoverLive) >>=
  (logOutput "buildInterference" buildInterference) >>=
  (logOutput "allocateRegisters" allocateRegisters) >>=
  (logOutput "patchInstructions" patchInstructions) >>=
  (logOutput "printX86" printX86)
