namespace FMinus

open AST // Import AST module (assumed to contain definitions of Exp type)

exception TypeError // Define TypeError exception

// Define types available in F- language
type Type =
  | Int
  | Bool
  | TyVar of string
  | Func of Type * Type

type TypeEnv = Map<string, Type> // Type environment as a mapping from strings to Types

module Type =

  // Mutable counter for generating fresh type variables
  let mutable typeVarCounter = 0

  // Generate a new type variable
  let newTyVar () =
    typeVarCounter <- typeVarCounter + 1
    TyVar ("'a" + string typeVarCounter)

  // Convert a Type to its string representation
  let rec toString (typ: Type): string =
    match typ with
    | Int -> "int"
    | Bool -> "bool"
    | TyVar s -> s
    | Func (t1, t2) -> sprintf "(%s) -> (%s)" (toString t1) (toString t2)

  // Mutable substitution map for type variables
  let mutable subst = Map.empty

  // Apply substitution to a type
  let rec applySubst (subst: Map<string, Type>) (typ: Type) : Type =
    match typ with
    | TyVar v ->
        match Map.tryFind v subst with
        | Some t -> applySubst subst t
        | None -> TyVar v
    | Func (t1, t2) -> Func (applySubst subst t1, applySubst subst t2)
    | t -> t

  // Unify two types
  let rec unify t1 t2 =
    match applySubst subst t1, applySubst subst t2 with
    | Int, Int | Bool, Bool -> () // Unifying primitive types
    | TyVar v, t | t, TyVar v ->
        if t = TyVar v then () else subst <- Map.add v t subst // Add substitution
    | Func (a1, r1), Func (a2, r2) ->
        unify a1 a2 // Unify argument types
        unify r1 r2 // Unify return types
    | _ -> raise TypeError // Incompatible types

  // Infer the type of an expression in a given environment
  let rec inferExpr (env: TypeEnv) (expr: Exp) : Type =
    match expr with
    | Num _ -> inferNum ()
    | True | False -> inferBool ()
    | Var x -> inferVar env x
    | Neg e -> inferNeg env e
    | Add (e1, e2) | Sub (e1, e2) -> inferAddSub env e1 e2
    | LessThan (e1, e2) | GreaterThan (e1, e2) -> inferComparison env e1 e2
    | Equal (e1, e2) | NotEq (e1, e2) -> inferEquality env e1 e2
    | IfThenElse (cond, thenExpr, elseExpr) -> inferIfThenElse env cond thenExpr elseExpr
    | LetIn (x, e1, e2) -> inferLetIn env x e1 e2
    | Fun (param, body) -> inferFun env param body
    | App (func, arg) -> inferApp env func arg
    | LetFunIn (f, x, e1, e2) -> inferLetFunIn env f x e1 e2
    | LetRecIn (f, x, e1, e2) -> inferLetRecIn env f x e1 e2

  and inferNum () : Type = Int

  and inferBool () : Type = Bool

  and inferVar (env: TypeEnv) (x: string) : Type =
    match Map.tryFind x env with
    | Some t -> applySubst subst t
    | None -> raise TypeError

  and inferNeg (env: TypeEnv) (e: Exp) : Type =
    let typ = inferExpr env e
    unify typ Int
    Int

  and inferAddSub (env: TypeEnv) (e1: Exp) (e2: Exp) : Type =
    let typ1 = inferExpr env e1
    let typ2 = inferExpr env e2
    unify typ1 Int
    unify typ2 Int
    Int

  and inferComparison (env: TypeEnv) (e1: Exp) (e2: Exp) : Type =
    let typ1 = inferExpr env e1
    let typ2 = inferExpr env e2
    unify typ1 Int
    unify typ2 Int
    Bool

  and inferEquality (env: TypeEnv) (e1: Exp) (e2: Exp) : Type =
    let typ1 = inferExpr env e1
    let typ2 = inferExpr env e2
    unify typ1 typ2
    Bool

  and inferIfThenElse (env: TypeEnv) (cond: Exp) (thenExpr: Exp) (elseExpr: Exp) : Type =
    let condType = inferExpr env cond
    unify condType Bool
    let thenType = inferExpr env thenExpr
    let elseType = inferExpr env elseExpr
    unify thenType elseType
    thenType

  and inferLetIn (env: TypeEnv) (x: string) (e1: Exp) (e2: Exp) : Type =
    let e1Type = inferExpr env e1
    let newEnv = Map.add x e1Type env
    inferExpr newEnv e2

  and inferFun (env: TypeEnv) (param: string) (body: Exp) : Type =
    let paramType = newTyVar ()
    let newEnv = Map.add param paramType env
    let bodyType = inferExpr newEnv body
    Func (applySubst subst paramType, bodyType)

  and inferApp (env: TypeEnv) (func: Exp) (arg: Exp) : Type =
    let funcType = inferExpr env func
    let argType = inferExpr env arg
    let returnType = newTyVar ()
    unify funcType (Func (argType, returnType))
    applySubst subst returnType

  and inferLetFunIn (env: TypeEnv) (f: string) (x: string) (e1: Exp) (e2: Exp) : Type =
    let paramType = newTyVar ()
    let returnType = newTyVar ()
    let newEnv = Map.add f (Func (paramType, returnType)) env
    let newEnvWithParam = Map.add x paramType newEnv
    let bodyType = inferExpr newEnvWithParam e1
    unify returnType bodyType
    inferExpr newEnv e2

  and inferLetRecIn (env: TypeEnv) (f: string) (x: string) (e1: Exp) (e2: Exp) : Type =
    let paramType = newTyVar ()
    let returnType = newTyVar ()
    let newEnv = Map.add f (Func (paramType, returnType)) env
    let newEnvWithParam = Map.add x paramType newEnv
    let bodyType = inferExpr newEnvWithParam e1
    unify returnType bodyType
    inferExpr newEnv e2

  // Infer the type of the entire program
  let infer (prog: Exp) : Type =
    inferExpr Map.empty prog // Start type inference with an empty environment
