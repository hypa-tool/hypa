module Term

open System

type PrePost = PRE | POST

// A RelVar is the one used for the predicates. It consist of a program variable and a copy it is resolved on, e.g., x_0
type RelVar = String * int

// A SingleVarPrePost is used to represent the transitions of a program. A variable has the form (x, PRE) or (x, POST)
type SingleVarPrePost = String * PrePost
type SingleVar = String


type VarType =
    | INT 
    | BOOL

    member this.AsString = 
        match this with
            | INT -> "Int"
            | BOOL -> "Bool"

/// The type representing an SMT formula
type Term<'T when 'T : comparison> =
    | Var of 'T
    | Const of int64
    | Add of list<Term<'T>>
    | Sub of Term<'T> * Term<'T>
    | Mul of list<Term<'T>>
    | UMin of Term<'T>
    | True
    | False
    | Eq of Term<'T> * Term<'T>
    | Le of Term<'T> * Term<'T>
    | Lt of Term<'T> * Term<'T>
    | Ge of Term<'T> * Term<'T>
    | Gt of Term<'T> * Term<'T>
    | And of list<Term<'T>>
    | Or of list<Term<'T>>
    | Implies of Term<'T> * Term<'T>
    | Iff of Term<'T> * Term<'T>
    | Neg of Term<'T>
    | Ite of Term<'T> * Term<'T> * Term<'T>
    | Let of list<'T*Term<'T>> * Term<'T>
    | Forall of list<'T * VarType> * Term<'T>
    | Exists of list<'T * VarType> * Term<'T>

    /// Returns all Vars used in this term
    member this.UsedVars =
        match this with
            | Var v -> Set.singleton v 
            | Const _  | True | False -> Set.empty
            | Eq (t1, t2) | Le(t1, t2) | Lt(t1, t2) | Ge(t1, t2) | Gt(t1, t2) | Sub(t1, t2) -> Set.union t1.UsedVars t2.UsedVars
            | Add l | Mul l | And l | Or l -> Set.unionMany (List.map (fun (x:Term<'T>) -> x.UsedVars) l)
            | Implies(f1, f2) | Iff(f1, f2) -> Set.union f1.UsedVars f2.UsedVars
            | Ite (f1, f2, f3) -> Set.unionMany [f1.UsedVars; f2.UsedVars;f3.UsedVars]
            | Neg f | UMin f | Forall(_, f) | Exists(_, f)   -> f.UsedVars
            | Let(bindings, body) -> failwith "Not supported"

    // Returns all vars that are free (i.e., not bond by some quantifier) in this term
    member this.FreeVars =
        match this with
            | Var v -> Set.singleton v 
            | Const _  | True | False -> Set.empty
            | Eq (t1, t2) | Le(t1, t2) | Lt(t1, t2) | Ge(t1, t2) | Gt(t1, t2) | Sub(t1, t2) -> Set.union t1.UsedVars t2.UsedVars
            | Add l  | Mul l | And l | Or l -> Set.unionMany (List.map (fun (x:Term<'T>) -> x.UsedVars) l)
            | Implies(f1, f2) | Iff(f1, f2) -> Set.union f1.UsedVars f2.UsedVars
            | Ite (f1, f2, f3) -> Set.unionMany [f1.UsedVars; f2.UsedVars;f3.UsedVars]
            | Neg f | UMin f -> f.UsedVars
            | Forall(v, f) | Exists(v, f)   -> 
                List.fold (fun s (x, _)-> Set.remove x s) f.UsedVars v
            | Let(bindings, body) -> failwith "Not supported"

    /// Given an assignment to all variables, evaluate the expression
    /// Boolean terms evaluate to 0 or 1
    member private this.EvalInt (A : Map<'T, int64>) = 
        match this with
            | Var s -> A.[s]
            | Const i -> i 
            | Add l -> (List.map (fun (x : Term<'T>) -> x.EvalInt A) l) |> List.sum
            | Sub(t1, t2) -> t1.EvalInt A - t2.EvalInt A
            | Mul l -> (List.map (fun (x : Term<'T>) -> x.EvalInt A) l) |> List.fold (fun s x -> s * x) 1
            | UMin(f) -> - f.EvalInt A
            | True -> 1
            | False -> 0
            | Eq(t1, t2) -> if t1.EvalInt A = t2.EvalInt A then 1 else 0
            | Le(t1, t2) -> if t1.EvalInt A <= t2.EvalInt A then 1 else 0
            | Lt(t1, t2) -> if t1.EvalInt A < t2.EvalInt A then 1 else 0
            | Ge(t1, t2) -> if t1.EvalInt A >= t2.EvalInt A then 1 else 0
            | Gt(t1, t2) -> if t1.EvalInt A > t2.EvalInt A then 1 else 0
            | And l -> if (List.map (fun (x : Term<'T>) -> x.EvalInt A) l) |> List.forall (fun x -> x = 1) then 1 else 0
            | Or l -> if (List.map (fun (x : Term<'T>) -> x.EvalInt A) l) |> List.exists (fun x -> x = 1) then 1 else 0
            | Implies(f1, f2) -> 
                let a1 = f1.EvalInt A
                let a2 = f2.EvalInt A
                if a2 = 1 then 1 else if a1 = 0 then 1 else 0
            | Iff(f1, f2) -> 
                let a1 = f1.EvalInt A
                let a2 = f2.EvalInt A
                if a1 = a2 then 1 else 0
            | Neg(f) -> 
                let a = f.EvalInt A
                if a = 1 then 0 else 1
            | Ite(f1, f2, f3) -> if f1.EvalInt A = 1 then f2.EvalInt A else f3.EvalInt A
            | Forall(v, f) -> failwith "Not Supprted yet"
            | Exists(v, f) -> failwith "Not Supprted yet"
            | Let _ -> failwith "Not Supprted yet"

    /// Evaluate this term as if its is a boolean term, i.e., assume it evaluates to 0 or 1
    member this.Eval (A : Map<'T, int64>) : bool = 
        if (this.EvalInt A) = 0 then 
            false 
        else 
            true

    /// Replaces all vars by the result of applying a function, i.e., map a function over the term
    member this.ReplaceVars (m : 'T -> 'a) = 
        match this with
            | Var s -> Var (m s)
            | Const i -> Const i
            | Add l -> Add (List.map (fun (x : Term<'T>) -> x.ReplaceVars m) l)
            | Sub(t1, t2) -> Sub(t1.ReplaceVars m, t2.ReplaceVars m)
            | Mul l -> Mul (List.map (fun (x : Term<'T>) -> x.ReplaceVars m) l)
            | UMin(f) -> UMin(f.ReplaceVars m)
            | True -> True
            | False -> False
            | Eq(t1, t2) -> Eq(t1.ReplaceVars m, t2.ReplaceVars m)
            | Le(t1, t2) -> Le(t1.ReplaceVars m, t2.ReplaceVars m)
            | Lt(t1, t2) -> Lt(t1.ReplaceVars m, t2.ReplaceVars m)
            | Ge(t1, t2) -> Ge(t1.ReplaceVars m, t2.ReplaceVars m)
            | Gt(t1, t2) -> Gt(t1.ReplaceVars m, t2.ReplaceVars m)
            | And l -> And (List.map (fun (x : Term<'T>) -> x.ReplaceVars m) l)
            | Or l -> Or (List.map (fun (x : Term<'T>) -> x.ReplaceVars m) l)
            | Implies(f1, f2) -> Implies(f1.ReplaceVars m, f2.ReplaceVars m)
            | Iff(f1, f2) -> Iff(f1.ReplaceVars m, f2.ReplaceVars m)
            | Neg(f) -> Neg(f.ReplaceVars m)
            | Ite(f1, f2, f3) -> Ite(f1.ReplaceVars m, f2.ReplaceVars m, f3.ReplaceVars m)
            | Forall(v, f) -> Forall(List.map (fun (x, s) -> (m x, s)) v, f.ReplaceVars m)
            | Exists(v, f) -> Exists(List.map (fun (x, s) -> (m x, s)) v, f.ReplaceVars m)
            | Let _ -> failwith ""

    /// Given a term with string variables, computes a string in SMTLIB format
    static member ToString(term : Term<String>)  =
        match term with
            | Var v -> v
            | Const n -> string(n)
            | Add l ->
                let m = List.map Term<_>.ToString l
                List.fold (fun s x -> s + " " + x) "(+" m + ")"
            | Sub (t1, t2) ->    
                let e1 = Term<_>.ToString t1
                let e2 = Term<_>.ToString t2
                "(- " + e1 + " " + e2 + ")"
            | Mul l ->
                let m = List.map Term<_>.ToString l
                List.fold (fun s x -> s + " " + x) "(*" m + ")"
            | UMin f ->   
                let e = Term<_>.ToString f
                "(- 0 " + e + ")"
            | True -> "true"
            | False -> "false"
            | Eq (t1, t2) ->    
                let e1 = Term<_>.ToString t1
                let e2 = Term<_>.ToString t2
                "(= " + e1 + " " + e2 + ")"
            | Le (t1, t2) ->
                let e1 = Term<_>.ToString t1
                let e2 = Term<_>.ToString t2
                "(<= " + e1 + " " + e2 + ")"
            | Lt (t1, t2) ->
                let e1 = Term<_>.ToString t1
                let e2 = Term<_>.ToString t2
                "(< " + e1 + " " + e2 + ")"
            | Ge (t1, t2) ->
                let e1 = Term<_>.ToString t1
                let e2 = Term<_>.ToString t2
                "(>= " + e1 + " " + e2 + ")"
            | Gt (t1, t2) ->
                let e1 = Term<_>.ToString t1
                let e2 = Term<_>.ToString t2
                "(> " + e1 + " " + e2 + ")"
            | And l ->   
                let m = List.map  Term<_>.ToString l
                match m with
                    | [] -> "true"
                    | [x] -> x
                    | _ -> List.fold (fun s x -> s + " " + x) "(and" m + ")"
            | Or l ->   
                let m = List.map  Term<_>.ToString l
                match m with
                    | [] -> "false"
                    | [x] -> x
                    | _ -> List.fold (fun s x -> s + " " + x) "(or" m + ")"
            | Implies (f1, f2) ->   
                let e1 = Term<_>.ToString f1
                let e2 = Term<_>.ToString f2
                "(=> " + e1 + " " + e2 + ")"
            | Iff (f1, f2) ->   
                let e1 = Term<_>.ToString f1
                let e2 = Term<_>.ToString f2
                "(<=> " + e1 + " " + e2 + ")"
            | Neg f ->   
                let e = Term<_>.ToString f
                "(not " + e + ")"
            | Ite (f1, f2, f3) ->   
                let e1 = Term<_>.ToString f1
                let e2 = Term<_>.ToString f2
                let e3 = Term<_>.ToString f3
                "(ite " + e1 + " " + e2 + " " + e3 + ")"
            | Forall (v, b) -> 
                let args = List.fold (fun a (v, s : VarType) -> a + " (" + string(v) + " " + s.AsString + ")") "" v
                let bs = Term<_>.ToString b
                "(forall (" + args + ")" + bs + ")"
            | Exists (v, b) -> 
                let args = List.fold (fun a (v, s : VarType) -> a + " (" + string(v) + " " + s.AsString + ")") "" v
                let bs = Term<_>.ToString b
                "(exists (" + args + ")" + bs + ")"
            | Let _ -> failwith "Not supported"


/// Expressions can be seen as a subtype of terms that only define arithmetic expressions.
/// They are used to simpfy the definition of a STS to allow for direct variable updates
type Expression<'T when 'T : comparison> =
    | EVar of 'T
    | EConst of int64
    | EAdd of list<Expression<'T>>
    | ESub of Expression<'T> * Expression<'T>
    | EMul of list<Expression<'T>>
    | EUMin of Expression<'T>
    | ENondet

    /// Convert this expression to a term
    member this.ToTerm =
        match this with 
            | EVar x -> Term.Var x
            | EConst c -> Term.Const c
            | EAdd l -> Term.Add (List.map (fun (x : Expression<'T>) -> x.ToTerm) l)
            | ESub(e1, e2) -> Term.Sub(e1.ToTerm, e2.ToTerm)
            | EMul l -> Term.Mul (List.map (fun (x : Expression<'T>) -> x.ToTerm) l)
            | EUMin e -> Term.UMin e.ToTerm
            | ENondet -> failwith "Not supported"

    /// Return all variables used in this expression
    member this.UsedVars =
        match this with 
            | EVar x -> Set.singleton x
            | EConst _ -> Set.empty
            | EAdd l | EMul l -> Set.unionMany (List.map (fun (x:Expression<'T>) -> x.UsedVars) l)
            | ESub(e1, e2) -> Set.union e1.UsedVars e2.UsedVars
            | EUMin e -> e.UsedVars
            | ENondet -> Set.empty

    /// Evaluate this expression given a variable assignment
    member this.Eval (A : Map<'T, int64>) = 
        match this with 
            | EVar x -> A.[x]
            | EConst c -> c
            | EAdd l -> (List.map (fun (x : Expression<'T>) -> x.Eval A) l) |> List.sum
            | ESub(e1, e2) -> e1.Eval A - e2.Eval A
            | EMul l -> (List.map (fun (x : Expression<'T>) -> x.Eval A) l) |> List.fold (fun s x -> x * s) 1
            | EUMin e -> - e.Eval A 
            | ENondet -> failwith "Not supported"

    /// Replaces the variables in this expression, i.e., map a function over the expression
    member this.ReplaceVars (m : 'T -> 'a) = 
        match this with
            | EVar s -> EVar (m s)
            | EConst i -> EConst i
            | EAdd l -> EAdd (List.map (fun (x : Expression<'T>) -> x.ReplaceVars m) l)
            | ESub(t1, t2) -> ESub(t1.ReplaceVars m, t2.ReplaceVars m)
            | EMul l -> EMul (List.map (fun (x : Expression<'T>) -> x.ReplaceVars m) l)
            | EUMin(f) -> EUMin(f.ReplaceVars m)
            | ENondet -> ENondet

/// A model for a term, i.e., a mapping of variables to integers.
/// We generate models of abstract states to allow for cheaper successor state computation.
type Model<'T when 'T : comparison> =
    {
        Assignments : Map<'T, int64>
    }
    
    member this.Vars = 
        this.Assignments.Keys |> seq
