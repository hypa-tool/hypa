module SuccessorHelper

open System
open System.Collections.Generic

open Term
open Abstraction
open TransitionSystem

/// Given a transition compute a formula (over String * int * PrePost) that represents this transition on a given copy i
/// This includes its guards and the updates performed by the transition 
let encodeTransitionStep (vars : VarManager<String>) (transition : GuardedUpdate) i : Term<String * int * PrePost> =
    let clauses = new List<Term<String * int * PrePost>>()
    for var in vars.Vars do 
        if transition.NonDetVars.Contains var |> not then 
            // Compute the right hand side of the update, i.e., either the expression or the variable (if the value is unchanged)
            let e = 
                if transition.Assignments.ContainsKey var then 
                    transition.Assignments.[var]
                else    
                    // If not referred to in the update the variable is unchanged
                    Expression.EVar var

            let left = Term.Var (var, i, POST)
            let right = e.ToTerm.ReplaceVars(fun n -> (n, i, PRE))
            let eq = Term.Eq(left, right)
            clauses.Add eq
        else 
            // For values that will be chosen non-deterministically we do nothing
            ()

    // Add the guard clause
    let guardClause = transition.Guard.ReplaceVars (fun n -> (n, i, PRE))

    // If it exists, add the additional condition of the guard 
    let updateClause = 
        transition.AdditionalCondition
        |> Option.map (fun x -> 
            x.ReplaceVars(fun (n, m) -> (n, i, m))
            )
    
    let t = if updateClause.IsSome then updateClause.Value :: guardClause::(Seq.toList clauses) else guardClause::(Seq.toList clauses)
    Term.And t


/// For a given copy i, encodes that all variables remain unchanged
let encodeTransitionStepStay (vars : list<VarManager<String>>) i =
    vars.[i].Vars
    |> Set.toList
    |> List.map (fun v -> Term.Eq(Var (v, i, PRE), Var (v, i, POST)))
    |> Term.And

/// Given a partial map from copies to transitions encode the update for those included and encode that those not included stay
let encodePartialStepViaMap (vars : list<VarManager<String>>) (transitions : Map<int, GuardedUpdate>) =
    let mutable clauses = []
    for i in 0..vars.Length-1 do
        if Map.containsKey i transitions then
            let transition = transitions.[i]
            // This copy makes a step
            let c = encodeTransitionStep vars.[i] transition i 
            clauses <- c::clauses
        else
            // This copy stays
            let c = encodeTransitionStepStay vars i
            clauses <- c :: clauses
    
    Term.And clauses


/// Given a set of variables compute all variables that might impact through a given transition map
let relevantPreVars (transistions : Map<int, GuardedUpdate>) (vars : Set<RelVar>) : Set<RelVar> = 
    let preVars = new HashSet<_>()
    for (n, i) in vars do 
        if transistions.ContainsKey i then 
            transistions.[i].ComputeImpactingVars n 
            |> Set.iter (fun x -> preVars.Add (x, i) |> ignore)
        else 
            preVars.Add (n, i) |> ignore

    preVars |> set

// #####################################################################################################################
// Types for Computation 


// We handle each computation step (e.g., checking if an abstract state is empty) by a type that includes an abstract member.
// This allows multiple definitions of a computation to be completely interchangeable (think of the abstract types as interfaces)

/// A function that supports sat checks and model generation in abstract states
type StateSatComputer = 
    /// Check if a given abstract state is satisfiable
    abstract member CheckSat : list<Term<RelVar>> ->  list<bool> -> bool

    /// Checks if a given abstract state is satisfiable (given the predicate map)
    abstract member CheckSatMap : PredicateMap ->  AbstractState -> bool

    /// Get models of a given abstract state
    abstract member GetModel : list<Term<RelVar>> ->  list<bool> -> Set<RelVar> -> option<list<Model<RelVar>>>

    /// Tries to compute models for an abstract state where an additional set of formulas holds, i.e., where the abstract stat is restrcited further
    abstract member GetModelGuarded : list<Term<RelVar>> ->  list<bool> -> list<Term<RelVar>> -> Set<RelVar> -> option<list<Model<RelVar>>>

/// The result when checking an implication p -> q form formulas p and q
type ImplicationStatus = POS | NEG | NEITHER

/// Compute implications between formulas
type ImplicationComputer =
    /// Given a partial update map and an abstract state, check if a given predicate is positively or negative implied after the transition
    abstract member TestImplicationOnStep : Map<int, GuardedUpdate> -> list<Term<RelVar>> -> list<bool> -> Term<RelVar> -> ImplicationStatus
    
    /// Given an abstract state, check if a given predicate is positively or negative implied in this state
    abstract member TestImplication : list<Term<RelVar>> -> list<bool> -> Term<RelVar> -> ImplicationStatus
  
/// Compute if in a given abstract state a guard can be satsified
type GuardSatComputer = 
    abstract member CanGuardsBeSat :  list<Term<RelVar>> -> list<bool> -> Map<int, Term<SingleVar>> -> bool

/// Given an abstract state and a set of copies that move, compute the set of abstract successors.
/// This is the main type used to construct the abstract system. Internally it uses the computation types given above
type SucComputer = 
    abstract member ComputeSuc: PredicateMap -> AbstractState ->  Set<int> -> seq<AbstractState>
