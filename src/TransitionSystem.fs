module TransitionSystem

open System
open Term

/// Manages the vars of the system by maintaining the set of vars as the type of each (currently we only use vars of type INT)
type VarManager<'T when 'T: comparison> =
    {
        Vars : Set<'T>;
        VarType : 'T -> VarType
    }

/// Represents a guarded transition of a STS
/// This consists of
/// 1) A guard of this transition
/// 2) A map of variables to update expression (this need not include all variables, i.e., some vars can be left underspecified)
/// 3) A list of vars that are chosen non-deterministically, i.e., the value of these variables can be set to any value (these variables must not overlap with those updated in 2)
/// 4) An additional constraint on this condition that expresses a relation between the pre and post state.
type GuardedUpdate =
    {
        Guard : Term<SingleVar>;
        Assignments : Map<String, Expression<String>>; 
        NonDetVars : Set<String> 
        AdditionalCondition : option<Term<SingleVarPrePost>>;
    }

    /// Returns all vars used in this transition
    member this.Vars = 
        let guardVars = this.Guard.FreeVars
        let assignmentVars = 
            this.Assignments
            |> Map.toSeq
            |> Seq.map (fun (_, e) -> e.UsedVars)
            |> Set.unionMany
        
        let additionalVars = 
            match this.AdditionalCondition with 
                | None -> Set.empty
                | Some x -> 
                    x.FreeVars
                    |> Set.map (fun (n, _) -> n)


        Set.unionMany [guardVars; assignmentVars; additionalVars; this.NonDetVars]

    /// Check if this guard is consistent, i.e., all nonDet vars may not be assigned a update
    member this.IsConsitent = 
        this.NonDetVars
        |> Set.forall (fun x -> this.Assignments.ContainsKey x |> not)

    /// Checks if a given var is left unchanged.
    /// This is the case when it has no update and is not set to non-deterministic
    member this.LeavesVarUnchanged (var : String) = 
        this.Assignments.ContainsKey var |> not && this.NonDetVars.Contains var |> not
        // If AdditionalCondition is used this gets more complicated

    
    /// Returns all vars that impact the variable provided as an argument
    /// In case on an update, this is just the vars used in the update
    /// If the var is left unchanged (i.e., is not updated but also is not chosen non-deterministically) it is only the var itself
    member this.VarsPreimage (s : String) = 
        
        if this.Assignments.ContainsKey s then 
            this.Assignments.[s].UsedVars
        else 
            Set.singleton s
    

    /// Compute all vars that impact a variable. This includes all vars used in the assignment, all vars used in the guard and all vars used in the additional condition
    member this.ComputeImpactingVars (name : String) = 
        let fromAssignment = 
            if Map.containsKey name this.Assignments then 
                this.Assignments.[name].UsedVars
            else
                Set.empty

        let fromGuard = this.Guard.FreeVars

        let fromAdditionalCondition = 
            match this.AdditionalCondition with 
                | None -> Set.empty
                | Some x -> 
                    if x.FreeVars.Contains (name, POST) then 
                        x.FreeVars 
                        |> Set.filter (fun (_, m) -> m = PRE)
                        |> Set.map (fun (n, _) -> n)
                    else    
                        Set.empty

        Set.unionMany [fromAssignment; fromAdditionalCondition; fromGuard]


 /// Represents a STS, the basic model used by HyPA
 /// This includes
 /// 1) the varaibles of this model
 /// 2) the set of control location
 /// 3) a partial map from control locations to conditions on the initial state
 /// 4) a mapping from locations to outgoing transitions
 /// 5)  a partial map from control locations to conditions that specifies the points at which the program is observed
type TransitionSystem =
    {
        Vars : VarManager<SingleVar>;
        Locations : Set<int>;
        Init : Map<int, Term<SingleVar>>;
        Step: Map<int, Set<int * GuardedUpdate>>;
        Observation : Map<int, Term<SingleVar>>;
    }

    /// Checks if the STS is consistent. This includes
    /// 1) All used vars in the program occur in the variable manager
    /// 2) All states appearing in the initial condition also appear in the locations
    /// 3) All states appearing in the observations also appear in the locations
    /// 4) All states in domain and codomain of step are valid locations, i.e., appear in the set of all locations
    /// 5) ALl guarded updates are consistent
    member this.IsConsitent = 
        let initVars = 
            this.Init
            |> Map.toSeq
            |> Seq.map (fun (_, f) -> f.FreeVars)
            |> Set.unionMany

        let obsVars = 
            this.Observation
            |> Map.toSeq
            |> Seq.map (fun (_, f) -> f.FreeVars)
            |> Set.unionMany

        let stepVars = 
            this.Step
            |> Map.toSeq
            |> Seq.map (fun (_, sucs) -> 
                sucs 
                |> Set.map (fun (_, f) -> f.Vars)
                |> Set.unionMany
                )
            |> Set.unionMany

        let usedVars = Set.unionMany [initVars; obsVars; stepVars]

        let varsC = Set.isSubset usedVars this.Vars.Vars

        let initC = 
            this.Init
            |> Map.keys
            |> Seq.forall (fun x -> Set.contains x this.Locations)

        let obsC = 
            this.Observation
            |> Map.keys
            |> Seq.forall (fun x -> Set.contains x this.Locations)

        let stepC = 
            (this.Step
            |> Map.keys
            |> Seq.forall (fun x -> Set.contains x this.Locations))
            &&
            (this.Step
            |> Map.toSeq
            |> Seq.map (fun (_, x) -> Set.map fst x) 
            |> Set.unionMany
            |> Set.forall (fun x -> Set.contains x this.Locations))

        let updateC = 
            this.Step
            |> Map.toSeq
            |> Seq.map (fun (_, x) -> Set.map snd x) 
            |> Set.unionMany
            |> Set.forall (fun x -> x.IsConsitent)

        varsC && initC && obsC && stepC && updateC

