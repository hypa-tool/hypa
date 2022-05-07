module SuccessorComputation

open System
open System.Collections.Generic

open Term
open TransitionSystem
open Abstraction
open SuccessorHelper


let swtotal0 = System.Diagnostics.Stopwatch()
let swtotal1 = System.Diagnostics.Stopwatch()
let swtotal2 = System.Diagnostics.Stopwatch()
let swtotal3 = System.Diagnostics.Stopwatch()
let swtotalg = System.Diagnostics.Stopwatch()


/// Checks if for a source abstract state and a target abstract state and a partial transitions map there exists an abstract edge. This always creates an SMT query
let private isValidAbstractEdge (vars : list<VarManager<String>>)  (predsSource : list<Term<RelVar>>) (predsTarget : list<Term<RelVar>>) (sSource : list<bool>) (sTarget : list<bool>) (transitions : Map<int, GuardedUpdate>) =
    let pre = 
        SMTUtil.encodeAbstractStateSatisfaction predsSource sSource
        |> fun x -> x.ReplaceVars (fun (n, i) -> n, i, PRE)

    let post = 
        SMTUtil.encodeAbstractStateSatisfaction predsTarget sTarget
        |> fun x -> x.ReplaceVars (fun (n, i) -> n, i, POST)

    let moveTerm = SuccessorHelper.encodePartialStepViaMap vars transitions

    let query = Term.And [pre; moveTerm; post]

    let varStringer (n, i : int, m : PrePost) = 
        n + "_" + string(i) + "_" + string(m)

    SMTUtil.isSat query varStringer (fun (n, i, _) -> vars.[i].VarType n)

type SucComputerDirect(tslist : list<TransitionSystem>, satComputer : StateSatComputer, guardSatComputer : GuardSatComputer, implicationCompute : ImplicationComputer) =

    let vars = 
        tslist
        |> List.map (fun x -> x.Vars)

    let hashed = new Dictionary<_,_>()

    let totalHashed = new Dictionary<_,_>()

    /// Given a source abstract state, transitions, and target predicates, compute all abstract states that can be reached
    let computeSucPredicatesDirect (transitions : Map<int, GuardedUpdate>) (sourcePreds : list<Term<RelVar>>) (s : list<bool>) (targetPreds : list<Term<RelVar>>) : seq<list<bool>> =
        let r =
            if hashed.ContainsKey transitions then
                hashed.[transitions]
            else
                let newDict = new Dictionary<_,_>()
                hashed.Add(transitions, newDict)
                newDict

        if r.ContainsKey (sourcePreds, s, targetPreds) then 
            r.[(sourcePreds, s, targetPreds)]
        else
            swtotal3.Start()
            let postivePreds = new HashSet<_>()
            let negativePreds = new HashSet<_>()

            // For each of the target predicates we compute if they are already implied (positively or negatively) as we do not need to consider those 
            for i in 0..targetPreds.Length - 1 do
                let p = targetPreds.[i]

                // Check implication on that predicate
                let res = implicationCompute.TestImplicationOnStep transitions sourcePreds s p 
                match res with
                    | POS -> 
                        postivePreds.Add i |> ignore
                    | NEG -> 
                        negativePreds.Add i |> ignore
                    | NEITHER -> ()

            // Now we determine if the use of models will be of any help
            // We check if we can push a model in PRE to a model over POST that is sufficient to evaluate all target Predicates
            // If additional conditions are used in the transition system, we may not be able to push a model as the update is not determintic 
            // If it is, we can use model to seep things up. If not we need to resort on SMT solving instead
            let canWePushAllVars = 
                targetPreds
                |> List.map (fun x -> x.FreeVars)
                |> Set.unionMany
                |> Set.exists (fun (n, i) -> 
                    if transitions.ContainsKey i then 
                        if transitions.[i].NonDetVars.Contains n then 
                            // The var is chosen non-deterministically, so no push through possible. We negate once at the end so return true
                            true
                        else 
                            false
                    else
                        false
                )
                |> not

            
            // Using model generation we can create a set of abstract states that definitely are abstract successors of the source abstract state
            // We collect these abstract states in definiteSucs
            let definiteSucs = 
                if canWePushAllVars |> not then
                    // We can *not* push all vars. So no definite answers possible
                    Set.empty
                else
                    // We can make use of models from the abstract state to evalute apply transitions

                    // Compute those vars that are relevant in the source (PRE) to determine the predicates in the target (POST)
                    let resultingSourceVars = 
                        targetPreds
                        |> List.map (fun x -> x.FreeVars)
                        |> Set.unionMany
                        |> Set.map (fun (n, i) -> 
                            if transitions.ContainsKey i then 
                                transitions.[i].VarsPreimage n 
                                |> Set.map (fun n -> n, i)
                            else
                                Set.singleton (n, i)
                            )
                        |> Set.unionMany


                    // Push a model over the pre vars to the post vars
                    // Due to the prior check we know that this push is possible
                    let pushThrough (m : Map<RelVar,int64>) = 
                        targetPreds
                        |> List.map (fun x -> x.FreeVars)
                        |> Set.unionMany
                        |> Set.map (fun (n, i) -> 
                            (n, i), 
                                if transitions.ContainsKey i && transitions.[i].Assignments.ContainsKey n then 
                                    transitions.[i].Assignments.[n].ReplaceVars (fun n -> n, i)
                                    |> fun x -> x.Eval m
                                else
                                    m.[(n, i)]
                            )
                        |> Map.ofSeq


                    let r = 
                        let guards = 
                            transitions
                            |> Map.toSeq
                            |> Seq.map (fun (i, f) -> f.Guard.ReplaceVars (fun n -> n, i))
                            |> Seq.toList

                        // Compute models for the source abstract state
                        let models = satComputer.GetModelGuarded sourcePreds s guards resultingSourceVars

                        if models.IsNone then 
                            // The current abstract state is unsat. This should never happen as this is enssured by the caller.
                            Set.empty
                        else
                            // Get a model containg all the variable required
                            models
                            |> Option.get
                            |> Seq.toList
                            // Map each model to the vector it lies in by evaluating each predicate in the post-model
                            |> List.map (fun m -> 
                                let pushedMap = pushThrough m.Assignments
                                let res = 
                                    targetPreds
                                    |> List.map (fun p -> p.Eval pushedMap)
                                res
                                )
                            |> set

                    r

                    
            // Generate all possible abstract successor state. 
            // We filter out those where we already know that there is a transition (definiteSucs) and restrict to those where the implication outcomes from before are possible.
            // If we e.g., determine that p1 is implied positively, we only need to consider those states where p1 is set to true.
            let possibleSucs =
                Util.computeBooleanPowerSet (List.length targetPreds)
                |> Seq.filter (fun x -> Seq.forall (fun y -> x.[y]) postivePreds && Seq.forall (fun y -> not x.[y]) negativePreds)
                // Filter out those that we already know
                |> Seq.filter (fun x -> Set.contains x definiteSucs |> not)

            // We can add the definite ones right away
            let sucStates = new HashSet<_>(definiteSucs)

            for s' in possibleSucs do
                // Only iterate over satifisable abstract states
                if satComputer.CheckSat targetPreds s' then
                    // Check via a SMT query if there is an abstract edge
                    if isValidAbstractEdge vars sourcePreds targetPreds s s' transitions then
                        sucStates.Add s' |> ignore

            r.Add((sourcePreds, s, targetPreds), sucStates)
            swtotal3.Stop()
            sucStates
    
    /// One additional level of optimization:
    /// If a predicate is shared between source and target and not effected by transitions we already know its truth value
    let computeSucPredicatesSimpleOpt1 (transitions : Map<int, GuardedUpdate>) (sourcePreds : list<Term<RelVar>>) (s : list<bool>) (targetPreds : list<Term<RelVar>>) : seq<list<bool>> = 
        swtotal2.Start()

        let reusablePreds = 
            List.allPairs (List.indexed targetPreds) (List.indexed sourcePreds)
            // Consider all predicates that occur before and after
            |> List.filter (fun ((_, p), (_, q)) -> p = q)
            // Filter for pairs where all variables are unchanged by the update, i.e., either the copy is not moved or remains unchanged
            |> List.filter (fun ((_, p), (_, _)) -> 
                p.FreeVars
                |> Set.forall (fun (n, i) -> transitions.ContainsKey i |> not || transitions.[i].LeavesVarUnchanged n)
                    )
            |> Seq.map (fun ((i, _), (j, _)) -> i, s.[j])
            |> Seq.toList

        let fixedIndices =
            reusablePreds
            |> Seq.map fst

        let remainingPredicates = 
            targetPreds
            |> List.indexed 
            |> List.filter (fun (i, _) -> Seq.contains i fixedIndices |> not)

        let indices, openPredicates = List.unzip remainingPredicates

        let subRes = 
            computeSucPredicatesDirect transitions sourcePreds s openPredicates
            |> Seq.map (fun x -> List.zip indices x)
            |> Seq.map (fun p ->
                List.append p reusablePreds
                |> List.sortBy fst // Sorting brings again in the correct order
                |> List.map snd
                )
        swtotal2.Stop()
        subRes


    interface SucComputer with 
        member this.ComputeSuc (predMap : PredicateMap) astate (sched : Set<int>) =
           
            let hashing =
                if totalHashed.ContainsKey predMap then
                    totalHashed.[predMap]
                else
                    let newDict = new Dictionary<_,_>()
                    totalHashed.Add(predMap, newDict)
                    newDict

            if hashing.ContainsKey (astate, sched) then
                hashing.[(astate, sched)]
            else
                swtotal0.Start()
                let preds = predMap.[astate.Locations]

                swtotalg.Start()
                let transitionsMap =
                    seq { for i in sched do i, tslist.[i].Step.[astate.Locations.[i]] }
                    |> Map.ofSeq
                    // Compute all combinations of edges for each copy
                    |> Util.cartesianMap 
                    // We filter out those transitions where the guards can not be satisfied. This is done globally (after all moves of all copies are fixed) opposed to locally
                    |> Seq.filter (fun x -> 
                        x 
                        |> Map.map (fun _ (_, t) -> t.Guard)
                        |> guardSatComputer.CanGuardsBeSat preds.PredList astate.PredicatesSat
                    )
                    |> Seq.toList
                    
                swtotalg.Stop()

                let sucs = new HashSet<AbstractState>()

                // Iterate over all combinations of outgoing transitions
                for l in transitionsMap do

                    let nextLocations = Array.copy astate.Locations
                    // Update the location of all moved copies
                    Map.iter (fun i (l, _) -> Array.set nextLocations i l) l 

                    // Extract only the data update (the guarded transitions)
                    let tranistions = Map.map (fun _ (_, f) -> f) l

                    let nextPreds = predMap.[nextLocations]

                    // Compute all abstract states at that location
                    let abstractSucs = computeSucPredicatesSimpleOpt1 tranistions preds.PredList astate.PredicatesSat nextPreds.PredList

                    for bvec in abstractSucs do 
                        sucs.Add{AbstractState.Locations = nextLocations; PredicatesSat = bvec} |> ignore
                
                hashing.Add((astate, sched), sucs)
                swtotal0.Stop()
                sucs