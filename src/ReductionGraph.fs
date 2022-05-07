module ReductionGraph

open System.IO
open System.Collections.Generic

open Term
open Abstraction
open Automaton
open TransitionSystem
open DNF

// A reduction graph represents the most basic abstraction computed using PA that is parametrized by a scheduling in each step. 
// This representation is then used to compute the games for the hyperproperty verification

/// A node in the reduction graph
type ReductionGraphNode = 
    {
        AbstractState : AbstractState;
        HasMovedSince : list<bool>;
        AutomatonState : int;
    }

    /// Compute a HTML representation of this node to be used in a DOT graph
    member this.AsHTML() = 
        let s = new StringWriter()
        s.Write (sprintf "%A" this.AbstractState.Locations + "<BR/>")
        s.Write (sprintf "%A" this.AbstractState.PredicatesSat + "<BR/>")
        //s.Write (sprintf "%A" this.HasMovedSince + "<BR/>")
        s.Write (sprintf "%i" this.AutomatonState )

        s.ToString()

    /// Compute a pure text representation
    member this.AsNonHTML() = 
        let s = new StringWriter()
        s.Write (sprintf "%A" this.AbstractState.Locations + " | ")
        s.Write (sprintf "%A" this.AbstractState.PredicatesSat + "| ")
        //s.Write (sprintf "%A" this.HasMovedSince + "<BR/>")
        s.Write (sprintf "%i" this.AutomatonState )

        s.ToString()


type Scheduling = Set<int>

/// The actual reduction graph 
type ReductionGraph =   
    {
        Nodes : HashSet<ReductionGraphNode>;
        InitialNodes : HashSet<ReductionGraphNode>;
        Edges : Dictionary<ReductionGraphNode, Dictionary<Scheduling, HashSet<ReductionGraphNode>>>;
    }



let swInit = System.Diagnostics.Stopwatch()
let swObservations = System.Diagnostics.Stopwatch()
let swAutomaton = System.Diagnostics.Stopwatch()
let swTransition = System.Diagnostics.Stopwatch()

let initalStateDNFHasher = Dictionary<array<int>, DNF>()

/// A container that lists all the hashing computer currently used
type HashingContainer =
    {
        SatHasher : SuccessorHelper.StateSatComputer;
        GuardSatComputer : SuccessorHelper.GuardSatComputer;
        SucComputer : SuccessorHelper.SucComputer;
        InitalStateDNFHasher : Dictionary<array<int>, DNF>;
        ObservationStateDNFHasher : Dictionary<array<int> * int, DNF>;
        AutomatonAlphabetDNFHasher : Dictionary<list<Term<RelVar>> * Term<RelVar>, DNF>;
    }

/// Construct the reduction graph from the STSs, DSA, and given predicates
let constructReductionGraph (tlist : list<TransitionSystem>) (predMap : PredicateMap) (A : DSA) (hashed : HashingContainer) =

    // =========================================== Compute Initial States ===========================================
    swInit.Start()
    let allAbstractInitialStates = new HashSet<AbstractState>()

    // Compute all possible start locations
    let possibleStartLocations =
        tlist
        |> List.map (fun t -> t.Init |> Map.toSeq |> Seq.map fst |> set)
        |> Util.cartesian
        |> List.map List.toArray

    for locs in possibleStartLocations do
        let preds = predMap.[locs]

        // Compute a DNF that characterises the initial states starting at loc
        let dnf =
            if hashed.InitalStateDNFHasher.ContainsKey locs then
                hashed.InitalStateDNFHasher.[locs]
            else
                let initFormulaConjunction : Term<RelVar> =
                    locs
                    |> Array.toList
                    |> List.mapi (fun i x -> tlist.[i].Init.[x].ReplaceVars(fun y -> y, i))
                    |> Term.And

                let dnf = 
                    match BooleanClosure.computeDNF preds.PredList initFormulaConjunction with
                    | None -> 
                        // We assume that the predicates are precise enough to capture the initial states, so raise an error
                        failwith ("The provided prediactes are not precise enough to capture the initial states at location "  + string(locs))
                    | Some phi -> phi

                hashed.InitalStateDNFHasher.Add(locs, dnf)
                dnf

        // After having computed the DNF we can now identify all abstract initial states (all models of the DNF)
        // Using a DNF here is efficient as many times the same initial condition is shared on multiple initial locations
        for predSat in Util.computeBooleanPowerSet (List.length preds.PredList) do
            if dnf.IsSat predSat then 
                // We check if the abstract state is also satisfiable, and, if so, add it to the set of initial states
                if hashed.SatHasher.CheckSat preds.PredList predSat then
                    let astate = {AbstractState.Locations = locs; PredicatesSat = predSat}
                    allAbstractInitialStates.Add astate |> ignore

    swInit.Stop()
    // =========================================== Compute Initial States - END ===========================================


    // =========================================== Compute Transitions ===========================================
    
    
    let queue = new Queue<ReductionGraphNode>() 
    let allNodes = new HashSet<ReductionGraphNode>()
    let initialNodes = new HashSet<ReductionGraphNode>()
    let edges = new Dictionary<ReductionGraphNode,Dictionary<Scheduling,HashSet<ReductionGraphNode>>>()


    // Add all initial states with the initial automaton state to the queue and as initialNodes
    for s in allAbstractInitialStates do 
        let a = {ReductionGraphNode.AbstractState = s; AutomatonState = A.InitialState; HasMovedSince = List.map (fun _ -> true) tlist}
        queue.Enqueue a
        allNodes.Add a |> ignore
        initialNodes.Add a |> ignore
    
    while queue.Count <> 0 do 
        let node = queue.Dequeue()

        if Set.contains node.AutomatonState A.SafeStates || Set.contains node.AutomatonState A.BadStates then 
            // This automaton state is a safe or bad state, we do not explore it further
            // In case of bad state a violation is caused either way and in case of a good state (by definition) no bad automaton state can be reached
            edges.Add(node, new Dictionary<_,_>())
        else 
            // =================== Compute all Valid Schedulings from this node ==================== 
            // Compute the observation points per copy 

            let locs = node.AbstractState.Locations
            let preds = predMap.[locs]

            // List that records which of the copies has already finished

            swObservations.Start()
            let hasReachedObsPoint = 
                [
                    for i, tl in List.indexed tlist do 
                        if tl.Observation.ContainsKey locs.[i] then 
                            let guard = tl.Observation.[locs.[i]] // The guard of the observation

                            // Compute a DNF that encodes all predicates that fulfill the observation guard. If possible hash this result to avoid recomputation
                            let dnf =
                                if hashed.ObservationStateDNFHasher.ContainsKey (locs, i) then
                                    hashed.ObservationStateDNFHasher.[locs, i]
                                else
                                    // Need to compute 
                                    let dnf = 
                                        match BooleanClosure.computeDNF preds.PredList (guard.ReplaceVars (fun n -> n, i)) with
                                            | None -> 
                                                // We assume that the 
                                                failwith ("The provided prediactes are not precise enough to capture the observation at location " + string(locs))
                                            | Some x -> x

                                    hashed.ObservationStateDNFHasher.Add((locs, i), dnf)
                                    dnf

                            dnf.IsSat node.AbstractState.PredicatesSat
                        else 
                            // This copy has not reached an observation point
                            false
                ]
            swObservations.Stop()
            // =================== END - Compute all Valid Schelduings from this node ==================== 


            if List.forall id hasReachedObsPoint && List.forall id node.HasMovedSince then
                // All copies have moved since the last transition and all copies have reached an observation point -> the automaton progresses

                // ================= Compute Automaton Sucessor via DNF computation
                // Find the unique automaton state
                swAutomaton.Start()
                let nextAutomatonState = 
                    A.Edges.[node.AutomatonState]
                    |> Seq.find (fun edge -> 

                        let formula = edge.Value

                        // Find a DNF for this formula (possibly hashed)
                        let dnf = 
                            if hashed.AutomatonAlphabetDNFHasher.ContainsKey(preds.PredList, formula) then 
                                hashed.AutomatonAlphabetDNFHasher.[(preds.PredList, formula)]
                            else 
                                let dnf = 
                                    match BooleanClosure.computeDNF preds.PredList formula with 
                                        | None ->   
                                            printfn "Predicate not precise enough for automaton step at loc %A. To find :\n %A \n in %A" locs A.Edges.[node.AutomatonState] preds.PredList
                                            failwith ""
                                        | Some x -> x 

                                hashed.AutomatonAlphabetDNFHasher.Add((preds.PredList, formula), dnf)
                                dnf
                        dnf.IsSat node.AbstractState.PredicatesSat             
                    )
                    |> fun x -> x.Key
                swAutomaton.Stop()
                // ================= 

                // As we reached a synch point, all schedulings are possible
                let possibleSchedluer = 
                    seq {0..List.length tlist - 1}
                    |> set
                    |> Util.computePowerSet
                    |> Seq.filter (Set.isEmpty >> not)


                let edgesForNode = new Dictionary<Scheduling,HashSet<ReductionGraphNode>>()
                for sched in possibleSchedluer do 
                    // reset the has move vector for all copies
                    let newHasMovedSince = 
                        node.HasMovedSince
                        |> List.map (fun _ -> false)

                    swTransition.Start()
                    let allSucs = 
                        hashed.SucComputer.ComputeSuc predMap node.AbstractState sched
                        |> Seq.map (fun x -> {ReductionGraphNode.AbstractState = x; AutomatonState = nextAutomatonState; HasMovedSince = newHasMovedSince}) // The automaton state remains unchanged
                    swTransition.Stop()

                    edgesForNode.Add(sched, new HashSet<_>(allSucs))

                    // Insert in the queue to be extended next
                    for n in allSucs do 
                        if allNodes.Contains n |> not then 
                            allNodes.Add n |> ignore 
                            queue.Enqueue n


                edges.Add(node, edgesForNode)
            else
                // Some copies have not moved yet, compute all schedulings for which this is the case

                // All copies that need to move
                let needsToMove = 
                    List.zip hasReachedObsPoint node.HasMovedSince
                    |> List.indexed
                    |> List.filter (fun (_, (obs, hasMoved)) -> (not hasMoved) || (not obs))
                    |> List.map fst 
                    |> set

                let possibleSchedluer = 
                    Util.computePowerSet needsToMove
                    |> Seq.filter (Set.isEmpty >> not)

                let edgesForNode = new Dictionary<Scheduling,HashSet<ReductionGraphNode>>()

                for sched in possibleSchedluer do 
                    // The new HasMovedSinceVector
                    let newHasMovedSince = 
                        node.HasMovedSince
                        |> List.mapi (fun i x -> if Set.contains i sched then true else x)

                    swTransition.Start()
                    let allSucs = 
                        hashed.SucComputer.ComputeSuc predMap node.AbstractState sched
                        |> Seq.map (fun x -> {ReductionGraphNode.AbstractState = x; AutomatonState = node.AutomatonState; HasMovedSince = newHasMovedSince}) // The automaton state remains unchanged
                    swTransition.Stop()
                    
                    edgesForNode.Add(sched, new HashSet<_>(allSucs))

                    // Insert in the queue to be extended next
                    for n in allSucs do 
                        if allNodes.Contains n |> not then 
                            allNodes.Add n |> ignore 
                            queue.Enqueue n

                edges.Add(node, edgesForNode)

    let res = 
        {
            ReductionGraph.Nodes = allNodes;
            InitialNodes = initialNodes;
            Edges = edges;
        }
    
    res

