module Automaton

open System.Collections.Generic

open Term
open TransitionSystem

open GraphUtil

// In our setting an automaton state is just a number
type AutomatonState = int

/// An automaton edge consist of a guard (a formula) and a target state
type AutomatonEdge = {
    Guard : Term<RelVar>;
    TargetState : AutomatonState;
}

/// A non-deterministic safety automaton 
/// In particular the edges can be non-deterministic, i.e., there can be multiple edges whose guard is satisfied by the same assignment
type NSA =
    {
        Vars : VarManager<RelVar>;
        States : Set<AutomatonState>;
        InitialStates : Set<AutomatonState>;
        BadStates : Set<AutomatonState>;
        Edges : Map<AutomatonState,Set<AutomatonEdge>>; 
    }

/// A deterministic safety automaton 
/// The edges maps each pair of states to a guard
/// For each state, exactly one outgoing edge is satisfied by any given model
type DSA =
    {
        Vars : VarManager<RelVar>;
        States : Set<AutomatonState>;
        InitialState : AutomatonState;
        BadStates : Set<AutomatonState>;
        SafeStates : Set<AutomatonState>; // Once a good state is reached, nothing bad can happen
        Edges : Map<AutomatonState, Map<AutomatonState, Term<RelVar>>>;// Assume to be determines. This needs to be ensured by the constructor
    }

    /// Checks if the automaton is consistent, i.e., states includes all states and each edge guard uses vars in Vars
    member this.IsConsitent =  
        let statesC = (Set.isSubset this.BadStates this.States) && (Set.isSubset this.SafeStates this.States)

        let edgesC = 
            (this.Edges
            |> Map.keys
            |> Seq.forall (fun x -> this.States.Contains x))
            &&
            (this.Edges
            |> Map.toSeq
            |> Seq.map (fun (_, x) -> Map.keys x |> set)
            |> Set.unionMany
            |> Set.forall (fun x -> this.States.Contains x))

        let updateC = 
            this.Edges
            |> Map.toSeq
            |> Seq.map (fun (_, x) -> Map.values x |> set)
            |> Set.unionMany
            |> Set.forall (fun x -> Set.isSubset x.FreeVars this.Vars.Vars)

        statesC && edgesC && updateC

/// A \forall^*\exists^* specification. It consist of the automaton matrix as a DSA and the quantifier structure given as pair (k, l) which defines the \forall^k\exists^l quantifier prefix. 
type Specification = 
    {
        Automaton : DSA;
        QuantifierStructure : int * int;
    }

/// Convert a NSA to a DSA 
let convertToDSA (A : NSA) = 

    let mutable currentId = 0
    let idMap = new Dictionary<Set<AutomatonState>, int>()


    idMap.Add (A.InitialStates, currentId)
    currentId <- currentId + 1

    // The DSA uses sets of NSA states of the DSA as states. We begin construction with the set of initial states of the NSA
    let queue = new Queue<Set<AutomatonState>>()
    queue.Enqueue A.InitialStates

    let mutable badStates = Set.empty

    let edgeMap = new Dictionary<AutomatonState, Dictionary<AutomatonState, Term<RelVar>>>()

    while queue.Count <> 0 do 
        let ps = queue.Dequeue()
        let psid = idMap.[ps]

        // A state is bad if any of its NSA states are bad
        if Set.count  (Set.intersect ps A.BadStates) <> 0 then 
            badStates <- badStates.Add psid

        // We collect all edges leaving any state in s
        let allGuards = new HashSet<Term<RelVar>>()
        for s in ps do 
            if Map.containsKey s A.Edges then 
                for e in A.Edges.[s] do 
                    allGuards.Add e.Guard |> ignore

        let allGuardsAsList = 
            allGuards 
            |> Seq.toList

        // We want to ensure that at most one edge can be taken at any time (to ensure that the automaton is deterministic)

        // A dict to collect the new outgoing edges from DSA state s
        let newEdges  = new Dictionary<AutomatonState, Term<RelVar>>()

        // We iterate over every possible combination of edges that can be taken at any given time
        for comb in Util.computeBooleanPowerSet (List.length allGuardsAsList) do
            
            // The combined guard is the conjunction of each of the edges
            let combinedGuard = 
                List.zip comb allGuardsAsList 
                |> List.map (fun (b, x) -> if b then x else Term.Neg x)
                |> Term.And

            // Check if this conjunction is sat, otherwise we do not need to add it to the automaton
            if SMTUtil.isSat combinedGuard (fun (n, i) -> n + "_" + string(i)) A.Vars.VarType then 
                
                // Compute the successor states for this edge
                let mutable successor_states = Set.empty
                for s in ps do 
                    if Map.containsKey s A.Edges then 
                        for e in A.Edges.[s] do 
                            let guardIndex = List.findIndex (fun x -> x = e.Guard) allGuardsAsList
                            if comb.[guardIndex] then 
                                // The guard is currently set to true
                                successor_states <- successor_states.Add e.TargetState

                // Add the set of states to the automaton (reuse the id if it already exists)
                // Otherwise generate a fresh id for this set
                let id_for_successor_states =
                    if idMap.ContainsKey successor_states then 
                        idMap.[successor_states]
                    else
                        idMap.Add(successor_states, currentId)
                        queue.Enqueue successor_states
                        let tmp = currentId
                        currentId <- currentId + 1
                        tmp

                // Add the move to the state
                if newEdges.ContainsKey id_for_successor_states then 
                    // If there already is an edge to this state we build the disjunction
                    let prev = newEdges.[id_for_successor_states]
                    newEdges.Remove id_for_successor_states |> ignore
                    let newGuard = Term.Or [prev; combinedGuard]
                    newEdges.Add(id_for_successor_states, newGuard)
                else 
                    newEdges.Add(id_for_successor_states, combinedGuard)

        edgeMap.Add(psid, newEdges)


    // The construction of the DSA is finished
    // We now compute all good states, i.e., states from which no bad state can be reached

    let all_states = {0..currentId-1} |> set
    let edges = seq {for s in edgeMap do for t in s.Value do (s.Key, t.Key) } |> Seq.toList
    let g : Graph<AutomatonState> = {Graph.Nodes = all_states; Edges = edges }
    let safe_states = 
        let canReachBad = g.ComputePred badStates |> set
        Set.filter (fun x -> Set.contains x canReachBad |> not) all_states

    let convertedEdgeMap = 
        let dictToMap (d : Dictionary<'a, 'b>) =
            d |> Seq.map (fun x -> (x.Key, x.Value)) |> Map.ofSeq

        edgeMap
        |> dictToMap
        |> Map.map (fun _ x -> dictToMap x)

    let res =
        {
            DSA.Vars = A.Vars;
            States = all_states;
            InitialState = idMap.[A.InitialStates]; // The initial state is, by construction always 0. Putting idMap.[A.InitialStates] here is easier to read
            BadStates = badStates;
            DSA.SafeStates = safe_states;
            Edges = convertedEdgeMap;
        }

    res