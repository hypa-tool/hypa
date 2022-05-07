module KSafetyGameConstructor

open System.Collections.Generic

open Automaton
open ReductionGraph
open SafetyGame

/// A game state corresponds directly to the nodes in the game constructed for k-safety
type GameState =
    | Regular of ReductionGraphNode 
    | SchedChoice of ReductionGraphNode * Set<int>
    | Initial of Set<ReductionGraphNode>


    member this.AutomatonState =
        match this with
            | Regular s | SchedChoice (s, _) -> s.AutomatonState
            | _ -> failwith "Should never happen"

/// Given the reduction graph (and the automaton used in the reduction graph), construct the game used in the simpled case of k-safety
let constructGameFromReductionGraph (r : ReductionGraph) (A : DSA) = 
    let nodes = new HashSet<_>()

    let sucessorMap = new Dictionary<_,_>()

    // For each node we add a regular node and the schelduing nodes for all valid schedulisng (as given in r)
    for rgn in r.Nodes do 
        let node = Regular rgn

        nodes.Add node |> ignore 

        let sucsForNode = new HashSet<_>()

        sucessorMap.Add(node, sucsForNode)

        for e in r.Edges.[rgn] do 
            let nodeChoice = SchedChoice(rgn, e.Key)
            nodes.Add nodeChoice |> ignore 
            sucsForNode.Add nodeChoice |> ignore 

            let sucForNodeChoice = new HashSet<_>()
            sucessorMap.Add(nodeChoice, sucForNodeChoice)

            for rgn' in e.Value do 
                sucForNodeChoice.Add (Regular rgn') |> ignore
                // Adding it to nodes will be done on the outer level

    // A state is bad if its automaton state is bad
    let badStates = new HashSet<_>()
    for s in nodes do 
        if Set.contains s.AutomatonState A.BadStates then 
            badStates.Add s |> ignore

    let safeStates = new HashSet<_>()
    for s in nodes do 
        if Set.contains s.AutomatonState A.SafeStates then 
            safeStates.Add s |> ignore

    let initState = Initial (r.InitialNodes |> set)
    nodes.Add initState |> ignore
    // Add all successors of the initial node
    sucessorMap.Add(initState, new HashSet<_>(r.InitialNodes |> set |> Set.map Regular))

    let controllingPlayer = new Dictionary<_,_>()
    for s in nodes do 
        let p = 
            match s with 
                | Regular _ -> SAFE
                | SchedChoice _ | Initial _ -> REACH
        controllingPlayer.Add(s, p)

    let reward = new Dictionary<_,_>()
    for s in nodes do 
        let r = 
            match s with 
                | SchedChoice(_, sched) -> 0
                | Regular _ | Initial _ -> 0
        reward.Add(s, r)

    let sg =    
        {
            SafetyGame.States = nodes;
            InitialState = initState;
            BadStates = badStates; 
            SafeStates = safeStates;
            ControllingPlayer = controllingPlayer;
            Reward = reward;
            Sucessors = sucessorMap;
        }

    sg