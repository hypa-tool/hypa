module BeyondGameConstructor

open System
open System.IO
open System.Collections.Generic


open Term
open TransitionSystem
open Abstraction
open Automaton
open SuccessorHelper
open SafetyGame
open ReductionGraph

/// Given an abstract state, a scheduling and a set of abstract states (target), determines if the restriction to the taregt is valid for the \exists-player. 
let isValidRestriction (guardSatComputer : GuardSatComputer) (tslist : list<TransitionSystem>) k l (predMap : PredicateMap) (sched : Set<int>) (s : AbstractState) (target : Set<AbstractState>) =
    
    let vars = 
        tslist
        |> List.map (fun x -> x.Vars)
    
    let locs = s.Locations

    let preds = predMap.[locs].PredList

    let varStringer (n, i, m) =
        n + "_" + string(i) + "_" + string(m)

    // Encode that the abstract satsifies the source abstract state
    let fixedPredClauses = 
        SMTUtil.encodeAbstractStateSatisfaction preds s.PredicatesSat
        |> fun x -> x.ReplaceVars (fun (n, i) -> n, i, PRE)

    // The universal copies among those schedueled
    let schedUniv = 
        Set.intersect sched ([0..k-1] |> set)

    // The existential copies among those schedueled
    let schedExists = 
        Set.intersect sched ([k..k+l-1] |> set)
    
    // Compute all possible next transition for the universal copies (that are scheduled)
    let transitionsMapUniv =
        seq { for i in schedUniv do i, tslist.[i].Step.[s.Locations.[i]] }
        |> Map.ofSeq
        // Compute all combinations
        |> Util.cartesianMap 
        |> Seq.filter (fun x -> 
            x 
            |> Map.map (fun _ (_, t) -> t.Guard)
            |> guardSatComputer.CanGuardsBeSat preds s.PredicatesSat
        )
        |> Seq.toList

    // Compute all possible next transition for the existentially quantified copies
    let transitionsMapExists =
        seq { for i in schedExists do i, tslist.[i].Step.[s.Locations.[i]] }
        |> Map.ofSeq
        // Compute all combinations
        |> Util.cartesianMap 
        |> Seq.filter (fun x -> 
            x 
            |> Map.map (fun _ (_, t) -> t.Guard)
            |> guardSatComputer.CanGuardsBeSat preds s.PredicatesSat
        )
        |> Seq.toList


    // The existentially quantified copies should have a move for each of the universal transitions, so we consider each universal move one after another
    let res = 
        transitionsMapUniv
        |> List.forall (fun univMove -> 
            // The location of the universal copies
            let univLoc = 
                [0..k-1]
                |> List.map (fun i -> if univMove.ContainsKey i then fst univMove.[i] else s.Locations.[i])
                |> List.toArray
            
            // The update formulas of the universal copies
            let univTransition = 
                univMove
                |> Map.map (fun _ (_, x) -> x)

            // Encode the update move of all universal copies
            let univMoveFormula = 
                [0..k-1]
                |> List.map (fun i -> 
                    if univTransition.ContainsKey i then 
                        SuccessorHelper.encodeTransitionStep vars.[i] univTransition.[i] i
                    else 
                        SuccessorHelper.encodeTransitionStepStay vars i
                    
                    )

            let headClause = Term.And (fixedPredClauses::univMoveFormula)

            // Build a disjunction over all moves available to the existential copies
            let tailClause = 
                transitionsMapExists
                |> List.map (fun existsMove -> 
                    let existsLoc = 
                        [k..k+l-1]
                        |> List.map (fun i -> if existsMove.ContainsKey i then fst existsMove.[i] else s.Locations.[i])
                        |> List.toArray

                    let combinedLoc = Array.append univLoc existsLoc

                    let existsTransition = 
                        existsMove
                        |> Map.map (fun _ (_, x) -> x)


                    // Encode the update move of all existential copies
                    let existsMoveFormula = 
                        [k..k+l-1]
                        |> List.map (fun i -> 
                            if existsTransition.ContainsKey i then 
                                SuccessorHelper.encodeTransitionStep vars.[i] existsTransition.[i] i
                            else 
                                SuccessorHelper.encodeTransitionStepStay vars i
                            )

                    // We only consider those abstract target states that match the location of the current exintial move
                    // Each of those candidates is translated into a formula
                    let possibleTargetStates = 
                        target
                        |> Set.toList
                        |> List.filter (fun x -> x.Locations = combinedLoc)
                        |> List.map (fun x -> x.PredicatesSat)
                        |> List.map (fun x -> 
                            SMTUtil.encodeAbstractStateSatisfaction predMap.[combinedLoc].PredList x
                            |> fun x -> x.ReplaceVars (fun (n, i) -> n, i, POST)
                            )
                        |> Term.Or

                    Term.And (possibleTargetStates::existsMoveFormula)
                )
                |> Term.Or

            let bodyFormula = Term.Implies(headClause, tailClause)

            // Now we add the quantifiers to the formula

            // All variables that we quantify existentially, i.e., the POST vars of all existentially quantify copies
            let existsVars = 
                [k..k+l-1]
                |> List.map (fun i ->
                    vars.[i].Vars
                    |> Set.map (fun n -> n, i )
                    )
                |> Set.unionMany
                |> Set.map (fun (n, i) -> (n, i, POST))
                |> Set.toList
                |> List.map (fun x -> x, INT)

            // All vars that we quantify universally, i.e., the PRE vars and the POST vars of all universal copies
            let univVars = 
                let univVars1 = 
                    [0..k+l-1]
                    |> List.map (fun i ->
                        vars.[i].Vars
                        |> Set.map (fun n -> n, i )
                        )
                    |> Set.unionMany
                    |> Set.map (fun (n, i) -> (n, i, PRE))

                let univVars2 = 
                    [0..k-1]
                    |> List.map (fun i ->
                        vars.[i].Vars
                        |> Set.map (fun n -> n, i )
                        )
                    |> Set.unionMany
                    |> Set.map (fun (n, i) -> (n, i, POST))
                
                Set.union univVars1 univVars2
                |> Set.toList
                |> List.map (fun x -> x, INT)

            let finalFormula = Term.Forall(univVars, Term.Exists (existsVars, bodyFormula))

            let res = SMTUtil.isSat finalFormula varStringer (fun _ -> INT)
        
            res
            )

    res


/// The game states in the game for \forall^*\exists^* properties
type GameStateExt =
    | RegularExt of ReductionGraphNode 
    // The boolean flag indicates if the restriction is maximal, in which case no check needs to be valid (as the set of all abstract sucvessors is always valid)
    | SchedChoiceExt of ReductionGraphNode * Set<int> * Set<ReductionGraphNode> * bool
    | InitialExt of Set<ReductionGraphNode>


    member this.AutomatonState =
        match this with
            | RegularExt s | SchedChoiceExt (s, _, _, _) -> s.AutomatonState
            | _ -> failwith "Unsupported"


/// Given the reduction graph (and the automaton used in the reduction graph), construct the game used for \forall^*\exists^* properties
let constructInitialAbstractionFromReductionGraph (r : ReductionGraph) (A : DSA) = 
    let nodes = new HashSet<_>()

    let sucessorMap = new Dictionary<_,_>()

    // For each node we add a Regular Game node
    for rgn in r.Nodes do 
        let node = RegularExt rgn

        nodes.Add node |> ignore 

        let sucsForNode = new HashSet<_>()

        sucessorMap.Add(node, sucsForNode)

        for e in r.Edges.[rgn] do 
            let sched = e.Key
            let sucs = e.Value |> seq |> set

            // For each subset of sucessors we add a SchedChoice state
            for A in Util.computePowerSet sucs do 
                if A.Count <> 0 then // We do not consider the empty restriction as it is always invalid
                    // The boolean flag is turned on whenever the size matches that of all sucessors. In this case we later do not need to check if the restriction is valid
                    let b =  sucs.Count = A.Count

                    let nodeChoice = SchedChoiceExt(rgn, sched, A, b)
                    nodes.Add nodeChoice |> ignore 
                    sucsForNode.Add nodeChoice |> ignore 

                    let sucForNodeChoice = new HashSet<_>()
                    sucessorMap.Add(nodeChoice, sucForNodeChoice)
                    // Only sucessors in A are possible
                    for rgn' in A do 
                        sucForNodeChoice.Add (RegularExt rgn') |> ignore
                        // Adding it to nodes will be done on the outer level

    let badStates = new HashSet<_>()
    for s in nodes do 
        if Set.contains s.AutomatonState A.BadStates then 
            badStates.Add s |> ignore

    let safeStates = new HashSet<_>()
    for s in nodes do 
        if Set.contains s.AutomatonState A.SafeStates then 
            safeStates.Add s |> ignore

    let initState = InitialExt (r.InitialNodes |> set)
    nodes.Add initState |> ignore
    // Add all successors of the initial node
    sucessorMap.Add(initState, new HashSet<_>(r.InitialNodes |> set |> Set.map RegularExt))

    let controllingPlayer = new Dictionary<_,_>()
    for s in nodes do 
        let p = 
            match s with 
                | RegularExt _ -> SAFE
                | SchedChoiceExt _ | InitialExt _ -> REACH
        controllingPlayer.Add(s, p)

    let reward = new Dictionary<_,_>()
    for s in nodes do 
        let r = 
            match s with 
                | SchedChoiceExt(_, _, A, _) -> Set.count A
                | RegularExt _ | InitialExt _ -> 0
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

/// Given a safety game, tries to find an invalid restriction by enumerating all transitions
let tryFindInvalidRestriction (guardSatComputer : GuardSatComputer) (tslist : list<TransitionSystem>) k l (predMap : PredicateMap) (sg : SafetyGame<GameStateExt>) =
    // Fist, compute *all* conditions that need to be checked
    let extractedConditions = new List<_>()
    for gstate in sg.States do
        match gstate with
            | SchedChoiceExt (s, sched, A, b) ->
                if b then   
                    // The restriction is valid by default
                    ()
                else 
                    let target = A |> Set.map (fun x -> x.AbstractState)
                    extractedConditions.Add(s.AbstractState, sched, target)
            | _ -> ()

    // Try to find a invalid restriction among those extracted in extractedConditions
    let res = 
        extractedConditions
        |> Seq.toList
        |> List.tryFind (fun (s, sched, target) -> 
            isValidRestriction guardSatComputer tslist k l predMap sched s target |> not
            )

    res

/// Given a safety game and a invalid restriction, refine the game by removing all invalid restrictions (those were the set of restrictions is smaller than the example provided)
/// We do this cleverly, i.e., we also remove all restrictions where the set of abstract successor states is restricted even further (is a subset).
/// This is possible as the set of valid restrictions is upwards closed. 
let refineGame (sg : SafetyGame<GameStateExt>) ((s, sched, target) : AbstractState * Set<int> * Set<AbstractState>) =
    let queue = new Queue<GameStateExt>()
    queue.Enqueue sg.InitialState

    let restrictedStates = new HashSet<_>()
    restrictedStates.Add sg.InitialState |> ignore

    let sucMap = new Dictionary<_,_>()

    while queue.Count <> 0 do
        let n = queue.Dequeue()
        let sucs = sg.Sucessors.[n]

        // We not only remove states but need to restrict moves
        let newSucs = 
            match n with
                | RegularExt _ -> 
                    let newSucs = new HashSet<_>()
                    for n' in sucs do 
                        match n' with 
                            | SchedChoiceExt (s', sched', target', _) -> 
                                let target' = target' |> Set.map (fun x -> x.AbstractState)
                                // Check if this restriction should be removed. This involes a subset check
                                if s'.AbstractState = s && sched = sched' && Set.isSubset target' target then 
                                    ()
                                    // Invalid restriction, so we do not add it
                                else
                                    // This is still valid. Add to the system
                                    newSucs.Add(n') |> ignore
                            | _ -> failwith "Not possible"
                    newSucs
                | _ -> 
                    let newSucs = new HashSet<_>(sucs)
                    newSucs

        for n' in newSucs do 
            if restrictedStates.Contains n' |> not then
                restrictedStates.Add n' |> ignore
                queue.Enqueue n'

        sucMap.Add(n, newSucs)
        
    let newBadStates = new HashSet<_>()
    for s in sg.BadStates do 
        if restrictedStates.Contains s then 
            newBadStates.Add s |> ignore

    let newSafeStates = new HashSet<_>()
    for s in sg.SafeStates do 
        if restrictedStates.Contains s then 
            newSafeStates.Add s |> ignore

    let newControllingPlayer = new Dictionary<_,_>()
    for s in restrictedStates do 
        newControllingPlayer.Add(s, sg.ControllingPlayer.[s])

    let newReward = new Dictionary<_,_>()
    for s in restrictedStates do 
        newReward.Add(s, sg.Reward.[s])

    let subGame =
        {
            SafetyGame.States = restrictedStates;
            InitialState = sg.InitialState;
            BadStates = newBadStates;
            SafeStates = newSafeStates;
            Sucessors = sucMap;
            ControllingPlayer = newControllingPlayer;
            Reward = newReward;
        }   

    subGame

/// Given a safety game and a invalid restriction, refine the game by removing the given invalid restriction
/// This is done naively, i.e., we do not use the upwards closures (as in refineGame) and only remove the given invalid restriction
let refineGameNaive (sg : SafetyGame<GameStateExt>) ((s, sched, target) : AbstractState * Set<int> * Set<AbstractState>) =
    let queue = new Queue<GameStateExt>()
    queue.Enqueue sg.InitialState

    let restrictedStates = new HashSet<_>()
    restrictedStates.Add sg.InitialState |> ignore

    let sucMap = new Dictionary<_,_>()

    while queue.Count <> 0 do
        let n = queue.Dequeue()

        let sucs = sg.Sucessors.[n]

        // We not only remove states but need to restrict moves
        let newSucs = 
            match n with
                | RegularExt _ -> 
                    let newSucs = new HashSet<_>()
                    for n' in sucs do 
                        match n' with 
                            | SchedChoiceExt (s', sched', target', _) -> 
                                let target' = target' |> Set.map (fun x -> x.AbstractState)
                                // We only remove the transition if its matches the given invalid restriction perfectly (*no* subset check)
                                if s'.AbstractState = s && sched = sched' && target' = target then 
                                    ()
                                    // Invalid restriction, so we do not add it
                                else
                                    // This is still valid. Add to the system
                                    newSucs.Add(n') |> ignore
                            | _ -> failwith "Not possible"
                    newSucs
                | _ -> 
                    let newSucs = new HashSet<_>(sucs)
                    newSucs

        for n' in newSucs do 
            if restrictedStates.Contains n' |> not then
                restrictedStates.Add n' |> ignore
                queue.Enqueue n'

        sucMap.Add(n, newSucs)

    let newBadStates = new HashSet<_>()
    for s in sg.BadStates do 
        if restrictedStates.Contains s then 
            newBadStates.Add s |> ignore

    let newSafeStates = new HashSet<_>()
    for s in sg.SafeStates do 
        if restrictedStates.Contains s then 
            newSafeStates.Add s |> ignore

    let newControllingPlayer = new Dictionary<_,_>()
    for s in restrictedStates do 
        newControllingPlayer.Add(s, sg.ControllingPlayer.[s])

    let newReward = new Dictionary<_,_>()
    for s in restrictedStates do 
        newReward.Add(s, sg.Reward.[s])

    let subGame =
        {
            SafetyGame.States = restrictedStates;
            InitialState = sg.InitialState;
            BadStates = newBadStates;
            SafeStates = newSafeStates;
            Sucessors = sucMap;
            ControllingPlayer = newControllingPlayer;
            Reward = newReward;
        }   
    subGame