module SafetyGame

open System
open System.IO
open System.Collections.Generic

open Util

type Player = SAFE | REACH

/// A generic safety game
type SafetyGame<'T when 'T : comparison> =   
    {
        States : HashSet<'T>;
        InitialState : 'T;
        Sucessors : Dictionary<'T, HashSet<'T>>;
        ControllingPlayer : Dictionary<'T, Player>;
        Reward : Dictionary<'T, int>;
        BadStates : HashSet<'T>;
        SafeStates : HashSet<'T>;
    }

    /// Compute a DOT graph from this game, marking special nodes
    member this.ToDotGraphMarked (labels : 'T -> String) (specialNodes : seq<'T>) =  
        let mutable unqiueId = 0 

        let nodeToIdDict : Dictionary<'T,String> = new Dictionary<_,_>()

        for n in this.States do 
            nodeToIdDict.Add(n, "n" + string unqiueId)
            unqiueId <- unqiueId + 1

        let s = new StringWriter()

        s.WriteLine ("strict digraph test {")
        s.WriteLine ("    forcelabels=true;")

        // First write the basic label of this node
        for n in this.States do 
            s.WriteLine ("    " + nodeToIdDict.[n] + "[label=" + labels n + "];")

        // The initial node is colored in blue
        s.WriteLine ("    " + nodeToIdDict.[this.InitialState] + "[color=blue];")

        // First write the basic label of this node
        for n in this.BadStates do 
            s.WriteLine ("    " + nodeToIdDict.[n] + "[color=red];")

        for n in this.SafeStates do 
            s.WriteLine ("    " + nodeToIdDict.[n] + "[color=green];")

        for n in this.States do 
            match this.ControllingPlayer.[n] with 
                | REACH ->
                    s.WriteLine ("    " + nodeToIdDict.[n] + "[shape=box];")
                | SAFE -> 
                    ()

        for n in specialNodes do 
            s.WriteLine ("    " + nodeToIdDict.[n] + "[fillcolor=yellow, style=filled];")

        // Add the edges
        for n in this.States do 
            for n' in this.Sucessors.[n] do
                s.WriteLine ("    " + nodeToIdDict.[n] + " -> " + nodeToIdDict.[n'] + ";")

        s.WriteLine ("}")
        // Convert to string and return
        s.ToString()

    /// Compute a DOT graph from this game
    member this.ToDotGraph (labels : 'T -> String) =  
        this.ToDotGraphMarked labels Seq.empty


/// The solution (aka winning strategy) for the safety game
type SafetyGameSol<'T when 'T : comparison> = 
    | SafeWins of Dictionary<'T, 'T>
    | ReachWins of Dictionary<'T, 'T>

    member this.Winner = 
        match this with
            | SafeWins _ -> SAFE
            | ReachWins _ -> REACH

/// Solve a safety game. Ich SAFE wins, we return a strategy that is optimal, i.e., always chooses a successor with highest reward
let solveSafetyGameOptimal<'T when 'T : comparison> (sg : SafetyGame<'T>) =
    let predMap = new Dictionary<'T, HashSet<'T>>()

    let reachWinningRegion = new HashSet<'T>()
    let counterDict = new Dictionary<'T, Counter>()

    let queue = new Queue<'T>()

    for s in sg.States do 
        predMap.Add(s, new HashSet<'T>())
    
    for s in sg.States do
        let sucs = sg.Sucessors.[s]
        for s' in sucs do
            predMap.[s'].Add s |> ignore

        // Count the number of successors for each node
        counterDict.Add(s, new Counter(sucs.Count))

        //if sg.BadStates.Contains s || sucs.Count = 0 then 
        if sg.BadStates.Contains s then 
            // All bad an sink states are winning for reahc
            reachWinningRegion.Add s |> ignore
            queue.Enqueue s

    // Invariantly, elements in the queue are always also in reachWinningRegion and added to the queue at most once. The loop terminates. 
    while queue.Count <> 0 do 
        let n = queue.Dequeue() // We can assume that n is also in reachWinningRegion

        for n' in predMap.[n] do 

            match sg.ControllingPlayer.[n'] with 
                | REACH -> 
                    // n' -> n and n is in reachWinningRegion, so n' is as well
                    if reachWinningRegion.Contains n' |> not then 
                        reachWinningRegion.Add n' |> ignore
                        queue.Enqueue n'
                | SAFE -> 
                    counterDict.[n'].Dec()
                    if counterDict.[n'].Get = 0 then
                        // All edges point to winning region so we can add it 
                        if reachWinningRegion.Contains n' |> not then 
                            reachWinningRegion.Add n' |> ignore
                            queue.Enqueue n'
                        
    // Computation of reachWinningRegion is done

    let winner = 
        if reachWinningRegion.Contains sg.InitialState then 
            // Reach wins
            // Compute shortest path to winning region using Floyd–Warshall
            // This ensures that the strategy actually enforces a visit to a bad state
            // This is useful for debugging purposes to visualizing the spoiling strategy

            let maxValue = new Dictionary<_,_>()
            let queue = new Queue<_>()

            for n in reachWinningRegion do 
                queue.Enqueue n
                if sg.BadStates.Contains n then
                    maxValue.Add(n, 0)
                else
                    maxValue.Add(n, Int32.MaxValue)     

            while queue.Count <> 0 do 
                let n = queue.Dequeue()

                let allSucsInRegionValues = new List<_>()

                for n' in sg.Sucessors.[n] do
                    if reachWinningRegion.Contains n' then 
                        allSucsInRegionValues.Add(maxValue.[n'])

                if allSucsInRegionValues.Count <> 0 then 
                    let current = maxValue.[n]

                    let newValue = 
                        match sg.ControllingPlayer.[n] with 
                            | SAFE -> 
                                allSucsInRegionValues
                                |> seq 
                                |> Seq.max
                            | REACH -> 
                                allSucsInRegionValues
                                |> seq 
                                |> Seq.min

                    let newBest = newValue + 1
                    if newBest <> current then 
                        maxValue.Remove n |> ignore
                        maxValue.Add(n, newBest)
                        // The value has changed to we need to recompute for all predeseccors
                        for n' in predMap.[n] do 
                            if reachWinningRegion.Contains n' then 
                                if queue.Contains n' |> not then 
                                    queue.Enqueue n'
                    

            let queue = new Queue<_>()
            queue.Enqueue sg.InitialState
            let alreadyConsidered = new HashSet<_>()
            alreadyConsidered.Add sg.InitialState |> ignore

            let strategyMap = new Dictionary<_,_>()

            while queue.Count <> 0 do 
                let n = queue.Dequeue()
                match sg.ControllingPlayer.[n] with 
                    | SAFE -> 
                        for n' in sg.Sucessors.[n] do 
                            if alreadyConsidered.Contains n' |> not then
                                queue.Enqueue n'
                                alreadyConsidered.Add n' |> ignore
                    | REACH -> 
                        let bestResponse = 
                            sg.Sucessors.[n]
                            |> Seq.filter (fun x -> reachWinningRegion.Contains x)
                            |> Seq.minBy (fun x -> maxValue.[x])

                        strategyMap.Remove n |> ignore
                        strategyMap.Add(n, bestResponse)
                        if alreadyConsidered.Contains bestResponse |> not then
                            queue.Enqueue bestResponse
                            alreadyConsidered.Add bestResponse |> ignore

            ReachWins strategyMap

        else 
            // Safe wins, compute strategy with maximal reward
            let safeStrat = new Dictionary<'T,'T>()

            for s in sg.States do
                if not (reachWinningRegion.Contains s) && sg.ControllingPlayer.[s] = SAFE then

                    let sucs = sg.Sucessors.[s]

                    if Seq.isEmpty sucs then 
                        // No successor of this node so no move by strategy is required
                        ()
                    else
                        let m = 
                            sg.Sucessors.[s] 
                            |> Seq.toList 
                            |> List.filter (reachWinningRegion.Contains >> not)
                            |> List.maxBy (fun x -> sg.Reward.[x])

                        safeStrat.Add(s, m) 
            
            SafeWins safeStrat

    winner, reachWinningRegion
    
/// Given a safety game and a strategy, we compute the reachable subgame and corresponding strategy on that subgame
let computeReachableGame (sg : SafetyGame<'T>) (sigma : SafetyGameSol<'T> ) =

    let strategyPlayer, strat = match sigma with SafeWins sigma -> SAFE, sigma | ReachWins sigma -> REACH, sigma
   
    let reachableStates = new HashSet<'T>()
    reachableStates.Add sg.InitialState |> ignore
    
    let queue = new Queue<'T>()
    queue.Enqueue(sg.InitialState)

    let newSucMap = new Dictionary<_,_>()

    while queue.Count <> 0 do
        let s = queue.Dequeue()

        if sg.ControllingPlayer.[s] = strategyPlayer then
            if sg.Sucessors.[s].Count = 0 then 
                // This state has no successors, so the strategy can not give one 
                newSucMap.Add(s, new HashSet<_>())
            else
                if strat.ContainsKey s then
                    let s' = strat.[s]
                    if not (reachableStates.Contains s') then
                        reachableStates.Add s' |> ignore
                        queue.Enqueue s'

                    // The node has a unique successor
                    newSucMap.Add(s, new HashSet<_>(Seq.singleton s'))
                else    
                    failwith "The strategy is invalid. It must return a successor"
        else
            let sucs = sg.Sucessors.[s]

            for s' in sucs do
                if not (reachableStates.Contains s') then
                    reachableStates.Add s' |> ignore
                    queue.Enqueue s'

            newSucMap.Add(s, sucs)


    let newBadStates = new HashSet<_>()
    for s in sg.BadStates do 
        if reachableStates.Contains s then 
            newBadStates.Add s |> ignore

    let newSafeStates = new HashSet<_>()
    for s in sg.SafeStates do 
        if reachableStates.Contains s then 
            newSafeStates.Add s |> ignore

    let newControllingPlayer = new Dictionary<_,_>()
    for s in reachableStates do 
        newControllingPlayer.Add(s, sg.ControllingPlayer.[s])

    let newReward = new Dictionary<_,_>()
    for s in reachableStates do 
        newReward.Add(s, sg.Reward.[s])

    let subGame =
        {
            SafetyGame.States = reachableStates;
            InitialState = sg.InitialState;
            BadStates = newBadStates;
            SafeStates = newSafeStates;
            Sucessors = newSucMap;
            ControllingPlayer = newControllingPlayer;
            Reward = newReward;
        }   

    let filteredStrat = new Dictionary<_,_>()
    for s in reachableStates do 
        if strat.ContainsKey s then
            filteredStrat.Add(s, strat.[s])
     
    let subStrat = match strategyPlayer with SAFE -> SafeWins filteredStrat | REACH -> ReachWins filteredStrat

    subGame, subStrat


