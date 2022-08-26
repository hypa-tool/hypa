module ModelChecker

open System.IO
open System.Collections.Generic

open Util

open GlobalConstants
open Automaton
open TransitionSystem
open Abstraction
open SafetyGame
open ReductionGraph
open KSafetyGameConstructor
open BeyondGameConstructor


/// Given a list of STSs and an automaton, verify the k-safety property on this instance
let private checkKSafetyDirect (tslist : list<TransitionSystem>) (predMap : PredicateMap) (A : DSA) (hashed : HashingContainer) =   

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printf "Started computation of the abstract schelduing graph..."

    // Start the computation of the reduction graph
    let swReductionGraph = System.Diagnostics.Stopwatch()
    swReductionGraph.Start()
    let rg = ReductionGraph.constructReductionGraph tslist predMap A hashed
    swReductionGraph.Stop()

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printfn "Done. Size of the abstract graph: %i. (Computed in %i ms)" rg.Nodes.Count swReductionGraph.ElapsedMilliseconds
        printf "Start construction of the game graph..."
    
    // Given the reduction graph, we compute the actual game from it
    let sw = System.Diagnostics.Stopwatch()
    sw.Restart()
    let sg = KSafetyGameConstructor.constructGameFromReductionGraph rg A
    sw.Stop()

    if List.contains OutputForPaper GlobalConstants.verboseLevel then 
        printf "| Size=%i | t_abs=%i ms " sg.States.Count swReductionGraph.ElapsedMilliseconds

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printfn "Done. Size of game %i. (Computed in %i ms)" sg.States.Count sw.ElapsedMilliseconds

    if GlobalConstants.printGameAndStrategyAsDotGraph then 
        // If the boolean flag ist set, we print the game graph as a dot graph
        // Used to debugging purposes

        if List.contains EachStep GlobalConstants.verboseLevel then 
            printf "Started DOT graph construction..."

        let path = GlobalConstants.tempPath + "/gameGraph.dot"
        
        let labelFunction (g : GameState) = 
            match g with 
                | Regular rgn -> "\"" + rgn.AsNonHTML() + "\""
                | SchedChoice (rgn, sched) ->   
                    let t = rgn.AsNonHTML()
                    let sched = Set.fold (fun s x -> s + string (x) + ",") "{" sched + "}"
                    "\"" + t + " | " + sched + "\""
                | Initial _ -> "\"Init\"" 

        File.WriteAllText(path, sg.ToDotGraph labelFunction)

        if List.contains EachStep GlobalConstants.verboseLevel then 
            printf "Done. "
    

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printf "Start solving of safety game...."

    // Solve the constructed safety game
    sw.Restart()
    let winner, reachRegion = SafetyGame.solveSafetyGameOptimal sg 
    sw.Stop()

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printfn "Done. (Solved in %i ms)" sw.ElapsedMilliseconds

    if GlobalConstants.printGameAndStrategyAsDotGraph then 
         // If the boolean flag ist set, we print the winning strategy as a dot graph
        // Used to debugging purposes

        if List.contains EachStep GlobalConstants.verboseLevel then 
            printf "Started DOT graph construction of winning strategy..."

        // Compute the restrcited graph of the winning strategy
        let restrcitedGame, _ = SafetyGame.computeReachableGame sg winner

        let path = GlobalConstants.tempPath + "/gameGraphStrategy.dot"
        
        let labelFunction (g : GameState) = 
            match g with 
                | Regular rgn -> "\"" + rgn.AsNonHTML() + "\""
                | SchedChoice (rgn, sched) ->   
                    let t = rgn.AsNonHTML()
                    let sched = Set.fold (fun s x -> s + string (x) + ",") "{" sched + "}"
                    "\"" + t + " | " + sched + "\""
                | Initial _ -> "\"Init\"" 
        
        File.WriteAllText(path, restrcitedGame.ToDotGraph labelFunction)

        if List.contains EachStep GlobalConstants.verboseLevel then 
            printf "Done. "
    
    winner.Winner

/// Given a list of STSs and an automaton, verify the \forall^l\exists^l property, i.e., a property beyond k-safety
let private checkBeyondDirect (tslist : list<TransitionSystem>) k l (predMap : PredicateMap) (A : DSA) (hashed : HashingContainer) =   

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printf "Started computation of the abstract schelduing graph..."

    // Start the computation of the reduction graph
    let swReductionGraph = System.Diagnostics.Stopwatch()
    swReductionGraph.Start()
    let rg = ReductionGraph.constructReductionGraph tslist predMap A hashed
    swReductionGraph.Stop()

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printfn "Done. Size of the abstract graph: %i. (Computed in %i ms)" rg.Nodes.Count swReductionGraph.ElapsedMilliseconds
    
    // Counter for the number of refinment iterations
    let mutable iterations = 0
    
    
    /// Solve the initial abstraction of the game by refining it on a lazy way, i.e., only refine when an invalid restriction is used.
    let rec solveIteratively (sg : SafetyGame<GameStateExt>) = 
        iterations <- iterations + 1
        let winner, _ = SafetyGame.solveSafetyGameOptimal sg 

        match winner with 
            | SafeWins _ ->
                // Safe wins the abstracted game. Check if all restrictions taken are valid
                let restrcitedSg, _ = SafetyGame.computeReachableGame sg winner

                let res = BeyondGameConstructor.tryFindInvalidRestriction hashed.GuardSatComputer tslist k l predMap restrcitedSg

                match res with 
                    | None -> 
                        // All restrictions are valid. Safe actually wins the game
                        SAFE
                    | Some cex -> 
                        // Found an invalid restriction. remove this restriction (and all smaller ones) and repeat
                        let refinedSg = BeyondGameConstructor.refineGame sg cex

                        solveIteratively refinedSg
            | ReachWins _ -> 
                // REACH wins
                if GlobalConstants.printGameAndStrategyAsDotGraph then 
                    let restrcitedSg, _ = SafetyGame.computeReachableGame sg winner
                    // We print the game graph as a dot graph to visulaiuze the spoiling strategy of REACH

                    if List.contains EachStep GlobalConstants.verboseLevel then 
                        printf "Started DOT graph construction..."

                    let path = GlobalConstants.tempPath + "/gameGraphStrategy.dot"
                    
                    let labelFunction (g : GameStateExt) = 
                        match g with 
                            | RegularExt rgn -> "\"" + rgn.AsNonHTML() + "\""
                            | SchedChoiceExt (rgn, sched, _, _) ->   
                                let t = rgn.AsNonHTML()
                                let sched = Set.fold (fun s x -> s + string (x) + ",") "{" sched + "}"
                                "\"" + t + " | " + sched + "\""
                            | InitialExt _ -> "\"Init\"" 

                    File.WriteAllText(path, restrcitedSg.ToDotGraph labelFunction)

                    if List.contains EachStep GlobalConstants.verboseLevel then 
                        printf "Done. "
 
                REACH
    
    
    /// Construct the game naively by removing all invalid restrictions at once.
    let rec constructNaiveGame sg =
        let res = BeyondGameConstructor.tryFindInvalidRestriction hashed.GuardSatComputer tslist k l predMap sg

        match res with 
            | None ->
                // No invalid restriction found, the game is fully constrcuted
                sg
            | Some cex ->
                // Found some invalid restriction. Remove it and repeat.
                let refinedSg = BeyondGameConstructor.refineGameNaive sg cex
                constructNaiveGame refinedSg

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printf "Start construction of the initial game graph abstraction..."

    // Construct the initial abstraction of the game. This still includes invalid restrictions
    let sg = BeyondGameConstructor.constructInitialAbstractionFromReductionGraph rg A

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printfn "Done. Size of initial abstraction %i" sg.States.Count

    // Solve the game, depending on what solver is used
    let winner = 
        match GlobalConstants.gameSolver with 
            | LAZY ->   
                if List.contains EachStep GlobalConstants.verboseLevel then 
                    printf "Started the lazy solving on the game abstraction..."

                // For the lazy solver, we solve iteratively
                let sw = System.Diagnostics.Stopwatch()
                sw.Start()
                let r = solveIteratively sg
                sw.Stop()

                if List.contains EachStep GlobalConstants.verboseLevel then 
                    printfn "Done. "
                    printfn "Number of Refinement Iterations: %i" iterations
                    printfn "Time to solve game (lazy): %i ms" sw.ElapsedMilliseconds
                    printfn "Cumulative time to construct abstraction and solve game: %i ms" (sw.ElapsedMilliseconds + swReductionGraph.ElapsedMilliseconds)

                if List.contains OutputForPaper GlobalConstants.verboseLevel then 
                    printfn "| Size=%i | t_abs=%i ms | #Ref=%i | t_solve=%i ms |" sg.States.Count swReductionGraph.ElapsedMilliseconds iterations sw.ElapsedMilliseconds
                   
                r
            | NAIVE -> 
                if List.contains EachStep GlobalConstants.verboseLevel then 
                    printf "Started the direct (naive) game construction..."

                let sw = System.Diagnostics.Stopwatch()
                sw.Start()

                // For the naive solver, we remove all invalid restrictions (this step is very expensive)
                let rsg = constructNaiveGame sg 
                
                if List.contains EachStep GlobalConstants.verboseLevel then 
                    printfn "Done. Size = %i." rsg.States.Count
                    printf "Started solving of the explict game..."

                // The resulting (without invalid restrictions) can be solved directly
                let w, _ = SafetyGame.solveSafetyGameOptimal rsg

                sw.Stop()

                if List.contains EachStep GlobalConstants.verboseLevel then 
                    printfn "Done. "
                    printfn "Time to solve game (naivly): %i ms" sw.ElapsedMilliseconds
                    printfn "Cumulative time to construct abstraction and solve game: %i ms" (sw.ElapsedMilliseconds + swReductionGraph.ElapsedMilliseconds)
            
                if List.contains OutputForPaper GlobalConstants.verboseLevel then 
                    printfn "| t_solve=%i ms |" sw.ElapsedMilliseconds

                w.Winner
    
    winner

/// Try to verify a k-safety property with a given list of STSs, predicates and a DSA
let checkKSafety (tslist : list<TransitionSystem>) (initPredMap : PredicateMap) (A : DSA) = 

    // Init all the hashers function for different parts of the construction
    let satHasher = StateSatComputer.StateSatComputerDirect(tslist)
    let implicationComputer = ImplicationTest.ImplicationComputerDirect(tslist)
    let guardSatComputer = GuardSatTest.GuardSatComputerDNF(tslist, satHasher, implicationComputer)
    let sucChecker = SuccessorComputation.SucComputerDirect (tslist, satHasher, guardSatComputer, implicationComputer)

    let hashed =
        { 
            HashingContainer.SatHasher = satHasher;
            GuardSatComputer = guardSatComputer;
            SucComputer = sucChecker;
            InitalStateDNFHasher = new Dictionary<_,_>();
            ObservationStateDNFHasher = new Dictionary<_,_>();
            AutomatonAlphabetDNFHasher = new Dictionary<_,_>()
        }

    let sw = System.Diagnostics.Stopwatch()
    sw.Start()
    let res = checkKSafetyDirect tslist initPredMap A hashed
    sw.Stop()

    if List.contains OutputForPaper GlobalConstants.verboseLevel then 
        printfn "| t=%i ms |" sw.ElapsedMilliseconds

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printfn "Finished solving of the game in %i ms" sw.ElapsedMilliseconds

    res


/// Try to verify a property beyond k-safety with a given list of STSs, predicates and a DSA
let checkBeyond (tslist : list<TransitionSystem>) k l (initPredMap : PredicateMap) (A : DSA) = 

    // Init all the hashers function for different parts of the construction
    let satHasher = StateSatComputer.StateSatComputerDirect(tslist)
    let implicationComputer = ImplicationTest.ImplicationComputerDirect(tslist)
    let guardSatComputer = GuardSatTest.GuardSatComputerDNF(tslist, satHasher, implicationComputer)
    let sucChecker = SuccessorComputation.SucComputerDirect (tslist, satHasher, guardSatComputer, implicationComputer)

    let hashed =
        { 
            HashingContainer.SatHasher = satHasher;
            GuardSatComputer = guardSatComputer;
            SucComputer = sucChecker;
            InitalStateDNFHasher = new Dictionary<_,_>();
            ObservationStateDNFHasher = new Dictionary<_,_>();
            AutomatonAlphabetDNFHasher = new Dictionary<_,_>()
        }

    let sw = System.Diagnostics.Stopwatch()
    sw.Start()
    let res = checkBeyondDirect tslist k l initPredMap A hashed
    sw.Stop()

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printfn "Finished solving of the game in %i ms" sw.ElapsedMilliseconds

    res
