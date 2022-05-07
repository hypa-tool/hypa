open System

open System.IO

open GlobalConstants
open Term
open TransitionSystem
open Abstraction
open Automaton
open SafetyGame
open Parser
open CommandLineParser

[<EntryPoint>]
let main argv =
    // ========================== Parse the Command Line Args and Config File =======================================
    
    // Parse the command line arguments
    let commandLineArgs = 
        match CommandLineParser.parseCommandLineArguments (Array.toList argv) with 
            | Error s -> 
                printfn "%s" s 
                exit 0
            | Ok x -> x

    
    let inputPath = 
        match commandLineArgs.InputFile with 
            | Some x -> 
                x
            | None -> 
                printfn "A input file must be specified using -i"
                exit 0

    // Globally set the game solver and the verbosity level
    
    // The temp path is always the current path
    GlobalConstants.tempPath <- "./"

    if commandLineArgs.GameSolver.IsSome then 
        GlobalConstants.gameSolver <- commandLineArgs.GameSolver.Value
    else 
        GlobalConstants.gameSolver <- Util.GameSolverType.LAZY

    if commandLineArgs.VerboseLevel.IsSome then 
        GlobalConstants.verboseLevel <- [commandLineArgs.VerboseLevel.Value]
    else 
        GlobalConstants.verboseLevel <- [EachStep]


    // By convention the config.conf file (that specifies the path to Z3) is located in the same directory as the HyPA executable
    // Get the path of the current binary
    let pathOfTheExectable = 
        let execName = System.Reflection.Assembly.GetExecutingAssembly().Location
        System.IO.Path.GetDirectoryName(execName)

    let configPath =   
        pathOfTheExectable + "/config.conf"

    // Check if the path to the config file is valid , i.e., the file exists
    if System.IO.FileInfo(configPath).Exists |> not then 
        printfn "The config.conf file does not exist in the same directory as the executable"
        exit 0

    // Parse the config File
    let configContent = 
        try
            File.ReadAllText configPath
        with 
            | _ -> 
                printfn "Could not open config file"
                exit 0
           
    match CommandLineParser.parseConfigFile configContent with 
        | Ok x -> 
            if x.Z3Path.IsSome then 
                GlobalConstants.z3Path <- x.Z3Path.Value
            else 
                printfn "The config.conf does not specify the path to Z3"
                exit 0

        | Error r -> 
            printfn "%s" r
            exit 0

    // Check that the Z3 path is valid
    if System.IO.FileInfo(GlobalConstants.z3Path).Exists |> not then 
        printfn "The path to the Z3 Solver is incorrect"
        exit 0

        
    // ========================= Read and Parse Input ========================================
    if List.contains EachStep GlobalConstants.verboseLevel then 
        printf "Read and Parse Input..."

    // Parse the input and extract the STSs, automaton and predicates
    let config = Parser.parseConfigFile inputPath

    let tslist = config.Tlist
    let k, l = config.QuantifierStructure
    let preds = config.Predicates

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printfn "Done"

    let mainSw = System.Diagnostics.Stopwatch()
    let sw = System.Diagnostics.Stopwatch()

    mainSw.Start()
    sw.Start()
    // =================================================================

    // =========================== Determinize the safety automaton  ======================================
    if List.contains EachStep GlobalConstants.verboseLevel then 
        printf "Determeinize Automaton..."
    // Determinize the safety automaton
    let detA = Automaton.convertToDSA config.Automaton
    sw.Stop()

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printfn "Done (in %i ms)." sw.ElapsedMilliseconds

    // =================================================================

    // =========================== Check if Transition System and Automaton are consistent ======================================
    if List.contains EachStep GlobalConstants.verboseLevel then 
        printf "Checking syntactic consistentcy...."

    if tslist |> List.exists (fun ts -> ts.IsConsitent |> not) then 
        printfn "The Transition systems are not consistent"
        exit 0 

    if detA.IsConsitent |> not then 
        printfn "The Automaton is not consistent"
        exit 0 

    let varsA = 
        detA.Vars.Vars
        |> Set.forall (fun (n, i) -> 
            (0 <= i && i <= config.TotalCout - 1) 
            &&
            tslist.[i].Vars.Vars.Contains n
            )

    if not varsA then 
        printfn "The automaton uses vars not in the STS"
        exit 0

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printfn "Done."

    // =================================================================

    // ===================== Extend the predicates to cover all locations  ============================================
    
    let allLocCombinations = 
        tslist
        |> List.map (fun x -> x.Locations)
        |> Util.cartesian
        |> List.map List.toArray

    // For each location in the product where no predicates are given, we use the empty set of predicates
    let extendedPredMap : PredicateMap = 
        [for loc in allLocCombinations do loc, if Map.containsKey loc preds then preds.[loc] else {Predicates.PredList = [];}]
        |> Map.ofSeq
    // =================================================================

    if List.contains OutputForPaper GlobalConstants.verboseLevel then 
        let name = Path.GetFileNameWithoutExtension(inputPath)
        // Output the current instance
        printfn "============ %s ============" name

    // ===================== Solve ============================================
    let winner =    
        if l = 0 then 
            // The property is k-safety. Use the k-safety game construction
            ModelChecker.checkKSafety tslist extendedPredMap detA
        else 
            // The property uses existential quantification. Use for involved game construction beyond k-safety

            if List.contains OutputForPaper GlobalConstants.verboseLevel then 
                // Print the solver beeing used
                printfn "Solver : %A" GlobalConstants.gameSolver

            ModelChecker.checkBeyond tslist k l extendedPredMap detA
    // =================================================================

    mainSw.Stop()

    if List.contains EachStep GlobalConstants.verboseLevel then 
        printfn ""

        match winner with 
            | SafetyGame.Player.SAFE -> printfn "========= The property holds ========= "
            | SafetyGame.Player.REACH -> printfn "=========  Property could not be verified ========= "

        printfn ""

        printfn "Total Time: %i ms" mainSw.ElapsedMilliseconds

    if List.contains OutputForPaper GlobalConstants.verboseLevel then 
        printfn ""

        match winner with 
            | SafetyGame.Player.SAFE -> printfn "The property holds"
            | SafetyGame.Player.REACH -> printfn "Property could not be verified"

        printfn "============================" 

    if List.contains DebugOutput GlobalConstants.verboseLevel then 
        printfn "Overall computation required %i SMT queries (%i could be hashed). This took %i ms" SMTUtil.numberOfQueries SMTUtil.numberOfHashedQueries SMTUtil.systemCallTimer.ElapsedMilliseconds 


        printfn "Init: %i ms | Obs %i ms | Automaton: %i ms | Transitions: %i ms" ReductionGraph.swInit.ElapsedMilliseconds ReductionGraph.swObservations.ElapsedMilliseconds ReductionGraph.swAutomaton.ElapsedMilliseconds ReductionGraph.swTransition.ElapsedMilliseconds

    if List.contains ResultOnly GlobalConstants.verboseLevel then 
        match winner with 
            | SafetyGame.Player.SAFE -> printfn "SAT"
            | SafetyGame.Player.REACH -> printfn "UNKNOWN"
    
    0