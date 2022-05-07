module CommandLineParser

open System
open FParsec

open Util
open GlobalConstants

/// A configuration file only includes the (absolute) path to Z3
type Configuration = 
    {
        Z3Path: option<String>;
    }

    static member Default = 
        {
            Z3Path = None
        }

/// The command line parameters given to HyPA
type CommandLineArguments = 
    {
        VerboseLevel : option<VerbosityLevel>;
        GameSolver: option<GameSolverType>;
        InputFile : option<string>
    }

    static member Default = 
        {
            VerboseLevel =  None
            GameSolver = None
            InputFile = None
        }

/// Parse the content of the config file
let parseConfigFile (s : string) = 
    let configUpdateParser (config: Configuration) =
        let z3Parser =
            skipString "[z3Path]" >>. spaces >>. many1CharsTill anyChar (skipNewline <|> eof)
            |>> (fun s -> Result.Ok { config with Z3Path = Some s })

        spaces
        >>. choice 
            [ 
                z3Parser // Option to add more parameters
            ]
        .>> spaces

    let rec configParser (config: Configuration) =
        (attempt (configUpdateParser config) 
            >>= (fun x -> 
                match x with 
                    | Result.Ok r -> configParser r
                    | Result.Error _ -> preturn x
                )
        )
        <|>% (Result.Ok config)

    let p = configParser Configuration.Default 

    match run p s with
        | Success (res, _, _) -> res
        | Failure (err, _, _) -> Result.Error "Parsing Error in Configuration File"
        


/// Parse the list of command line args for HyPA
let parseCommandLineArguments (args : list<String>) =
    let rec parseArgumentsRec (args : list<String>) opt = 

        match args with 
            | [] -> Result.Ok opt
            | x::xs -> 
                match x with 
                    | "-i" -> 
                        // Set the input file
                        match xs with 
                            | [] -> 
                                Result.Error "Option -i must be followed by an argument" 
                            | y::ys -> 
                                parseArgumentsRec ys {opt with InputFile = Some(y)}

                    | "-v" -> 
                        match xs with 
                            | [] -> 
                                Result.Error "Option -v must be followed by an argument" 
                            | y::ys -> 
                                try     
                                    let vl = System.Int32.Parse y
                                    // Match on the level and set the verbosity level
                                    match vl with 
                                        | 0 -> parseArgumentsRec ys { opt with VerboseLevel = Some GlobalConstants.VerbosityLevel.ResultOnly }
                                        | 1 -> parseArgumentsRec ys { opt with VerboseLevel = Some GlobalConstants.VerbosityLevel.OutputForPaper }
                                        | 2 -> parseArgumentsRec ys { opt with VerboseLevel = Some GlobalConstants.VerbosityLevel.EachStep }
                                        | 3-> parseArgumentsRec ys { opt with VerboseLevel = Some GlobalConstants.VerbosityLevel.DebugOutput }
                                        | _ -> Result.Error ("Unsupported Verbosity Level: " + y)
                                with _ -> Result.Error ("Unsupported Verbosity Level: " + y)

                    | "-s" -> 
                        match xs with 
                            | [] -> 
                                Result.Error "Option -s must be followed by an argument" 
                            | y::ys -> 
                                // Set the solver type
                                match y with 
                                    | "naive" -> parseArgumentsRec ys { opt with GameSolver = Some NAIVE }
                                    | "lazy" -> parseArgumentsRec ys { opt with GameSolver = Some LAZY }
                                    | _ -> Result.Error ("Unsupported Game Solver: " + y)

                    | _ -> Result.Error ("Option " + x + " is not supported" )
        
    parseArgumentsRec args CommandLineArguments.Default
                                