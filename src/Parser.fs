module Parser

open System
open System.IO
open FParsec

open Term
open TransitionSystem
open Automaton
open Abstraction

/// The configuartion on which HyPA is run. All information are given in the .hyap file
type RunConfiguration = 
    {
        Tlist : list<TransitionSystem>;
        Automaton : NSA;
        QuantifierStructure : int * int;
        Predicates : PredicateMap;
        Comment : String
    }

    member this.TotalCout = 
        let k, l = this.QuantifierStructure
        k+ l

/// A parser for relation variables as used in the predicates (Of the form x_i).
let private relVarParser =
    pipe3
        (many1Chars letter)
        (pstring "_")
        pint32
        (fun x _ z -> (x, z))

/// A parser for formulas using variables of the form x_i
let private genericRelVarParser =
    TermParser.termParser relVarParser

/// A parser for formulas using variables of the form x or x' used to encode step conditions
let private genericPrePostVarParser =
    let prePostParser =
        pipe2
            (many1Chars letter)
            (charReturn '\'' POST <|> preturn PRE)
            (fun x y -> (x, y))
    TermParser.termParser prePostParser

/// A parser for formulas using variables of the form x. Used, e.g., for guards of transitions
let private genericSingeVarParser =
    let singleVarParser =
        (many1Chars letter)
    TermParser.termParser singleVarParser

/// A parser for expressions using variables of the form x. Used, e.g., for updates in the STS
let private genericSingeVarExression =
    let singleVarParser =
        (many1Chars letter)
    TermParser.expressionParser singleVarParser      
        

// ================================================ PARSER FOR Transition System ================================================

let private initFormulaParser =
    let pairParser =
        spaces >>. pchar '(' >>. spaces >>.
        pipe2
            (pint32 .>> spaces .>> pchar ':' .>> spaces)
            genericSingeVarParser
            (fun x y -> (x, y))
        .>> spaces .>> pchar ')'

    spaces >>. many1 (pairParser .>> spaces)
    |>> Map.ofList

let private stepParser =  
    let varAssignmentParser = 
        pipe3 
            (many1Chars letter)
            (spaces >>. pstring ":=")
            (spaces >>. genericSingeVarExression)
            (fun x _ z -> (x, z))

    let varAssignmentListParser = 
        spaces >>. pchar '[' >>. spaces >>. 
        sepBy (varAssignmentParser .>> spaces) (pchar ',' .>> spaces)
        .>> spaces .>> pchar ']'
        |>> (fun x -> Map.ofSeq x)

    let nonDetParser = 
        let formulaParser = 
            (attempt(genericPrePostVarParser |>> Some)) <|> preturn None


        spaces >>. pchar '[' >>. spaces >>. 
            pipe2 
                (sepBy ((many1Chars letter) .>> spaces) (pchar ',' .>> spaces))
                (skipChar '|' >>. spaces >>. formulaParser .>> spaces .>> pchar ']')
                (fun x y -> set x, y)

    let guardedTransitionParser = 
        spaces >>. pchar '(' >>. 
        pipe4
            (spaces >>. genericSingeVarParser .>> spaces .>> pchar ',')
            (spaces >>. varAssignmentListParser .>> spaces .>> pchar ',')
            (spaces >>. nonDetParser .>> spaces .>> pchar ',')
            (spaces >>. pint32)
            (fun x y (a, b) z -> z, {GuardedUpdate.Guard = x; Assignments = y; NonDetVars = a; AdditionalCondition = b})
        .>> spaces .>> pchar ')'

    let guardedTransitionSetParser =
        spaces >>. pchar '{' >>. 
        many1 (guardedTransitionParser .>> spaces)
        .>> spaces .>> pchar '}'
        |>> set

    let parseEdgeAlignment =
        pipe2
            (pint32 .>> spaces .>> pchar ':' .>> spaces)
            (guardedTransitionSetParser .>> spaces)
            (fun x y -> (x, y))

    spaces
    >>.
    many (parseEdgeAlignment .>> spaces)
    |>> Map.ofList


let private varManagerSingleParser =
    let parseVarSet =
        spaces >>. pchar '{' >>. spaces
        >>.
        sepBy (many1Chars letter .>> spaces) (pchar ',' .>> spaces)
        .>> spaces .>> pchar '}'
        |>> (fun x -> x |> set)

    parseVarSet
    |>> (fun a -> {VarManager.Vars = a; VarType = fun _ -> INT})
    
let private varManagerRelParser =
    let parseVarSet =
        spaces >>. pchar '{' >>. spaces
        >>.
        sepBy (relVarParser .>> spaces) (pchar ',' .>> spaces)
        .>> spaces .>> pchar '}'
        |>> (fun x -> x |> set)

    parseVarSet
    |>> (fun a -> {VarManager.Vars = a; VarType = fun _ -> INT})

let private intSetParser =
    spaces >>. pchar '{' >>. spaces
    >>.
    sepBy (pint32 .>> spaces) (pchar ',' .>> spaces)
    .>> spaces .>> pchar '}'
    |>> (fun x -> x |> set)

let private tSParser =
    pipe5
        (spaces >>. pstring "[vars]" >>. varManagerSingleParser)
        (spaces >>. pstring "[locations]" >>. spaces >>. intSetParser)
        (spaces >>. pstring "[init]" >>. initFormulaParser)
        (spaces >>. pstring "[step]" >>. stepParser)
        (spaces >>. pstring "[obs]" >>. initFormulaParser)
        (fun a b c d e -> {TransitionSystem.TransitionSystem.Vars = a; Locations = b; Init = c; Step = d; Observation = e})


/// Parse a string into a transition system
let parseTS (s: string) =
    let full = tSParser .>> eof
    let res = run full s
    match res with
        | Success (res, _, _) -> res
        | Failure (err, _, _) -> 
            printfn "Could not parse tranistion system: %s" err
            exit 0
    

// ================================================ PARSER FOR Transition System - END ================================================



// ================================================ PARSER FOR Atomaton ================================================

let private automatonEdgeMapParser = 
    let automatonEdgeParser =
        spaces >>. pchar '(' 
        >>.
        pipe2
            (genericRelVarParser .>> spaces .>> pstring "," .>> spaces)
            pint32
            (fun x y -> {AutomatonEdge.Guard = x; TargetState = y})
        .>> 
        spaces .>> pchar ')'

    let automatonEdgeSetParser =
        spaces >>. pchar '{' >>. 
        many1 (automatonEdgeParser .>> spaces)
        .>> spaces .>> pchar '}'
        |>> set

    let automatonOutgoigingEdgesParser =
        pipe2
            (pint32 .>> spaces .>> pchar ':' .>> spaces)
            (automatonEdgeSetParser .>> spaces)
            (fun x y -> (x, y))

    spaces
    >>.
    many (automatonOutgoigingEdgesParser .>> spaces)
    |>> Map.ofList

let private automatonStateSetParser =
    spaces >>. pchar '{' >>. spaces
    >>.
    sepBy pint32 (spaces >>. pchar ',' >>. spaces)
    .>> pchar '}'
    |>> set


let private autParser =
    pipe5
        (spaces >>. pstring "[states]" >>. automatonStateSetParser)
        (spaces >>. pstring "[initial]" >>. automatonStateSetParser)
        (spaces >>. pstring "[bad]" >>. automatonStateSetParser)
        (spaces >>. pstring "[vars]" >>. varManagerRelParser)
        (spaces >>. pstring "[edges]" >>. automatonEdgeMapParser)
        (fun states initStates badStates vars edges -> 
            {NSA.States = states; InitialStates = initStates; BadStates = badStates; Vars = vars; Edges = edges})

/// Parse a string into a NSA
let parseAutomaton (s : string)=
    let full = autParser .>> spaces .>> eof
    let res = run full s
    match res with
        | Success (res, _, _) -> res
        | Failure (err, _, _) -> 
            printfn "Could not parse automaton: %s" err
            exit 0


// ================================================ PARSER FOR Automaton - End ================================================

// ================================================ PARSER FOR Predicate List ================================================

let private predicateMapParser =
    
    let predicatesParser =
        spaces >>. pchar '{' >>. spaces >>.
        sepBy (genericRelVarParser .>> spaces) (pchar ',' >>. spaces)
        .>>
        pchar '}' .>> spaces
        |>> (fun x -> {Predicates.PredList = x})

    let intArrayParser =
        spaces >>. pchar '[' >>. spaces >>.
        many (pint32 .>> spaces)
        .>> spaces .>> pchar ']'
        |>> List.toArray

    let intArrayListParser =
        spaces >>. 
        many (intArrayParser .>> spaces)
        |>> set

    let predicateAllignmentParser =
        pipe2
            (intArrayListParser .>> spaces .>> pchar ':' .>> spaces)
            (predicatesParser .>> spaces)
            (fun x y -> [for a in x do (a, y)])

    spaces >>. 
    many (predicateAllignmentParser .>> spaces)
    |>> (List.concat >> Map.ofList)

/// Parse a String into a poredicate map
let parsePrediactes (s : string) : PredicateMap=
    let full = predicateMapParser .>> spaces .>> eof
    let res = run full s
    match res with
        | Success (res, _, _) -> res
        | Failure (err, _, _) -> 
            printfn "Could not parse predicate map: %s" err
            exit 0

// ================================================ PARSER FOR Predicate List - End ================================================

// ================================================ PARSER FOR Entire configuration ================================================

/// Given the path to the input file (usually a .hypa file), we parse the content of the problem.
/// It then checks if each of the paths used therein (for e.g., the STS) exists, opens them and parses them.
let parseConfigFile path =  
    // Read the config file
    let confContent = 
        try 
            File.ReadAllText path 
        with _ ->   
            printfn "Could not open file %s" path 
            exit 0

    let fileNameParser = 
        spaces >>. many1Satisfy (fun c -> c <> ',' && c <> ' ' && c <> '\n' && c <> ']')  

    let fileListParser = 
        spaces >>. pchar '[' >>.
        sepBy1 (fileNameParser .>> spaces) (pchar ',' .>> spaces)
        .>> spaces .>> pchar ']'

    let cfParser =  
        pipe5
            (spaces >>. pstring "[systems]" >>. fileListParser)
            (spaces >>. pstring "[automaton]" >>. spaces >>. fileNameParser)
            (spaces >>. pstring "[qs]" >>. spaces >>. pchar '(' >>. spaces >>.  pint32 .>>. (spaces >>. pchar ',' >>. spaces >>. pint32 .>> spaces .>> pchar ')'))
            (spaces >>. pstring "[preds]" >>. fileNameParser)
            (spaces >>. pstring "[comment]" >>. many1Chars anyChar)
            (fun a b c d e -> (a, b, c, d, e))

    let full = cfParser .>> spaces .>> eof
    let (tsFiles, automatonFile, (k, l), predFile, c) =  
        match run full confContent with
            | Success (res, _, _) -> res
            | Failure (err, _, _) -> 
                printfn "Could not parse run config file: %s" err
                exit 0
    
    // Gets that path of the file (all files must be located in the same directory)
    // We therfore get that path of the inputFile
    let mainpath = System.IO.FileInfo(path).Directory.FullName
            
    // Open and parse the transition systems
    let tslist = 
        tsFiles
        |> List.map (fun x -> 
            try 
                File.ReadAllText (mainpath + "/" +  x)
            with _ -> 
                printfn "Could not open file %s" path 
                exit 0
            )
        |> List.map (fun x -> parseTS x)

    // Open and parse the automaton 
    let automaton =
        (
            try 
                File.ReadAllText (mainpath + "/" +  automatonFile)
            with _ -> 
                printfn "Could not open file %s" path 
                exit 0 
        )
        |> parseAutomaton 
    
    // Open and parse the predicates map 
    let predMap = 
        (
            try 
                File.ReadAllText (mainpath + "/" +  predFile)
            with _ -> 
                printfn "Could not open file %s" path 
                exit 0 
        )
        |> parsePrediactes

    {
        RunConfiguration.Tlist = tslist;
        Automaton = automaton;
        QuantifierStructure = (k, l);
        Predicates = predMap;
        Comment = c
    }

// ================================================ PARSER FOR Entire configuration - END ================================================
