module SMTUtil

open System
open System.IO
open System.Collections.Generic

open Term

open FParsec

// Fixes the SMT logic, we simply use ALL
let private logic = "ALL"

/// Given a list of predicates and a list of booleans indicating the satisfaction of each predicate, construct a combined formula
let encodeAbstractStateSatisfaction (preds : list<Term<RelVar>>) (s:list<bool>)  =
    List.zip preds s
    |> List.map (fun (t, b) -> if b then t else Term.Neg t)
    |> Term.And


// A stopwatch to stop execution time of each system call
let mutable systemCallTimer = System.Diagnostics.Stopwatch()

// Count the number of queries and the number of SMT queries and the number of queries that could be hashed (for Debug puproses)
let mutable numberOfQueries = 0
let mutable numberOfHashedQueries = 0

// A hash function that hashes each term that has been checked for SAT
let isSatHasher = new Dictionary<_,_>()

// The path to which the SMT query is written before calling Z3
let private pathToFile = GlobalConstants.tempPath + "/query.smt2"
 
/// Use Z3 to detrimen if a given formula is satsfiable
let private isSatStringTerm (term : Term<String>) (varTypes : Set<String * VarType>) = 
    if isSatHasher.ContainsKey(term) then
        numberOfHashedQueries <- numberOfHashedQueries + 1 
        isSatHasher.[term]
    else 
        numberOfQueries <- numberOfQueries + 1
        systemCallTimer.Start()
        
        // Write the variables types for the SMTLIb query
        let declareVarsString =
            varTypes
            |>  Set.fold (fun s (name, t) -> s + "(declare-fun " + name + " () " + t.AsString + ")\n") ""


        let qu =
            "(set-logic " + logic + ")\n" +
            declareVarsString + 
            "(assert\n" +
            Term<_>.ToString term +
            "\n)\n" +
            "(check-sat)"

        // Write the query to the file     
        File.WriteAllText(pathToFile, qu)

        let p = new System.Diagnostics.Process();
        p.StartInfo.RedirectStandardOutput <- true
        p.StartInfo.UseShellExecute <- false
        p.StartInfo.FileName <- GlobalConstants.z3Path;
        p.StartInfo.Arguments <- pathToFile

        // Start the SMT solver
        p.Start() |> ignore
        
        let sres = (p.StandardOutput.ReadToEnd())

        systemCallTimer.Stop()
        
        // Analyse the result of Z3
        let res = if sres = "sat\n" then true elif sres = "unsat\n" then false else failwith ("Unexpected Output by Z3: " + sres)

        isSatHasher.Add(term, res)
        res

// A random generator to ensure reproducible results for model generation
let private r = new System.Random(0)

let modelHasher = new Dictionary<_,_>()

/// Computes models for a given query
let private getModelsStringTerm (term : Term<String>) (varTypes : Set<String * VarType>) = 
    if modelHasher.ContainsKey(term, varTypes) then
        numberOfHashedQueries <- numberOfHashedQueries + 1 
        modelHasher.[term, varTypes]
    else 
        numberOfQueries <- numberOfQueries + 1
        systemCallTimer.Start()

        let declareVarsString =
            varTypes
            |>  Set.fold (fun s (name, t) -> s + "(declare-fun " + name + " () " + (t).AsString + ")\n") ""

    
        let mutable qu =
            "(set-logic " + logic + ")\n" +
            "(set-option :smt.arith.random_initial_value true)\n" + // Set the Z3 options to generte multiple values
            declareVarsString + 
            "(assert\n" +
            Term<_>.ToString term +
            "\n)\n"

        // We generate 10 models for each abstract state. Can be changed in the future. 
        let numberOfModels = 10

        // Using different random seeds, we genarte Z3 models 
        for _ in 1..numberOfModels do 
            let i = r.Next(30)
            qu <- 
                qu + 
                "(check-sat-using (using-params qflra :random_seed " + string(i) + "))\n" +
                "(get-model)"

        
        File.WriteAllText(pathToFile, qu)

        let p = new System.Diagnostics.Process();
        p.StartInfo.RedirectStandardOutput <- true
        p.StartInfo.UseShellExecute <- false
        p.StartInfo.FileName <- GlobalConstants.z3Path;
        p.StartInfo.Arguments <- pathToFile

        p.Start() |> ignore
        
        let sres = (p.StandardOutput.ReadToEnd())

        systemCallTimer.Stop()

        // The vars used in the formula are of the form x_i, so we create a parser for such varaibles
        let relVarParser =
            pipe3
                (many1Chars letter)
                (pstring "_")
                pint32
                (fun x _ z -> (x, z))

        let modelParser = TermParser.parseModel relVarParser
        
        // Extract the models by splitting at "sat" and parsing each model separataly
        let res = 
            if sres.StartsWith "sat" then 
                let splitted = 
                    sres.Split("sat")
                    |> Array.removeAt 0

                let models = 
                    splitted
                    |> Array.map (fun x -> modelParser x)
                    |> Array.toList

                
                Some models
            elif sres.StartsWith "unsat" then 
                None

            else 
                failwith ("Unexpected Output:" + sres)


        modelHasher.Add((term, varTypes), res)
        res


/// Check if a formula is satisfiable
let isSat<'T when 'T: comparison> (term : Term<'T>) (varNameMapper : 'T -> String) (typeMapper : 'T -> VarType) = 
    let vars = term.FreeVars

    let declareVarsList =
        vars
        |>  Set.map (fun x -> (varNameMapper x, typeMapper x))

    let termAsStringTerm = term.ReplaceVars varNameMapper

    isSatStringTerm termAsStringTerm declareVarsList

/// Compute models for a given formula (or None if the formula is unsat)
let getModels<'T when 'T: comparison> (term : Term<'T>) (vars : Set<'T>) (varNameMapper : 'T -> String) (typeMapper : 'T -> VarType) = 

    let declareVarsList =
        term.FreeVars
        |>  Set.map (fun x -> (varNameMapper x, typeMapper x))

    let varsAsString = 
        vars 
        |> Set.map (fun x -> (varNameMapper x, typeMapper x))

    let decl = Set.union declareVarsList varsAsString

    let termAsStringTerm = term.ReplaceVars varNameMapper

    getModelsStringTerm termAsStringTerm decl 
    
/// Check if a formula is valid
let isValid<'T when 'T: comparison> (term : Term<'T>) (varNameMapper : 'T -> String) (typeMapper : 'T -> VarType) = 

    let res = isSat (Term.Neg term) varNameMapper typeMapper
    if res then 
        false
    else
        true