module ImplicationTest

open System.Collections.Generic

open Term
open TransitionSystem
open SuccessorHelper 

let swim0 = System.Diagnostics.Stopwatch()
let swim1 = System.Diagnostics.Stopwatch()
let swim2 = System.Diagnostics.Stopwatch()

type ImplicationComputerDirect (tslist : list<TransitionSystem>) = 

    let vars = 
        tslist
        |> List.map (fun x -> x.Vars)

    let predicateImplicationViaStepHash = new Dictionary<_,_>()

    // Given an abstract state (sourcePreds, s) and an update (transitions) check if p holds when taking the step
    let testImplWithMoveDirect (transitions : Map<int, GuardedUpdate>) (sourcePreds : list<Term<RelVar>>) (s : list<bool>) (p : Term<RelVar>)  =

        // The precondition encoding the abstract state
        let pre = 
            SMTUtil.encodeAbstractStateSatisfaction sourcePreds s
            |> fun x -> x.ReplaceVars (fun (n, i) -> n, i, PRE)

        // The formula describing the move (generated from the transitions)
        let moveTerm = encodePartialStepViaMap vars transitions
        
        let post = p.ReplaceVars (fun (n, i) -> n, i, POST)

        let varStringer (n, i : int, m : PrePost) = 
            n + "_" + string(i) + "_" + string(m)

        // The combined query
        let posquery =
            Term.Implies (Term.And [pre; moveTerm], post)

        if SMTUtil.isValid posquery varStringer (fun (n, i, _) -> vars.[i].VarType n) then
            // Positive implication holds
            POS
        else
            // Check the negation of the negative query
            let negquery =
                Term.Implies (Term.And [pre; moveTerm], Term.Neg post)
            
            if SMTUtil.isValid negquery varStringer (fun (n, i, _) -> vars.[i].VarType n) then
                // Negative implication holds
                NEG
            else 
                NEITHER

    /// Performs the same as testImplWithMoveDirect but adds one more level of optimization by hashing results via hashing of prefixes of the abstract state
    let testImplWithMoveOpt1 (transitions : Map<int, GuardedUpdate>) (sourcePreds : list<Term<RelVar>>) (s : list<bool>) (p : Term<RelVar>) =

        let r =
            if predicateImplicationViaStepHash.ContainsKey (transitions, p) then
                predicateImplicationViaStepHash.[(transitions, p)]
            else
                let innerMap = new Dictionary<_,_>()
                innerMap.Add([], ImplicationStatus.NEITHER)
                predicateImplicationViaStepHash.Add ((transitions, p), innerMap)
                innerMap

        let zipped = List.zip sourcePreds s

        // We are guaranteed to find this at least for the empty list []
        let satPrefix = Seq.find r.ContainsKey (Util.listPrefixes zipped)

        let res = 
            match r.[satPrefix] with
                | POS -> POS
                | NEG -> NEG
                | NEITHER ->
                    // Now we need to check for the full predicate set
                    if satPrefix= zipped then
                        // The result is hashed for the full predicate collection. No need to recompute
                        NEITHER
                    else
                        let res = testImplWithMoveDirect transitions sourcePreds s p
                        r.Add(zipped, res)
                        res
        res

    let withoutMovesHasher = new Dictionary<_,_>()

    /// Check if a given abstract state implies a given formula p (without any move)
    let testImplWithoutMove (preds : list<Term<RelVar>>) (s : list<bool>) (p : Term<RelVar>) =
        if withoutMovesHasher.ContainsKey (preds, s, p) then 
            withoutMovesHasher.[(preds, s, p)]
        else 
            // Begin by doing a quick syntactic check if we have the SAME predicate in the list. In this case we can directly read of the implication. 
            let res =
                match List.tryFindIndex (fun x -> x = p) preds with 
                | Some i -> if s.[i] then POS else NEG
                | None -> 
                    // Check if p = top
                    if SMTUtil.isValid p (fun (n, i) -> n + "_" + string(i)) (fun _ -> INT) then 
                        POS
                    else 
                        // Need to recompute this
                        let pre = SMTUtil.encodeAbstractStateSatisfaction preds s
                        
                        let post = p 
                        // First check for positive implication
                        let posquery =
                            Term.Implies (pre, post)

                        if SMTUtil.isValid posquery (fun (n, i) -> n + "_" + string(i)) (fun (n, i) -> vars.[i].VarType n) then 
                            POS
                        else
                            // Then check for negative implication
                            let negquery =
                                Term.Implies (pre, Term.Neg post)
                            
                            if SMTUtil.isValid negquery (fun (n, i) -> n + "_" + string(i)) (fun (n, i) -> vars.[i].VarType n) then 
                                NEG
                            else 
                                NEITHER

            // Hash the result for future uses            
            withoutMovesHasher.Add((preds, s, p), res)
            res
        
    
    // ######################################################################################################    

    interface ImplicationComputer with 

        member this.TestImplicationOnStep (transitions : Map<int, GuardedUpdate>) (sourcePreds : list<Term<RelVar>>) (s : list<bool>) (p : Term<RelVar>) = 
            swim0.Start()
            // Consider all Vars that could affect the value of p after taking transitions
            let impactingVars = relevantPreVars transitions p.FreeVars

            let relevantPredicates, relevantPredicateSat = 
                List.zip sourcePreds s 
                // Filter out the relevant predicates that actually reason about varaibles that can impact p
                |> List.filter (fun (p, _) -> Set.intersect p.FreeVars impactingVars |> Set.count <> 0)
                |> List.unzip

            // Only check the implication on this smaller set of predicates
            let res = testImplWithMoveOpt1 transitions relevantPredicates relevantPredicateSat p 
            swim0.Stop()
            res

        member this.TestImplication (sourcePreds : list<Term<RelVar>>) (s : list<bool>) (p : Term<RelVar>) = 
            swim1.Start()
            let relevantVars = p.FreeVars
            let relevantPredicates, relevantPredicateSat = 
                List.zip sourcePreds s 
                // Filter out the relevant predicates
                |> List.filter (fun (p, _) -> Set.intersect p.FreeVars relevantVars |> Set.count <> 0)
                |> List.unzip

            let res = testImplWithoutMove relevantPredicates relevantPredicateSat p
            swim1.Stop()
            res
