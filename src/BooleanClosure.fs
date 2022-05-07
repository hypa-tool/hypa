module BooleanClosure 

open System 
open System.Collections.Generic

open Util
open Term
open DNF

let swtotal = System.Diagnostics.Stopwatch()
let sw1 = System.Diagnostics.Stopwatch()
let sw2 = System.Diagnostics.Stopwatch()
let sw3 = System.Diagnostics.Stopwatch()

/// Given a set of terms and a term p, tries to represent p as a boolean combination of the given list of terms (as a DNF) by iterating over all disjuncts
let private computeDnfNaive (predicates : list<Term<RelVar>>) (p : Term<RelVar>) =
    
    if SMTUtil.isValid p (fun (n, i) -> n + "_" + string(i)) (fun _ -> INT) then 
        // p = T, so return DNF for true, i.e., all clauses

        let allClauses = 
            Util.computeBooleanPowerSet predicates.Length
            |> Seq.map (fun x -> 
                x
                |> List.mapi (fun i b -> if b then POS i else NEG i)
                |> set
                )
                
        {DNF.DNF.Clauses = allClauses}
        |> Some
    elif SMTUtil.isValid (Term.Neg p) (fun (n, i) -> n + "_" + string(i)) (fun _ -> INT) then 
        // p = false, return the empty DNF
        {DNF.DNF.Clauses = Seq.empty} |> Some
    else 
        swtotal.Start()

        sw1.Start()

        // ====================================
        // STEP 1 - Compute all conjuncts that imply the formula and collect them
        let dnf = new HashSet<_>()
        for comb in Util.computeBooleanPowerSet (List.length predicates) do

            let conjunction =
                List.zip predicates comb
                |> List.map (fun (x, b) -> if b then x else Term.Neg x)
                |> Term.And

            // Check if conjunction -> p
            let query = Term.Implies (conjunction, p)
            
            if SMTUtil.isValid query (fun (n, i) -> n + "_" + string(i)) (fun _ -> INT) then
                let tv = List.map (fun x -> if x then TOP else BOT) comb
                dnf.Add tv |> ignore

        sw1.Stop()

        // ====================================
        // STEP 2 - Try to make the formula small, i.e., express it with as few disjunct as possible. We do this by merging disjunct together if they differ it at most one location

        sw2.Start()

        /// Check if two lists differ in at most one position
        let differAtMostOnce l1 l2 =
            let rec countDiffsRec l1 l2 a = 
                match l1, l2 with
                    | [], [] -> true
                    | x::xs, y::ys -> 
                        if x = y then 
                            countDiffsRec xs ys a 
                        else
                            if a >= 1 then 
                                false
                            else 
                                countDiffsRec xs ys (a+1)
                    | _ -> failwith "Impossible"
            countDiffsRec l1 l2 0

        // We iteratively merge two disjuncts that disagree in at most one position

        let mutable foundNewCombination = true

        while foundNewCombination do
            let res =
                Seq.allPairs dnf dnf
                |> Seq.tryFind (fun (x, y) -> x <> y && differAtMostOnce x y)

            match res with
                | None ->
                    // Can terminate now, found minimal model as there are no further merges possible
                    foundNewCombination <- false
                | Some (c1, c2) ->
                    // We found tow disjuncts that can be merged
                    // Find the index where they differ
                    let index = List.findIndex (fun (x, y) -> x <> y) (List.zip c1 c2)

                    // Replace the index where they differ with a DASH (aka the do not care value)
                    let newC = List.mapi (fun i x -> if i = index then DASH else x) c1

                    dnf.Remove c1 |> ignore
                    dnf.Remove c2 |> ignore
                    dnf.Add newC |> ignore

        sw2.Stop()

        // ====================================
        // STEP 3 Convert from ThreeValuedList to a DNFClause by ignoring all dashes

        let candidateDNF = 
            dnf
            |> Seq.map (fun x -> 
                x
                |> Seq.indexed
                |> Seq.choose (fun (i, y) -> match y with DASH -> None | TOP -> Some (POS i) | BOT -> Some (NEG i) )
                |> set
                )

        // ====================================
        // STEP 4 - Check if the model identified is equivalent to p, i.e., is implied by p (it implies p by construction)
        sw3.Start()

        let disjunction = 
            candidateDNF
            |> Seq.map (fun clause ->
                clause
                |> Set.map (fun x ->
                    match x with 
                        | POS i -> predicates.[i]
                        | NEG i -> Term.Neg predicates.[i]
                    )
                |> Seq.toList
                |> Term.And
                )
            |> Seq.toList
            |> Term.Or

        // Check if p -> disjunction
        let query = Term.Implies(p, disjunction)
        
        let res = 
            if SMTUtil.isValid query (fun (n, i) -> n + "_" + string(i)) (fun _ -> INT) then
                // p is a boolean combination and candidateDNF a minimal DNF
                Some {Clauses = candidateDNF }
            else
                // p is no boolean combination of the provided list of predicates
                None

        sw3.Stop()
        swtotal.Stop()
        
        res

/// Given a set of terms and a term p, tries to represent p as a boolean combination of the given list of terms (as a DNF).
/// Returns None if p is not in the Boolean Closure of the terms
let computeDNF (predicates : list<Term<RelVar>>) (p : Term<RelVar>) =

    let varsInP = p.FreeVars

    // We index and filter out those predicates that use variables occuring in p
    // The indexing is used to map the returned DNF back to one used in the original predicate list
    let indexedPredicates =
        predicates
        |> List.indexed
        |> List.filter (fun (_, v) -> Set.count(Set.intersect v.FreeVars varsInP) <> 0)
        
    let relevantPredicates = 
        indexedPredicates
        |> List.map (fun (_, v) -> v)

    match computeDnfNaive relevantPredicates p  with
        | None -> None 

        | Some dnf ->
            // Match the indices back to the original list of predicates
            let rematchIndex i = 
                fst indexedPredicates.[i]
            Some (dnf.RemapIndices rematchIndex)


