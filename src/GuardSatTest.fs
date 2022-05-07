module GuardSatTest

open System.Collections.Generic

open Term
open TransitionSystem
open SuccessorHelper

type GuardSatComputerDNF(tslist : list<TransitionSystem>, stateSatComputer : StateSatComputer, implicationComputer : ImplicationComputer) = 

    let vars = 
        tslist
        |> List.map (fun x -> x.Vars)

    
    let hasher = new Dictionary<_,_>()

    /// Checks if collection of guards can be satsfied in a given abstract state 
    let canGuardsBeSat (preds : list<Term<RelVar>>) (s : list<bool>) (guards : Map<int, Term<SingleVar>>) =
        
        if hasher.ContainsKey (preds, s, guards) then 
            hasher.[(preds, s, guards)]
        else 

            let predSatTerm = 
                SMTUtil.encodeAbstractStateSatisfaction preds s

            let guardsTerm =
                guards
                |> Map.toList
                |> List.map (fun (i, t) -> t.ReplaceVars (fun n -> (n, i)) )
                |> Term.And
            
            // Build and solve SMT query
            let res =
                let conjunction = Term.And [predSatTerm; guardsTerm]

                SMTUtil.isSat conjunction (fun (n, i) -> n + "_" + string(i)) (fun (n, i) -> vars.[i].VarType n)

            hasher.Add((preds, s, guards), res)
            res


    interface GuardSatComputer with 
        member this.CanGuardsBeSat (preds : list<Term<RelVar>>) (s : list<bool>) (guards : Map<int, Term<SingleVar>>) =

            let guardsAsSeq = Map.toSeq guards

            // Before doing the direct check, we check implication for each of the guards
            let implicationResult = 
                guardsAsSeq
                |> Seq.map (fun (i,x) -> x.ReplaceVars (fun n -> n, i))
                |> Seq.map (fun x -> implicationComputer.TestImplication preds s x)

            if Seq.contains ImplicationStatus.NEG implicationResult then 
                // At least one of the guards is negatively implied, so the guards can not be sat
                false 
            else 
                // We filter out those guards for which the implication was indecisive (i.e., NEITHER)
                // All positive implications can be ignored as they are always satisfied
                let relevantGuardMap = 
                    Seq.zip guardsAsSeq implicationResult
                    // We filter out those that we do not know yet. There is no NEG and all POS can be dropped
                    |> Seq.filter (fun (_, r) -> r = ImplicationStatus.NEITHER)
                    |> Seq.map fst
                    |> Map.ofSeq

                let relevantVars = 
                    relevantGuardMap
                    |> Map.toSeq
                    |> Seq.map (fun (i, t) -> t.ReplaceVars (fun n -> (n, i)) )
                    |> Seq.map (fun x -> x.FreeVars)
                    |> Set.unionMany

                // We restrict to those predicates that are relevant for the guards
                let relevantPredicates, relevantPredicateSat = 
                    List.zip preds s 
                    // Filter out the relevant predicates
                    |> List.filter (fun (p, _) -> Set.intersect p.FreeVars relevantVars |> Set.count <> 0)
                    |> List.unzip 

                canGuardsBeSat relevantPredicates relevantPredicateSat relevantGuardMap
