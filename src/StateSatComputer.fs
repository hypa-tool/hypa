module StateSatComputer

open System.Collections.Generic

open Term
open Abstraction
open TransitionSystem
open SuccessorHelper

let swtotal = System.Diagnostics.Stopwatch()
let swmodel = System.Diagnostics.Stopwatch()
let c = Util.Counter()

type StateSatComputerDirect(tlist : list<TransitionSystem>) =

    // hashes satisfiable and unsatisfiable instances
    let unsatHash = new HashSet<list<Term<RelVar> * bool>>()
    let satHash = new HashSet<list<Term<RelVar> * bool>>()

    // Hasher dictionary for models
    let modelHasher = new Dictionary<_,_>()

    /// Checks if a given abstract state is satisfiable
    let checkSat (preds : list<Term<RelVar>>) (s : list<bool>) =
            swtotal.Start()
            c.Inc()
            let zipped = List.zip preds s

            let res = 
                if satHash.Contains zipped then
                    true
                else
                    if Seq.exists (fun x -> unsatHash.Contains x) (Util.listPrefixes zipped) then
                        // A prefix is already unsat so this formula is also unsat
                        false
                    else
                        let varStringer (n, i) =
                            n + "_" + string(i)

                        let phi = 
                            SMTUtil.encodeAbstractStateSatisfaction preds s

                        if SMTUtil.isSat phi varStringer (fun (n, i) -> tlist.[i].Vars.VarType n) then 
                            satHash.Add zipped |> ignore
                            true
                        else 
                            unsatHash.Add zipped |> ignore
                            false
            swtotal.Stop()
            res

    // Get models of a given abstract state that additinally satisfies additional conditions (guards)
    let getModelGuarded (preds : list<Term<RelVar>>) (s : list<bool>) (guards : list<Term<RelVar>>) (vars : Set<RelVar>) =
            swmodel.Start()
            c.Inc()
            let zipped = List.zip preds s

            let res = 
                if modelHasher.ContainsKey (zipped, guards, vars) then
                    modelHasher.[(zipped, guards, vars)]
                else
                    // Build conjunction of abstract states and additional formulas
                    let phi = 
                        Term.And ((SMTUtil.encodeAbstractStateSatisfaction preds s) :: guards)

                    let varStringer (n, i) =
                            n + "_" + string(i)

                    let res = 
                        SMTUtil.getModels phi vars varStringer (fun (n, i) -> tlist.[i].Vars.VarType n)
                        |> Option.map (List.map (fun x -> {Model.Assignments = x}))

                    modelHasher.Add((zipped, guards, vars), res)
                    res

            swmodel.Stop()
            res

    interface StateSatComputer with 
        member this.CheckSat (preds : list<Term<RelVar>>) (s : list<bool>) =
            checkSat preds s

        member this.CheckSatMap (predMap : PredicateMap) (astate : AbstractState) =
            checkSat predMap.[astate.Locations].PredList astate.PredicatesSat

        member this.GetModel (preds : list<Term<RelVar>>) (s : list<bool>) (vars : Set<RelVar>) =
            getModelGuarded preds s List.empty vars

        member this.GetModelGuarded (preds : list<Term<RelVar>>) (s : list<bool>) (guards : list<Term<RelVar>>) (vars : Set<RelVar>) =
            getModelGuarded preds s guards vars



