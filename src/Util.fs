module Util

open System

type ThreeValued = TOP | BOT | DASH

type GameSolverType =  NAIVE | LAZY

let rec concreteBool (a : list<ThreeValued>) =
    match a with    
        | [] -> Seq.singleton []
        | x::xs -> 
            let recRes = concreteBool xs
            match x with 
                | TOP -> Seq.map (fun l -> true::l) recRes
                | BOT -> Seq.map (fun l -> false::l) recRes
                | DASH -> Seq.append (Seq.map (fun l -> true::l) recRes) (Seq.map (fun l -> false::l) recRes)

type Counter(init : int) =
    let mutable a = init

    new () = Counter(0)

    member this.Reset() =   
        a <- 0

    member this.Get = a

    member this.Inc() =
        a <- a + 1

    member this.Inc(x) =
        a <- a + x
    
    member this.Dec() =
        a <- a - 1

    member this.Dec(x) =
        a <- a - x

/// Compute the cartesian product of a list of sets
let rec cartesian (lstlst : list<Set<'a>>) =
    match lstlst with
        | [] -> List.singleton []
        | x::xs ->  
            [for p in cartesian xs  do for a in x do a::p]


/// Compute the cartesian product of maps
let rec cartesianMap (m : Map<'a, Set<'b>>) =
    if Map.isEmpty m then
        Seq.singleton Map.empty
    else
        let k, v = m |> Map.toSeq |> Seq.find (fun _ -> true)

        let recRes = cartesianMap (Map.remove k m)

        seq {
            for m' in recRes do
                for l in v do
                    Map.add k l m'
        }

/// Compute all prefixes of a list
let listPrefixes l =
    seq {for i in List.length l - 1..-1..-1 do l.[0..i]}
    

/// Compute the powerset for a given set
let computePowerSet (s : Set<'a>) =
    let asList = Set.toList s 

    let rec computeFiniteChoices (A : list<'a>) =
        match A with
            | [] -> Seq.singleton Set.empty
            | x::xs ->
                let r = computeFiniteChoices xs
                Seq.append (Seq.map (fun y -> Set.add x y) r) r

    computeFiniteChoices asList

/// Given a number n, compute the set of all boolean lists of length n
let rec computeBooleanPowerSet n =
    if n = 0 then
        Seq.singleton []
    else
        let r = computeBooleanPowerSet (n-1)
        Seq.append (Seq.map (fun x -> true::x) r) (Seq.map (fun x -> false::x) r)
