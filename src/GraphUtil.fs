module GraphUtil

open System
open System.Collections.Generic


/// A simple generic graph representation 
type Graph<'a when 'a: equality> =
    {
        Nodes : seq<'a>;
        Edges : seq<'a * 'a>
    }

    /// For a given target compute all nodes that have some path to that target
    member this.ComputePred (target : seq<'a>) : seq<'a> = 

        let predMap = new Dictionary<'a, HashSet<'a>>() 

        for s in this.Nodes do 
            predMap.Add(s, new HashSet<'a>())

        for (s, t) in this.Edges do 
            predMap.[t].Add s |> ignore


        let q = new Queue<'a>()

        let res = new HashSet<'a>()


        for s in target do 
            q.Enqueue s
            res.Add s |> ignore


        while q.Count <> 0 do
            let s = q.Dequeue()

            for p in predMap.[s] do 
                if res.Contains p |> not then 
                    res.Add p |> ignore
                    q.Enqueue p 

        res