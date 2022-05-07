module DNF

/// A single literal in a a DNF.
/// The index refers to the position in a predicate vector
type DNFLiteral = 
    | POS of int 
    | NEG of int

    member this.Var =
        match this with
            | POS i | NEG i -> i 

    member this.IsSat (a : list<bool>) =
        match this with
            | POS i -> a.[i]
            | NEG i -> not a.[i]

    member this.RemapIndices (m : int -> int) = 
        match this with
            | POS i -> POS (m i)
            | NEG i -> NEG (m i)
    
/// A DNF Clause is a set (conjunction) of literals
type DNFClause = Set<DNFLiteral>

/// Evaluate a clause on an assignment
let private evalClause (clause : DNFClause) (a : list<bool>) = 
    clause
    |> Set.forall (fun x -> x.IsSat a) 

/// A NDF is a seq (disjunction) of clauses
type DNF = 
    {
        Clauses : seq<DNFClause>
    }

    /// Check if this DNF is sat by a given assignment
    member this.IsSat (a : list<bool>) =
        this.Clauses
        |> Seq.exists (fun c -> evalClause c a)

    /// Map the indices of the DNF
    member this.RemapIndices (m : int -> int) = 
        {
            Clauses =
                this.Clauses
                |> Seq.map (Set.map (fun l ->l.RemapIndices m))
        }