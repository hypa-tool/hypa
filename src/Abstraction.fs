module Abstraction

open Term

type Predicates =
    {
        // The list of predicates that are being tracked
        PredList : list<Term<RelVar>>;
    }

/// A map of locations (in the product) to the predicates being tracked at that location
type PredicateMap = Map<array<int>, Predicates>


/// An abstract state consisting of both a location (in the product) and the satisfaction of each predicate at that location
type AbstractState =
    {
        Locations : array<int>;
        PredicatesSat : list<bool>;
    }

