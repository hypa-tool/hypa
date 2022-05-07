module GlobalConstants

type VerbosityLevel =  
    | ResultOnly
    | OutputForPaper
    | EachStep
    | DebugOutput


let mutable verboseLevel : list<VerbosityLevel> = []

// Determines which solver should be used to verify \forall^*\exists^* properties. 
let mutable gameSolver = Util.GameSolverType.NAIVE

// The main path where all intermediate outputs are written to. By default this is the current directory. 
let mutable tempPath = "./"

// The path to the Z3 executable
let mutable z3Path = ""

// Print the game and spoiling strategy as a DOT graph. Used for debugging only
let mutable printGameAndStrategyAsDotGraph = false