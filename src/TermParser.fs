module TermParser

open FParsec

open Term

/// Given a parser for variables, construct a parser for SMT Lib formulas
let termParser (varParser : Parser<'a, unit>) = 
    let termParser, termParserRef  = createParserForwardedToRef()
    
    let variableParser =
        varParser
        |>> Var

    let constParser =
        pint64 |>> Const

    let addParser =
        spaces >>. pstring "(+"
        >>.
        (many1 termParser)
        |>> (fun x -> Add(x))
        .>> spaces .>> pchar ')'

    let subParser =
        spaces >>. pstring "(-"
        >>.
        (many1 termParser)
        |>> (fun x ->  
            match x with 
                | [a] -> UMin a
                | [a; b] -> Sub(a, b)
                | _ -> failwith "Not supported"
        )
        .>> spaces .>> pchar ')'

    let mulParser =
        spaces >>. pstring "(*"
        >>.
        (many1 termParser)
        |>> (fun x -> Mul(x))
        .>> spaces .>> pchar ')'

    let parseTrue =
        stringReturn "true" True

    let parseFalse =
        stringReturn "false" False


    let parseEq =
        pstring "(="
        >>.
        pipe2
            termParser
            termParser
            (fun x y -> Eq(x, y))
        .>> spaces .>> pchar ')'


    let parseLe =
        pstring "(<="
        >>.
        pipe2
            termParser
            termParser
            (fun x y -> Le(x, y))
        .>> spaces .>> pchar ')'
    
    let parseLt =
        pstring "(<"
        >>.
        pipe2
            termParser
            termParser
            (fun x y -> Lt(x, y))
        .>> spaces .>> pchar ')'
    
    let parseGe =
        pstring "(>="
        >>.
        pipe2
            termParser
            termParser
            (fun x y -> Ge(x, y))
        .>> spaces .>> pchar ')'
    
    let parseGt =
        pstring "(>"
        >>.
        pipe2
            termParser
            termParser
            (fun x y -> Gt(x, y))
        .>> spaces .>> pchar ')'

    let parseLe =
        pstring "(<="
        >>.
        pipe2
            termParser
            termParser
            (fun x y -> Le(x, y))
        .>> spaces .>> pchar ')'

    let parseAnd =
        spaces >>. pstring "(and"
        >>.
        (many1 termParser)
        |>> (fun x -> And(x))
        .>> spaces .>> pchar ')'

    let parseOr =
        spaces >>. pstring "(or"
        >>.
        (many1 termParser)
        |>> (fun x -> Or(x))
        .>> spaces .>> pchar ')'

    let parseImplies =
        pstring "(=>"
        >>.
        pipe2
            termParser
            termParser
            (fun x y -> Implies(x, y))
        .>> spaces .>> pchar ')'

    let parseIff =
        pstring "(iff"
        >>.
        pipe2
            termParser
            termParser
            (fun x y -> Iff(x, y))
        .>> spaces .>> pchar ')'

    let parseNeg =
        pstring "(not"
        >>.
        termParser
        .>> spaces .>> pchar ')'
        |>> Neg

    let parseIte =
        pstring "(ite"
        >>.
        pipe3
            termParser
            termParser
            termParser
            (fun x y z -> Ite(x, y, z))
        .>> spaces .>> pchar ')'

    let parseLet =
        let parseAssign =
            spaces >>.
            pipe2
                (pchar '(' >>. varParser)
                (spaces >>. termParser)
                (fun x y -> (x, y))
            .>> spaces .>> pchar ')'


        let parseSeq =
            spaces >>. pchar '(' >>.
            many parseAssign
            .>> spaces .>> pchar ')'

        pstring "(let"
        >>. parseSeq
        .>>. termParser
        .>> spaces .>> pchar ')'
        |>> Let

    // Try all available parser and take the first that succeeds. Parsing is easy as the SMTLIB formula is in prefix notation. 
    do termParserRef :=
        spaces >>. choice [ 
            constParser
            addParser
            subParser
            mulParser
            parseTrue
            parseFalse
            parseLe
            parseLt
            parseGe
            parseGt
            parseAnd
            parseOr
            parseImplies
            parseIff
            parseNeg
            parseEq
            parseIte
            parseLet
            variableParser 
        ] .>> spaces

    termParser

/// Given a parser for variables, parses a given string to a term
let parseTerm varParser s = 
    let parser = 
        spaces >>. termParser varParser .>> spaces .>> eof
    let res = run parser s
    match res with
        | Success (res, _, _) -> res
        | Failure (err, _, _) -> failwith err

/// Given a parser for variables, construct a parser for expressions
let expressionParser (varParser : Parser<'a, unit>) = 
    let expParser, expParserRef  = createParserForwardedToRef()

    let variableParser =
        varParser
        |>> EVar

    let constParser =
        pint64 |>> EConst

    let addParser =
        spaces >>. pstring "(+"
        >>.
        (many1 expParser)
        |>> (fun x -> EAdd(x))
        .>> spaces .>> pchar ')'

    let subParser =
        spaces >>. pstring "(-"
        >>.
        (many1 expParser)
        |>> (fun x ->  
            match x with 
                | [a] -> EUMin a
                | [a; b] -> ESub(a, b)
                | _ -> failwith "Not supported"
        )
        .>> spaces .>> pchar ')'

    let mulParser =
        spaces >>. pstring "(*"
        >>.
        (many1 expParser)
        |>> (fun x -> EMul(x))
        .>> spaces .>> pchar ')'
    
    // Try all available parsers 
    do expParserRef :=
        spaces >>. choice [ 
            constParser
            addParser
            subParser
            mulParser
            variableParser 
        ] .>> spaces

    expParser

/// Given a parser for the variables and a string, parse the string to an expression
let parseExpression varParser s =
    let parser = 
        spaces >>. expressionParser varParser .>> spaces .>> eof
    let res = run parser s
    match res with
        | Success (res, _, _) -> res
        | Failure (err, _, _) -> failwith err


/// Given a variable parser, construct a parser for a model returned by Z3
let private modelParser (varParser : Parser<'a, unit>) =
    let definitionParser = 
        spaces >>. pstring "(" .>> spaces .>> pstring "define-fun" >>. spaces >>.
        pipe2
            (varParser .>> spaces .>> pstring "()" .>> spaces .>> pstring "Int")
            (spaces >>. expressionParser varParser)
            (fun x y -> (x, y))
        .>> spaces .>> pstring ")"
        |>> (fun (k, x) -> (k, x.Eval Map.empty))


    spaces >>. pstring "(" >>. spaces >>.  many (definitionParser .>> spaces) .>> spaces .>> pstring ")"
    |>> (fun x -> Map.ofList x)

/// Given a variable parser and a string, parse the string to a model
let parseModel varParser (s : string) = 
        let parser = modelParser varParser .>> spaces .>> eof
        let res = run parser s
        match res with
            | Success (res, _, _) -> res
            | Failure (err, _, _) -> failwith err
