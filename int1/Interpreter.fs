module Interpreter
open Parser

type Literal =
    | BOOL of bool
    | NUMBER of float
    | STRING of string
    | NIL

let runtimeError m =
    failwith m


let CNUMBER value : float =
    match value with
    | BOOL b -> runtimeError "Operand must be a number."
    | NUMBER f -> f
    | STRING s -> runtimeError "Operand must be a number."
    | NIL -> runtimeError "Operand must be a number."

let CSTRING value : string =
    match value with
    | BOOL b -> runtimeError "Operand must be a string."
    | NUMBER f -> runtimeError "Operand must be a string."
    | STRING s -> s
    | NIL -> runtimeError "Operand must be a string."



let isNumbery value =
    match value with
    | BOOL b -> false
    | NUMBER f -> true
    | STRING s -> false
    | NIL -> false

let isStringy value =
    match value with
    | BOOL b -> false
    | NUMBER f -> false
    | STRING s -> true
    | NIL -> false

let isTruthy value =
    match value with
    | BOOL b -> b
    | NUMBER f -> not (f = 0.0)
    | STRING s -> (String.length s) > 0
    | NIL -> false

let isEqual left right =
    match left, right with
    | NIL, NIL ->  true
    | NIL, _ -> false
    | BOOL a, BOOL b -> a=b
    | NUMBER a, NUMBER b -> a=b
    | STRING a, STRING b -> a=b
    | _ -> false
        

let negative value =
    match value with
    | BOOL b -> runtimeError "- operator does not work on bool"
    | NUMBER f -> NUMBER -f
    | STRING s -> runtimeError "- operator does not work on string"
    | NIL -> runtimeError "- operator does not work on NIL"

let rec evalExpression (e:expr) : Literal  =
    match e with 
#if OLD
        | EqualityExpr (c, more) -> prettyPrint (ComparisonExpr c)
                                    match more with
                                        | MORE z -> 
                                            match z.Head with 
                                                | op , cmp ->
                                                        printfn "%A" op
                                                        prettyPrint (ComparisonExpr cmp)
                                        | ZERO -> ()
        | ComparisonExpr (a, more) -> prettyPrint  (AdditionExpr a)
                                      match more with
                                            | MORE z -> 
                                                match z.Head with 
                                                    | op , add ->
                                                            printfn "%A" op
                                                            prettyPrint (AdditionExpr add)
                                            | ZERO -> ()
        | AdditionExpr (e, more) -> prettyPrint  (MultiplicationExpr e)
                                    match more with
                                        | MORE z -> 
                                            match z.Head with 
                                                | op , mul ->
                                                        printfn "%A" op
                                                        prettyPrint (MultiplicationExpr mul)
                                        | ZERO -> ()
        | MultiplicationExpr (e, more) -> prettyPrint  (UnaryExpr e)
                                          match more with
                                                | MORE z -> 
                                                    match z.Head with 
                                                        | op , un ->
                                                                printfn "%A" op
                                                                prettyPrint (UnaryExpr un)
                                                | ZERO -> ()
#endif
        | BinaryExpr e ->       let left,op,right = e
                                let leftValue = evalExpression left
                                let rightValue = evalExpression right
                                match op with
                                | ADD_OP MINUS  -> NUMBER (CNUMBER leftValue - CNUMBER rightValue)
                                | MULTIPLY_OP DIV -> NUMBER (CNUMBER leftValue / CNUMBER rightValue)
                                | MULTIPLY_OP MUL -> NUMBER (CNUMBER leftValue * CNUMBER rightValue)
                                | ADD_OP PLUS -> if isStringy leftValue then
                                                     STRING( CSTRING leftValue + CSTRING rightValue)
                                                 else 
                                                     NUMBER( CNUMBER leftValue + CNUMBER rightValue)
                                | COMPARISON_OP LT -> BOOL( CNUMBER leftValue < CNUMBER rightValue) 
                                | COMPARISON_OP GT -> BOOL( CNUMBER leftValue > CNUMBER rightValue) 
                                | COMPARISON_OP LTE -> BOOL( CNUMBER leftValue <= CNUMBER rightValue) 
                                | COMPARISON_OP GTE -> BOOL( CNUMBER leftValue >= CNUMBER rightValue) 
                                | EQUALITY_OP NOT_EQUALS -> BOOL( not( isEqual leftValue rightValue))
                                | EQUALITY_OP EQUAL_EQUAL -> BOOL (isEqual leftValue rightValue)
                                | _ -> runtimeError "Unsupported operator: %A" op
        | UnaryExpr e ->        match e with 
                                | UNARY (op,right) ->   let rv = evalExpression right
                                                        match op with
                                                        | BANG -> BOOL (not (isTruthy rv))
                                                        | NEGATIVE -> NUMBER (- CNUMBER rv)
                                | PRIMARY p -> evalExpression (PrimaryExpr p)
        | PrimaryExpr e ->  match e with 
                            | Parser.NUMBER n-> NUMBER n.value
                            | Parser.STRING s -> STRING s.value
                            | Parser.BOOL b -> BOOL b.value
                            | Parser.NIL -> NIL
                            | Parser.IDENTIFIER i -> NUMBER 0.0 // TBD IDENTIFIER i.name
                            | Parser.THIS -> NUMBER 0.0 // TBD
        | GroupingExpr e ->    evalExpression e
        //| _ -> failwith "Unexpected expression."

let toString lit =
    let result = match lit with
    | NUMBER n -> string n
    | STRING s -> s
    | BOOL b -> string b
    | NIL -> "NIL"
    result

let rec execStatements( statements:Stmt option list) =
    match statements with
    | [] -> ()
    | s :: xs -> 
        let result = match s with 
                        | None -> NIL
                        | Some( Stmt.Expression e) -> evalExpression e 
                        | Some( Stmt.Print p) -> evalExpression p
                        | Some( Stmt.Variable (name,None)) -> NIL
                        | Some( Stmt.Variable (name,Some(expr.PrimaryExpr e))) -> evalExpression (PrimaryExpr e)
                        | Some( Stmt.Variable (name,Some(expr.UnaryExpr e))) -> evalExpression (UnaryExpr e)
                        | Some( Stmt.Variable (name,Some(expr.BinaryExpr e))) -> evalExpression (BinaryExpr e)
                        | Some( Stmt.Variable (name,Some(expr.GroupingExpr e))) -> evalExpression (GroupingExpr e)
#if OLD
                        // TBD Why can't I use Some(expr.Expression e) instead of 4 lines above???
                        | Some( Variable (name,Some(expr.Expression e))) -> evalExpression( e)
#endif

        printfn "%s" (toString result) |> ignore
        execStatements xs
        
let interpret (statements:Stmt option list) : unit = 
    try
        execStatements statements
    with 
    | :? System.Exception as ex -> runtimeError ex.Message
