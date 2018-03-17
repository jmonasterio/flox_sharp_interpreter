module Interpreter
open Parser


type Literal =
    | BOOL of bool
    | NUMBER of float
    | STRING of string
    | NIL

let runtimeError m =
    failwith m

type InterpreterContext =
    {
    values: Map<string,Literal>;
    }

let initInterpreterContext =
    {
    values = [] |> Map.ofSeq
    }


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

let rec evalExpression (e:expr) ctx = //: (Literal, InterpreterContext) =
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
                                let leftValue, ctx' = evalExpression left ctx
                                let rightValue, ctx'' = evalExpression right ctx'
                                match op with
                                | ADD_OP MINUS  -> NUMBER (CNUMBER leftValue - CNUMBER rightValue), ctx''
                                | MULTIPLY_OP DIV -> NUMBER (CNUMBER leftValue / CNUMBER rightValue), ctx''
                                | MULTIPLY_OP MUL -> NUMBER (CNUMBER leftValue * CNUMBER rightValue), ctx''
                                | ADD_OP PLUS -> if isStringy leftValue then
                                                     STRING( CSTRING leftValue + CSTRING rightValue), ctx''
                                                 else 
                                                     NUMBER( CNUMBER leftValue + CNUMBER rightValue), ctx''
                                | COMPARISON_OP LT -> BOOL( CNUMBER leftValue < CNUMBER rightValue), ctx''
                                | COMPARISON_OP GT -> BOOL( CNUMBER leftValue > CNUMBER rightValue), ctx''
                                | COMPARISON_OP LTE -> BOOL( CNUMBER leftValue <= CNUMBER rightValue), ctx''
                                | COMPARISON_OP GTE -> BOOL( CNUMBER leftValue >= CNUMBER rightValue), ctx''
                                | EQUALITY_OP NOT_EQUALS -> BOOL( not( isEqual leftValue rightValue)), ctx''
                                | EQUALITY_OP EQUAL_EQUAL -> BOOL (isEqual leftValue rightValue), ctx''
                                | _ -> runtimeError "Unsupported operator: %A" op
        | UnaryExpr e ->        match e with 
                                | UNARY (op,right) ->   let rv, ctx' = evalExpression right ctx
                                                        let lit = match op with
                                                                    | BANG -> BOOL (not (isTruthy rv))
                                                                    | NEGATIVE -> NUMBER (- CNUMBER rv)
                                                        (lit,ctx')
                                | PRIMARY p -> evalExpression (PrimaryExpr p) ctx
        | PrimaryExpr e ->  match e with 
                            | Parser.NUMBER n-> NUMBER n.value, ctx
                            | Parser.STRING s -> STRING s.value, ctx
                            | Parser.BOOL b -> BOOL b.value, ctx
                            | Parser.NIL -> NIL, ctx
                            | Parser.IDENTIFIER i -> NUMBER 0.0, ctx // TBD IDENTIFIER i.name
                            | Parser.THIS -> NUMBER 0.0, ctx // TBD
        | GroupingExpr e ->    evalExpression e ctx
        //| _ -> failwith "Unexpected expression."

let toString lit =
    let result = match lit with
    | NUMBER n -> string n
    | STRING s -> s
    | BOOL b -> string b
    | NIL -> "NIL"
    result

let rec execStatements( statements:Stmt option list) ctx =
    match statements with
    | [] -> ()
    | s :: xs -> 
        let result, ctx' = match s with 
                        | None -> NIL, ctx
                        | Some( Stmt.Expression e) -> evalExpression e ctx
                        | Some( Stmt.Print p) -> evalExpression p ctx
                        | Some( Stmt.Variable (name,None)) -> NIL, ctx
                        | Some( Stmt.Variable (name,Some(expr.PrimaryExpr e))) -> evalExpression (PrimaryExpr e) ctx
                        | Some( Stmt.Variable (name,Some(expr.UnaryExpr e))) -> evalExpression (UnaryExpr e) ctx
                        | Some( Stmt.Variable (name,Some(expr.BinaryExpr e))) -> evalExpression (BinaryExpr e) ctx 
                        | Some( Stmt.Variable (name,Some(expr.GroupingExpr e))) -> evalExpression (GroupingExpr e) ctx
#if OLD
                        // TBD Why can't I use Some(expr.Expression e) instead of 4 lines above???
                        | Some( Variable (name,Some(expr.Expression e))) -> evalExpression( e)
#endif

        printfn "%s" (toString result) |> ignore
        let ctx'' = execStatements xs ctx'
        ctx''


        
let interpret (statements:Stmt option list) : unit = 
    try
        let ctx = initInterpreterContext
        let ctx' = execStatements statements ctx
        ()
    with 
    | :? System.Exception as ex -> runtimeError ex.Message
