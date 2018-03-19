module Interpreter
open Scanner
open Parser


type Literal =
    | BOOL of bool
    | NUMBER of float
    | STRING of string
    | NIL

let runtimeError m =
    failwith m

type Environment =
    {
    values: Map<string,Literal>;
    enclosing: Environment option;
    }

let initEnvironment enclosing =
    {
    values = [] |> Map.ofSeq
    enclosing = enclosing
    }

let rec lookup (name:identifier_terminal) env = 
    // In the book, this took a TOKEN, but I think this is better.
    if( not (env.values.ContainsKey name.name) )then
        match env.enclosing with
        | Some( env) ->  lookup name env
        | None ->   let msg = sprintf "Undefined variable in lookup: %s" name.name
                    failwith msg
    else 
        (env.values.Item name.name, env)


 
let rec assign (name:identifier_terminal) (value:Literal) ctx =
    if ctx.values.ContainsKey name.name then
        { ctx with values = ctx.values.Add( name.name, value)
        }
    else
        match ctx.enclosing with
        | None -> failwith (sprintf "Undefined variable in assign: %s." name.name)
        | Some( env) -> assign name value env

let define (name:identifier_terminal) value ctx =
    { ctx with values = ctx.values.Add ( name.name, value )
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
        | AssignExpr e ->       let name,ex = e
                                let value, ctx' = evalExpression ex ctx
                                value, assign name value ctx'
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
                                //| _ -> runtimeError ( sprintf" Unsupported operator: %A" op)
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
                            | Parser.IDENTIFIER i -> lookup i ctx
                            | Parser.THIS -> NUMBER 0.0, ctx // TBD
        | GroupingExpr e ->    evalExpression e ctx
        | LogicalExpr e -> let left,op,right = e    
                           let leftValue, ctx' = evalExpression left ctx
                           match op with
                                | AND -> if not (isTruthy leftValue) then  
                                            leftValue, ctx'
                                         else
                                            let rightValue, ctx'' = evalExpression right ctx'
                                            rightValue, ctx''

                                | OR -> if isTruthy leftValue then  
                                            leftValue, ctx'
                                        else
                                            let rightValue, ctx'' = evalExpression right ctx'
                                            rightValue, ctx''


                            
        //| _ -> failwith "Unexpected expression."

let toString lit =
    let result = match lit with
                    | NUMBER n -> string n
                    | STRING s -> s
                    | BOOL b -> string b
                    | NIL -> "NIL"
    result



let rec evalIf condition thenExpr elseExpr lastResult env =
    let lit, env' = evalExpression condition env
    if isTruthy lit then
        execSingleStatement thenExpr lastResult env'
    else
        match elseExpr with
        | Some(stmt) -> execSingleStatement stmt lastResult env'
        | None -> lastResult, env'

and evalWhile condition stmt lastResult env =
    let conditionLiteral, env' = evalExpression condition env
    if isTruthy conditionLiteral then
        let lit, env'' = execSingleStatement stmt lastResult env'
        evalWhile condition stmt lit env''
    else
        // Not really used, but I'd like while loop to return it's last value.
        lastResult, env

and execSingleStatement statement lastResult env =
            match statement with 
                                | Stmt.Expression e -> evalExpression e env
                                | Stmt.Print p ->       let lit, env' = evalExpression p env
                                                        printfn "%s" (toString ( lit))
                                                        (lit, env')
                                | Stmt.Variable (name,None) -> NIL, env
                                | Stmt.Variable (name,Some(expr.PrimaryExpr e)) -> let value, ctx' = evalExpression (PrimaryExpr e) env
                                                                                   value, define name value ctx'  
                                | Stmt.Variable (name,Some(expr.UnaryExpr e)) ->     let value, ctx' = evalExpression (UnaryExpr e) env
                                                                                     value, define name value ctx'  
                                | Stmt.Variable (name,Some(expr.BinaryExpr e)) ->    let value, ctx' = evalExpression (BinaryExpr e) env 
                                                                                     value, define name value ctx'  
                                | Stmt.Variable (name,Some(expr.GroupingExpr e)) ->  let value, ctx' = evalExpression (GroupingExpr e) env
                                                                                     value, define name value ctx'  
                                | Stmt.Variable (name,Some(expr.AssignExpr e)) ->  let value, ctx' = evalExpression (AssignExpr e) env
                                                                                   value, define name value ctx'  
                                | Stmt.Variable (name,Some(expr.LogicalExpr e)) ->  let value, ctx' = evalExpression (LogicalExpr e) env
                                                                                    value, define name value ctx'  
                                | Stmt.Block stms ->    // Exec more statements in child context. (TBD This is much nicer than book!)
                                                        let childEnv = initEnvironment( Some(env) )
                                                        execStatements stms childEnv 
                                | Stmt.If (condition,thenExpr,elseExpr) -> evalIf condition thenExpr elseExpr lastResult env
                                
                                | Stmt.While (condition, stmt) ->   evalWhile condition stmt lastResult env


// Implements the VISITOR pattern from book.
// I want to keep track of the "last" result on BLOCKS and LOOPS -- jorge.
and execStatements( statements:Stmt list) ctx : Literal * Environment =
    match statements with
    | [] -> NIL, ctx
    | s :: xs -> 
        let result, ctx' = execSingleStatement s NIL ctx
                                                                       


#if OLD
                        // TBD Why can't I use Some(expr.Expression e) instead of 4 lines above???
                        | Some( Variable (name,Some(expr.Expression e))) -> evalExpression( e)
#endif
        // TODO: Remove this if you don't want to print intermediate results.
        //printfn "%s" (toString result) |> ignore
        execStatements xs ctx'
        
let interpret (statements:Stmt list) : unit = 
    try
        let ctx = initEnvironment None
        let ctx' = execStatements statements ctx
        ()
    with 
    | :? System.Exception as ex -> runtimeError ex.Message


    // FIB: var a = 0; var b = 1; while (a < 10000) {   print a;  var temp = a;  a = b;  b = temp + b;}