module Interpreter
open Scanner
open Parser

let runtimeError m =
    failwith m

type decl_types = 
    | DECL of function_statement // For lox code    
    | NATIVE of identifier_terminal // For internal functions      

type Literal =
    | BOOL of bool
    | NUMBER of float
    | STRING of string
    | NIL
    | CALL of loxCallable

and Environment =
    {
    values: Map<string,Literal>;
    enclosing: Environment option;
    globals: Environment;
    }

and loxCallable =
    {
        //arity: int;  // TBD: Not like in book, we just calculate this when needed.
        decl: decl_types;
        closure: Environment;
    }

type param = {
    name: identifier_terminal
    value: Literal
    }


// Will create GLOBALs if you pass NONE of enclosing on first call.
let initEnvironment (enclosing:Environment option) =
    match enclosing with 
    | None ->
        let rec newEnv = {
                         values = [] |> Map.ofSeq
                         enclosing = None
                         globals = newEnv // Self-refer to yourself.
                         }
        newEnv
    | Some(enc) ->  {
                    values = [] |> Map.ofSeq
                    enclosing = Some(enc)
                    globals = enc.globals
                    }

let rec lookup (name:identifier_terminal) env = 
    // In the book, this took a TOKEN, but I think this is better.
    if( not (env.values.ContainsKey name.name) )then
        match env.enclosing with
        | Some( env) ->  lookup name env
        | None -> if( not (env.globals.values.ContainsKey name.name)) then
                    let msg = sprintf "Undefined variable in lookup: %s" name.name
                    failwith msg
                  else
                    lookup name env.globals
    else 
        (env.values.Item name.name, env)


 
let rec assign (name:identifier_terminal) (value:Literal) env =
    if env.values.ContainsKey name.name then
        { env with values = env.values.Add( name.name, value) // New map with the updated entry.
        }
    else
        match env.enclosing with
        | None -> failwith (sprintf "Undefined variable in assign: %s." name.name)
        | Some( env') -> assign name value env'

let define (name:identifier_terminal) value env =
    { env with values = env.values.Add ( name.name, value )
    }


let CNUMBER value : float =
    match value with
    | BOOL b -> runtimeError "Operand must be a number."
    | NUMBER f -> f
    | STRING s -> runtimeError "Operand must be a number."
    | NIL -> runtimeError "Operand must be a number."
    | CALL c-> runtimeError "TBD"

let CSTRING value : string =
    match value with
    | BOOL b -> runtimeError "Operand must be a string."
    | NUMBER f -> runtimeError "Operand must be a string."
    | STRING s -> s
    | NIL -> runtimeError "Operand must be a string."
    | CALL c-> runtimeError "TBD"



let isNumbery value =
    match value with
    | BOOL b -> false
    | NUMBER f -> true
    | STRING s -> false
    | NIL -> false
    | CALL c-> runtimeError "TBD"

let isStringy value =
    match value with
    | BOOL b -> false
    | NUMBER f -> false
    | STRING s -> true
    | NIL -> false
    | CALL c-> runtimeError "TBD"

let isTruthy value =
    match value with
    | BOOL b -> b
    | NUMBER f -> not (f = 0.0)
    | STRING s -> (String.length s) > 0
    | NIL -> false
    | CALL c -> runtimeError "TBD"

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
    | CALL f -> runtimeError "- operator does not work on a FUNCTION"


let toString lit =
    match lit with
                    | NUMBER n -> string n
                    | STRING s -> s
                    | BOOL b -> string b
                    | NIL -> "NIL"
                    | CALL c -> match c.decl with 
                                | DECL d -> sprintf "Function(%A)" d.functionName 
                                | NATIVE name -> sprintf "Native(%A)" name
    

// Visitor for expressions
let rec evalExpression (e:expr) env = 
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
                                let value, env' = evalExpression ex env
                                value, assign name value env'
        | BinaryExpr e ->       let left,op,right = e
                                let leftValue, env' = evalExpression left env
                                let rightValue, env'' = evalExpression right env'
                                match op with
                                | ADD_OP MINUS  -> NUMBER (CNUMBER leftValue - CNUMBER rightValue), env''
                                | MULTIPLY_OP DIV -> NUMBER (CNUMBER leftValue / CNUMBER rightValue), env''
                                | MULTIPLY_OP MUL -> NUMBER (CNUMBER leftValue * CNUMBER rightValue), env''
                                | ADD_OP PLUS -> if isStringy leftValue then
                                                     STRING( CSTRING leftValue + CSTRING rightValue), env''
                                                 else 
                                                     NUMBER( CNUMBER leftValue + CNUMBER rightValue), env''
                                | COMPARISON_OP LT -> BOOL( CNUMBER leftValue < CNUMBER rightValue), env''
                                | COMPARISON_OP GT -> BOOL( CNUMBER leftValue > CNUMBER rightValue), env''
                                | COMPARISON_OP LTE -> BOOL( CNUMBER leftValue <= CNUMBER rightValue), env''
                                | COMPARISON_OP GTE -> BOOL( CNUMBER leftValue >= CNUMBER rightValue), env''
                                | EQUALITY_OP NOT_EQUALS -> BOOL( not( isEqual leftValue rightValue)), env''
                                | EQUALITY_OP EQUAL_EQUAL -> BOOL (isEqual leftValue rightValue), env''
                                //| _ -> runtimeError ( sprintf" Unsupported operator: %A" op)
        | UnaryExpr e ->        match e with 
                                | UNARY (op,right) ->   let rv, env' = evalExpression right env
                                                        let lit = match op with
                                                                    | BANG -> BOOL (not (isTruthy rv))
                                                                    | NEGATIVE -> NUMBER (- CNUMBER rv)
                                                        (lit,env')
                                | PRIMARY p -> evalExpression (PrimaryExpr p) env
        | PrimaryExpr e ->  match e with 
                            | Parser.NUMBER n-> NUMBER n.value, env
                            | Parser.STRING s -> STRING s.value, env
                            | Parser.BOOL b -> BOOL b.value, env
                            | Parser.NIL -> NIL, env
                            | Parser.IDENTIFIER i -> lookup i env
                            | Parser.THIS -> NUMBER 0.0, env // TBD
        | GroupingExpr e ->    evalExpression e env
        | LogicalExpr e -> let left,op,right = e    
                           let leftValue, env' = evalExpression left env
                           match op with
                                | AND -> if not (isTruthy leftValue) then  
                                            leftValue, env'
                                         else
                                            let rightValue, env'' = evalExpression right env'
                                            rightValue, env''

                                | OR -> if isTruthy leftValue then  
                                            leftValue, env'
                                        else
                                            let rightValue, env'' = evalExpression right env'
                                            rightValue, env''
        | CallExpr e -> let calleeName, args = e
                        // Evaluate parameters in order

                        // TBD: Can't use map, because need to thread the ENV through (I think env can change???)
                        let rec evalArgsInOrder (newList:Literal list) (args:expr list) (env:Environment) =
                            match args with
                            | [] -> List.rev newList, [], env
                            | arg::xs -> let lit, env' = evalExpression arg env
                                         evalArgsInOrder (lit :: newList) xs env'  

                        let evaluatedArgs, ignore, env1 = evalArgsInOrder [] args env
                        let floxFunction, env2 = evalExpression calleeName env1
                        match floxFunction with 
                                                | CALL c -> let lit, env3 = callFunction c evaluatedArgs env2 
                                                            let updatedCallable = CALL { c with closure = env3}
                                                            match c.decl with
                                                            | DECL decl -> let env4 = assign decl.functionName updatedCallable env3
                                                                           lit, env4
                                                            | _ ->failwith "NATIVE functions cannot be overriden."
                                                | _ -> failwith (sprintf "Can only call functions and classes.: %A" floxFunction)

and evalFor forStmt lastResult env =
    lastResult, env
and evalIf ifs lastResult env =
    let lit, env' = evalExpression ifs.condition env
    if isTruthy lit then
        execSingleStatement ifs.thenBranch lastResult env'
    else
        match ifs.elseBranch with
        | Some(stmt) -> execSingleStatement stmt lastResult env'
        | None -> lastResult, env'

and evalWhile (whileStmt: while_statement) lastResult env =
    let conditionLiteral, env' = evalExpression whileStmt.condition env
    if isTruthy conditionLiteral then
        let lit, env'' = execSingleStatement whileStmt.body lastResult env'
        evalWhile whileStmt lit env''
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
                                | Stmt.Variable (name,Some(expr.PrimaryExpr e)) -> let value, env' = evalExpression (PrimaryExpr e) env
                                                                                   value, define name value env'  
                                | Stmt.Variable (name,Some(expr.UnaryExpr e)) ->     let value, env' = evalExpression (UnaryExpr e) env
                                                                                     value, define name value env'  
                                | Stmt.Variable (name,Some(expr.BinaryExpr e)) ->    let value, env' = evalExpression (BinaryExpr e) env 
                                                                                     value, define name value env'  
                                | Stmt.Variable (name,Some(expr.GroupingExpr e)) ->  let value, env' = evalExpression (GroupingExpr e) env
                                                                                     value, define name value env'  
                                | Stmt.Variable (name,Some(expr.AssignExpr e)) ->  let value, env' = evalExpression (AssignExpr e) env
                                                                                   value, define name value env'  
                                | Stmt.Variable (name,Some(expr.LogicalExpr e)) ->  let value, env' = evalExpression (LogicalExpr e) env
                                                                                    value, define name value env'  
                                | Stmt.Variable (name,Some(expr.CallExpr e)) ->  let value, env' = evalExpression (CallExpr e) env
                                                                                 value, define name value env'  
                                | Stmt.Block stms ->    // Exec more statements in child context. (TBD This is much nicer than book!)
                                                        let childEnv = initEnvironment (Some(env))
                                                        execStatements stms NIL childEnv 

#if BAD
    TBD: Not compile  using 'Record Pattern                              | Stmt.If { if_statement.condition = condition;
                                            if_statement.thenExpr = thenExpr;
                                            if_statement.elseExpr = elseExpr; } -> evalIf condition thenExpr elseExpr lastResult env
#endif
                                | Stmt.If ifs -> evalIf ifs lastResult env
                                | Stmt.ForStmt forStmt -> evalFor forStmt lastResult env
                                | Stmt.While whileStmt ->   evalWhile whileStmt lastResult env
                                | Stmt.FunctionStmt funcStmt ->     // Interpreting a function definition adds it to the environment.
                                                                    // TBD: COuld be cleaner.
                                                                    let (c:loxCallable) = { decl = DECL funcStmt; closure = env } // Is this the right env? Won't have function name in it, yet. 
                                                                    NIL, define funcStmt.functionName (CALL c) env
                                | Stmt.ReturnStmt returnStmt -> // We return values back through call stack instead of THROW that book uses.
                                                                evalExpression returnStmt.value env


// Implements the VISITOR pattern from book.
// I want to keep track of the "last" result on BLOCKS and LOOPS -- jorge.
and execStatements( statements:Stmt list) (lastReturn:Literal) env : Literal * Environment =
    match statements with
    | [] -> lastReturn, env
    | s :: xs -> 
        let result, ctx' = execSingleStatement s NIL env
        // TODO: Remove this if you don't want to print intermediate results.
        //printfn "%s" (toString result) |> ignore
        execStatements xs result ctx'

// TBD: I think I have the definition of ARGS and PARAMs reversed.
and callFunction (c:loxCallable) (args:Literal list) (env:Environment) : Literal * Environment  =
    let (lit:Literal), childEnvRet  = match c.decl with
                                    | NATIVE n -> match n.name with 
                                                  | "clock" -> STRING (System.DateTime.Now.ToString("")), env
                                                  | _ -> failwith "Unknown native function."
                                    | DECL decl -> 
                                        let rec evalParamsInOrder (parameters: identifier_terminal list) (args: Literal list) (env:Environment) =
                                            if (List.length parameters) <> (List.length args) then   
                                                failwith "Unexpected number of arguments to function." // Book does not have. May be impossible.
                                            else
                                                // Assume args and params in same order
                                                match args with 
                                                | arg::xsArg -> match parameters with 
                                                                 | par::xsPar -> let env' = define par arg env
                                                                                 evalParamsInOrder xsPar xsArg env'
                                                            
                                                                 | _ -> failwith "impossible case"
                                                | [] -> env // Break recursion

                                        //let childEnv = initEnvironment ( Some( env.globals)) // New Environment with globals in it.
                                        let childEnv = { c.closure with enclosing = Some(env) }
                                        let childEnv2 = evalParamsInOrder  decl.parameters args childEnv
                                        execStatements [decl.body] NIL childEnv2
    lit, env // childEnv' <- Changed to try to get closures to work.

        
let interpret (statements:Stmt list) : unit = 
    try
        let env = initEnvironment None

        let clockIdentifier : identifier_terminal = { name = "clock" }
        let clock: loxCallable = { decl = NATIVE clockIdentifier; closure=env;  }
        let clockLit = CALL clock 
        let ctx' = { env with globals = define clockIdentifier clockLit env.globals }
        let ctx'' = execStatements statements NIL ctx'
        ()
    with 
    | :? System.Exception as ex -> runtimeError ex.Message

    // Recursive count: fun count(n) { if(n>1) count(n-1); print n;} count(3);
    // FIB: var a = 0; var b = 1; while (a < 10000) {   print a;  var temp = a;  a = b;  b = temp + b;}

    // fun f(a,b) { print a+b;} f(1,2);

    //fun makeCounter() {   var i = 0;   fun count() {     i = i + 1;     print i;   }   return count; } var counter = makeCounter(); counter(); counter(); // "1" then "2".
