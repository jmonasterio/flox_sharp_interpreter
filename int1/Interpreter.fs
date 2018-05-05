module Interpreter
//open Scanner
open Parser
open System.Linq

//type UniqueId = System.Guid // Added by the resolver pass, later.

let runtimeError m =
    failwith m

type ResolveDistance = int

type ResolveDistanceTarget = {
    dist: ResolveDistance;
    id: identifier_terminal; // Just here to make debugging easier.
}


type ScopeDistanceMap = Map<UniqueId,ResolveDistanceTarget>

type decl_types = 
    | DECL of function_statement // For lox code    
    | NATIVE of identifier_terminal // For internal functions      

type Literal =
    | BOOL of bool
    | NUMBER of float
    | STRING of string
    | NIL
    | CALL of loxCallable
    | CLASS of loxClass
    | INSTANCE of loxInstance
    | METHOD of loxFunction // TBD: Not in book
    | FUNCTION of loxFunction // TBD: Not in book

and LiteralMap = Map<IdentifierName,Literal>

and ClosureKey = UniqueId
and ClosureMap = Map<ClosureKey,LoxEnvironment list>
and FieldMap = Map<IdentifierName,Literal>
and MethodMap = Map<IdentifierName,loxFunction>

and LoxEnvironment =
    {
    values: LiteralMap; //  variable name -> literal
    enclosing: LoxEnvironment option;
    }

and Environment =
    {
    localDistances: ScopeDistanceMap; // distance back from current scope to scope that has the value
    localScopes: LoxEnvironment list
    closures: ClosureMap; // need some indirection to the closures.
    globalScope: LoxEnvironment
    }

and loxCallable =
    {
        //arity: int;  // TBD: Not like in book, we just calculate this when needed.
        decl: decl_types;
        closureKey: ClosureKey;
    }

and loxClass = // 12.1
    {
        id: IdentifierName
        mutable methods: MethodMap
        arity: int;
    }

and loxInstance = // 12.2
    {
        klass: loxClass
        mutable fields: FieldMap // TBD: Horrible. Shoule be kept in ENV instead of part of state of loxInstance.
    }

and loxFunction =
    {
        method: function_statement
        closure: Environment
    }

let findMethod (inst:loxInstance) (id:identifier_terminal) =
    inst.klass.methods.TryFind id.name 

// Can return a "field" or a "property" or a "method".
let getField (inst:loxInstance) (id:identifier_terminal) =
    match inst.fields.TryFind id.name with
    | Some(lit) -> lit
    | None -> match findMethod inst id with
                | Some(meth) -> METHOD meth
                | None -> failwith (sprintf "Undefined property: %A" id.name)

let setField (inst:loxInstance) (id:identifier_terminal) (value:Literal) =
    let newMap = inst.fields.Add( id.name, value)
    inst.fields <- newMap
    value


// TBD: Kinda sucks that these can't be in the resolver.

let emptyMap<'K,'V when 'K : comparison >(): Map<'K,'V>  = [] |> Map.ofSeq

let pushScope newScope (env:Environment) =
    { env with localScopes = newScope :: env.localScopes }

let pushNewScope (env:Environment) =
    let newScope = { values = emptyMap(); enclosing = None } //; enclosing = Some(env.localScopes.Head); }
    pushScope newScope env

let popScope env =
    match env.localScopes with
    | [] -> failwith "Nothing to pop!"
    | _::rest -> { env with localScopes = rest }

let rec ancestor dist scopes =
    match List.tryItem  dist scopes with
        | Some enc -> enc
        | _ -> failwith "ancestor not found."

let findScopeAtLocalDistance (id:identifier_terminal) env =
    match env.localDistances.TryFind id.guid with
    | Some(rdt) -> ancestor (rdt.dist) env.localScopes 
    | None -> env.globalScope

type param = {
    name: identifier_terminal
    value: Literal
    }

type tempx = {
     lit: Literal;
     env: Environment; }


let initScope (enc:LoxEnvironment option) =
    {
    values = emptyMap()
    enclosing = enc
    }

// Will create GLOBALs if you pass NONE of enclosing on first call.
let initEnvironment scopeDistanceMap =
    {
    localDistances = scopeDistanceMap // distance back from current scope to scope that has the value
    globalScope= initScope None
    localScopes= [initScope None]
    closures = emptyMap()
    }


let rec lookupVariableInScope (foundScope:LoxEnvironment) (id:identifier_terminal) = 
    if foundScope.values.ContainsKey id.name then
        foundScope.values.Item id.name 
    else 
        match foundScope.enclosing with
        | Some(encloser) -> lookupVariableInScope encloser id
        | None -> failwith "Could not find variable in scopes"


let rec lookupVariable (id:identifier_terminal) (   env:Environment) : Literal = 
    let foundScope = findScopeAtLocalDistance id env 
    lookupVariableInScope foundScope id 
                            

let rec wrapClosure (env:Environment) (closureKey:ClosureKey) =
    if closureKey = -1 then
        env
    else if env.closures.ContainsKey closureKey then
        let clos = (env.closures.Item closureKey)
        { env with localScopes = clos }
    else failwith (sprintf "Cannot find closureKey. For %A" closureKey)

                    
#if OLD
let rec lookup (name:identifier_terminal) (env:Environment) = 
    // In the book, this took a TOKEN, but I think this is better.
    if( not (env.localScopes.Head.values.ContainsKey name.name) )then
        match env.localScopes.Head.enclosing with
        | Some( env) ->  lookup name env
        | None -> if( not (env.values.ContainsKey name.name)) then
                    let msg = sprintf "Undefined variable in lookup: %s" name.name
                    failwith msg
                  else
                    lookup name env
    else 
        (env.values.Item name.name, env)
#endif


let assignValue value env (id:identifier_terminal) =
    let assignAt (dist:ResolveDistance) (id:identifier_terminal) (value:Literal) (env:Environment) =
        if dist < 0 || dist > (List.length env.localScopes) then
            failwith "Index out of range"
        else 
            let len = List.length env.localScopes
            let offset = dist //len - dist -1
            let scope = env.localScopes.Item offset
            let newMap = scope.values.Add(id.name, value)
            let newScope = { scope with values = newMap }
            // TBD: Check for out of range
            let newScopeList = List.mapi (fun i x -> if i = dist then newScope else x) env.localScopes
            { env with localScopes = newScopeList }

 
    let rec assignGlobal (id:identifier_terminal) (value:Literal) (env:Environment) =
        if env.globalScope.values.ContainsKey id.name then
            { env with globalScope = 
                                        { env.globalScope with values = env.globalScope.values.Add( id.name, value) // New map with the updated entry.
                                        }
            }
        else
            failwith (sprintf "Undefined variable in assign: %s." id.name)


 
    match env.localDistances.TryFind id.guid with
    | Some(rdt) -> value, assignAt rdt.dist id value env
    | None -> value, assignGlobal id value env


let define (id:identifier_terminal) value (env:Environment) =
    let scope = env.localScopes.Head
    let newMap = scope.values.Add(id.name, value)
    let newScope = { scope with values = newMap }
    // TBD: Check for out of range
    let newScopeList = List.mapi (fun i x -> if i = 0 then newScope else x) env.localScopes
    //printfn "%A" newScopeList
    value, { env with localScopes = newScopeList }

let defineGlobal (id:identifier_terminal) value (env:Environment) =
    let scope = env.globalScope
    let newMap = scope.values.Add(id.name, value)
    let newScope = { scope with values = newMap }
    value, { env with globalScope = newScope }

let toString lit =
    match lit with
                    | NUMBER n -> string n
                    | STRING s -> s
                    | BOOL b -> string b
                    | NIL -> "NIL"
                    | CALL c -> match c.decl with 
                                | DECL d -> sprintf "Function(%A)" d.id 
                                | NATIVE name -> sprintf "Native(%A)" name
                    | CLASS c -> c.id
                    | INSTANCE i -> i.klass.id + " instance"
                    | METHOD m -> m.method.id.name + " method"
                    | FUNCTION f -> f.method.id.name + "function"

let CNUMBER value : float =
    match value with
    | BOOL b -> runtimeError "Operand must be a number."
    | NUMBER f -> f
    | STRING s -> runtimeError "Operand must be a number."
    | NIL -> runtimeError "Operand must be a number."
    | CALL c-> runtimeError "TBD"
    | CLASS c -> runtimeError "Operand must be a number."
    | INSTANCE c -> runtimeError "Operand must be a number."
    | METHOD m -> runtimeError "Operand must be a number."
    | FUNCTION f -> runtimeError "Operand must be a number."

let CSTRING value : string =
    match value with
    | BOOL b -> runtimeError "Operand must be a string."
    | NUMBER f -> runtimeError "Operand must be a string."
    | STRING s -> s
    | NIL -> runtimeError "Operand must be a string."
    | CALL c-> runtimeError "TBD"
    | CLASS c-> c.id
    | INSTANCE i -> i.klass.id + " instance"
    | METHOD m -> m.method.id.name + " method"
    | FUNCTION f -> f.method.id.name + "function"

let isNumbery value =
    match value with
    | NUMBER f -> true
    | CALL c-> runtimeError "TBD"
    | _ -> false

let isStringy value =
    match value with
    | BOOL b -> false
    | NUMBER f -> false
    | STRING s -> true
    | NIL -> false
    | CALL c-> runtimeError "TBD"
    | INSTANCE i-> false
    | CLASS c -> false
    | METHOD m -> false
    | FUNCTION f -> false

let isTruthy value =
    match value with
    | BOOL b -> b
    | NUMBER f -> not (f = 0.0)
    | STRING s -> (String.length s) > 0
    | NIL -> false
    | INSTANCE i -> false
    | CLASS c -> false
    | CALL c -> runtimeError "TBD"
    | METHOD m -> runtimeError "TBD"
    | FUNCTION f -> runtimeError "TBD"

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
    | INSTANCE i -> runtimeError "- operator does not work on an INSTANCE"
    | CLASS c -> runtimeError "- operator does not work on an CLASS"
    | METHOD m -> runtimeError "- operator does not work on an METHOD"
    | FUNCTION f -> runtimeError "- operator does not work on an FUNCTION"
    


// Visitor for expressions
let rec evalExpression (e:expr) (env:Environment) = 
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
        | AssignExpr e ->       let value, env' = evalExpression e.value env
                                assignValue value env' e.id 
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
                            | Parser.IDENTIFIER i -> (lookupVariable i env), env
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

                        let evaluatedArgs, _, env1 = evalArgsInOrder [] args env

                        let floxFunction, env2 = evalExpression calleeName env1

                        match floxFunction with 
                        | CALL c -> callFunction c evaluatedArgs env2
                        | CLASS c -> callConstructor c evaluatedArgs env2
                                     
                        | _ -> failwith (sprintf "Can only call functions and classes.: %A" floxFunction)

        | GetExpr e-> let lit,env' = evalExpression e.object env
                      let lit' = match lit with
                                  | INSTANCE inst -> getField inst e.id
                                                    
                                  | _ -> failwith "Only instances have properties"
                      lit', env'
        | SetExpr e-> let lit, env' = evalExpression e.object env
                      match lit with
                        | INSTANCE inst ->  let value, env'' = evalExpression e.value env'
                                            setField inst e.id value |> ignore // TBD: Mutation
                                            value, env''
                        | _ -> failwith "Only instances have fields"


and evalFor forStmt lastResult env =
    failwith "Should not get here, because for loop desugared into a while loop."
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
                                | Stmt.Variable {name=name; initializer=None} -> NIL, env
                                | Stmt.Variable {name=name; initializer=Some(expr.PrimaryExpr e)} ->   let value, env' = evalExpression (PrimaryExpr e) env
                                                                                                       define name value env'  
                                | Stmt.Variable {name=name; initializer=Some(expr.UnaryExpr e)} ->     let value, env' = evalExpression (UnaryExpr e) env
                                                                                                       define name value env'  
                                | Stmt.Variable {name=name; initializer=Some(expr.BinaryExpr e)} ->    let value, env' = evalExpression (BinaryExpr e) env 
                                                                                                       define name value env'  
                                | Stmt.Variable {name=name; initializer=Some(expr.GroupingExpr e)} ->  let value, env' = evalExpression (GroupingExpr e) env
                                                                                                       define name value env'  
                                | Stmt.Variable {name=name; initializer=Some(expr.AssignExpr e)} ->    let value, env' = evalExpression (AssignExpr e) env
                                                                                                       define name value env'  
                                | Stmt.Variable {name=name; initializer=Some(expr.LogicalExpr e)} ->   let value, env' = evalExpression (LogicalExpr e) env
                                                                                                       define name value env'  
                                | Stmt.Variable {name=name; initializer=Some(expr.CallExpr e)} ->   let value, env' = evalExpression (CallExpr e) env
                                                                                                    define name value env'  
                                | Stmt.Variable {name=name; initializer=Some(expr.GetExpr e)} ->   let value, env' = evalExpression (GetExpr e) env
                                                                                                   define name value env'  
                                | Stmt.Variable {name=name; initializer=Some(expr.SetExpr e)} ->   let value, env' = evalExpression (SetExpr e) env
                                                                                                   define name value env'  
                                | Stmt.Block stms ->    // Exec more statements in child context. (TBD This is much nicer than book!)
                                                        let env1 = pushNewScope env
                                                        let lit,env2 = execStatements stms NIL env1
                                                        lit, popScope env2
                                        
#if BAD
    TBD: Not compile  using 'Record Pattern                              | Stmt.If { if_statement.condition = condition;
                                            if_statement.thenExpr = thenExpr;
                                            if_statement.elseExpr = elseExpr; } -> evalIf condition thenExpr elseExpr lastResult env
#endif
                                | Stmt.If ifs -> evalIf ifs lastResult env
                                | Stmt.ForStmt forStmt -> evalFor forStmt lastResult env
                                | Stmt.While whileStmt ->   evalWhile whileStmt lastResult env
                                | Stmt.FunctionStmt funcStmt ->     // Interpreting a function definition adds it to the environment.
                                                                    // 
                                                                    // NOTE: For recursion, the function name itself needs to be in the closure.
                                                                    // There was no good way to do this, so I made a separate map of all the closures
                                                                    //      for each funcStmt.id
                                                                    // TBD: If found about about "let rec" with lazy, after I did all this.
                                                                    //  I can probably get rid of closures collection.

                                                                    let (c:loxCallable) = { decl = DECL funcStmt; closureKey = funcStmt.id.guid }
                                                                    let lit,env2 = define funcStmt.id (CALL c) env
                                                                    let env3 = { env2 with closures = env2.closures.Add( funcStmt.id.guid, env2.localScopes) } 
                                                                    lit,env3


                                | Stmt.ReturnStmt returnStmt -> // We return values back through call stack instead of THROW that book uses.
                                                                evalExpression returnStmt.value env
                                | Stmt.Class classStmt ->  let lit, env' = define classStmt.name NIL env
                                                           let methods = classStmt.methods |> Seq.map (fun f-> f.id.name, { closure = env'; method = f; }) |> Map.ofSeq

                                                           let klass = CLASS( { id = classStmt.name.name; methods=methods; arity=0 })
                                                           assignValue klass env' classStmt.name // TBD: In book returned null (lit)
                                                           
                                | _ ->failwith "Not implemented"


// Implements the VISITOR pattern from book.
// I want to keep track of the "last" result on BLOCKS and LOOPS -- jorge.
and execStatements( statements:Stmt list) (lastReturn:Literal) (env:Environment) : Literal * Environment =
    match statements with
    | [] -> lastReturn, env
    | s :: xs -> 
        let lit, env1 =execSingleStatement s NIL env
        execStatements xs lit env1

// This function is much more complex in Java.
and executeBlock( statements: Stmt list)  (closure:Environment) =
    execStatements statements NIL closure

and callConstructor (c:loxClass) (args:Literal list) (envIn:Environment) : Literal * Environment =
    let instance = INSTANCE { klass = c; fields = emptyMap() } // TBD
    instance, envIn

// TBD: I think I have the definition of ARGS and PARAMs reversed.
and callFunction (c:loxCallable) (args:Literal list) (envIn:Environment) : Literal  * Environment  =
    let envClosure = wrapClosure envIn c.closureKey
    match c.decl with
    | NATIVE n -> match n.name with 
                    | "clock" -> STRING (System.DateTime.Now.ToString("")), envClosure
                    | _ -> failwith "Unknown native function."
    | DECL decl -> 
        let rec defineParamsInOrder (parameters: identifier_terminal list) (args: Literal list) (env:Environment) =
            if (List.length parameters) <> (List.length args) then   
                failwith "Unexpected number of arguments to function." // Book does not have. May be impossible.
            else
                // Assume args and params in same order
                match args with 
                | arg::xsArg -> match parameters with 
                                    | par::xsPar -> let lit,env' = define par arg env
                                                    defineParamsInOrder xsPar xsArg env'
                                                            
                                    | _ -> failwith "invalid case"
                | [] -> env // Break recursion

        let env1 = pushNewScope envClosure

        // See 10.4. We need a new scope for each funtion call to hold the params/args.
        let env2 = defineParamsInOrder  decl.parameters args env1 // Then add the local args

        // Execute statements in body of function (also, a new scope here because I wanted the body to be  balck)
        //let lit = match decl.body with
        //| Block b -> let lit, env3 = executeBlock b env2
        //             lit
        //| _ -> failwith "Unexpected body"                         
        let lit, env3 = execSingleStatement decl.body NIL env2

        // After executing, we are done with env2.
        //lit, popScope env3 // The caller only cares about the changed CLOSURES HERE. Every other part of popped environment will be ignored.

        // TBD: This is so yucky. Lots of effort here to fix test#9. Not sure how to make it better.
        let envClosureOut = popScope env3
        lit, { envIn with closures = envClosureOut.closures.Add( c.closureKey, envClosureOut.localScopes); } 

        
let interpret (statements:Stmt list) (scopeDistanceMap: ScopeDistanceMap) : unit = 
    try
        let env = initEnvironment scopeDistanceMap

        let clockIdentifier : identifier_terminal = { name = "clock"; guid = newGuid() }
        let clock: loxCallable = { decl = NATIVE clockIdentifier; closureKey= -1;  }
        let clockLit = CALL clock 
        let funcLit,ctx' = defineGlobal clockIdentifier clockLit env
        let ctx'' = execStatements statements funcLit ctx'
        ()
    with 
    | :? System.Exception as ex -> runtimeError ex.Message


    // var x; x=2; print x; 
    // var a = "global"; {   fun showA() {     print a;  }   showA();   var a = "block";   showA(); }

    // var a=1; { var b=2; print a; print b; b=b+1; { b=b+1; print a; print b;}}
    // var a=1; fun f(){  print a; var a=2; print a; } f();
    // fun f(a,b) { print a+b;} f(1,2);
    
    //  var a = 0; while( a <= 0) { print a; a=1; print a;}

    // Recursive count: fun count(n) { if(n>1) count(n-1); print n;} count(3);
    // FIB: var a = 0; var b = 1; while (a < 10000) {   print a;  var temp = a;  a = b;  b = temp + b;}


    //fun makeCounter() {   var i = 0;   fun count() {     i = i + 1;     print i;   }   return count; } var counter = makeCounter(); counter(); counter(); // "1" then "2".
