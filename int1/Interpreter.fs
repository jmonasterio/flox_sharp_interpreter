module Interpreter
//open Scanner
open System
open System.IO
open Parser
open Resolver
open System.Linq
open Scanner

//type UniqueId = System.Guid // Added by the resolver pass, later.


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
        arity: int;  
        decl: decl_types;
        closureKey: ClosureKey;
    }

and loxClass = // 12.1
    {
        id: identifier_terminal
        mutable methods: MethodMap
        superclass: loxClass option
    }

and loxInstance = // 12.2
    {
        klass: loxClass
        mutable fields: FieldMap // TBD: Horrible. Shoule be kept in ENV instead of part of state of loxInstance.
    }

and loxFunction =
    {
        method: loxCallable
        id: identifier_terminal
        isInitializer: bool // TBD: Hate bools
    }

let rec wrapClosure (env:Environment) (closureKey:ClosureKey) =
    if closureKey = -1 then
        env
    else if env.closures.ContainsKey closureKey then
        let clos = (env.closures.Item closureKey)
        { env with localScopes = clos }
    else failwith (sprintf "Cannot find closureKey. For %A" closureKey)

let define (id:identifier_terminal) value (env:Environment) =
    let scope = env.localScopes.Head
    let newMap = scope.values.Add(id.name, value)
    let newScope = { scope with values = newMap }
    // TBD: Check for out of range
    let newScopeList = List.mapi (fun i x -> if i = 0 then newScope else x) env.localScopes
    //printfn "%A" newScopeList
    value, { env with localScopes = newScopeList }

let makeEnvWithClosure funcStmt env=
    let (c:loxCallable) = { decl = DECL funcStmt; closureKey = funcStmt.id.guid; arity = funcStmt.parameters.Length }
    let lit,env2 = define funcStmt.id (CALL c) env
    let env3 = { env2 with closures = env2.closures.Add( funcStmt.id.guid, env2.localScopes) } 
    lit,env3

let bind (method:loxFunction) (instance:loxInstance) (env:Environment)   =
    let closureKey = method.method.closureKey
    let closure = wrapClosure env closureKey
    let thisId =  { name = "this"; guid = newGuid() }
    let lit, env' = define thisId (INSTANCE instance) closure
    let env2 = { env' with closures = env'.closures.Add( method.id.guid, env'.localScopes) } // TBD: DUPish
    METHOD method, env2

let rec findMethodOnClass (klass:loxClass) (name:IdentifierName) : loxFunction option =
    match klass.methods.TryFind name with 
    | Some(meth) -> Some(meth)
    | None -> match klass.superclass with
                | Some(sc) -> match findMethodOnClass sc name with
                                | Some(meth) -> Some(meth)
                                | None -> None
                | None -> None

let findMethod (inst:loxInstance) (name:IdentifierName) : loxFunction option =
    findMethodOnClass inst.klass name 

let getArity (c:loxClass) =
    match findMethodOnClass c "init" with
                    | Some(initializer) -> initializer.method.arity
                    | None -> 0

// Can return a "field" or a "property" or a "method".
let getField (inst:loxInstance) (id:identifier_terminal) (env:Environment)  =
    match inst.fields.TryFind id.name with
    | Some(lit) -> lit, env
    | None -> match findMethod inst id.name with
                | Some(meth) -> let m', env' = bind meth inst env 
                                m', env'
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


type param = {
    name: identifier_terminal
    value: Literal
    }

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


let findScopeAtLocalDistance (id:identifier_terminal) env =
    match env.localDistances.TryFind id.guid with
    | Some(rdt) -> ancestor (rdt.dist) env.localScopes 
    | None -> env.globalScope


let rec lookupVariableInScope (foundScope:LoxEnvironment) (id:identifier_terminal) = 
    if foundScope.values.ContainsKey id.name then
        foundScope.values.Item id.name 
    else 
        match foundScope.enclosing with
        | Some(encloser) -> lookupVariableInScope encloser id
        | None -> failwith (sprintf "Could not find variable, %A, in scopes" id)


let lookupVariable (id:identifier_terminal) (   env:Environment) : Literal = 
    let foundScope = findScopeAtLocalDistance id env 
    lookupVariableInScope foundScope id 

let assignValue value env (id:identifier_terminal) =
    let assignAt (dist:ResolveDistance) (id:identifier_terminal) (value:Literal) (env:Environment) =
        if dist < 0 || dist > (List.length env.localScopes) then
            failwith "Index out of range"
        else 
            let scope = env.localScopes.Item dist
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
                    | CLASS c -> c.id.name
                    | INSTANCE i -> i.klass.id.name + " instance"
                    | METHOD m -> m.id.name + " method"
                    | FUNCTION f -> f.id.name + "function"

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
    | CLASS c-> c.id.name
    | INSTANCE i -> i.klass.id.name + " instance"
    | METHOD m -> m.id.name + " method"
    | FUNCTION f -> f.id.name + "function"

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
        | AssignExpr e ->       let value, env' = evalExpression e.value env
                                assignValue value env' e.id 
        | BinaryExpr e ->       let leftValue, env' = evalExpression e.left env
                                let rightValue, env'' = evalExpression e.right env'
                                match e.binOp with
                                | ADD_OP add_operator.MINUS  -> NUMBER (CNUMBER leftValue - CNUMBER rightValue), env''
                                | MULTIPLY_OP DIV -> NUMBER (CNUMBER leftValue / CNUMBER rightValue), env''
                                | MULTIPLY_OP MUL -> NUMBER (CNUMBER leftValue * CNUMBER rightValue), env''
                                | ADD_OP add_operator.PLUS -> if isStringy leftValue then
                                                                     STRING( CSTRING leftValue + CSTRING rightValue), env''
                                                                 else 
                                                                     NUMBER( CNUMBER leftValue + CNUMBER rightValue), env''
                                | COMPARISON_OP LT -> BOOL( CNUMBER leftValue < CNUMBER rightValue), env''
                                | COMPARISON_OP GT -> BOOL( CNUMBER leftValue > CNUMBER rightValue), env''
                                | COMPARISON_OP LTE -> BOOL( CNUMBER leftValue <= CNUMBER rightValue), env''
                                | COMPARISON_OP GTE -> BOOL( CNUMBER leftValue >= CNUMBER rightValue), env''
                                | EQUALITY_OP NOT_EQUALS -> BOOL( not( isEqual leftValue rightValue)), env''
                                | EQUALITY_OP equal_operator.EQUAL_EQUAL -> BOOL (isEqual leftValue rightValue), env''
                                //| _ -> runtimeError ( sprintf" Unsupported operator: %A" op)
        | UnaryExpr e ->        match e with 
                                | UNARY u ->   let rv, env' = evalExpression u.right env
                                               let lit = match u.unOp with
                                                            | unary_operator.BANG -> BOOL (not (isTruthy rv))
                                                            | NEGATIVE -> NUMBER (- CNUMBER rv)
                                               (lit,env')
                                | PRIMARY p -> evalExpression (PrimaryExpr p) env
        | PrimaryExpr e ->  match e with 
                            | Parser.NUMBER n-> NUMBER n.value, env
                            | Parser.STRING s -> STRING s.value, env
                            | Parser.BOOL b -> BOOL b.value, env
                            | Parser.NIL -> NIL, env
                            | Parser.IDENTIFIER i -> (lookupVariable i env), env
                            | Parser.THIS t -> lookupVariable t env, env
                            | Parser.SUPER s -> lookupVariable s env, env
        | GroupingExpr e ->    evalExpression e env
        | LogicalExpr e -> let leftValue, env' = evalExpression e.left env
                           match e.logOp with
                                | logical_operator.AND -> if not (isTruthy leftValue) then  
                                                            leftValue, env'
                                                          else
                                                            let rightValue, env'' = evalExpression e.right env'
                                                            rightValue, env''

                                | logical_operator.OR -> if isTruthy leftValue then  
                                                            leftValue, env'
                                                         else
                                                            let rightValue, env'' = evalExpression e.right env'
                                                            rightValue, env''
        | CallExpr e -> // Evaluate parameters in order

                        // TBD: Can't use map, because need to thread the ENV through (I think env can change???)
                        let rec evalArgsInOrder (newList:Literal list) (args:expr list) (env:Environment) =
                            match args with
                            | [] -> List.rev newList, [], env
                            | arg::xs -> let lit, env' = evalExpression arg env
                                         evalArgsInOrder (lit :: newList) xs env'  

                        let evaluatedArgs, _, env1 = evalArgsInOrder [] e.arguments env

                        let floxFunction, env2 = evalExpression e.callee env1

                        match floxFunction with 
                        | CALL c -> callFunction c evaluatedArgs env2
                        | METHOD m -> callFunction m.method evaluatedArgs env2
                        | CLASS c -> callConstructor c evaluatedArgs env2
                                     
                        | _ -> failwith (sprintf "Can only call functions and classes.: %A" floxFunction)

        | GetExpr e-> let lit,env' = evalExpression e.object env
                      let lit',env'' = match lit with
                                          | INSTANCE inst -> getField inst e.id env'
                                          | _ -> failwith "Only instances have properties"
                      lit', env''
        | SetExpr e-> let lit, env' = evalExpression e.object env
                      match lit with
                        | INSTANCE inst ->  let value, env'' = evalExpression e.value env'
                                            setField inst e.id value |> ignore // TBD: Mutation
                                            value, env''
                        | _ -> failwith "Only instances have fields"


//and evalFor forStmt lastResult env =
//    failwith "Should not get here, because for loop desugared into a while loop."
and evalIf (ifs:if_statement) lastResult env =
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
                                | ExpressionStmt e -> evalExpression e env
                                | PrintStmt p ->        let lit, env' = evalExpression p env
                                                        printfn "%s" (toString ( lit))
                                                        (lit, env')
                                | VariableStmt {name=name; initializer=None} -> NIL, env
                                | VariableStmt {name=name; initializer=Some(expr.PrimaryExpr e)} ->   let value, env' = evalExpression (PrimaryExpr e) env
                                                                                                      define name value env'  
                                | VariableStmt {name=name; initializer=Some(expr.UnaryExpr e)} ->     let value, env' = evalExpression (UnaryExpr e) env
                                                                                                      define name value env'  
                                | VariableStmt {name=name; initializer=Some(expr.BinaryExpr e)} ->    let value, env' = evalExpression (BinaryExpr e) env 
                                                                                                      define name value env'  
                                | VariableStmt {name=name; initializer=Some(expr.GroupingExpr e)} ->  let value, env' = evalExpression (GroupingExpr e) env
                                                                                                      define name value env'  
                                | VariableStmt {name=name; initializer=Some(expr.AssignExpr e)} ->    let value, env' = evalExpression (AssignExpr e) env
                                                                                                      define name value env'  
                                | VariableStmt {name=name; initializer=Some(expr.LogicalExpr e)} ->   let value, env' = evalExpression (LogicalExpr e) env
                                                                                                      define name value env'  
                                | VariableStmt {name=name; initializer=Some(expr.CallExpr e)} ->   let value, env' = evalExpression (CallExpr e) env
                                                                                                   define name value env'  
                                | VariableStmt {name=name; initializer=Some(expr.GetExpr e)} ->   let value, env' = evalExpression (GetExpr e) env
                                                                                                  define name value env'  
                                | VariableStmt {name=name; initializer=Some(expr.SetExpr e)} ->   let value, env' = evalExpression (SetExpr e) env
                                                                                                  define name value env'  
                                | BlockStmt stms ->    // Exec more statements in child context. (TBD This is much nicer than book!)
                                                        let env1 = pushNewScope env
                                                        let lit,env2 = execStatements stms NIL env1
                                                        lit, popScope env2
                                        
                                | IfStmt ifs -> evalIf ifs lastResult env
                                // DESUGARED: | ForStmt forStmt -> evalFor forStmt lastResult env
                                | WhileStmt whileStmt ->   evalWhile whileStmt lastResult env
                                | FunctionStmt funcStmt ->     // Interpreting a function definition adds it to the environment.
                                                                    // 
                                                                    // NOTE: For recursion, the function name itself needs to be in the closure.
                                                                    // There was no good way to do this, so I made a separate map of all the closures
                                                                    //      for each funcStmt.id
                                                                    // TBD: If found about about "let rec" with lazy, after I did all this.
                                                                    //  I can probably get rid of closures collection.
                                                                    makeEnvWithClosure funcStmt env


                                | ReturnStmt returnStmt -> // We return values back through call stack instead of THROW that book uses.
                                                                evalExpression returnStmt.value env
                                | ClassStmt classStmt ->   let lit, env' = define classStmt.name NIL env


                                                           let superLoxClass, env'' = 
                                                               match classStmt.superclass with
                                                               | None -> None, env'
                                                               | Some( sc) -> let evSuperClass, env4 = evalExpression (PrimaryExpr (Parser.IDENTIFIER sc)) env'
                                                                              match evSuperClass with
                                                                              | Literal.CLASS c ->    // TBD: Below is Similar to makeEnvWithClosure
                                                                                                      // TBD: Also similar to bind()
                                                                                                      let env5 = pushNewScope env4

                                                                                                      let superId =  { name = "super"; guid = newGuid() }
                                                                                                      let lit,env6 = define superId (Literal.CLASS c) env5
                                                                                                      let env7 = { env6 with closures = env6.closures.Add( c.id.guid, env6.localScopes) } 
                                                                                                      Some(c), env7
                                                                              | _ -> failwith "Superclass must be a class."

                                                

                                                           
                                                           let methods = classStmt.methods 
                                                                                    |> Seq.map (fun funcStmt -> funcStmt.id.name, 
                                                                                                                    { method = 
                                                                                                                        { decl = DECL funcStmt; 
                                                                                                                          closureKey = funcStmt.id.guid; 
                                                                                                                          arity = funcStmt.parameters.Length }; 
                                                                                                                      id=funcStmt.id; 
                                                                                                                      isInitializer = (funcStmt.id.name = "init") }) 
                                                                                    |> Map.ofSeq
                                                           let env''' = env'' |> List.foldBack (fun funcStmt ee-> let lit,e1 = makeEnvWithClosure funcStmt ee  
                                                                                                                  e1 ) classStmt.methods

    

                                                           let klass = CLASS( { id = classStmt.name; methods=methods; superclass = superLoxClass })

                                                           // If there is a superclass, pop the "enclosing" scope we pushed above.
                                                           let env5 = 
                                                               match classStmt.superclass with
                                                               | None -> env'''
                                                               | Some( sc) ->  popScope env''' // enclosing?


                                                           let result,env'''' = assignValue klass env5 classStmt.name // TBD: In book returned null (lit)
                                                           
                                                           result, env''''

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
    let instance = { klass = c; fields = emptyMap() } // TBD

    let lit, env' = 
        match findMethod instance "init" with
        | Some(initializer) -> let lit', env' = bind initializer instance envIn
                               match lit' with 
                               | METHOD m -> callFunction (m.method) args env'
                               | _ -> failwith "Expected a method here."
        | None -> NIL, envIn

    INSTANCE instance, env' // TBD is this the right return value?

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

        let lit, env3 = execSingleStatement decl.body NIL env2

        // After executing, we are done with env2.
        //lit, popScope env3 // The caller only cares about the changed CLOSURES HERE. Every other part of popped environment will be ignored.

        // TBD: This is so yucky. Lots of effort here to fix test#9. Not sure how to make it better.
        let envClosureOut = popScope env3
        lit, { envIn with closures = envClosureOut.closures.Add( c.closureKey, envClosureOut.localScopes); } 

        
let interpret ((statements:Stmt list), (scopeDistanceMap: ScopeDistanceMap)) : unit = 
    try
        let env = initEnvironment scopeDistanceMap

        let clockIdentifier : identifier_terminal = { name = "clock"; guid = newGuid() }
        let clock: loxCallable = { decl = NATIVE clockIdentifier; closureKey= -1; arity=0 }
        let clockLit = CALL clock 
        let funcLit,ctx' = defineGlobal clockIdentifier clockLit env
        let ctx'' = execStatements statements funcLit ctx'
        ()
    with 
    | :? System.Exception as ex -> runtimeError ex.Message



// TBD: These chain together, but barely. The types passed around are really lame.
let run source =
    try
        source  |> scan 
                |> parse 
                |> resolverPass  // Semantic analsysis passes
                |> interpret
    with
    | :? System.Exception as ex -> printfn "FAIL: %A" ex.Message


let runPrompt x =
    while true do
        printf "> "
        run(Console.ReadLine()) |> ignore

let runFile path =
    let text = File.ReadAllText path
    run text