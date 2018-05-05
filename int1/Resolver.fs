module Resolver

open Parser
open Interpreter // Need statments, etc.


// Chapter 11: Does semantic analysis after parser to find which declaration every variable refers to. 

type BindingSteps = // BOOK used a boolean here.
    | DECLARED
    | DEFINED

type ScopeMap = Map<IdentifierName,BindingSteps>
type ScopeMapList = ScopeMap list

type functionType =
    | IN_FUNCTION
    | IN_NONE
    

type ResolverContext = {
    scopes: ScopeMapList
    distanceMap : ScopeDistanceMap
    enclosingFunction : functionType
    }

let initResolverContext =
    {
    scopes = [[] |> Map.ofSeq] 
    distanceMap = [] |> Map.ofSeq
    enclosingFunction = IN_NONE
    }

// Calculate the distance to the variable an store in a map
// 11.4 in book: Where the key is the expr in the syntax tree, which is unique in JAVA (but not in F#)
let rec resolveLocal (id:identifier_terminal) (ctx:ResolverContext) : ResolverContext =
    let idName = id.name
    let optDist = List.tryFindIndex (fun (x:ScopeMap) -> x.ContainsKey idName) ctx.scopes
    match optDist with
    | Some(dist) -> //let len = List.length ctx.scopes
                    let offset = dist // len-dist-1
                    //printfn "ID: %A DIST: %A" id offset
                    { ctx with distanceMap = (ctx.distanceMap.Add( id.guid, { id=id; dist=offset;})) }
    | None ->    // TBD:If not found then assume global.
                 ctx

let beginScope ctx = 
    let scopeMap = [] |> Map.ofSeq
    { ctx with scopes = scopeMap :: ctx.scopes }

let endScope ctx = 
    match ctx.scopes with
    | [] -> failwith "ended too many scopes";
    | _::xs -> { ctx with scopes = xs }


let declare (id:identifier_terminal) ctx =
    match ctx.scopes with
    | [] -> ctx
    | x::xs -> let newHead = x.Add( id.name, DECLARED)
               { ctx with scopes = newHead::xs }

let define (id:identifier_terminal) ctx =
    match ctx.scopes with
    | [] -> ctx
    | (x:ScopeMap)::xs -> let newHead = x.Add( id.name, DEFINED)
                          { ctx with scopes = newHead::xs }

        
let visitVariableExpr (id: identifier_terminal) (ctx:ResolverContext) : ResolverContext =
    ctx |> resolveLocal id  /// THIS IS THE PROBLEM.


    
let rec resolveExpression (e:expr) (ctx:ResolverContext) : ResolverContext =
    match e with 
        | AssignExpr e ->          
                                   ctx |> resolveExpression e.value
                                       //|> define e.id // <-- This not in book. Trying to fix : var x; x=2; print x; 
                                       |> resolveLocal e.id

                                
        | BinaryExpr e ->       let left,op,right = e // TBD: Recrod
                                ctx |> resolveExpression left
                                    |> resolveExpression right
        | UnaryExpr e ->        match e with 
                                | UNARY (op,right) ->   ctx |> resolveExpression right
                                | PRIMARY p -> resolveExpression (PrimaryExpr p) ctx
        | PrimaryExpr e ->  match e with
                                    | Parser.IDENTIFIER id -> // TBD: In book, this is a separate varaible expression.
#if NO_WORKEY
                                                                match ctx.scopes with
                                                                                        | x::xs -> if x.ContainsKey(id.name) && (x.Item(id.name) = DECLARED) then
                                                                                                        failwith ( sprintf "Cannot read var in it's own initializer: %A" e)
                                                                                                    else 
                                                                                                        ()
                                                                                        | []-> ()
#endif
                                                                visitVariableExpr id ctx

                                    | _ -> ctx //easiest of all
        | GroupingExpr e ->   ctx |> resolveExpression e
        | LogicalExpr e ->  let left,op,right = e    
                            ctx |> resolveExpression left
                                |> resolveExpression right
        | CallExpr e -> let calleeName, args = e
                        let rec resolveArgumentExpressions (args:expr list) (ctx:ResolverContext) : ResolverContext =
                            match args with
                            | [] -> ctx
                            | x::xs -> ctx |> resolveExpression x |> resolveArgumentExpressions xs 
                        ctx |> resolveExpression calleeName
                            //|> beginScope
                            |> resolveArgumentExpressions args
                            //|> endScope
        | GetExpr e -> ctx |> resolveExpression e.object
        | SetExpr e -> ctx |> resolveExpression e.value |> resolveExpression e.object
                            
                            

let resolveOptionalExpression (e:expr option) (ctx:ResolverContext) = 
    match e with 
    | None -> ctx
    | Some(ex) -> resolveExpression ex ctx

let visitVariableStmt (ex:expr) (id: identifier_terminal) (ctx:ResolverContext) : ResolverContext =
   
   ctx |> declare id 
       |> resolveExpression ex
       |> define id


// TBD: Turn into a map
let rec declareParams (p:identifier_terminal list) (ctx:ResolverContext) =
    match p with
    | x::xs -> ctx |> declare x |> define x |> declareParams xs
    | _ -> ctx 

let rec resolveSingleStatement statement (ctx:ResolverContext) : ResolverContext =
            match statement with 
                                | Stmt.Expression e -> ctx |> resolveExpression e
                                | Stmt.Print p ->       ctx |> resolveExpression p
                                | Stmt.Variable {name=name;initializer=None} -> ctx |> declare name
                                                                    
                                | Stmt.Variable {name=name;initializer=Some(expr.PrimaryExpr e)} -> visitVariableStmt (PrimaryExpr e) name ctx
                                | Stmt.Variable {name=name;initializer=Some(expr.UnaryExpr e)} ->     visitVariableStmt ( UnaryExpr e) name ctx
                                | Stmt.Variable {name=name;initializer=Some(expr.BinaryExpr e)} ->    visitVariableStmt ( BinaryExpr e) name ctx 
                                | Stmt.Variable {name=name;initializer=Some(expr.GroupingExpr e)} ->  visitVariableStmt ( GroupingExpr e) name ctx
                                | Stmt.Variable {name=name;initializer=Some(expr.AssignExpr e)} ->  visitVariableStmt ( AssignExpr e) name ctx
                                | Stmt.Variable {name=name;initializer=Some(expr.LogicalExpr e)} ->  visitVariableStmt ( LogicalExpr e) name ctx  
                                | Stmt.Variable {name=name;initializer=Some(expr.CallExpr e)} ->  visitVariableStmt ( CallExpr e) name ctx 
                                | Stmt.Block stmts ->   ctx |> beginScope 
                                                            |> resolveStatements stmts
                                                            |> endScope 
                                | Stmt.Variable {name=name;initializer=Some(expr.GetExpr e)} ->  visitVariableStmt ( GetExpr e) name ctx 
                                | Stmt.Variable {name=name;initializer=Some(expr.SetExpr e)} ->  visitVariableStmt ( SetExpr e) name ctx 
#if OLD
                                | Stmt.FunctionBody stmts -> ctx |> resolveStatements stmts // Funciton body not treated as a block in original.
#endif
                                | Stmt.If ifs -> ctx |> resolveExpression ifs.condition
                                                     |> resolveSingleStatement ifs.thenBranch
                                                     |> resolveOptionalSingleStatement ifs.elseBranch 
                                | Stmt.ForStmt forStmt ->   let (initializer, condition, increment, stmt) = forStmt // TBD Change to a record.
                                                            ctx |> resolveOptionalSingleStatement initializer
                                                                |> resolveOptionalExpression condition
                                                                |> resolveOptionalSingleStatement increment
                                                                |> resolveSingleStatement stmt
                                | Stmt.While whileStmt ->   ctx |> resolveExpression whileStmt.condition
                                                                |> resolveSingleStatement whileStmt.body
                                | Stmt.FunctionStmt funcStmt ->     ctx |> declare funcStmt.id
                                                                        |> define funcStmt.id 
                                                                        |> resolveFunction funcStmt functionKind.FUNCTION
                                | Stmt.ReturnStmt returnStmt -> // We return values back through call stack instead of THROW that book uses.
                                                                if( ctx.enclosingFunction = IN_FUNCTION) then
                                                                    ctx |> resolveExpression ( returnStmt.value ) 
                                                                else
                                                                    failwith "Cannot return from top-level code"
                                | Stmt.Class cls ->    let rec addMethod lst kind ctx = // TBD: Isn't this just  FOLD?
                                                          match lst with
                                                          | [] -> ctx
                                                          | meth::xs -> ctx |> resolveFunction meth kind 
                                                                            |> addMethod xs kind 
                                
                                                       ctx |> declare cls.name 
                                                           |> define cls.name
                                                           |> resolveLocal cls.name
                                                           //|> addMethod cls.methods  METHOD
                                                           |> List.foldBack (fun meth -> resolveFunction meth functionKind.METHOD) cls.methods

                                | _ -> failwith "unknown stament type"

and resolveFunction (f:function_statement) (kind:functionKind)  ctx =
    let currentFunction = ctx.enclosingFunction // See 11.5.1: Detecting return outside of function.
    let ctx' = { ctx with enclosingFunction = IN_FUNCTION }
    let ctx'' = ctx'    |> beginScope 
                        |> declareParams f.parameters 
                        |> resolveSingleStatement f.body // This has a further scope, because I treat body like a block.
                        |> endScope
    {ctx'' with enclosingFunction = currentFunction }

and resolveOptionalSingleStatement statement (ctx:ResolverContext) : ResolverContext =
    match statement with 
    | Some(s) -> resolveSingleStatement s ctx
    | None -> ctx

// Implements the VISITOR pattern from book.
and resolveStatements( statements:Stmt list) (ctx: ResolverContext)  : ResolverContext  =
    match statements with
    | [] -> ctx // Stop recursion
    | s :: xs -> 
        ctx |> resolveSingleStatement s 
            |> resolveStatements xs 
        // TODO: Remove this if you don't want to print intermediate results.
        //printfn "%s" (toString result) |> ignore
        

let resolverPass (statements:Stmt list) : ScopeDistanceMap = // THIS IS PROBLEM. Need to return a new statmentList with annotations.
    try
        let ctx = initResolverContext |> resolveStatements statements
        ctx.distanceMap
    with 
    | :? System.Exception as ex -> runtimeError ex.Message
