﻿module Resolver

open Parser
//open Interpreter // Need statments, etc.


// Chapter 11: Does semantic analysis after parser to find which declaration every variable refers to. 

let runtimeError m =
    failwith m


type BindingSteps = // BOOK used a boolean here.
    | DECLARED
    | DEFINED

type ScopeMap = Map<IdentifierName,BindingSteps>
type ScopeMapList = ScopeMap list

type classType =
    | IN_CLASS
    | NO_CLASS
    | IN_SUBCLASS

type ResolveDistance = int

type ResolveDistanceTarget = {
    dist: ResolveDistance;
    id: identifier_terminal; // Just here to make debugging easier.
}


type ScopeDistanceMap = Map<UniqueId,ResolveDistanceTarget>

type ResolverContext = {
    scopes: ScopeMapList
    distanceMap : ScopeDistanceMap
    enclosingFunction : functionKind // TBD: Maybe put functionType and classType into a struct
    enclosingClass: classType
    }

let initResolverContext =
    {
    scopes = [[] |> Map.ofSeq] 
    distanceMap = [] |> Map.ofSeq
    enclosingFunction = functionKind.NONE
    enclosingClass = NO_CLASS
    }

// Calculate the distance to the variable an store in a map
// 11.4 in book: Where the key is the expr in the syntax tree, which is unique in JAVA (but not in F#)
let rec resolveLocal (id:identifier_terminal) (ctx:ResolverContext) : ResolverContext =
    let optDist = List.tryFindIndex (fun (x:ScopeMap) -> x.ContainsKey id.name) ctx.scopes
    match optDist with
    | Some(dist) -> { ctx with distanceMap = (ctx.distanceMap.Add( id.guid, { id=id; dist=dist;})) }
    | None ->    ctx

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

let addThisToScope ctx = 
    let thisId = { name = "this"; guid = newGuid() }
    ctx |> declare thisId // Different from book 12.5
        |> define thisId

let addSuperClassToScope ctx id = 
    ctx |> declare id // Different from book 12.5
        |> define id
        
let visitVariableExpr (id: identifier_terminal) (ctx:ResolverContext) : ResolverContext =
    ctx |> resolveLocal id 


    
let rec resolveExpression (e:expr) (ctx:ResolverContext) : ResolverContext =
    match e with 
        | AssignExpr e ->          
                                   ctx |> resolveExpression e.value
                                       |> resolveLocal e.id

                                
        | BinaryExpr e ->       ctx |> resolveExpression e.left
                                    |> resolveExpression e.right
        | UnaryExpr e ->        match e with 
                                | UNARY u ->   ctx |> resolveExpression u.right
                                | PRIMARY p -> resolveExpression (PrimaryExpr p) ctx
        | PrimaryExpr e ->  match e with
                                    | Parser.IDENTIFIER id -> // TBD: In book, this is a separate variableExpr expression.
                                                                visitVariableExpr id ctx

                                    | Parser.THIS t ->                               
                                                        match ctx.enclosingFunction with
                                                        | functionKind.NONE | functionKind.FUNCTION -> if ctx.enclosingClass = NO_CLASS then
                                                                                                            failwith "Cannot use 'this' outside of a class."
                                                        | _ -> () // No error
                                                        visitVariableExpr t ctx
                                    | Parser.SUPER s -> match ctx.enclosingClass with
                                                        | NO_CLASS -> failwith "Cannot use 'super' outside of a class."; // TBD: Lox.error
                                                        | IN_SUBCLASS -> ()
                                                        | IN_CLASS ->  failwith "Cannot use 'super' in a class with no superclass."
                                    
                                                        // This is tricky and took a while to debug. The resolver wants to resolve "super", but the
                                                        // interpreter needs s.name to contain the name of the method to call.
                                                        visitVariableExpr { name="super";guid=s.guid} ctx
                                    | _ -> ctx //easiest of all
        | GroupingExpr e ->   ctx |> resolveExpression e
        | LogicalExpr e ->    ctx |> resolveExpression e.left
                                |> resolveExpression e.right
        | CallExpr e -> let rec resolveArgumentExpressions (args:expr list) (ctx:ResolverContext) : ResolverContext =
                            match args with
                            | [] -> ctx
                            | x::xs -> ctx |> resolveExpression x |> resolveArgumentExpressions xs 
                        ctx |> resolveExpression e.callee
                            //|> beginScope
                            |> resolveArgumentExpressions e.arguments
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

let setInClass flag ctx = 
    { ctx with enclosingClass = flag }

let setInFunction flag ctx =
    { ctx with enclosingFunction = flag }

let rec resolveSingleStatement statement (ctx:ResolverContext) : ResolverContext =
            match statement with 
            | ExpressionStmt e -> ctx |> resolveExpression e
            | PrintStmt p ->  ctx |> resolveExpression p
            | VariableStmt {name=name;initializer=None} -> ctx |> declare name
                                                                    
            | VariableStmt {name=name;initializer=Some(expr.PrimaryExpr e)} -> visitVariableStmt (PrimaryExpr e) name ctx
            | VariableStmt {name=name;initializer=Some(expr.UnaryExpr e)} ->     visitVariableStmt ( UnaryExpr e) name ctx
            | VariableStmt {name=name;initializer=Some(expr.BinaryExpr e)} ->    visitVariableStmt ( BinaryExpr e) name ctx 
            | VariableStmt {name=name;initializer=Some(expr.GroupingExpr e)} ->  visitVariableStmt ( GroupingExpr e) name ctx
            | VariableStmt {name=name;initializer=Some(expr.AssignExpr e)} ->  visitVariableStmt ( AssignExpr e) name ctx
            | VariableStmt {name=name;initializer=Some(expr.LogicalExpr e)} ->  visitVariableStmt ( LogicalExpr e) name ctx  
            | VariableStmt {name=name;initializer=Some(expr.CallExpr e)} ->  visitVariableStmt ( CallExpr e) name ctx 
            | BlockStmt stmts ->   ctx |> beginScope 
                                        |> resolveStatements stmts
                                        |> endScope 
            | VariableStmt {name=name;initializer=Some(expr.GetExpr e)} ->  visitVariableStmt ( GetExpr e) name ctx 
            | VariableStmt {name=name;initializer=Some(expr.SetExpr e)} ->  visitVariableStmt ( SetExpr e) name ctx 
            | IfStmt ifs -> ctx |> resolveExpression ifs.condition
                                        |> resolveSingleStatement ifs.thenBranch
                                        |> resolveOptionalSingleStatement ifs.elseBranch 
            | ForStmt forStmt ->   ctx |> resolveOptionalSingleStatement forStmt.initializer
                                            |> resolveOptionalExpression forStmt.condition
                                            |> resolveOptionalSingleStatement forStmt.increment
                                            |> resolveSingleStatement forStmt.body
            | WhileStmt whileStmt ->   ctx |> resolveExpression whileStmt.condition
                                                |> resolveSingleStatement whileStmt.body
            | FunctionStmt funcStmt ->     ctx |> declare funcStmt.id
                                                    |> define funcStmt.id 
                                                    |> resolveFunction funcStmt functionKind.FUNCTION
            | ReturnStmt returnStmt -> // We return values back through call stack instead of THROW that book uses.
                                            match ctx.enclosingFunction with
                                            | functionKind.FUNCTION -> ctx |> resolveExpression ( returnStmt.value ) 
                                            | functionKind.METHOD -> ctx |> resolveExpression ( returnStmt.value ) 
                                            | functionKind.INITIALIZER -> failwith "Cannot return a value from an initializer."
                                            | functionKind.NONE -> failwith "Cannot return from top-level code"


            | ClassStmt cls ->      let enclosingClass =ctx.enclosingClass

                                    let calcFuncKind (funcStmt:function_statement) = match funcStmt.id.name with
                                                                                    | "init" -> functionKind.INITIALIZER // So we can error if initializer tries to return a value.
                                                                                    | _ -> functionKind.METHOD
                                                       
                                    ctx |> setInClass (if cls.superclass = None then IN_CLASS else IN_SUBCLASS)
                                        |> declare cls.name 
                                        |> define cls.name
                                        |> resolveLocal cls.name
                                        |> resolveSuperclass cls.superclass
                                        |> beginScope
                                        |> addThisToScope
                                        //|> addMethod cls.methods  METHOD
                                        |> List.foldBack (fun meth -> resolveFunction meth (calcFuncKind meth)) cls.methods
                                        |> endScope
                                        |> endOptionalSuperClassScope cls.superclass
                                        |> setInClass enclosingClass

            | _ -> failwith "unknown statement type"

and resolveFunction (f:function_statement) (kind:functionKind)  ctx =
    let currentFunction = ctx.enclosingFunction // See 11.5.1: Detecting return outside of function.
    let ctx'' = ctx     |> setInFunction kind
                        |> beginScope 
                        |> declareParams f.parameters 
                        |> resolveSingleStatement f.body // This has a further scope, because I treat body like a block.
                        |> endScope
                        |> setInFunction currentFunction
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

and resolveSuperclass (superIdOpt:identifier_terminal option) (ctx:ResolverContext) : ResolverContext =
        match superIdOpt with 
        | Some( id) ->  let superId =  { name = "super"; guid = newGuid() }
                        ctx |> resolveLocal id
                           |> beginScope // Superclass support
                           |> declare superId // superclass
                           |> define superId
        | None -> ctx
and endOptionalSuperClassScope (superIdOpt:identifier_terminal option) (ctx:ResolverContext) : ResolverContext  =  
        match superIdOpt with 
        | Some( id) -> ctx |> endScope
        | None -> ctx        

let resolverPass (statements:Stmt list)  = // THIS IS PROBLEM. Need to return a new statmentList with annotations.
    try
        let ctx = initResolverContext |> resolveStatements statements
        (statements,ctx.distanceMap) // So we can chain
    with 
    | :? System.Exception as ex -> runtimeError ex.Message
