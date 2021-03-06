﻿module Parser
open Scanner
open System.Linq.Expressions
open System

type UniqueId = int // System.Guid // Added by the resolver pass, later.
type IdentifierName = string

let mutable xxguid = 1000
let newGuid() =
    xxguid <- xxguid+1;
    xxguid

// TERMINALS
type number_terminal = { value: float }
type string_terminal = { value: string }
type boolean_terminal = { value: bool }

type identifier_terminal = { name : IdentifierName; guid: UniqueId }

// Operators

//type assignment_operator = 
//    | EQUALS // Probably not in this group. TDB: Different from book.

type equal_operator =
    | EQUAL_EQUAL
    | NOT_EQUALS

type comparison_operator =
    | LT
    | LTE
    | GT
    | GTE

type unary_operator =
    | NEGATIVE
    | BANG

type mul_operator = 
    | MUL
    | DIV

type add_operator = 
    | PLUS
    | MINUS

type binary_operator =
    | EQUALITY_OP of equal_operator
    | COMPARISON_OP of comparison_operator
    | MULTIPLY_OP of mul_operator
    | ADD_OP of add_operator
//    | ASSIGNMENT_OP of assignment_operator

type logical_operator =
    | AND
    | OR

// Grammar
type expr =
    // These are outputs
    | UnaryExpr of unary 
    | PrimaryExpr of primary
    | BinaryExpr of binary
    | GroupingExpr of grouping
    | AssignExpr of assign
    | LogicalExpr of logical
    | CallExpr of calling
    | GetExpr of getter // Property access 12.3.1
    | SetExpr of setter // Property access 12.3.2


and calling = { callee: expr; arguments: expr list} 
and binary = { left: expr; binOp: binary_operator; right: expr} // binary_operator different from book.
and logical = { left: expr; logOp: logical_operator; right: expr} // logical_operator different from book.
and grouping = expr
and primary = 
    | NUMBER of number_terminal 
    | STRING of string_terminal
    | BOOL of boolean_terminal
    | NIL //of nil_terminal
    | IDENTIFIER of identifier_terminal
    | THIS of identifier_terminal
    | SUPER of identifier_terminal // Contains the method called on super.
and unary = 
    | UNARY of unary_op
    | PRIMARY of primary // TBD: Without this we never "FINISH".
and assign = { id:identifier_terminal; value:expr; guid: UniqueId} // Book used a token instead of identifier terminal
and getter = { object:expr; id:identifier_terminal}
and setter = { object:expr; id:identifier_terminal; value:expr}
and unary_op = { unOp : unary_operator; right: expr} 

type Stmt =
    | ExpressionStmt of expr // Just evaluates to a value, and then is ignored.
    | PrintStmt of expr
    | VariableStmt of var_statement
    | BlockStmt of Stmt list
    | IfStmt of if_statement 
    | WhileStmt of while_statement
    | ForStmt of for_statement   
    | FunctionStmt of function_statement
    | ReturnStmt of return_statement
    | ClassStmt of class_decl
    //| FunctionBody of Stmt list // Function body (not counted as block because resolver handles different
and return_statement = { keyword: string; value: expr; } // TBD: Book says "keyword" is so we can use it's location for error reporting.
and while_statement = { condition: expr; body: Stmt}
and if_statement = { condition : expr; thenBranch : Stmt; elseBranch : Stmt option }
and function_statement = { id: identifier_terminal; parameters: identifier_terminal list; body: Stmt; }
    // TBD: Would it be better if the types below were structs instead of tuples (so each part has a name).
    // Did if_statement as an example -- a little more self documenting. The matches must still be against a tuple.
and for_statement =  { initializer: Option<Stmt>; condition: Option<expr>; increment:Option<Stmt>; body: Stmt }
and var_statement = { name:identifier_terminal; initializer: Option<expr> } // Not in book.
and class_decl = { name: identifier_terminal; superclass: identifier_terminal option; methods: function_statement list }

let rec prettyPrint (e:expr)  =
    match e with 
        | BinaryExpr e ->       prettyPrint e.left
                                printfn "%A" e.binOp
                                prettyPrint e.right
        | UnaryExpr e ->        match e with 
                                | UNARY u ->   match u.unOp with
                                                | BANG -> printf "!"
                                                | NEGATIVE -> printf "-"
                                | PRIMARY p -> prettyPrint (PrimaryExpr p)
        | PrimaryExpr e -> match e with 
                            | NUMBER n-> printfn "%f" n.value
                            | STRING s -> printfn "%s" s.value
                            | BOOL b -> printfn "%A" b.value
                            | NIL -> printfn "NIL"
                            | IDENTIFIER ii -> printfn "%s" ii.name
                            | THIS tt -> printfn "THIS"
                            | SUPER ss -> printfn "SUPER"
        | GroupingExpr e ->    printf "("
                               prettyPrint e
                               printf ")"
        | AssignExpr e -> printfn  "var %s =" (e.id.name)
                          prettyPrint (e.value)
        | LogicalExpr e ->      prettyPrint e.left
                                printfn "%A" e.logOp
                                prettyPrint e.right
        | CallExpr c -> printfn "%A" c
        | GetExpr g -> printfn "%A" g
        | SetExpr s -> printfn "%A" s

type ParserContext = {
    current: int
    tokens: Scanner.Token list
    hadError: bool
    }

let initParserContext tokens =
    let newCtx = {
        current = 0
        tokens = tokens
        hadError = false
        }
    newCtx    

let report line where message =
    printfn "[line %A] Error %s: %s" line where message

let errorP ctx message =
    let token = ctx.tokens.[ctx.current]
    if token.tokenType = EOF then
        report token.line "at end" message
    else
        report token.line ("at '" + token.lexeme + "'") message
    { ctx with hadError = true; }


let peek ctx =
    ctx.tokens.[ctx.current]

let isAtEnd ctx =
    let token = peek ctx
    token.tokenType = EOF

let check ctx matchTokenType = 
    if isAtEnd ctx then
        false
    else
        let token = peek ctx
        token.tokenType = matchTokenType


// TBD: The most recently consume token (might be better to just store that).
let previous ctx =
    ctx.tokens.[ctx.current-1]

let advance ctx = 
    if not (isAtEnd ctx) then
        let ctx' = { ctx with current=ctx.current+1 }
        (previous ctx', ctx')
        
    else
        (previous ctx, ctx)

type ParserResult = {
    matched: Token option;
    butFound: Token; // What was actually found, if match wasn't found.
}
   
let matchParser ctx tokenTypeList =
    let isFilter ctx token =
        check ctx token
    match List.tryFind (isFilter ctx) tokenTypeList with 
    | Some(_)  -> 
        let token, newCtx = advance ctx
        (newCtx, { matched = Some(token); butFound = token} )
    | None -> (ctx, {matched = None; butFound = peek ctx} )

// Recursive descent parser

let derefNumber ol =
    match ol with
    | Some(NumberLiteral sl)  -> sl
    | _ -> failwith "Expected number"

let derefString ol =
    match ol with
    | Some(StringLiteral sl)  -> sl
    | _ -> failwith "Expected string"

let consume ctx tokenType message =
    if check ctx tokenType then
        let token,ctx = advance ctx
        ctx, token
    else
        let newCtx = errorP ctx message
        failwith message

// Book did not have this concept.
let makeLogicalOp token : logical_operator =
    match token.tokenType with
    | TokenType.AND -> AND
    | TokenType.OR -> OR
    | _ -> failwith (sprintf "Unexpected logical operator: %A" token.tokenType)


// Book did not have this concept.
let makeBinaryOp token : binary_operator =
    match token.tokenType with
    | TokenType.EQUAL_EQUAL -> EQUALITY_OP EQUAL_EQUAL
    //| TokenType.EQUAL -> EQUALITY_OP EQUALS
    | TokenType.BANG_EQUAL -> EQUALITY_OP NOT_EQUALS
    | TokenType.LESS -> COMPARISON_OP LT
    | TokenType.LESS_EQUAL -> COMPARISON_OP LTE
    | TokenType.GREATER -> COMPARISON_OP GT
    | TokenType.GREATER_EQUAL -> COMPARISON_OP GTE
    | TokenType.STAR -> MULTIPLY_OP MUL
    | TokenType.SLASH -> MULTIPLY_OP DIV
    | TokenType.PLUS -> ADD_OP PLUS
    | TokenType.MINUS -> ADD_OP MINUS
    | _ -> failwith (sprintf "Unexpected operator: %A" token.tokenType)
    

// TBD not typesafe because 2 lists have to be kept in sync.
let rec primary ctx =
    let ctx', matchedToken = matchParser ctx [FALSE; TRUE; TokenType.NIL; TokenType.NUMBER; TokenType.STRING; LEFT_PAREN; TokenType.IDENTIFIER; TokenType.THIS; TokenType.SUPER]
    match matchedToken.matched with
    | Some(token) ->
        match token.tokenType with
        | FALSE ->
            let result = PrimaryExpr ( BOOL { value= false}) // TBD: In book was LiteralExpr
            result, ctx'
        | TRUE ->
            let result = PrimaryExpr ( BOOL { value= true}) // TBD: In book was LiteralExpr
            result, ctx'
        | TokenType.NIL ->
            let result = PrimaryExpr ( NIL ) // TBD: In book was LiteralExpr
            result, ctx'
        | TokenType.NUMBER ->
            let prevTok = (previous ctx')
            let result = PrimaryExpr ( NUMBER { value= derefNumber prevTok.literal }) // TBD: In book was LiteralExprLiteralExpr (previous ctx).literal
            result, ctx'
        | TokenType.STRING ->
            let prevTok = (previous ctx')
            let result = PrimaryExpr ( STRING { value= derefString prevTok.literal}) // TBD: In book was LiteralExprLiteralExpr (previous ctx).literal
            result, ctx'
        | TokenType.LEFT_PAREN ->
            let ctx'', ex = expression ctx'
            let ctx''', token = consume ctx'' RIGHT_PAREN "Except ')' after expression."
            let result = GroupingExpr ex
            result, ctx'''
        | TokenType.THIS ->
            let prevTok = (previous ctx')
            let result = PrimaryExpr ( THIS { name = "this"; guid = newGuid()}) // ThisExpr
            result, ctx' // TBD
        | TokenType.SUPER ->
            let prevTok = (previous ctx')
            let ctx'', token = consume ctx' DOT "Expect '.' after 'super'."
            let ctx''', method = consume ctx'' TokenType.IDENTIFIER "Expect superclass method name."
            let result = PrimaryExpr( SUPER { name = method.lexeme; guid = newGuid() }) 
            result, ctx'''

        | TokenType.IDENTIFIER ->
            let prevTok = (previous ctx')
            let result = PrimaryExpr( IDENTIFIER { name = prevTok.lexeme; guid = newGuid() }) // TBD: Maybe makes sense for identifier to be a literal.
            result, ctx'
        | _ -> 
            let newCtx = errorP ctx "Expect expression not in set..."
            failwith "Expect expression not in set..."
    | None ->
        let newCtx = errorP ctx (sprintf "Expect expression, but found: %A" matchedToken.butFound )
        failwith "Expect expression"


and call ctx =

    let rec addArguments ctx callee (arguments: expr list) = // TBD: Was called finishCall in book

        if not (isAtEnd ctx) && not( check ctx RIGHT_PAREN) then // Different from book: Added isAtEnd()
                    let ctx', arg = expression ctx

                    match matchParser ctx' [TokenType.COMMA] with
                    | ctx'', { matched = Some(_)} -> 
                        addArguments ctx'' callee ( arg :: arguments  )
                    | ctx'', { matched = None } -> 
                        let ctx''', token = consume ctx'' RIGHT_PAREN "Expected ')' after arguments."
                        CallExpr { callee = callee; arguments = arg :: arguments}, ctx'''  // Another break for recursion 
        else
                    // No params (or end of input).
                    let ctx', token = consume ctx RIGHT_PAREN "Expected ')' after no arguments."
                    CallExpr { callee = callee; arguments = arguments}, ctx'  // Break recursion
            
    let rec walkGetters ((ex:expr), (ctx:ParserContext)) : expr * ParserContext =
        match matchParser ctx [LEFT_PAREN;DOT] with
        | ctx'', { matched = Some(tok) } ->  match tok.tokenType with 
                                             | TokenType.LEFT_PAREN -> let ctx''',ex2 = addArguments ctx'' ex []
                                                                       walkGetters (ctx''', ex2)
                                             | TokenType.DOT -> let ctx''', name = consume ctx'' TokenType.IDENTIFIER "Expect property name after '.'."
                                                                let expr = GetExpr( { object=ex; id={ name = name.lexeme; guid= newGuid() }})
                                                                walkGetters (expr, ctx''')
                                             | _ -> ex,ctx'' // TBD: I think this case is impossible.
        | ctx'', { matched = None } -> ex, ctx'' // Expression

    ctx |> primary |> walkGetters

 // Have to use "AND" below because expression is circular.
and unary ctx : ParserContext* expr   =
    let isMatched = matchParser ctx [TokenType.BANG; TokenType.MINUS]
    match isMatched with
    | ctx', { matched = Some(token) } ->
        let tokOp = previous ctx'
        let newCtx, right = unary ctx'
        match tokOp.tokenType with
        | TokenType.BANG ->
            let result = UnaryExpr (UNARY { unOp = unary_operator.BANG; right= right})   // TBD: This is a horrible convert
            newCtx, result
        | TokenType.MINUS ->
            let result = UnaryExpr (UNARY { unOp = unary_operator.NEGATIVE; right = right}) // TBD: This is a horrible convert
            newCtx, result
        | _ -> failwith "Invalid unary operator"

    | ctx', { matched = None } ->
        let result, ctx2 = call ctx' // TBD results in this file are all backwards so chaining doesn't work.
        ctx2,result 
and moreLogical lstTokens parentFunc (ctx, ex1) =
     let ctx' = ctx

     match matchParser ctx' lstTokens with
     | ctx'', { matched = Some(matchedToken)} -> let ctx''', right = parentFunc ctx''
                                                 let opLogical = makeLogicalOp matchedToken
                                                 let expr2 = LogicalExpr { left = ex1; logOp = opLogical; right= right}
                                                 moreLogical lstTokens parentFunc (ctx''', expr2)
     | ctx'', { matched = None } ->
        ctx'', ex1

and moreBinary lstTokens (ctx,ex1)  =
    match matchParser ctx lstTokens with
    | ctx', { matched = Some(matchedToken) } ->
        let opBinary = makeBinaryOp matchedToken
        match expression ctx' with 
        | ctx', UnaryExpr u ->match u with 
                                        | PRIMARY p -> 
                                            // Stop recursion
                                            let expr2 = BinaryExpr { left = ex1; binOp = opBinary; right = PrimaryExpr p }
                                            moreBinary lstTokens (ctx', expr2) 
                                            //newCtx, expr2
                                        | UNARY { unOp = op; right = exprRight} -> 
                                            // Recurse
                                            let unRight = UnaryExpr (UNARY { unOp = op; right= exprRight})
                                            let expr2 = BinaryExpr { left = ex1; binOp = opBinary; right = unRight }
                                            moreBinary lstTokens (ctx', expr2) 
        | ctx', PrimaryExpr p -> let expr2 = BinaryExpr { left = ex1; binOp = opBinary; right = PrimaryExpr p} // This case needed because primary() function can return lots of things.
                                 moreBinary lstTokens (ctx', expr2) 
        | ctx', GroupingExpr g ->   let expr2 = BinaryExpr { left = ex1; binOp = opBinary; right = GroupingExpr g}
                                    moreBinary lstTokens (ctx', expr2) 
        | ctx', BinaryExpr b -> moreBinary lstTokens (ctx', BinaryExpr {left= ex1; binOp = opBinary; right = BinaryExpr b})
        | _ -> failwith "did not expect any other kind of exprssion"
    | ctx', { matched = None } ->
        ctx', ex1


//ctx,  UnaryExpr( PRIMARY (NUMBER { value = 0.0} ))
and multiplication ctx  =
    unary ctx |> moreBinary  [TokenType.STAR;TokenType.SLASH]

//ctx,  UnaryExpr( PRIMARY (NUMBER { value = 0.0} ))
and addition ctx  =
    multiplication ctx |> moreBinary  [TokenType.MINUS;TokenType.PLUS]

and comparison ctx =
    addition ctx |> moreBinary  [GREATER; GREATER_EQUAL; LESS; LESS_EQUAL]
    
and equality ctx =
    comparison ctx |> moreBinary [BANG_EQUAL; TokenType.EQUAL_EQUAL]

and logicalAnd ctx = 
    equality ctx |> moreLogical [TokenType.AND] equality

and logicalOr ctx =
    logicalAnd ctx |> moreLogical [TokenType.OR] logicalAnd

and assignment ctx =
    let ctx', ex = logicalOr ctx
    let isMatched = matchParser ctx' [TokenType.EQUAL]
    match isMatched with
        | ctx'', {matched = Some(token)} ->
            let ctx''', value = assignment ctx'' // Recursive
            match ex with
            | PrimaryExpr p ->
                match p with
                | IDENTIFIER ii -> 
                    ctx''', AssignExpr { id = ii; value= value; guid = newGuid() }
                | _ -> failwith "Unsupported"
            | GetExpr g ->
                // What we thought was a getExpr is actually a SetExpr because we found an assignement.
                ctx''', SetExpr { id = g.id; value = value; object = g.object}
            | _ ->  let equals = previous ctx'' // This gets printed on error.
                    failwith (sprintf "Invalid assignment target %A" equals)

        | ctx'', { matched = None } ->
            (ctx'', ex)


and expression ctx : ParserContext * expr = // TBD: This is weirdo.
    assignment ctx

let synchronize ctx =
    
    let rec eatTokens ctx =
        if not (isAtEnd ctx) then 
          let token = previous ctx
          if token.tokenType = SEMICOLON then
              let tok = peek ctx
              match tok.tokenType with
                    | CLASS -> ctx
                    | FUN -> ctx
                    | VAR -> ctx
                    | FOR -> ctx
                    | IF -> ctx
                    | WHILE -> ctx
                    | PRINT -> ctx
                    | RETURN -> ctx
                    | _ -> 
                       let (token, ctx') = advance ctx
                       eatTokens ctx'
          else
            ctx
        else
            ctx

    let ctx' = eatTokens ctx
    let (token, ctx') = advance ctx'
    ctx'


let expressionStatement ctx =
    let (ctx', expr) = expression ctx
    let ctx', token = consume ctx' SEMICOLON "Expected ';' after expression."
    ctx', ExpressionStmt expr

let printStatement ctx = 
    let (ctx', value) = expression ctx
    let ctx', token = consume ctx' SEMICOLON "Expected ';' after value."
    ctx', PrintStmt value
 
let varDeclaration ctx =
    let ctx', name = consume ctx TokenType.IDENTIFIER "Expect variable name."
    let ctx'', matchedToken = matchParser ctx' [EQUAL]
    let ctx''', (initializer:expr option) = match matchedToken with
                                                | { matched = Some(token)} ->   let newCtx, ex = expression ctx''
                                                                                newCtx, Some(ex)
                                                | { matched = None } -> ctx'', None
    let ctx'''', semi = consume ctx''' TokenType.SEMICOLON "Expect ';' after variable declaration."
    (ctx'''',  { name = name.lexeme; guid = newGuid() }, initializer )  // TBD: name.literal??? or IDENTIFIER name.lexeme


type functionKind =
    | NONE
    | FUNCTION
    | METHOD
    | INITIALIZER
        
// Desugar FOR loop into several statements (while loop) instead of changing interpreter.
// This was just an example like in the book. This could be done in the Interperter
let desugarFor (forStmt:for_statement) =
    let body' = match forStmt.increment with
                | Some(incStmt) -> BlockStmt [forStmt.body; incStmt]
                | None -> forStmt.body
    let condition:expr = match forStmt.condition with
                            | Some(condition) -> condition
                            | None -> PrimaryExpr( BOOL { value = true; })
    let body'' = WhileStmt( { condition = condition; body = body';} )
    let body''' = match forStmt.initializer with
                     | None -> body''
                     | Some (initializer) -> BlockStmt [initializer; body'']
    //printf "%A" body'''
    body'''   


// TBD: This function is really yucky.
let rec declaration ctx = 
    try
        let ctx', matchedToken = matchParser ctx [VAR;FUN;CLASS]
        let ctx'', dec = match matchedToken with
                                                | { matched = Some(token)} -> match token.tokenType with 
                                                                                        | VAR -> let ctx'', v, opt = varDeclaration ctx'
                                                                                                 ctx'', VariableStmt({ name=v; initializer=opt})
                                                                                        | FUN -> let ctx'',f = functionDeclaration FUNCTION ctx'
                                                                                                 ctx'', FunctionStmt(f)
                                                                                        | CLASS -> let ctx'', c = classDeclaration ctx'
                                                                                                   ctx'', ClassStmt(c)
                                                                                        | _ -> failwith "INTERNAL: Need to machParser above."
                                                | { matched = None}  -> statement ctx'    
        (ctx'', Some(dec))
    with
        _ -> let ctx'' = synchronize ctx
             (ctx'', None)

and block ctx  =
    let rec addStatements ctx (statements: Stmt list) =
        if not (isAtEnd ctx) && not (check ctx TokenType.RIGHT_BRACE) then
            match (declaration ctx) with 
            | ctx', Some(statement) -> addStatements ctx' ( statement :: statements  )
            | ctx', None -> ctx', statements
        else
            ctx, statements

    let ctx', statements = addStatements ctx []
    let ctx'', token = consume ctx' RIGHT_BRACE "Except '}' after expression."
    ctx'', BlockStmt( List.rev statements)

and statement ctx   =
    let ctx', matchedToken = matchParser ctx [PRINT;LEFT_BRACE;IF;WHILE;FOR;RETURN]
    match matchedToken with
    | { matched = Some(token)} -> match token.tokenType with 
                                    | TokenType.PRINT -> printStatement ctx'
                                    | TokenType.LEFT_BRACE ->  block ctx' 
                                    | TokenType.IF -> ifStatement ctx'
                                    | TokenType.WHILE -> whileStatement ctx'
                                    | TokenType.FOR ->  let ctx'', (forStmt:for_statement) = forStatement ctx'
                                                        ctx'', (desugarFor forStmt)
                                    | TokenType.RETURN -> returnStatement ctx'
                                    | _ -> failwith "INTERNAL: match case missing"
    | { matched = None } -> expressionStatement ctx'

and returnStatement ctx =
    let keyw = previous ctx;
    let ctx', value = if( not( check ctx SEMICOLON)) then
                            expression ctx
                       else
                            ctx, PrimaryExpr( NIL)
    let ctx'', _ = consume ctx' SEMICOLON "Expected ';' after return value."
    ctx'', ReturnStmt ( { keyword = keyw.lexeme; value = value;})

and forStatement ctx: ParserContext * for_statement  = 
    let ctx', token = consume ctx LEFT_PAREN "Expected '(' after 'for'."

    let ctx'', matchedToken = matchParser ctx' [VAR;SEMICOLON]
    let ctx2,(initializer:Option<Stmt>) = match matchedToken with
                                                | {matched = Some(token)} -> match token.tokenType with
                                                                                | TokenType.VAR -> let tempCtx, id, init = varDeclaration ctx''
                                                                                                   tempCtx, Some(VariableStmt({name=id;initializer=init}))
                                                                                | TokenType.SEMICOLON -> ctx'', None;
                                                                                | _ -> failwith "Not possible?"
                                                | {matched = None } ->  let tempCtx, stm = expressionStatement ctx' // IMPORTANT: Back to previous context!
                                                                        tempCtx, Some(stm)
    let condition, ctx3 = if not ( check ctx2 SEMICOLON ) then
                                let tempCtx, exp = expression ctx2
                                Some( exp), tempCtx
                          else
                                None, ctx2
    let ctx4, token = consume ctx3 SEMICOLON "Expected ';' after loop condition."

    let (increment:Option<Stmt>), ctx5 = if not ( check ctx4 RIGHT_PAREN ) then
                                                let tempCtx, exp = statement ctx4 // BOOK Used expr for increment.
                                                Some( exp), tempCtx
                                         else
                                                None, ctx4
    let ctx6, token = consume ctx5 RIGHT_PAREN "Expected ')' after for clauses."
    let ctx7,body = statement ctx6
    ctx7, { initializer = initializer; condition= condition; increment= increment; body = body}

and whileStatement ctx = 
    let ctx', token = consume ctx LEFT_PAREN "Expected '(' after 'while'."
    let ctx'', condition = expression ctx'
    let ctx''', token = consume ctx'' RIGHT_PAREN "Expected ')' after condition."
    let ctx'''',body = statement ctx'''
    ctx'''', WhileStmt ( { condition= condition; body = body})

and ifStatement ctx =
    // TBD: Chain this together better.
    let ctx', _ = consume ctx LEFT_PAREN "Except '(' after 'if'."
    let ctx'', condition = expression ctx'
    let ctx''', _ = consume ctx'' RIGHT_PAREN "Except ')' after 'if' condition."
    let ctx'''',thenBranch = statement ctx'''
    match matchParser ctx'''' [ELSE] with
    | newCtx, { matched = Some(_)} -> let lastCtx,elseBranch = statement newCtx
                                      lastCtx, IfStmt { condition = condition;
                                      thenBranch = thenBranch;
                                      elseBranch = Some(elseBranch)}
    | lastCtx, { matched = None}  -> lastCtx, IfStmt { condition = condition;
                                     thenBranch = thenBranch;
                                     elseBranch = None }

// TBD: Will be reused later for methods.
and functionDeclaration (kind:functionKind) ctx : ParserContext * function_statement = 

    let rec matchParams paramList ctx =
        if List.length paramList >= 8 then
            errorP ctx "Cannot have more than 8 parameters." |> ignore // TBD: Better error handling?
            [], ctx
        else
            let ctx, identifier = consume ctx TokenType.IDENTIFIER "Expect parameter name."
            let name = { name = identifier.lexeme; guid = newGuid() }
            let result = name :: paramList
            let ctx'', matchedToken = matchParser ctx [COMMA]
            match matchedToken with
                                | { matched = Some(comma)} -> matchParams result ctx''
                                | { matched = _ } -> (result, ctx'') // Break recursion

    let ctx', token = consume ctx TokenType.IDENTIFIER (sprintf "Expect %A name." kind)
    let id: identifier_terminal = { name = token.lexeme; guid = newGuid() }
    let ctx'', _ = consume ctx' TokenType.LEFT_PAREN (sprintf "Expect '(' after %A name." kind)
    let parameters, ctx''' = if not( check ctx'' RIGHT_PAREN ) then
                                matchParams [] ctx''
                             else
                                [], ctx''
    let ctx4', _ = consume ctx''' TokenType.RIGHT_PAREN "Expect ')' after parameters."
    let ctx5', _ = consume ctx4' TokenType.LEFT_BRACE (sprintf "Expect '{' before %A body." kind)
    let ctx6', bodyStmt = block ctx5'  // Book did not use a BLOCK here for function body.
    ctx6', { id = id; parameters = parameters; body = bodyStmt}

and classDeclaration ctx =
    let ctx', name = consume ctx TokenType.IDENTIFIER "Expect class name."
    let id: identifier_terminal = { name = name.lexeme; guid = newGuid() } // TBD: Do I need a guid for classes?

    let ctx0, matchedToken = matchParser ctx' [LESS]
    let ctx1, optSuperclass = match matchedToken with
                                | { matched = Some(token)} -> 
                                    match token.tokenType with 
                                    | TokenType.LESS -> 
                                                let ctx1, name = consume ctx0 TokenType.IDENTIFIER "Expect superclass name."
                                                //let prevTok = (previous ctx0)
                                                let superclass = { name = name.lexeme; guid = newGuid() } // TBD: Was expr.Variable in book.
                                                ctx1, Some(superclass)
                                    | _ -> failwith (sprintf "Did not expect any other match, but found: %A" matchedToken.butFound)
                                | _ -> ctx0, None



    let ctx2, token = consume ctx1 TokenType.LEFT_BRACE "Expect '{' before class body."
    let rec addMethods ctx (methods: function_statement list) =
        if not (isAtEnd ctx) && not (check ctx TokenType.RIGHT_BRACE) then
            let ctx', method = functionDeclaration FUNCTION ctx // Methods do not have the "fun" keyword. (12.1)
            addMethods ctx' ( method :: methods  )
        else
            ctx, methods

    let ctx3, methods = addMethods ctx2 []
    let ctx4, token = consume ctx3 RIGHT_BRACE "Except '}' after expression."
    ctx4, { name = id; superclass = optSuperclass; methods = methods }
    


let parse tokens = 

    xxguid <- 1000

    let ctx = initParserContext tokens

    let rec parseStatements (ctx:ParserContext) (listOfStatements:Stmt list) =
        if not( isAtEnd ctx) then
            let ctx', s = declaration ctx
            let ctx'', xs = match s with 
                            | Some(s') -> (ctx', s' :: listOfStatements)
                            | None -> ctx', listOfStatements // Happens after a synchronize.
            parseStatements ctx'' xs
        else
            (ctx, List.rev listOfStatements)

    let (ctx', statements) = parseStatements ctx []
    statements
