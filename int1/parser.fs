module Parser
open Scanner
open System.Linq.Expressions

// TERMINALS
type number_terminal = { value: float }
type string_terminal = { value: string }
type boolean_terminal = { value: bool }
type identifier_terminal = { name : string }

#if OLD
//type nil_terminal = NILTERMINAL

type open_paren_terminal = OPEN
type close_paren_terminal = CLOSE



//type combOr<'t,'u> =
//        | T of 't
//        | U of 'u
#endif

#if OLD
// *
type zeroOrMore<'t> = 
    | ZERO
    | MORE of List<'t>

// +
type oneOrMore<'t> = List<'t>

// ? 
type oneOrNone<'t> = Option<'t>
#endif

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





#if OLD
type expr =
    | EqualityExprssion
    | GroupingExpr of open_paren_terminal * expr * close_paren_terminal
    | BinaryExpr of expr * operator * expr
    | UnaryExpr of combOr<unary_operator * expr, primary>
    | MultiplicationExpr of unary_operator * expr * zeroOrMore< mul_operator * unary_operator * expr>
    | PrimaryExpr of primary
#endif



type expr =
    // These are for order of operations
#if OLD
    | EqualityExpr of equality
    | ComparisonExpr of comparison
    | AdditionExpr of addition
    | MultiplicationExpr of multiplication
#endif
    // These are outputs
    | UnaryExpr of unary 
    | PrimaryExpr of primary
    | BinaryExpr of binary
    | GroupingExpr of grouping
    | AssignExpr of assign
    | LogicalExpr of logical

    //| Expression of expr
and binary = expr * binary_operator * expr // Left/Operator/Right   <- binary_operator different from book.
and logical = expr * logical_operator * expr // Left/Operator/Right   <- logical_operator different from book.
and grouping = expr
and primary = 
    | NUMBER of number_terminal 
    | STRING of string_terminal
    | BOOL of boolean_terminal
    | NIL //of nil_terminal
    | IDENTIFIER of identifier_terminal
    | THIS 
and unary = 
    | UNARY of unary_operator * expr // TBD: Does not match book.
    | PRIMARY of primary // <-- Without this we never "FINISH".
and assign = (identifier_terminal * expr) // name * value  // TBD: Book used a token instead of identifier terminal
#if OLD
and multiplication = unary * zeroOrMore< mul_operator * unary>

and addition = multiplication * zeroOrMore< add_operator * multiplication>

and comparison = addition * zeroOrMore< comparison_operator * addition>

and equality = comparison * zeroOrMore< equal_operator * comparison>


type expression = equality
#endif

type Stmt =
    | Expression of expr // Just evaluates to a value, and then is ignored.
    | Print of expr
    | Variable of identifier_terminal * Option<expr> // name * initializer  <- // TBD: Not in book.
    | Block of Stmt list
    | If of expr * Stmt * Stmt option // condition  thenBranch  elseBranch
    | While of expr * Stmt // condition * body
    | ForStmt of for_statement   
and for_statement =  Option<Stmt> * Option<expr> * Option<Stmt> * Stmt   // initializer * condition * increment * statement

#if FALSE
let (^^) p q = not(p && q) && (p || q) // makeshift xor operator

let rec eval = function
    | True          -> true
    | And(e1, e2)   -> eval(e1) && eval(e2)
    | Nand(e1, e2)  -> not(eval(e1) && eval(e2))
    | Or(e1, e2)    -> eval(e1) || eval(e2)
    | Xor(e1, e2)   -> eval(e1) ^^ eval(e2)
    | Not(e1)       -> not(eval(e1))
*/

let (|ZOM|) (c:zeroOrMore<'t>) =
    match c with 
        | MORE z -> Some(c)
        | ZERO -> None
#endif

let rec prettyPrint (e:expr)  =
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
                                prettyPrint left
                                printfn "%A" op
                                prettyPrint right
        | UnaryExpr e ->        match e with 
                                | UNARY (op,right) ->   match op with
                                                        | BANG -> printf "!"
                                                        | NEGATIVE -> printf "-"
                                | PRIMARY p -> prettyPrint (PrimaryExpr p)
        | PrimaryExpr e -> match e with 
                            | NUMBER n-> printfn "%f" n.value
                            | STRING s -> printfn "%s" s.value
                            | BOOL b -> printfn "%A" b.value
                            | NIL -> printfn "NIL"
                            | IDENTIFIER ii -> printfn "%s" ii.name
                            | THIS -> printfn "THIS"
        | GroupingExpr e ->    printf "("
                               prettyPrint e
                               printf ")"
        | AssignExpr e -> let name,value =e
                          printfn  "var %s =" name.name 
                          prettyPrint value
        | LogicalExpr e ->      let left,op,right = e
                                prettyPrint left
                                printfn "%A" op
                                prettyPrint right
        //| _ -> failwith "Not expected."



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


// The most recently consume token (might be better to just store that).
let previous ctx =
    ctx.tokens.[ctx.current-1]

let advance ctx = 
    if not (isAtEnd ctx) then
        let ctx' = { ctx with current=ctx.current+1 } // THis is stupid.
        (previous ctx', ctx')
        
    else
        (previous ctx, ctx)
   
let matchParser ctx tokenTypeList =
    let isFilter ctx token =
        check ctx token
    match List.tryFind (isFilter ctx) tokenTypeList with 
    | Some(_)  -> 
        let token, newCtx = advance ctx
        (newCtx, Some(token))
    | None -> (ctx, None)

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
// primary → NUMBER | STRING | "false" | "true" | "nil" | "(" expression ")" | IDENTIFIER | THIS ;
let rec primary ctx =
    let ctx', matchedToken = matchParser ctx [FALSE; TRUE; TokenType.NIL; TokenType.NUMBER; TokenType.STRING; LEFT_PAREN; TokenType.IDENTIFIER; TokenType.THIS]
    match matchedToken with
    | Some(token) ->
        match token.tokenType with
        | FALSE ->
            let result = PrimaryExpr ( BOOL { value= false}) // TBD: In book was LiteralExpr
            ctx', result
        | TRUE ->
            let result = PrimaryExpr ( BOOL { value= true}) // TBD: In book was LiteralExpr
            ctx', result
        | TokenType.NIL ->
            let result = PrimaryExpr ( NIL ) // TBD: In book was LiteralExpr
            ctx', result
        | TokenType.NUMBER ->
            let prevTok = (previous ctx')
            let result = PrimaryExpr ( NUMBER { value= derefNumber prevTok.literal }) // TBD: In book was LiteralExprLiteralExpr (previous ctx).literal
            ctx', result
        | TokenType.STRING ->
            let prevTok = (previous ctx')
            let result = PrimaryExpr ( STRING { value= derefString prevTok.literal}) // TBD: In book was LiteralExprLiteralExpr (previous ctx).literal
            ctx', result
        | TokenType.LEFT_PAREN ->
            let ctx'', ex = expression ctx'
            let ctx''', token = consume ctx'' RIGHT_PAREN "Except ')' after expression."
            let result = GroupingExpr ex
            ctx''', result
        | TokenType.THIS ->
            let result = PrimaryExpr ( NIL ) // TBD: In book was LiteralExpr
            ctx', result // TBD
        | TokenType.IDENTIFIER ->
            let prevTok = (previous ctx')
            let result = PrimaryExpr( IDENTIFIER { name = prevTok.lexeme }) // TBD: Maybe makes sense for identifier to be a literal.
            ctx', result
        | _ -> 
            let newCtx = errorP ctx "Expect expression not in set..."
            failwith "Expect expression not in set..."
    | None ->
        let newCtx = errorP ctx "Expect expression."
        failwith "Expect expression"
            

 // Have to use "AND" below because expression is circular.
and unary ctx : ParserContext* expr   =
    let isMatched = matchParser ctx [TokenType.BANG; TokenType.MINUS]
    match isMatched with
    | ctx', Some(token) ->
        let tokOp = previous ctx'
        let newCtx, right = unary ctx'
        match tokOp.tokenType with
        | TokenType.BANG ->
            let result = UnaryExpr (UNARY(unary_operator.BANG, right))   // TBD: This is a horrible convert
            newCtx, result
        | TokenType.MINUS ->
            let result = UnaryExpr (UNARY(unary_operator.NEGATIVE, right)) // TBD: This is a horrible convert
            newCtx, result
        | _ -> failwith "Invalid unary operator"

    | ctx', None ->
        primary ctx'

and moreLogical lstTokens parentFunc (ctx, ex1) =
     //let ctx', expr = parentFunc ctx
     let ctx' = ctx

     match matchParser ctx' lstTokens with
     | ctx'', Some(matchedToken) ->  let ctx''', right = parentFunc ctx''
                                     let opLogical = makeLogicalOp matchedToken
                                     let expr2 = LogicalExpr (ex1, opLogical, right)
                                     moreLogical lstTokens parentFunc (ctx''', expr2)
     | ctx'', None ->
        ctx'', ex1

and moreBinary lstTokens (ctx,ex1)  =
    match matchParser ctx lstTokens with
    | ctx', Some(matchedToken) ->
        let opBinary = makeBinaryOp matchedToken
        match expression ctx' with 
        | ctx', UnaryExpr u ->match u with 
                                        | PRIMARY p -> 
                                            // Stop recursion
                                            let expr2 = BinaryExpr (ex1, opBinary, PrimaryExpr p )
                                            moreBinary lstTokens (ctx', expr2) 
                                            //newCtx, expr2
                                        | UNARY (op,exprRight) -> 
                                            // Recurse
                                            let unRight = UnaryExpr (UNARY (op, exprRight))
                                            let expr2 = BinaryExpr (ex1, opBinary, unRight )
                                            moreBinary lstTokens (ctx', expr2) 
        | ctx', PrimaryExpr p -> let expr2 = BinaryExpr( ex1, opBinary, PrimaryExpr p) // This case needed because primary() function can return lots of things.
                                 moreBinary lstTokens (ctx', expr2) 
        | ctx', GroupingExpr g ->   let expr2 = BinaryExpr( ex1, opBinary, GroupingExpr g)
                                    moreBinary lstTokens (ctx', expr2) 
        | ctx', BinaryExpr b -> moreBinary lstTokens (ctx', BinaryExpr( ex1, opBinary, BinaryExpr b))
        | _ -> failwith "did not expect any other kind of exprssion"
    | ctx', None ->
        ctx', ex1


#if OLD
let rec moreUnary ctx lstTokens =
    match matchParser ctx lstTokens with
    | true, newCtx ->
        let tokOp, newCtx = previous newCtx
        let newCtx, exprRight = unary newCtx
        let expr2 = UnaryExpr (tokOp,exprRight)
        moreUnary newCtx lstTokens
    | false, newCtx ->
        newCtx, primary ctx
#endif




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
        | ctx'', Some(token) ->
            let ctx''', value = assignment ctx'' // Recursive
            match ex with
            | PrimaryExpr p ->
                match p with
                | IDENTIFIER ii -> 
                    ctx''', AssignExpr (ii, value)
            | _ ->  let equals = previous ctx'' // This gets printed on error.
                    failwith (sprintf "Invalid assignment target %A" equals)

        | ctx'', None ->
            (ctx'', ex)


and expression ctx : ParserContext * expr = // This is weirdo.
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
    ctx', Expression expr

let printStatement ctx = 
    let (ctx', value) = expression ctx
    let ctx', token = consume ctx' SEMICOLON "Expected ';' after value."
    ctx', Print value
 
    



let varDeclaration ctx =
    let ctx', name = consume ctx TokenType.IDENTIFIER "Expect variable name."
    let ctx'', matchedToken = matchParser ctx' [EQUAL]
    let ctx''', (initializer:expr option) = match matchedToken with
                                                | Some(token) -> let newCtx, ex = expression ctx''
                                                                 newCtx, Some(ex)
                                                | None -> ctx'', None
    let ctx'''', semi = consume ctx''' TokenType.SEMICOLON "Expect ';' after variable declaration."
    (ctx'''', Variable ( { name = name.lexeme}, initializer ) ) // TBD: name.literal??? or IDENTIFIER name.lexeme
    
// Desugar FOR loop into several statements (while loop) instead of changing interpreter.
// This was just an example like in the book. This could be done in the Interperter
let desugarFor (forStmt:for_statement) =
    let initializer, conditionOption, increment, body = forStmt
    let body' = match increment with
                | Some(incStmt) -> Block [body; incStmt]
                | None -> body
    let condition:expr = match conditionOption with
                        | Some(condition) -> condition
                        | None -> PrimaryExpr( BOOL { value = true; })
    let body'' = While( condition, body')
    let body''' = match initializer with
                     | None -> body''
                     | Some (initializer) -> Block [initializer; body]
    body'''                   

let rec declaration ctx = 
    try
        let ctx', matchedToken = matchParser ctx [VAR]
        let ctx'', dec = match matchedToken with
                                        | Some(token) -> varDeclaration ctx'
                                        | None -> statement ctx'    
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
    ctx'', Block (List.rev statements)


and statement ctx   =
    let ctx', matchedToken = matchParser ctx [PRINT;LEFT_BRACE;IF;WHILE;FOR]
    match matchedToken with
    | Some(token) -> match token.tokenType with 
                        | TokenType.PRINT -> printStatement ctx'
                        | TokenType.LEFT_BRACE ->  block ctx' 
                        | TokenType.IF -> ifStatement ctx'
                        | TokenType.WHILE -> whileStatement ctx'
                        | TokenType.FOR ->  let ctx'', (forStmt:for_statement) = forStatement ctx'
                                            ctx'', (desugarFor forStmt)
    | None -> expressionStatement ctx'

and forStatement ctx: ParserContext * for_statement  = 
    let ctx', token = consume ctx LEFT_PAREN "Expected '(' after 'for'."

    let ctx'', matchedToken = matchParser ctx [VAR;SEMICOLON]
    let ctx2,(initializer:Option<Stmt>) = match matchedToken with
                                            | Some(token) -> match token.tokenType with
                                                                                    | TokenType.VAR -> let tempCtx, stm = varDeclaration ctx''
                                                                                                       tempCtx, Some(stm)
                                                                                    | TokenType.SEMICOLON -> ctx'', None;
                                                                                    | _-> let tempCtx, stm = expressionStatement ctx' // IMPORTANT: Back to previous context!
                                                                                          tempCtx, Some(stm)
                                            | None -> failwith "Expected token after '(' in 'for'." // Not in book.
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
    ctx7, (initializer, condition, increment, body)

and whileStatement ctx = 
    let ctx', token = consume ctx LEFT_PAREN "Expected '(' after 'while'."
    let ctx'', condition = expression ctx'
    let ctx''', token = consume ctx'' RIGHT_PAREN "Expected ')' after condition."
    let ctx'''',body = statement ctx'''
    ctx'''', While (condition, body)

and ifStatement ctx =
    // TBD: Chain this together better.
    let ctx', token = consume ctx LEFT_PAREN "Except '(' after 'if'."
    let ctx'', condition = expression ctx'
    let ctx''', token = consume ctx'' RIGHT_PAREN "Except ')' after 'if' condition."
    let ctx'''',thenBranch = statement ctx'''
    match matchParser ctx'''' [ELSE] with
    | newCtx, Some(token) -> let lastCtx,elseBranch = statement newCtx
                             lastCtx, If (condition, thenBranch, Some(elseBranch))
    | lastCtx, None -> lastCtx, If (condition, thenBranch, None)

let parse tokens = 
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
