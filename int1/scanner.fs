module Scanner

    // This is the lexer

    open System

    type TokenType =  LEFT_PAREN| RIGHT_PAREN| LEFT_BRACE| RIGHT_BRACE | COMMA| DOT| MINUS| PLUS| SEMICOLON| SLASH| STAR
                        // One or two character tokens.
                        | BANG| BANG_EQUAL
                        | EQUAL| EQUAL_EQUAL
                        | GREATER| GREATER_EQUAL
                        | LESS| LESS_EQUAL
                        // Literals.
                        | IDENTIFIER| STRING| NUMBER
                        // Keywords.
                        | AND| CLASS| ELSE| FALSE| FUN| FOR| IF| NIL| OR
                        | PRINT| RETURN| SUPER| THIS| TRUE| VAR| WHILE
                        | EOF


    type LiteralValue = 
        | StringLiteral of string
        | NumberLiteral of float
        | IdentifierLiteral of string


    type Token = {
        tokenType : TokenType
        lexeme: string
        literal: Option<LiteralValue>
        line: int
        }

    type ScannerContext = {
        source: string
        ch: char option // will be None at EOF
        current: int
        atEnd: bool
        start: int
        line: int
        hadError: bool
        tokens: Token list
        }


    let peek (ctx:ScannerContext)  =
        Seq.tryItem ctx.current ctx.source // Return None at end.

    let peekNext ctx  =
        Seq.tryItem (ctx.current + 1) ctx.source // Return None at end.

    let advance ctx  =
        let newch = peek ctx
        let result = {
            ctx with 
                current = ctx.current+1; 
                ch = newch
                atEnd = (newch = None)
        }
        result


    let addTokenWithLiteral tokenType objectLiteral lexeme ctx  =
        let token = {
            tokenType = tokenType;
            lexeme = lexeme
            literal = objectLiteral;
            line = ctx.line;
        }
        let result = { 
            ctx with
                tokens = token :: ctx.tokens 
        }
        result
    
    
    let addToken  tokenType lexeme ctx = 
        let literal = None
        addTokenWithLiteral  tokenType literal lexeme ctx

    let isAtEnd ctx =
        ctx.atEnd

    // It's like a conditional "advance". It only consumes the character if it's what we're looking for.
    let matchChar  expected ctx = 
        match peek ctx with
        | Some(ch) when ch = expected -> (true, advance ctx)
        | _ -> (false, ctx)
   
 
    let addTokenOptionalEqual  tokenType tokenTypeWithEqual lexeme ctx = 
        match matchChar '=' ctx with
        | (true,newctx) ->
            addTokenWithLiteral  tokenTypeWithEqual None (lexeme+"=") newctx
        | (false, newctx) ->
            addTokenWithLiteral  tokenType None lexeme newctx


    let report line where message =
        printfn "[line %A] Error%A:%A" line where message


    let error  message ctx =
        report ctx.line "" message
        { ctx with hadError = true; }


    let rec consumeUntilEndOfLine ctx =
        if( not ( peek ctx = Some('\n')) && (not (isAtEnd ctx)) ) then
            ctx |> advance  
                |> consumeUntilEndOfLine
        else
            ctx
    

    let advanceIfMatch ch ctx =
        if ( peek ctx = Some(ch)) then   
            advance ctx
        else
            ctx

    let rec stringLiteral ctx =
        if( not ( peek ctx = Some('\"')) && (not (isAtEnd ctx)) ) then
            // Support multiline strings
            ctx |> advanceIfMatch '\n' |> advance  |> stringLiteral  
        else
            if isAtEnd ctx then
                error  "Unterminated string" ctx
            else
                // TBD: Simplify
                let advancedCtx = advance  ctx // Closing "
                let value = advancedCtx.source.[advancedCtx.start+1 .. advancedCtx.current-2]
                let literal = Some(StringLiteral value)
                addTokenWithLiteral  STRING literal value advancedCtx



    let isDigit (ch: char option) =
        match ch with
            |  Some(c) when (c >= '0' && c <= '9') -> true
            | _ -> false

    let isAlpha ch =
        match ch with
        | Some(ch) when (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch = '_' -> true
        | _ -> false

    let isAlphaNumeric ch =
        isAlpha ch || isDigit ch

    // TBD: Similar to consumeUntilEndOfLine
    let rec consumeDigits ctx =
        if isDigit( peek ctx ) then
            ctx |> advance  
                |> consumeDigits  
        else
            ctx

    let consumeFractionalPart ctx =
        match peek ctx with 
        | Some('.') when isDigit( peekNext ctx) ->
            ctx |> advance  
                |> consumeDigits 
        | _ -> ctx

    let rec identifier ctx  =
        if isAlphaNumeric (peek ctx ) then
            identifier (advance ctx ) 
        else
            let text = ctx.source.[ctx.start .. ctx.current-1]
            match text with
                | "and" -> addToken  AND text ctx
                | "class" -> addToken CLASS text ctx
                | "else" -> addToken  ELSE text ctx
                | "false" -> addToken  FALSE text ctx
                | "for" -> addToken  FOR text ctx
                | "fun" -> addToken  FUN text ctx
                | "if" -> addToken  IF text ctx
                | "nil" -> addToken  NIL text ctx
                | "or" -> addToken  OR text ctx
                | "print" -> addToken  PRINT text ctx
                | "return" -> addToken  RETURN text ctx
                | "super" -> addToken  SUPER text ctx
                | "this" -> addToken  THIS text ctx
                | "true" -> addToken  TRUE text ctx
                | "var" -> addToken  VAR text ctx
                | "while" -> addToken  WHILE text ctx
                | _ -> 
                    let identifierLiteral = Some(IdentifierLiteral text)
                    addTokenWithLiteral IDENTIFIER identifierLiteral text ctx

        

    let numberLiteral  ctx =


        let newCtx2 = ctx |> consumeDigits   
                          |> consumeFractionalPart  
        // TBD: Cleanup
        let digitString = ctx.source.[ctx.start .. ctx.current-1]
        let ff = Double.Parse digitString
        let literal = Some(NumberLiteral ff)
        addTokenWithLiteral NUMBER literal digitString newCtx2 

        // Active patterns used to pattern match tokens.
    let (|Alpha|_|) (ch:char option) =
        if isAlpha ch then
            Some()
        else
            None

    let (|Digit|_|) (ch:char option) =
        if isDigit ch then
            Some()
        else
            None


    let addCommentOrSlash ctx =
        match matchChar   '/'  ctx with
        |  (true, newctx) -> consumeUntilEndOfLine newctx 
        | (false, newctx) -> addToken SLASH "/" newctx

    let advanceLine (ctx:ScannerContext) =
        { ctx with line=ctx.line+1}

    let scanToken ctx =
        let ctx = advance  ctx
        match ctx.ch with
            | Some('(') -> addToken LEFT_PAREN "(" ctx
            | Some(')') -> addToken RIGHT_PAREN ")" ctx
            | Some('{') -> addToken LEFT_BRACE "{" ctx
            | Some( '}') -> addToken RIGHT_BRACE "}" ctx
            | Some( ',') -> addToken COMMA "," ctx
            | Some( '.') -> addToken DOT "." ctx
            | Some( '-' ) -> addToken MINUS "-" ctx
            | Some( '+' ) -> addToken PLUS "+" ctx
            | Some( ';' ) -> addToken SEMICOLON ";" ctx
            | Some( '*' ) -> addToken STAR "*" ctx
            | Some( '!' ) -> addTokenOptionalEqual   BANG BANG_EQUAL "!" ctx
            | Some( '=' ) -> addTokenOptionalEqual   EQUAL EQUAL_EQUAL "=" ctx
            | Some( '<' ) -> addTokenOptionalEqual   LESS LESS_EQUAL "<" ctx
            | Some( '>' ) -> addTokenOptionalEqual   GREATER GREATER_EQUAL ">" ctx
            | Some( '/' ) -> addCommentOrSlash ctx
            | Some( ' ') -> ctx
            | Some( '\r') -> ctx
            | Some( '\t') -> ctx
            | Some( '\n') -> advanceLine ctx
            | Some( '"') -> stringLiteral  ctx
            | Digit -> numberLiteral  ctx 
            | Alpha -> identifier  ctx
            | _ -> ctx




    let initScanContext source  =
        {
        source = source;
        current = 0;
        atEnd = false; // TBD: We might be at end?
        start = 0;
        line = 1;
        hadError = false;
        ch = None; // TBD: Is this really a good idea? We might not be at end?
        tokens = [];
        }


    let moveToCurrent ctx:ScannerContext =
        { ctx with start = ctx.current; }

    let reverseTokens ctx:ScannerContext =
        { ctx with tokens = List.rev ctx.tokens }

    let rec scanTokens (ctx:ScannerContext) : ScannerContext =
        if not (isAtEnd ctx ) then
                ctx |> moveToCurrent
                    |> scanToken 
                    |> scanTokens // Recurse
           else
                ctx |> addToken  EOF "EOF" 
                    |> reverseTokens // List is backwards, because we accumulate from start.
 
    let scan source =
        ( initScanContext source |> scanTokens  ).tokens // TBD: maybe return context???
