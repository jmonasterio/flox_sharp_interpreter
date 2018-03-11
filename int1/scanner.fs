module Scanner

    open System
    open System.IO

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
        ch: char
        current: int
        start: int
        line: int
        hadError: bool
        tokens: Token list
        }



    let advance ctx source =
        let result = {
            ctx with 
                current = ctx.current+1;
                ch = Seq.item ctx.current source
        }
        result


    let addTokenWithLiteral ctx tokenType objectLiteral =
        let token = {
            tokenType = tokenType;
            lexeme = "ch???"; // TBD
            literal = objectLiteral;
            line = ctx.line;
        }
        let result = { 
            ctx with
                tokens = token :: ctx.tokens 
        }
        result
    
    
    let addToken ctx tokenType = 
        let literal = None
        addTokenWithLiteral ctx tokenType literal

    let isAtEnd ctx source =
        ctx.current >= String.length source

    // It's like a conditional "advance". It only consumes the character if it's what we're looking for.
    let matchChar ctx source expected = 
        if isAtEnd ctx source then
            (false, ctx)
        else
            if not (Seq.item ctx.current source = expected) then
                (false, ctx)
            else
                (true, { ctx with current = ctx.current + 1;})
            
   
 
    let addTokenOptionalEqual ctx source tokenType tokenTypeWithEqual = 
        let (matched,newctx) = matchChar ctx source '='
        if matched then
            addTokenWithLiteral newctx tokenTypeWithEqual None
        else
            addTokenWithLiteral newctx tokenType None


    let report line where message =
        printfn "[line %A] Error%A:%A" line where message


    let error ctx message =
        report ctx.line "" message
        { ctx with hadError = true; }

    let peek ctx source =
        if isAtEnd ctx source then
            '\x00'
        else
            Seq.item ctx.current source   // change to better syntax

    let peekNext ctx (source:string) =
        let nextPos = ctx.current + 1
        if( nextPos >= String.length source) then 
            '\x00'
        else
            Seq.item nextPos source  //source.[nextPos]

    let rec consumeUntilEndOfLine ctx source =
        if( not ( peek ctx source = '\n') && (not (isAtEnd ctx source)) ) then
            let newctx = advance ctx source
            consumeUntilEndOfLine newctx source
        else
            ctx
    
    let rec stringLiteral ctx source =
        if( not ( peek ctx source = '\"') && (not (isAtEnd ctx source)) ) then
            // Support multiline strings
            let newCtx = if ( peek ctx source = '\n') then   
                            { ctx with current = ctx.current+1}
                            else
                            ctx
            let advancedCtx = advance newCtx source
            stringLiteral advancedCtx source
        else
            if isAtEnd ctx source then
                error ctx "Unterminated string"
            else
                let advancedCtx = advance ctx source // Closing "
                let value = source.[advancedCtx.start+1 .. advancedCtx.current-1]
                let literal = Some(StringLiteral value)
                addTokenWithLiteral ctx STRING literal



    let isDigit ch =
        match ch with
            |  '0' -> true
            |  '1' -> true
            |  '2' -> true
            |  '3' -> true
            |  '4' -> true
            |  '5' -> true
            |  '6' -> true
            |  '7' -> true
            |  '8' -> true
            |  '9' -> true
            | _ -> false

    let isAlpha ch =
        (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch = '_'

    let rec consumeDigits ctx source =
        if isDigit( peek ctx source) then
            let newCtx = advance ctx source 
            consumeDigits newCtx source
        else
            ctx

    let consumeFractionalPart ctx source =
        if (peek ctx source) = '.' && isDigit( peekNext ctx source) then
            let ctxNext = advance ctx source
            consumeDigits ctxNext source
        else
            ctx

    let rec identifier ctx (source:string) =
        if isAlpha (peek ctx source) then
            identifier (advance ctx source) source
        else
            let text = source.[ctx.start .. ctx.current-1]
            match text with
                | "and" -> addToken ctx AND
                | "class" -> addToken ctx CLASS
                | "else" -> addToken ctx ELSE
                | "false" -> addToken ctx FALSE
                | "for" -> addToken ctx FOR
                | "fun" -> addToken ctx FUN
                | "if" -> addToken ctx IF
                | "nil" -> addToken ctx NIL
                | "or" -> addToken ctx OR
                | "print" -> addToken ctx PRINT
                | "return" -> addToken ctx RETURN
                | "super" -> addToken ctx SUPER
                | "this" -> addToken ctx THIS
                | "true" -> addToken ctx TRUE
                | "var" -> addToken ctx VAR
                | "while" -> addToken ctx WHILE
                | _ -> 
                    let identifierLiteral = Some(IdentifierLiteral text)
                    addTokenWithLiteral ctx IDENTIFIER identifierLiteral

        

    let numberLiteral ctx (source:string) =
        let newCtx = consumeDigits ctx source
        let newCtx2 = consumeFractionalPart newCtx source
        let ff = Double.Parse source.[newCtx2.start .. newCtx2.current-1]
        let literal = Some(NumberLiteral ff)
        addTokenWithLiteral newCtx2 NUMBER literal

        // Active patterns used to pattern match tokens.
    let (|Alpha|_|) (ch:char) =
        if isAlpha ch then
            Some()
        else
            None

    let (|Digit|_|) (ch:char) =
        if isDigit ch then
            Some()
        else
            None


    let scanToken ctx source =
        let ctx = advance ctx source
        match ctx.ch with
            | '(' -> addToken ctx LEFT_PAREN
            | ')' -> addToken ctx RIGHT_PAREN
            | '{' -> addToken ctx LEFT_BRACE
            | '}' -> addToken ctx RIGHT_BRACE
            | ',' -> addToken ctx COMMA
            | '.' -> addToken ctx DOT
            | '-' -> addToken ctx MINUS
            | '+' -> addToken ctx PLUS
            | ';' -> addToken ctx SEMICOLON
            | '*' -> addToken ctx STAR
            | '!' -> addTokenOptionalEqual ctx source BANG BANG_EQUAL
            | '=' -> addTokenOptionalEqual ctx source EQUAL EQUAL_EQUAL
            | '<' -> addTokenOptionalEqual ctx source LESS LESS_EQUAL
            | '>' -> addTokenOptionalEqual ctx source GREATER GREATER_EQUAL
            | '/' -> let (matched, newctx) = matchChar ctx source '/'
                     if  matched then
                        consumeUntilEndOfLine newctx source
                     else
                        addToken newctx SLASH
            | ' ' -> ctx
            | '\r' -> ctx
            | '\t' -> ctx
            | '\n' -> { ctx with line=ctx.line+1}
            | '"' -> stringLiteral ctx source
            | Digit -> numberLiteral ctx source
            | Alpha -> identifier ctx source
            | _ -> ctx




    let initScanContext  =
        let newCtx = {
            current = 0;
            start = 0;
            line = 1;
            hadError = false;
            ch = ' ';
            tokens = [];
            }
        newCtx    


    let moveToCurrent ctx:ScannerContext =
        let result =  { ctx with
                            start = ctx.current;
                            }
        result

    let rec scanTokens ctx source =
        if not (isAtEnd ctx source) then
                let ctx' = moveToCurrent ctx
                let ctx' = scanToken ctx' source
                scanTokens ctx' source
            else
               let ctx' = addToken ctx EOF
               let ctx' = { ctx' with tokens = List.rev ctx'.tokens } // List is backwards, because we accumulate from start.
               ctx'
 
