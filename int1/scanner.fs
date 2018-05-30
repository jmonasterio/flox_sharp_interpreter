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



    let advance source ctx  =
        let result = {
            ctx with 
                current = ctx.current+1;
                ch = Seq.item ctx.current source
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

    let isAtEnd source ctx =
        ctx.current >= String.length source

    // It's like a conditional "advance". It only consumes the character if it's what we're looking for.
    let matchChar  source expected ctx = 
        if isAtEnd source ctx then
            (false, ctx)
        else
            if not (Seq.item ctx.current source = expected) then
                (false, ctx)
            else
                (true, { ctx with current = ctx.current + 1;})
            
   
 
    let addTokenOptionalEqual  source tokenType tokenTypeWithEqual lexeme ctx = 
        let (matched,newctx) = matchChar source '=' ctx 
        if matched then
            addTokenWithLiteral  tokenTypeWithEqual None (lexeme+"=") newctx
        else
            addTokenWithLiteral  tokenType None lexeme newctx


    let report line where message =
        printfn "[line %A] Error%A:%A" line where message


    let error  message ctx =
        report ctx.line "" message
        { ctx with hadError = true; }

    let peek source (ctx:ScannerContext)  =
        if isAtEnd source ctx then
            None
        else
            Some( Seq.item ctx.current source )  // TBD change to better syntax

    let peekNext (source:string) ctx  =
        let nextPos = ctx.current + 1
        if( nextPos >= String.length source) then 
            None
        else
            Some(Seq.item nextPos source ) // TBD: Try item

    let rec consumeUntilEndOfLine source ctx =
        if( not ( peek  source ctx = Some('\n')) && (not (isAtEnd source ctx)) ) then
            ctx |> advance source 
                |> consumeUntilEndOfLine source
        else
            ctx
    
    let rec stringLiteral source ctx =
        if( not ( peek source ctx = Some('\"')) && (not (isAtEnd source ctx)) ) then
            // Support multiline strings
            let newCtx = if ( peek source ctx = Some('\n')) then   
                            { ctx with current = ctx.current+1}
                            else
                            ctx
            newCtx |> advance source |> stringLiteral source 
        else
            if isAtEnd source ctx then
                error  "Unterminated string" ctx
            else
                // TBD: Simplify
                let advancedCtx = advance source ctx // Closing "
                let value = source.[advancedCtx.start+1 .. advancedCtx.current-2]
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

    let rec consumeDigits source ctx =
        if isDigit( peek source ctx ) then
            ctx |> advance source 
                |> consumeDigits source 
        else
            ctx

    let consumeFractionalPart source ctx =
        if (peek source ctx) = Some('.') && isDigit( peekNext source ctx) then
            ctx |> advance source 
                |> consumeDigits source
        else
            ctx

    let rec identifier (source:string) ctx  =
        if isAlphaNumeric (peek source ctx ) then
            identifier source (advance source ctx ) 
        else
            let text = source.[ctx.start .. ctx.current-1]
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

        

    let numberLiteral  (source:string) ctx =
        let newCtx2 = ctx |> consumeDigits  source 
                          |> consumeFractionalPart source 
        // TBD: Cleanup
        let digitString = source.[newCtx2.start .. newCtx2.current-1]
        let ff = Double.Parse digitString
        let literal = Some(NumberLiteral ff)
        addTokenWithLiteral NUMBER literal digitString newCtx2 

        // Active patterns used to pattern match tokens.
    let (|Alpha|_|) (ch:char) =
        if isAlpha (Some(ch)) then
            Some()
        else
            None

    let (|Digit|_|) (ch:char) =
        if isDigit (Some(ch)) then
            Some()
        else
            None


    let scanToken source ctx =
        let ctx = advance source ctx
        match ctx.ch with
            | '(' -> addToken LEFT_PAREN "(" ctx
            | ')' -> addToken RIGHT_PAREN ")" ctx
            | '{' -> addToken LEFT_BRACE "{" ctx
            | '}' -> addToken RIGHT_BRACE "}" ctx
            | ',' -> addToken COMMA "," ctx
            | '.' -> addToken DOT "." ctx
            | '-' -> addToken MINUS "-" ctx
            | '+' -> addToken PLUS "+" ctx
            | ';' -> addToken SEMICOLON ";" ctx
            | '*' -> addToken STAR "*" ctx
            | '!' -> addTokenOptionalEqual  source BANG BANG_EQUAL "!" ctx
            | '=' -> addTokenOptionalEqual  source EQUAL EQUAL_EQUAL "=" ctx
            | '<' -> addTokenOptionalEqual  source LESS LESS_EQUAL "<" ctx
            | '>' -> addTokenOptionalEqual  source GREATER GREATER_EQUAL ">" ctx
            | '/' -> let (matched, newctx) = matchChar  source '/'  ctx
                     if  matched then
                        consumeUntilEndOfLine source newctx 
                     else
                        addToken SLASH "/" newctx
            | ' ' -> ctx
            | '\r' -> ctx
            | '\t' -> ctx
            | '\n' -> { ctx with line=ctx.line+1}
            | '"' -> stringLiteral source ctx
            | Digit -> numberLiteral source ctx 
            | Alpha -> identifier source ctx
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

    let rec scanTokens (source:string) (ctx:ScannerContext) : ScannerContext =
        if not (isAtEnd source ctx ) then
                let ctx' = moveToCurrent ctx
                let ctx'' = scanToken source ctx'
                scanTokens source ctx''
            else
               let ctx' = addToken  EOF "EOF" ctx
               { ctx' with tokens = List.rev ctx'.tokens } // List is backwards, because we accumulate from start.
 
    let scan source =
        ( initScanContext |> scanTokens source ).tokens
