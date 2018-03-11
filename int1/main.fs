// F# interpreter

open System
open System.IO
open Scanner
open Parser

let run source =
    let ctx = initScanContext // TBD: Hide inside like we did for parse below.
    let newCtx = scanTokens ctx source
    printfn "%A" newCtx.tokens

    let expression = parse newCtx.tokens
    printfn "%A" expression

let runPrompt x =
    while true do
        printf "> "
        run(Console.ReadLine()) |> ignore

let runFile path =
    let text = File.ReadAllText path
    run text



[<EntryPoint>]
let main argv =
    printfn "Hello World from F#!"

    let e = MultiplicationExpr( 
                PRIMARY(NUMBER {value = 2.0}),  
                MORE( [ MUL, UNARY( BANG, UnaryExpr(PRIMARY( NUMBER {value = 1.0}))) ])) 
    printfn "%A" e


//    let e2 = AdditionExpr( MultiplicationExpr(
//                PRIMARY(STRING {value = "TEST"}),  
//                MORE( [ MUL, UNARY_OPERATOR( BANG, PRIMARY( NUMBER {value = 1.0})) ])) ) 
//    printfn "%A" e


    prettyPrint e
    if ((Array.length argv) > 1) then
            printfn "Usage: jlox [script]"
        else 
            if (Array.length argv = 1) then
                runFile argv.[0]
            else 
                runPrompt ""
        

    0 // return an integer exit code


