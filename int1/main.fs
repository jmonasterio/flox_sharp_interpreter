// F# interpreter
open System
open System.IO
open Scanner
open Parser
open Interpreter

let run source =
    let tokens = scan source
    try
        //printfn "%A" tokens
        let statementList = parse tokens
        //printfn "%A" statementList
        interpret statementList
    with
    | :? System.Exception as ex -> printfn "FAIL: %A" ex.Message


let runPrompt x =
    while true do
        printf "> "
        run(Console.ReadLine()) |> ignore

let runFile path =
    let text = File.ReadAllText path
    run text



[<EntryPoint>]
let main argv =
    printfn "flox#"

#if OLD
    let e = BinaryExpr( 
                PrimaryExpr( Parser.NUMBER {value = 2.0}), 
                MULTIPLY_OP MUL, 
                UnaryExpr( UNARY( BANG, UnaryExpr(PRIMARY( Parser.NUMBER {value = 1.0}))) ) )
    printfn "%A" e
//    let e2 = AdditionExpr( MultiplicationExpr(
//                PRIMARY(STRING {value = "TEST"}),  
//                MORE( [ MUL, UNARY_OPERATOR( BANG, PRIMARY( NUMBER {value = 1.0})) ])) ) 
//    printfn "%A" e


    prettyPrint e
#endif


    if ((Array.length argv) > 1) then
            printfn "Usage: flox [script]"
        else 
            if (Array.length argv = 1) then
                runFile argv.[0]
            else 
                runPrompt ""
        

    0 // return an integer exit code


