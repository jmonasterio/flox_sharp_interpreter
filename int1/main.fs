module flox
// F# interpreter
open Interpreter


[<EntryPoint>]
let main argv =
    printfn "flox#"

    if ((Array.length argv) > 1) then
            printfn "Usage: flox [script]"
        else 
            if (Array.length argv = 1) then
                runFile argv.[0]
            else 
                runPrompt ""
        

    0 // return an integer exit code


