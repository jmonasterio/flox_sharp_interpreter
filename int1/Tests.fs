module Tests
open System

open Interpreter

#if OLD
open NUnit.Framework

[<Test>]
let xxx() =
    printfn "hello"


[<Test>]
let ``Can parse and solve addition problems`` () =
    run """

        print "TEST #0";
        { print clock(); }

        """
    Assert.That true
#endif