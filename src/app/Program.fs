open Library
open FSharp.Data
open System.IO

let inputData = InputData.Load (Path.Combine(Directory.GetCurrentDirectory(), "fake-data.txt"))

printfn "Hello from F#"

HomeroomSolver inputData