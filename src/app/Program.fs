open Library
open FSharp.Data
open System.IO

let inputData = InputData.Load (Path.Combine(Directory.GetCurrentDirectory(), "fake-data.txt"))

match HomeroomSolver inputData with
| Ok _ -> exit 0 
| _ -> exit -1