open Library
open FSharp.Data
open System.IO

System.Console.OutputEncoding <- System.Text.Encoding.UTF8;

let inputData = InputData.Load (Path.Combine(Directory.GetCurrentDirectory(), "fake-data.txt"))

match HomeroomSolver inputData with
| Ok (overall_stats, stats_out, data_out) -> 
    System.IO.File.WriteAllText("out-stats.txt", overall_stats + "\n" + stats_out)
    System.IO.File.WriteAllText("out-data.txt", data_out)
    exit 0 
| _ -> exit -1