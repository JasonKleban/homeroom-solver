module Library

open Microsoft.Z3
open FSharp.Data
open System.Collections.Generic

type InputData =
    CsvProvider<
        HasHeaders=false,
        Schema="Name (string), Gender (string), Race (string), Performance (string), SpecialNeeds (string)",
        Separators="\t"
     >

type StudentConst = { 
    index : int
    name : string;
    gender : Expr;
    race : Expr;
    performance : Expr;
    specialServices : Expr;
    homeroom : IntExpr
}

let num_homerooms = 3
let gender_g_test_max = 2
let race_g_test_max = 2

module Solver =
    let HomeroomSolver (ctx: Context) (data: InputData) : unit =
        let s = ctx.MkSolver()
        let genderSort = ctx.MkEnumSort("Gender", [| "FEMALE" ; "MALE" ; "OTHER" |])
        let raceSort = ctx.MkEnumSort("Race", [| "BL" ; "WH" ; "HI" ; "AS" ; "MU" ; "AM" |])
        let performanceSort = ctx.MkEnumSort("Performance", [| "ABOVE" ; "AVERAGE" ; "BELOW" |]);
        let specialServicesSort = ctx.MkEnumSort("SpecialServices", [| "YES" ; "NO" |]);

        let studentConsts = 
            Seq.mapi 
                (fun (index : int) (row : InputData.Row) ->
                    let genderConst = ctx.MkConst($"_{index}_gender", genderSort)
                    let raceConst = ctx.MkConst($"_{index}_race", raceSort)
                    let performanceConst = ctx.MkConst($"_{index}_performance", performanceSort)
                    let specialServicesConst = ctx.MkConst($"_{index}_specialServices", specialServicesSort)
                    let homeroomConst = ctx.MkIntConst($"_{index}_homeroom")

                    s.Assert(ctx.MkEq(
                        genderConst,
                        match row.Gender.Trim().ToUpperInvariant() with
                        | "F" | "FEMALE" -> genderSort.Consts[0]
                        | "M" | "MALE" -> genderSort.Consts[1]
                        | "O" | "OTHER" -> genderSort.Consts[2]
                        | _ -> failwith $"""Unrecognized Gender designation in row ${index} ("{row.Name}"): `{row.Gender}`"""))

                    s.Assert(ctx.MkEq(
                        raceConst,
                        match row.Race.ToUpperInvariant() with
                        | "BL" -> raceSort.Consts[0]  
                        | "WH" -> raceSort.Consts[1]
                        | "HI" -> raceSort.Consts[2]
                        | "AS" -> raceSort.Consts[3]
                        | "MU" -> raceSort.Consts[4]
                        | "AM" -> raceSort.Consts[5]
                        | _ -> failwith $"""Unrecognized Race designation in row ${index} ("{row.Name}"): `{row.Race}`"""))

                    s.Assert(ctx.MkEq(
                        performanceConst,
                        match row.Performance.Trim().ToUpperInvariant() with
                        | "ABOVE" -> performanceSort.Consts[0]
                        | "AVERAGE" -> performanceSort.Consts[1]
                        | "BELOW" -> performanceSort.Consts[2]
                        | _ -> failwith $"""Unrecognized Performance designation in row ${index} ("{row.Name}"): `{row.Performance}`"""))

                    s.Assert(ctx.MkEq(
                        specialServicesConst,
                        match row.SpecialNeeds.Trim().ToUpperInvariant() with
                        | "Y" | "YES" -> specialServicesSort.Consts[0]
                        | "N" | "NO" -> specialServicesSort.Consts[1]
                        | _ -> failwith $"""Unrecognized Special Services designation in row ${index} ("{row.Name}"): `{row.SpecialNeeds}`"""))

                    s.Assert(ctx.MkLe(ctx.MkInt 0, homeroomConst))
                    s.Assert(ctx.MkLt(homeroomConst, ctx.MkInt num_homerooms))

                    {
                        index = index
                        name = row.Name
                        gender = genderConst
                        race = raceConst
                        performance = performanceConst
                        specialServices = specialServicesConst
                        homeroom = homeroomConst
                    })
                data.Rows

        let max_class_size = System.Convert.ToInt32(System.Math.Ceiling(1.02 * float (Seq.length studentConsts) / float num_homerooms))

        printfn $"There are {Seq.length studentConsts} students to be assigned to {num_homerooms} homerooms with no more than {max_class_size} students per homeroom."

        for homeroom in 0 .. num_homerooms do
            s.Assert(ctx.MkLe(ctx.MkAdd(
                Seq.map
                    (fun studentConst -> ctx.MkITE(ctx.MkEq(studentConst.homeroom, ctx.MkInt homeroom), ctx.MkInt 1, ctx.MkInt 0) :?> ArithExpr)
                    studentConsts
                |> Seq.toArray
            ), 
            ctx.MkInt max_class_size))

        match s.Check() with
        | Status.SATISFIABLE ->
            let model = s.Model

            for homeroom, homeroomStudentConsts in Seq.groupBy (fun studentConst -> System.Int32.Parse ((model.Eval studentConst.homeroom).ToString())) studentConsts do
                printfn $"Homeroom {homeroom} has {Seq.length homeroomStudentConsts} students"
        | _ -> printfn $"No solution found"



let HomeroomSolver (data: InputData) : unit =
    Microsoft.Z3.Global.ToggleWarningMessages(true)
    Log.Open "test.log" |> ignore

    using (new Context(Dictionary(dict [ ("model", "true") ]))) (fun ctx -> Solver.HomeroomSolver ctx data)