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
                    let genderConst = 
                        match row.Gender.Trim().ToUpperInvariant() with
                        | "F" | "FEMALE" -> genderSort.Consts[0]
                        | "M" | "MALE" -> genderSort.Consts[1]
                        | "O" | "OTHER" -> genderSort.Consts[2]
                        | _ -> failwith $"""Unrecognized Gender designation in row ${index} ("{row.Name}"): `{row.Gender}`"""
                    let raceConst = 
                        match row.Race.ToUpperInvariant() with
                        | "BL" -> raceSort.Consts[0]  
                        | "WH" -> raceSort.Consts[1]
                        | "HI" -> raceSort.Consts[2]
                        | "AS" -> raceSort.Consts[3]
                        | "MU" -> raceSort.Consts[4]
                        | "AM" -> raceSort.Consts[5]
                        | _ -> failwith $"""Unrecognized Race designation in row ${index} ("{row.Name}"): `{row.Race}`"""
                    let performanceConst = 
                        match row.Performance.Trim().ToUpperInvariant() with
                        | "ABOVE" -> performanceSort.Consts[0]
                        | "AVERAGE" -> performanceSort.Consts[1]
                        | "BELOW" -> performanceSort.Consts[2]
                        | _ -> failwith $"""Unrecognized Performance designation in row ${index} ("{row.Name}"): `{row.Performance}`"""
                    let specialServicesConst = 
                        match row.SpecialNeeds.Trim().ToUpperInvariant() with
                        | "Y" | "YES" -> specialServicesSort.Consts[0]
                        | "N" | "NO" -> specialServicesSort.Consts[1]
                        | _ -> failwith $"""Unrecognized Special Services designation in row ${index} ("{row.Name}"): `{row.SpecialNeeds}`"""
                    let homeroomConst = ctx.MkIntConst $"_{index}_homeroom"

                    s.Assert(ctx.MkEq(ctx.MkConst($"_{index}_gender", genderSort), genderConst))
                    s.Assert(ctx.MkEq(ctx.MkConst($"_{index}_race", raceSort), raceConst))
                    s.Assert(ctx.MkEq(ctx.MkConst($"_{index}_performance", performanceSort), performanceConst))
                    s.Assert(ctx.MkEq(ctx.MkConst($"_{index}_specialServices", specialServicesSort), specialServicesConst))

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

        // The Es for g-test calculations
        let populationCounts = 
            ({|
                genderCounts = Array.map (fun _ -> 0) genderSort.Consts
                raceCounts = Array.map (fun _ -> 0) raceSort.Consts
                performanceCounts = Array.map (fun _ -> 0) performanceSort.Consts
                specialServicesCounts = Array.map (fun _ -> 0) specialServicesSort.Consts
            |},
            studentConsts)
            ||> Seq.fold
                (fun acc studentConst -> 
                    let foundGenderIndex = Array.findIndex ((=) studentConst.gender) genderSort.Consts 
                    let foundRaceIndex = Array.findIndex ((=) studentConst.race) raceSort.Consts 
                    let foundPeformanceIndex = Array.findIndex ((=) studentConst.performance) performanceSort.Consts 
                    let foundSpecialServicesIndex = Array.findIndex ((=) studentConst.specialServices) specialServicesSort.Consts 
                    {| acc with 
                        genderCounts = Array.updateAt foundGenderIndex (acc.genderCounts[foundGenderIndex] + 1) acc.genderCounts 
                        raceCounts = Array.updateAt foundRaceIndex (acc.raceCounts[foundRaceIndex] + 1) acc.raceCounts 
                        performanceCounts = Array.updateAt foundPeformanceIndex (acc.performanceCounts[foundPeformanceIndex] + 1) acc.performanceCounts 
                        specialServicesCounts = Array.updateAt foundSpecialServicesIndex (acc.specialServicesCounts[foundSpecialServicesIndex] + 1) acc.specialServicesCounts 
                    |})

        printfn $"There are {Seq.length studentConsts} students to be assigned to {num_homerooms} homerooms with no more than {max_class_size} students per homeroom."
        printfn $"Student Body Attribute Counts"
        printfn "%A" populationCounts

        for homeroom in 0 .. num_homerooms do
            s.Assert(ctx.MkLe(ctx.MkAdd(
                Seq.map
                    (fun studentConst -> ctx.MkITE(ctx.MkEq(studentConst.homeroom, ctx.MkInt homeroom), ctx.MkInt 1, ctx.MkInt 0) :?> ArithExpr)
                    studentConsts
                |> Seq.toArray
            ), 
            ctx.MkInt max_class_size))

        // Create g-test scores-holding consts for each gender designation
        let g_test_scores_gender = 
            Array.mapi 
                (fun e gender_index -> ctx.MkConst($"_gender_{gender_index}_g_test_score", ctx.IntSort) :?> ArithExpr)
                genderSort.Consts

        // Create count-holding consts in each homeroom for each gender designation
        let homeroom_gender_counts = 
            Array.map
                (fun homeroom_index ->
                    Array.mapi 
                        (fun e gender_index -> ctx.MkConst($"_homeroom_{homeroom_index}_gender_{gender_index}_count", ctx.IntSort) :?> ArithExpr)
                        genderSort.Consts)
                [| 0 .. num_homerooms |]
            
        // Bind the count-holding consts to a tally by homeroom
        for homeroom_index in [| 0 .. num_homerooms |] do
            for gender_index in [| 0 .. genderSort.Consts.Length |] do
                s.Assert(ctx.MkEq(ctx.MkAdd(
                    Seq.map
                        (fun studentConst -> ctx.MkITE(ctx.MkAnd(ctx.MkEq(studentConst.gender, genderSort.Consts[gender_index]), ctx.MkEq(studentConst.homeroom, ctx.MkInt homeroom_index)), ctx.MkInt 1, ctx.MkInt 0) :?> ArithExpr)
                        studentConsts
                    |> Seq.toArray
                ), 
                homeroom_gender_counts[homeroom_index][gender_index]))

        // ln_approx(x) = 2(x-1/x+1)
        let ln_approx (x : ArithExpr) = 
            ctx.MkMul(
                ctx.MkReal 2, 
                ctx.MkDiv(
                    ctx.MkAdd [| x ; ctx.MkReal 1 |], 
                    ctx.MkAdd [| x ; ctx.MkReal -1 |]))

        // g-test summed term: O * ln_approx(O/E)
        let g_test_summed_term (o : ArithExpr) (e : ArithExpr) =
            ctx.MkMul(o, ln_approx (ctx.MkDiv(o, e)))

        // Bind the g-test scores-holding consts to their computation including the 
        for gender_index in [| 0 .. genderSort.Consts.Length |] do
            s.Assert(
                ctx.MkEq(
                    // 2 * Σ O * ln_approx(O/E)
                    ctx.MkMul(
                        ctx.MkReal 2,
                        ctx.MkAdd(
                            Seq.map 
                                (fun homeroom_index -> 
                                    g_test_summed_term 
                                        (homeroom_gender_counts[homeroom_index][gender_index])
                                        (ctx.MkReal populationCounts.genderCounts[gender_index]))
                                [| 0 .. num_homerooms |]
                            |> Seq.toArray
                        )
                    ),
                    g_test_scores_gender[gender_index]))

        for score in g_test_scores_gender do
            s.Assert(ctx.MkLe(score, ctx.MkReal gender_g_test_max))

        for gender in genderSort.Consts do
            // assert that the g-test for this gender across homerooms is lower than the maximum
            for homeroom in 0 .. num_homerooms do
                s.Assert(ctx.MkLe(ctx.MkAdd(
                    Seq.map
                        (fun studentConst -> 
                            ctx.MkITE(
                                ctx.MkAnd(
                                    ctx.MkEq(studentConst.homeroom, ctx.MkInt homeroom),
                                    ctx.MkEq(studentConst.gender, gender)),
                                ctx.MkInt 1, 
                                ctx.MkInt 0) :?> ArithExpr)
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
    // Log.Open "test.log" |> ignore

    using (new Context(Dictionary(dict [ ("model", "true") ]))) (fun ctx -> Solver.HomeroomSolver ctx data)