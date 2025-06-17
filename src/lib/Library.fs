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
let gender_g_test_max = 100
let race_g_test_max = 4

module Solver =
    let HomeroomSolver (ctx: Context) (data: InputData) : unit =
        let s = ctx.MkSolver()
        let genderSort = ctx.MkEnumSort("Gender", [| "FEMALE" ; "MALE" ; "OTHER" |])
        let raceSort = ctx.MkEnumSort("Race", [| "BL" ; "WH" ; "HI" ; "AS" ; "MU" ; "AM" |])
        let performanceSort = ctx.MkEnumSort("Performance", [| "ABOVE" ; "AVERAGE" ; "BELOW" |]);
        let specialServicesSort = ctx.MkEnumSort("SpecialServices", [| "YES" ; "NO" |]);

        let studentConsts = 
            data.Rows
            |> Seq.mapi 
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
            |> Seq.toArray

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
            ||> Array.fold
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

        printfn $"There are {Array.length studentConsts} students to be assigned to {num_homerooms} homerooms with no more than {max_class_size} students per homeroom."
        printfn $"Student Body Attribute Counts"
        printfn "%A" populationCounts

        for homeroom in 0 .. num_homerooms - 1 do
            s.Assert(ctx.MkLe(ctx.MkAdd(
                Seq.map
                    (fun studentConst -> ctx.MkITE(ctx.MkEq(studentConst.homeroom, ctx.MkInt homeroom), ctx.MkInt 1, ctx.MkInt 0) :?> ArithExpr)
                    studentConsts
                |> Seq.toArray
            ), 
            ctx.MkInt max_class_size))

        // Create g-test scores-holding consts for each gender designation
        let half_g_test_scores_gender = 
            Array.mapi 
                (fun gender_index _ -> ctx.MkConst($"_half_gender_{gender_index}_g_test_score", ctx.RealSort) :?> ArithExpr)
                genderSort.Consts

        // Create count-holding consts in each homeroom for each gender designation
        let homeroom_gender_counts = 
            Array.map
                (fun homeroom_index ->
                    Array.mapi 
                        (fun gender_index _ -> ctx.MkConst($"_homeroom_{homeroom_index}_gender_{gender_index}_count", ctx.RealSort) :?> ArithExpr)
                        genderSort.Consts)
                [| 0 .. num_homerooms - 1 |]
            
        // Bind the count-holding consts to a tally by homeroom
        for homeroom_index in [| 0 .. num_homerooms - 1 |] do
            for gender_index in [| 0 .. genderSort.Consts.Length - 1 |] do
                let population_with = 
                    studentConsts
                    |> Array.where (fun studentConst -> studentConst.gender = genderSort.Consts[gender_index])
                    |> Array.map
                        (fun studentConst -> 
                            ctx.MkITE(
                                ctx.MkEq(studentConst.homeroom, ctx.MkInt homeroom_index), 
                                ctx.MkReal 1, 
                                ctx.MkReal 0) :?> ArithExpr)
                s.Assert(ctx.MkEq(
                    (if Array.isEmpty population_with then ctx.MkReal 0 :> ArithExpr else ctx.MkAdd population_with), 
                    homeroom_gender_counts[homeroom_index][gender_index]))

        // ln_approx(x) = 2(x-1/x+1)
        let ln_approx (x : ArithExpr) = 
            ctx.MkMul(
                ctx.MkReal 2, 
                ctx.MkDiv(
                    ctx.MkAdd [| x ; ctx.MkReal 1 |], 
                    ctx.MkAdd [| x ; ctx.MkReal -1 |]))

        // g-test summed term: O * ln_approx(O/E)
        let g_test_summed_term (o : ArithExpr) (e : ArithExpr) = ctx.MkMul(o, ln_approx (ctx.MkDiv(o, e)))

        // Bind the g-test scores-holding consts to their computation including the 
        for gender_index in [| 0 .. genderSort.Consts.Length - 1 |] do
            let sum_terms = 
                Array.choose 
                    (fun homeroom_index -> 
                        let attributePopulationCount = populationCounts.genderCounts[gender_index]
                        if attributePopulationCount = 0 then None
                        else
                            Some (g_test_summed_term 
                                (homeroom_gender_counts[homeroom_index][gender_index])
                                (ctx.MkReal (attributePopulationCount, num_homerooms))))
                    [| 0 .. num_homerooms - 1 |]
            if not (Array.isEmpty sum_terms)
            then s.Assert(
                    ctx.MkEq(
                        // Σ O * ln_approx(O/E)
                        ctx.MkAdd sum_terms,
                        half_g_test_scores_gender[gender_index]))
            else s.Assert(ctx.MkEq(ctx.MkReal 0, half_g_test_scores_gender[gender_index]))

        for score in half_g_test_scores_gender do
            s.Assert(ctx.MkLe(score, ctx.MkReal (gender_g_test_max, 2)))

        printfn "%A" s

        match s.Check() with
        | Status.SATISFIABLE ->
            let model = s.Model

            let evalParseInt x = 
                try
                    System.Int32.Parse((model.Eval x).ToString()) 
                with 
                    _ -> failwith $"Unexpected format in evalParseInt '{x}'"

            let evalParseDecimal x =
                try
                    match (model.Eval x).ToString().Split '/' with
                    | [| num ; den |] -> decimal (System.Int32.Parse num) / decimal (System.Int32.Parse den)
                    | [| num |] -> decimal (System.Int32.Parse num)
                    | _ -> failwith $"Unexpected format in evalParseDecimal '{x}'"
                with
                    _ -> failwith $"Unexpected format in evalParseDecimal '{x}'"

            for homeroom_index, homeroomStudentConsts in 
                studentConsts 
                |> Seq.groupBy (fun studentConst -> evalParseInt studentConst.homeroom) 
                |> Seq.sortBy (fun (homeroom_index, _) -> homeroom_index) do
                    printfn "%s" ($"Homeroom {homeroom_index + 1} has {Seq.length homeroomStudentConsts} students.  " +
                        $"Gender counts: {evalParseInt(homeroom_gender_counts[homeroom_index][0])}, " +
                        $"{evalParseInt(homeroom_gender_counts[homeroom_index][1])}, " +
                        $"{evalParseInt(homeroom_gender_counts[homeroom_index][2])}")

            printfn "%s" ($"Gender G-Test Scores: " +
                        $"%0.3f{2.0M * evalParseDecimal (half_g_test_scores_gender[0])} " +
                        $"%0.3f{2.0M * evalParseDecimal (half_g_test_scores_gender[1])} " +
                        $"%0.3f{2.0M * evalParseDecimal (half_g_test_scores_gender[2])}")
        | _ -> 
            printfn $"No solution found"
            //printfn "%A" s.UnsatCore



let HomeroomSolver (data: InputData) : unit =
    Microsoft.Z3.Global.ToggleWarningMessages true
    Microsoft.Z3.Global.SetParameter("parallel.enable", "true")
    // Log.Open "test.log" |> ignore

    // https://microsoft.github.io/z3guide/programming/Parameters
    using (new Context(Dictionary(dict [ 
        "model", "true"
        //"model_validate", "true"
        //"trace", "true"
        //"unsat_core", "true"
        "stats", "true"
    ]))) (fun ctx -> Solver.HomeroomSolver ctx data)