module Library

open Microsoft.Z3
open FSharp.Data
open System.Collections.Generic

type InputData =
    CsvProvider<
        HasHeaders=false,
        Schema="Id (String), Name (string), Gender (string), Race (string), Performance (string), SpecialNeeds (string), Restriction (string option)",
        Separators="\t"
     >

type Restriction =
    | MustBe of int
    //| MustNotBe of int
    //| MustMatch of string
    //| MustNotMatch of string
    | NoRestriction

type StudentConst = { 
    original: InputData.Row
    gender : Expr;
    race : Expr;
    performance : Expr;
    specialServices : Expr;
    restriction : Restriction;
    homeroom : IntExpr;
}

let num_homerooms = 5

module Solver =
    let discrete_dimension 
        (ctx: Context) 
        (s: Solver)
        (dimension_name : string)
        (z3sort : EnumSort) 
        (studentConsts : StudentConst array)
        (selector : StudentConst -> Expr) =
        // Create count-holding consts in each homeroom for each distinct value
        let counts_by_homeroom = 
            Array.map
                (fun homeroom_index ->
                    Array.mapi 
                        (fun value_index _ -> 
                            ctx.MkConst(
                                $"_homeroom_{homeroom_index}_{dimension_name}_{value_index}_count", 
                                ctx.RealSort) :?> ArithExpr)
                        z3sort.Consts)
                [| 0 .. num_homerooms - 1 |]
            
        // Bind the count-holding consts to a tally by homeroom
        for homeroom_index in [| 0 .. num_homerooms - 1 |] do
            for value_index in [| 0 .. z3sort.Consts.Length - 1 |] do
                let population_with = 
                    studentConsts
                    |> Array.where (fun studentConst -> selector studentConst = z3sort.Consts[value_index])
                    |> Array.map
                        (fun studentConst -> 
                            ctx.MkITE(
                                ctx.MkEq(studentConst.homeroom, ctx.MkInt homeroom_index), 
                                ctx.MkReal 1, 
                                ctx.MkReal 0) :?> ArithExpr)
                s.Assert(ctx.MkEq(
                    (if Array.isEmpty population_with then ctx.MkReal 0 :> ArithExpr else ctx.MkAdd population_with), 
                    counts_by_homeroom[homeroom_index][value_index]))

        counts_by_homeroom

    let balance_discrete_dimension 
        (ctx: Context) 
        (s: Solver)
        (dimension_name : string)
        (z3sort : EnumSort) 
        (studentConsts : StudentConst array)
        (selector : StudentConst -> Expr) 
        (full_pop_counts : int array) =
        // Create count-holding consts in each homeroom for each distinct value
        let counts_by_homeroom = 
            Array.map
                (fun homeroom_index ->
                    Array.mapi 
                        (fun value_index _ -> 
                            ctx.MkConst(
                                $"_homeroom_{homeroom_index}_{dimension_name}_{value_index}_count", 
                                ctx.RealSort) :?> ArithExpr)
                        z3sort.Consts)
                [| 0 .. num_homerooms - 1 |]
            
        // Bind the count-holding consts to a tally by homeroom and
        // Assert the counts are low enough as an easier constraint to find?
        for homeroom_index in [| 0 .. num_homerooms - 1 |] do
            for value_index in [| 0 .. z3sort.Consts.Length - 1 |] do
                let population_with = 
                    studentConsts
                    |> Array.where (fun studentConst -> selector studentConst = z3sort.Consts[value_index])
                    |> Array.map
                        (fun studentConst -> 
                            ctx.MkITE(
                                ctx.MkEq(studentConst.homeroom, ctx.MkInt homeroom_index), 
                                ctx.MkReal 1, 
                                ctx.MkReal 0) :?> ArithExpr)
                let max_of_value_in_room = System.Convert.ToInt32(System.Math.Ceiling(1.02 * float (full_pop_counts[value_index]) / float num_homerooms)) + 1
                s.Assert(ctx.MkEq(
                    (if Array.isEmpty population_with then ctx.MkReal 0 :> ArithExpr else ctx.MkAdd population_with), 
                    counts_by_homeroom[homeroom_index][value_index]))
                if not (Array.isEmpty population_with) then
                    s.Assert(ctx.MkLt(
                        counts_by_homeroom[homeroom_index][value_index],
                        ctx.MkReal max_of_value_in_room))

        counts_by_homeroom

    let loadStudentConsts 
        (ctx: Context)
        (s: Solver)
        (data : InputData)
        (performanceSort: EnumSort)
        (genderSort: EnumSort)
        (raceSort: EnumSort)
        (specialServicesSort: EnumSort) = 
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
                let restriction = 
                    match row.Restriction with
                    | None -> NoRestriction
                    | Some s -> 
                        match s.Substring(0, 1), s.Substring 1, s with
                        //| "!", rest, _ when rest |> Seq.forall System.Char.IsDigit -> MustNotBe (System.Int32.Parse rest)
                        //| "!", rest, _ when rest |> Seq.forall System.Char.IsAsciiLetterUpper -> MustNotMatch rest
                        | _, _, s when s |> Seq.forall System.Char.IsDigit -> MustBe (System.Int32.Parse s - 1)
                        //| _, _, s when s |> Seq.forall System.Char.IsAsciiLetterUpper -> MustMatch s
                        | _, _, "" -> NoRestriction
                        | _ -> failwith "Invalid Restriction '{s}'"

                s.Assert(ctx.MkEq(ctx.MkConst($"_{index}_gender", genderSort), genderConst))
                s.Assert(ctx.MkEq(ctx.MkConst($"_{index}_race", raceSort), raceConst))
                s.Assert(ctx.MkEq(ctx.MkConst($"_{index}_performance", performanceSort), performanceConst))
                s.Assert(ctx.MkEq(ctx.MkConst($"_{index}_specialServices", specialServicesSort), specialServicesConst))

                s.Assert(ctx.MkLe(ctx.MkInt 0, homeroomConst))
                s.Assert(ctx.MkLt(homeroomConst, ctx.MkInt num_homerooms))

                match restriction with
                | MustBe homeroom_index -> s.Assert(ctx.MkEq(homeroomConst, ctx.MkInt homeroom_index))
                | _ -> ()

                {
                    original = row
                    gender = genderConst
                    race = raceConst
                    performance = performanceConst
                    specialServices = specialServicesConst
                    homeroom = homeroomConst
                    restriction = restriction
                })
        |> Seq.toArray

    let HomeroomSolver (ctx: Context) (data: InputData) =
        let s = ctx.MkSolver()
        let genderSort = ctx.MkEnumSort("Gender", [| "FEMALE" ; "MALE" ; "OTHER" |])
        let raceSort = ctx.MkEnumSort("Race", [| "BL" ; "WH" ; "HI" ; "AS" ; "MU" ; "AM" |])
        let performanceSort = ctx.MkEnumSort("Performance", [| "ABOVE" ; "AVERAGE" ; "BELOW" |])
        let specialServicesSort = ctx.MkEnumSort("SpecialServices", [| "YES" ; "NO" |])

        // parse and register each student row in the context
        let studentConsts = loadStudentConsts ctx s data performanceSort genderSort raceSort specialServicesSort

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

        let dimension_stats (z3sort : EnumSort) (full_pop_counts : int array) = 
            Array.zip 
                [| 0 .. z3sort.Consts.Length - 1 |] 
                full_pop_counts 
            |> Array.map (fun (value_index, count) -> 
                let pct = if Seq.length studentConsts = 0 then "--" else sprintf $"%.3g{100.0 * float count / float (Seq.length studentConsts)}%%"
                sprintf $"%A{z3sort.Consts[value_index]} {count} (↔ {pct})")
            |> String.concat ", "

        let overall_stats = 
            sprintf $"There are {Array.length studentConsts} students to be assigned to {num_homerooms} homerooms with no more than {max_class_size} students per homeroom.\n"
            + sprintf $"  By ELA: { dimension_stats performanceSort populationCounts.performanceCounts }\n"
            + sprintf $"  By gender: { dimension_stats genderSort populationCounts.genderCounts }\n"
            + sprintf $"  By race: { dimension_stats raceSort populationCounts.raceCounts }\n"
            + sprintf $"  By special services: { dimension_stats specialServicesSort populationCounts.specialServicesCounts }\n"

        printf "%s" overall_stats

        // All homerooms must be smaller than max_class_size
        for homeroom in 0 .. num_homerooms - 1 do
            s.Assert(ctx.MkLe(ctx.MkAdd(
                Seq.map
                    (fun studentConst -> ctx.MkITE(ctx.MkEq(studentConst.homeroom, ctx.MkInt homeroom), ctx.MkInt 1, ctx.MkInt 0) :?> ArithExpr)
                    studentConsts
                |> Seq.toArray
            ), 
            ctx.MkInt max_class_size))

        // track ELAs per homeroom
        let counts_by_homeroom_performance = 
            discrete_dimension 
                ctx
                s
                "performance" 
                performanceSort 
                studentConsts
                (fun s -> s.performance)
        
        // If possible, no student of a certain performance level should be alone in a homeroom
        for homeroom_index in [| 0 .. num_homerooms - 1 |] do
            for performance_index in [| 0 .. performanceSort.Consts.Length - 1 |] do
                if 2 <= populationCounts.performanceCounts[performance_index] then 
                    s.Assert(ctx.MkDistinct(ctx.MkInt 1, counts_by_homeroom_performance[homeroom_index][performance_index]))

        // balance gender designations across all homerooms
        let counts_by_homeroom_gender = 
            balance_discrete_dimension 
                ctx
                s
                "gender" 
                genderSort 
                studentConsts
                (fun s -> s.gender) 
                populationCounts.genderCounts 

        // balance race designations across all homerooms
        let counts_by_homeroom_race = 
            balance_discrete_dimension 
                ctx
                s
                "race" 
                raceSort 
                studentConsts
                (fun s -> s.race) 
                populationCounts.raceCounts

        // track Special Services needs per homeroom
        let counts_by_homeroom_special_services = 
            discrete_dimension 
                ctx
                s
                "specialservices" 
                specialServicesSort 
                studentConsts
                (fun s -> s.specialServices)

        // printfn "%A" s

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

            let stats_out = 
                studentConsts 
                |> Seq.groupBy (fun studentConst -> evalParseInt studentConst.homeroom) 
                |> Seq.sortBy (fun (homeroom_index, _) -> homeroom_index)
                |> Seq.map (fun (homeroom_index, homeroomStudentConsts) ->
                    let dimension_stats_2 (z3sort : EnumSort) (full_pop_counts : int array) (counts_by_homeroom: ArithExpr array array) = 
                        Array.zip 
                            [| 0 .. z3sort.Consts.Length - 1 |] 
                            (counts_by_homeroom[homeroom_index] |> Array.map evalParseInt) 
                        |> Array.map (fun (value_index, count) -> 
                            let across_dimension = if full_pop_counts[value_index] = 0 then "--" else sprintf $"%.3g{100.0 * float count / float (full_pop_counts[value_index])}%%"
                            let among_room = if Seq.length homeroomStudentConsts = 0 then "--" else sprintf $"%.3g{100.0 * float count / float (Seq.length homeroomStudentConsts)}%%"
                            sprintf $"%A{z3sort.Consts[value_index]} {count} (↕ {across_dimension}) (↔ {among_room})")
                        |> String.concat ", "

                    sprintf $"Homeroom {homeroom_index + 1} has {Seq.length homeroomStudentConsts} students.\n"
                    + sprintf $"  By ELA: { dimension_stats_2 performanceSort populationCounts.performanceCounts counts_by_homeroom_performance }\n"
                    + sprintf $"  By gender: { dimension_stats_2 genderSort populationCounts.genderCounts counts_by_homeroom_gender }\n"
                    + sprintf $"  By race: { dimension_stats_2 raceSort populationCounts.raceCounts counts_by_homeroom_race }\n"
                    + sprintf $"  By special needs: { dimension_stats_2 specialServicesSort populationCounts.specialServicesCounts counts_by_homeroom_special_services }\n")
                |> String.concat ""

            let data_out = 
                sprintf $"Id	Name	Gender Designation	Race Designation	ELA Designation	Special Services	Homeroom\n"
                + (studentConsts
                |> Seq.sortBy (fun studentConst -> evalParseInt studentConst.homeroom, studentConst.original.Name)
                |> Seq.map (fun studentConst -> 
                    sprintf $"{studentConst.original.Id}	\"{studentConst.original.Name}\"	{studentConst.original.Gender}	{studentConst.original.Race}	{studentConst.original.Performance}	{studentConst.original.SpecialNeeds}	{1 + evalParseInt studentConst.homeroom}\n")
                |> String.concat "")

            printfn ""
            printfn "%s" stats_out
            printfn "%s" data_out

            Ok (overall_stats, stats_out, data_out)
        | _ -> 
            printfn $"No solution found"
            printfn $"{s.Statistics}"
            // printfn $"{s.UnsatCore}"
            Error ()



let HomeroomSolver (data: InputData) =
    Microsoft.Z3.Global.ToggleWarningMessages true
    Microsoft.Z3.Global.SetParameter("parallel.enable", "true")
    // Log.Open "test.log" |> ignore

    // https://microsoft.github.io/z3guide/programming/Parameters
    using (new Context(Dictionary(dict [ 
        "model", "true"
        //"model_validate", "true"
        //"trace", "true"
        "unsat_core", "true"
        "stats", "true"
    ]))) (fun ctx -> Solver.HomeroomSolver ctx data)