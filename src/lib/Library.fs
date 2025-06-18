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
//let performance_g_test_min = 2.0
let gender_g_test_max = 2.0
let race_g_test_max = 2.0

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

    // ln_approx(x) = 2(x-1/x+1)
    let ln_approx (ctx: Context) (x : ArithExpr) = 
        ctx.MkMul(
            ctx.MkReal 2, 
            ctx.MkDiv(
                ctx.MkAdd [| x ; ctx.MkReal -1 |], 
                ctx.MkAdd [| x ; ctx.MkReal 1 |]))

    // g-test summed term: O * ln_approx(O/E)
    let g_test_summed_term (ctx: Context) (o : ArithExpr) (e : ArithExpr) = ctx.MkMul(o, ln_approx ctx (ctx.MkDiv(o, e)))

    let balance_discrete_dimension 
        (ctx: Context) 
        (s: Solver)
        (dimension_name : string)
        (z3sort : EnumSort) 
        (studentConsts : StudentConst array)
        (selector : StudentConst -> Expr) 
        (full_pop_counts : int array)
        (g_test_score_precipice : float)
        (precipice_is_maximum : bool) =
        // Create g-test scores-holding consts for each distinct value
        let half_g_test_scores = 
            Array.mapi 
                (fun value_index _ -> 
                    ctx.MkConst(
                        $"_half_{dimension_name}_{value_index}_g_test_score", 
                        ctx.RealSort))
                z3sort.Consts

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

        // Bind the g-test scores-holding consts to their computation including the 
        for value_index in [| 0 .. z3sort.Consts.Length - 1 |] do
            let sum_terms = 
                Array.choose 
                    (fun homeroom_index -> 
                        if full_pop_counts[value_index] = 0 then None
                        else
                            Some (g_test_summed_term 
                                ctx
                                (counts_by_homeroom[homeroom_index][value_index])
                                (ctx.MkReal (full_pop_counts[value_index], num_homerooms))))
                    [| 0 .. num_homerooms - 1 |]
            if not (Array.isEmpty sum_terms)
            then s.Assert(
                    ctx.MkEq(
                        // Σ O * ln_approx(O/E)
                        ctx.MkAdd sum_terms,
                        half_g_test_scores[value_index]))
            else s.Assert(ctx.MkEq(ctx.MkReal 0, half_g_test_scores[value_index]))

        for score in half_g_test_scores do
            if precipice_is_maximum
            then s.Assert(ctx.MkLe(score :?> ArithExpr, ctx.MkReal ((g_test_score_precipice / 2.0).ToString())))
            else s.Assert(ctx.MkGe(score :?> ArithExpr, ctx.MkReal ((g_test_score_precipice / 2.0).ToString())))

        counts_by_homeroom, half_g_test_scores

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
                        | _, _, s when s |> Seq.forall System.Char.IsDigit -> MustBe (System.Int32.Parse s)
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

        printfn $"There are {Array.length studentConsts} students to be assigned to {num_homerooms} homerooms with no more than {max_class_size} students per homeroom."
        printfn $"  By ELA: %A{ Array.zip performanceSort.Consts populationCounts.performanceCounts }"
        printfn $"  By gender: %A{ Array.zip genderSort.Consts populationCounts.genderCounts }"
        printfn $"  By race: %A{ Array.zip raceSort.Consts populationCounts.raceCounts }"
        printfn $"  By special services: %A{ Array.zip specialServicesSort.Consts populationCounts.specialServicesCounts }"

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
        let counts_by_homeroom_gender, half_g_test_scores_gender = 
            balance_discrete_dimension 
                ctx
                s
                "gender" 
                genderSort 
                studentConsts
                (fun s -> s.gender) 
                populationCounts.genderCounts 
                gender_g_test_max
                true

        // balance race designations across all homerooms
        let counts_by_homeroom_race, half_g_test_scores_race = 
            balance_discrete_dimension 
                ctx
                s
                "race" 
                raceSort 
                studentConsts
                (fun s -> s.race) 
                populationCounts.raceCounts 
                race_g_test_max
                true

        // let counts_by_homeroom_gender = 
        //     discrete_dimension 
        //         "gender" 
        //         genderSort 
        //         (fun s -> s.gender) 
        //         populationCounts.genderCounts

        // let counts_by_homeroom_race = 
        //     discrete_dimension 
        //         "race" 
        //         raceSort 
        //         (fun s -> s.race) 
        //         populationCounts.raceCounts 

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

            for homeroom_index, homeroomStudentConsts in 
                studentConsts 
                |> Seq.groupBy (fun studentConst -> evalParseInt studentConst.homeroom) 
                |> Seq.sortBy (fun (homeroom_index, _) -> homeroom_index) do
                    printfn $"Homeroom {homeroom_index + 1} has {Seq.length homeroomStudentConsts} students."
                    printfn $"  By ELA: %A{ Array.zip performanceSort.Consts (counts_by_homeroom_performance[homeroom_index] |> Array.map evalParseInt) }"
                    printfn $"  By gender: %A{ Array.zip genderSort.Consts (counts_by_homeroom_gender[homeroom_index] |> Array.map evalParseInt) }"
                    printfn $"  By race: %A{ Array.zip raceSort.Consts (counts_by_homeroom_race[homeroom_index] |> Array.map evalParseInt) }"
                    printfn $"  By special needs: %A{ Array.zip specialServicesSort.Consts (counts_by_homeroom_special_services[homeroom_index] |> Array.map evalParseInt) }"

            printfn "G-Test Scores:"
            //printfn $"  By ELA: %A{Array.zip performanceSort.Consts (half_g_test_scores_performance |> Array.map evalParseDecimal)}"
            printfn $"  By gender: %A{Array.zip genderSort.Consts (half_g_test_scores_gender |> Array.map evalParseDecimal)}"
            printfn $"  By race: %A{Array.zip raceSort.Consts (half_g_test_scores_race |> Array.map evalParseDecimal)}"

            printfn ""
            for studentConst in 
                studentConsts
                |> Seq.sortBy (fun studentConst -> evalParseInt studentConst.homeroom, studentConst.original.Name)
                do
                    printfn $"""{studentConst.original.Id}	"{studentConst.original.Name}"	{studentConst.original.Gender}	{studentConst.original.Race}	{studentConst.original.Performance}	{studentConst.original.SpecialNeeds}	{evalParseInt (studentConst.homeroom)}"""

            Ok ()
        | _ -> 
            printfn $"No solution found"
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
        //"unsat_core", "true"
        "stats", "true"
    ]))) (fun ctx -> Solver.HomeroomSolver ctx data)