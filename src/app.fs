module App

// ------------------------------------------------------------------------------------------------
// Types
// ------------------------------------------------------------------------------------------------

type Record = 
  { Kind : RecordKind 
    Fields : RecordField list }

and RecordField = 
  { Name : string option
    Value : Value }

and RecordKind = 
  Function | Block | Choice

and Primitive = String of string | Int of int

and Reference = 
  | Name of string
  | Sample of Primitive
  
and Value = 
  { Kind : ValueKind 
    Evaluated : Value option }

and ValueKind = 
  | Assign of Reference
  | Dot of Value * string
  | Call of Reference * Value
  | Record of Record
  | Fail


// ------------------------------------------------------------------------------------------------
// Operations
// ------------------------------------------------------------------------------------------------

let rec mostEvaluated value = 
  match value.Evaluated with 
  | Some e -> mostEvaluated e
  | None -> value.Kind

let rec tryGetValue value = 
  match value.Evaluated, value.Kind with 
  | Some e, _ -> tryGetValue e
  | None, Fail -> Some Fail
  | None, (Assign (Sample _) as v) -> Some v
  | None, Record { Kind = (Block | Function) as kind; Fields = flds } ->
      let flds = 
        List.foldBack (fun fld res ->
          match res with 
          | None -> None
          | Some flds ->
              match tryGetValue fld.Value with
              | Some v -> Some ({ fld with Value = { Kind = v; Evaluated = None }} :: flds)
              | None -> None ) flds (Some [])
      flds |> Option.map (fun flds -> 
        if kind = Block && flds |> Seq.exists (fun fld -> fld.Value.Kind = Fail) then Fail
        else Record { Kind = kind; Fields = flds })
  | _ -> None

let evalReference fields ref = 
  match ref with 
  | Sample(v) -> { Kind = Assign (Sample(v)); Evaluated = None }
  | Name(n) -> match Map.tryFind n fields with Some v -> v | _ -> failwithf "Field %s not found in: %A" n [ for kvp in fields -> kvp.Key ]

let getFieldValues args = 
  [ for f in args.Fields do 
      match f.Name, f.Value with
      | Some n, { Kind = v } -> yield n, v
      | None, _ -> () ]

let getArgValues args = 
  [ for f in args.Fields do 
      match f.Name, f.Value with
      | Some n, { Kind = Assign (Sample p) } -> yield n, p 
      | None, _ -> ()
      | Some _, v -> failwithf "getArgValues: Expected Assign (Sample p) but got: %A" v ]

let rec evalValue fields value = 
  let newEval = 
    match value.Evaluated with 
    | Some v -> evalValue fields v
    | None ->
        match value.Kind with 
        | Fail -> value
        | Dot(ref, n) ->
            let ref = evalValue fields ref
            match tryGetValue ref with 
            | Some (Record recd) -> { Kind = (dict (getFieldValues recd)).[n]; Evaluated = None }
            | Some Fail -> { Kind = Fail; Evaluated = None }
            | Some e -> failwithf "evalValue: Argument of dot should evaluate to record. Got: %A" e
            | None -> { Kind = Dot(ref, n); Evaluated = None }

        | Assign ref -> evalReference fields ref
        | Call(ref, args) -> 
            match tryGetValue args with 
            | None -> { Kind = Call(ref, evalValue fields args); Evaluated = None }
            | Some Fail ->
                { Kind = Fail; Evaluated = None }
            | Some (Record args) -> 
                match ref with 
                | Sample _ -> failwith "Call reference should be name!"

                | Name (("equals" | "mult" | "add") as fn) -> 
                    let args = dict (getArgValues args)
                    match fn, args.["first"], args.["second"] with
                    | "mult", Int n1, Int n2 -> { Kind = Assign (Sample (Int (n1 * n2))); Evaluated = None }
                    | "add", Int n1, Int n2 -> { Kind = Assign (Sample (Int (n1 + n2))); Evaluated = None }
                    | "equals", Int n1, Int n2 when n1 = n2 -> { Kind = Assign (Sample (Int n1)); Evaluated = None }
                    | "equals", String s1, String s2 when s1 = s2 -> { Kind = Assign (Sample (String s1)); Evaluated = None }
                    | "equals", Int n1, Int n2 -> { Kind = Fail; Evaluated = None }
                    | "equals", String s1, String s2 -> { Kind = Fail; Evaluated = None }
                    | fn, a1, a2 -> failwithf "Invalid %s call: %A, %A" fn a1 a2

                | Name "match-string" -> 
                    let args = dict (getArgValues args)
                    match args.["it"], args.["str"] with
                    | String it, String str when it.StartsWith str ->
                        { Kind = Assign (Sample (String (it.Substring(str.Length)))); Evaluated = None }
                    | String _, String _ ->
                        { Kind = Fail; Evaluated = None }
                    | _ -> failwith "invalid match-string call"

                | Name fn -> 
                    let fv = match Map.tryFind fn fields with Some v -> v | _ -> failwithf "Function %s not found in: %A" fn [ for kvp in fields -> kvp.Key ]
                    match fv with 
                    | { Kind = Record recd } -> 
                        let args = dict (getFieldValues args)
                        let newFields = recd.Fields |> List.map (fun fld ->
                          if fld.Name.IsSome && args.ContainsKey(fld.Name.Value) then
                            { fld with Value = { Kind = args.[fld.Name.Value]; Evaluated = None } }
                          else fld)
                        { Kind = Record { Kind = Block; Fields = newFields }; Evaluated = None }

                    | _ -> failwith "evalValue: Function was not a record"
            | Some _ -> failwith "evalValue: Arguments should be record"
        | Record recd -> evalRecord fields recd
  { value with Evaluated = Some newEval }

and evalRecord parentFields recd = 
  let flds, _ = recd.Fields |> List.fold (fun (fldsList, fldsMap) fld ->
    let fld = { fld with Value = evalValue fldsMap fld.Value }
    let fldsMap = if fld.Name.IsSome then Map.add fld.Name.Value fld.Value fldsMap else fldsMap 
    (fld::fldsList, fldsMap)) ([], parentFields) 
  let flds = List.rev flds

  match recd.Kind with 
  | Function ->
      { Kind = Record { recd with Fields = flds }; Evaluated = None }
  
  | Block -> 
      if flds |> Seq.exists (fun fld -> fld.Value.Kind = Fail) then { Kind = Fail; Evaluated = None }
      else { Kind = Record { recd with Fields = flds }; Evaluated = None }
      
  | Choice -> 
      let vals = flds |> List.map (fun fld -> tryGetValue fld.Value)
      let valsPrefix = vals |> List.takeWhile Option.isSome |> List.choose id
      let firstSucc = valsPrefix |> List.tryFind (fun v -> v <> Fail)
      match firstSucc with 
      | Some res -> { Kind = res; Evaluated = None } // return first evaluated succeeding case
      | None when valsPrefix.Length = vals.Length -> { Kind = Fail; Evaluated = None } // all choices failed
      | None -> { Kind = Record { recd with Fields = flds }; Evaluated = None } // needs more evaluating


// ------------------------------------------------------------------------------------------------
// User interface
// ------------------------------------------------------------------------------------------------

open Elmish
open Tbd.Html
open Fable.Core
open Fable.Import
open Fable.PowerPack
open Fable.PowerPack.Keyboard

let renderTable data = 
  h?table ["class"=>"data"] [
    for row in data -> h?tr [] [
      for col in row -> h?td [] [ text (string col) ]
    ]
  ]


type Model = 
  { Document : Value }
    
type Event = 
  | Evaluate
  
let update model = function
  | Evaluate -> printfn "yo"; { model with Document = evalValue Map.empty model.Document }

let cols els = 
  h?table [] [
    h?tr [] [ for e in els -> h?td [ "class" => "cell cell-col" ] [ e ] ]
  ]

let rows els = 
  h?table [] [ 
    for e in els -> h?tr [] [ h?td [ "class" => "cell cell-row" ] [ e ] ] 
  ]

let rec renderField fld =
  cols [
    if fld.Name.IsSome then
      yield h?strong [] [ text fld.Name.Value ]
    yield renderValue false fld.Value
  ]

and renderValue topLevel value = 
  match mostEvaluated value with 
  | Assign(Name s) -> text s
  | Assign(Sample(String s)) -> text (sprintf "\"%s\"" s)
  | Assign(Sample(Int n)) -> text (string n)
  | Dot(value, n) -> cols [ renderValue false value; text ("." + n) ]
  | Call(Name s, value) -> cols [ text s; renderValue false value]
  | Call(Sample _, value) -> failwith "Strange call!"
  | Record recd ->
      h?div [] [
        h?em [] [ text (string recd.Kind) ]
        h?br [] [] 
        (if topLevel then cols else rows)
          [ for r in recd.Fields -> renderField r ]
      ]
  | Fail -> text "(Fail)"

let view trigger state =
  h?div [] [
    h?button [ "click" =!> fun _ _ -> trigger Evaluate ] [ text "Evaluate step" ] 
    h?div [] [ renderValue true state.Document ]
  ]

// ------------------------------------------------------------------------------------------------
// DSL
// ------------------------------------------------------------------------------------------------

let (=>) n v = { Name = Some n; Value = v }
let (!>) v = { Name = None; Value = v }
let set a = { Kind = Assign a; Evaluated = None }
let dot r n = { Kind = Dot(r, n); Evaluated = None }
let fn rcd = { Kind = Record { Kind = Function; Fields = rcd }; Evaluated = None }
let choose rcd = { Kind = Record { Kind = Choice; Fields = rcd }; Evaluated = None }
let blck rcd = { Kind = Record { Kind = Block; Fields = rcd }; Evaluated = None }
let app n a = { Kind = Call(n, { Kind = Record { Kind = Block; Fields = a }; Evaluated = None }); Evaluated = None }
let appr n r = { Kind = Call(n, { Kind = Assign(Name r); Evaluated = None }); Evaluated = None }
let s n = Sample(String n)
let i n = Sample(Int n)
let n n = Name n

let demo = blck [ 
  "match-digit" => ( fn [
    "it" => set (s "")
    "tmp" => ( choose [
      !> ( blck [ 
        "rest" => ( app (n "match-string") [ "it" => set (n "it"); "str" => set (s "1") ] )  
        "value" => set (i 1)
      ] )
      !> ( blck [ 
        "rest" => ( app (n "match-string") [ "it" => set (n "it"); "str" => set (s "2") ] )  
        "value" => set (i 2)
      ] )
      !> ( blck [ 
        "rest" => ( app (n "match-string") [ "it" => set (n "it"); "str" => set (s "3") ] )  
        "value" => set (i 3)
      ] )
    ] )
    "res" => dot (set (n "tmp")) "value"
  ] )

  "parse" => ( fn [
    "input" => set (s "")
    "it" => set (n "input")
    "num1" => ( app (n "match-digit") [ "it" => set (n "it") ] )
    "it" => dot (set (n "num1")) "tmp"
    "it" => dot (set (n "it")) "rest"
    "num1" => dot (set (n "num1")) "res"
    "op" => ( choose [
      !> ( blck [
        "rest" => 
          ( app (n "match-string") 
              [ "it" => set (n "it"); "str" => set (s "*") ] )
        "kind" => set (s "times")
      ] )
      !> ( blck [
        "rest" => 
          ( app (n "match-string") 
              [ "it" => set (n "it"); "str" => set (s "+") ] )
        "kind" => set (s "plus")
      ] )
    ] )
    "it" => dot (set (n "op")) "rest"
    "op" => dot (set (n "op")) "kind"
    "num2" => ( app (n "match-digit") [ "it" => set (n "it") ] )
    "num2" => dot (set (n "num2")) "res"
  ] )


  "eval" => ( fn [
    "num1" => set (i 0)
    "num2" => set (i 0)
    "op" => set (s "")
    "res" => ( choose [ 
      !> ( blck [ 
        !> ( app (n "equals") [ "first" => set (n "op"); "second" => set (s "plus") ] )
        "value" => ( app (n "add") [ "first" => set (n "num1"); "second" => set (n "num2") ] )
      ])
      !> ( blck [ 
        !> ( app (n "equals") [ "first" => set (n "op"); "second" => set (s "times") ] )
        "value" => ( app (n "mult") [ "first" => set (n "num1"); "second" => set (n "num2") ] )
      ])
    ] )
  ])

  "p1" => ( app (n "parse") [ "input" => set (s "2+3") ] )
  "p2" => ( app (n "parse") [ "input" => set (s "2*3") ] )
  "e1" => ( appr (n "eval") "p1" )
  "e2" => ( appr (n "eval") "p2" )
  "v1" => ( dot (set (n "e1")) "res" )
  "v2" => ( dot (set (n "e2")) "res" )
  "v1" => ( dot (set (n "v1")) "value" )
  "v2" => ( dot (set (n "v2")) "value" )
]

let state = { Document = demo }
createVirtualDomApp "out" state view update 