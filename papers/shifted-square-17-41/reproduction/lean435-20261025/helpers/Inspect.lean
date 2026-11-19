-- Trusted judge source: parses only NDJSON, never imports a candidate olean.
import Lake.Check.Compare
import Lake.Check.Axioms
import Lean.Data.Json.FromToJson

open Lean LeanExport Lake.Check

def readNames (config : Json) (key : String) : IO (Array Name) := do
  let strings : Array String ← IO.ofExcept <| fromJson? (← IO.ofExcept <| config.getObjVal? key)
  -- The protected Python guard admits only dot-separated ASCII identifiers.
  pure <| strings.map fun name => (name.splitOn ".").foldl Name.str Name.anonymous

-- Exact primitive roots used by Lake 4.35.0's comparator.
def primitives : Array Name := #[
  `Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd, `Nat.div, `Nat.mod,
  `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft,
  `Nat.shiftRight, `String.ofList, `Char.ofNat, `List, `eagerReduce,
  `Nat, `String, `String.mk, `Char, `optParam, `autoParam, `semiOutParam, `outParam]

def main (args : List String) : IO UInt32 := do
  try
    let solutionPath ← match args with
      | [_, solution, _] => pure solution
      | [solution] => pure solution
      | _ => throw <| IO.userError "One inventory export or two exports plus protected config required"
    let solution ← parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
    let mut targets : Array Name := #[]
    let mut protectedDefinitions : Array Name := #[]
    let mut axioms : Array Name := #[]
    let mut axiomFree : Array Name := #[]
    if let [challengePath, _, configPath] := args then
      let config ← IO.ofExcept <| Lean.Json.parse (← IO.FS.readFile configPath)
      targets ← readNames config "theorem_names"
      protectedDefinitions ← readNames config "protected_definition_names"
      axioms ← readNames config "permitted_axioms"
      axiomFree ← readNames config "axiom_free_controls"
      let holes ← readNames config "definition_holes"
      if targets.isEmpty || !holes.isEmpty then throw <| IO.userError "Nonempty exact targets required"
      let challenge ← parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
      IO.ofExcept <| compareAt challenge solution targets #[] (primitives ++ protectedDefinitions)
      -- ConstantInfo BEq uses Expr.eqv, which ignores binder names/annotations.
      -- This fixed exact-source mode also preserves those frozen interface details.
      for name in targets do
        let some expected := challenge.constMap[name]?
          | throw <| IO.userError s!"Missing expected target {name}"
        let some actual := solution.constMap[name]?
          | throw <| IO.userError s!"Missing solution target {name}"
        if !(expected.type.equal actual.type) then
          throw <| IO.userError s!"Exact target type/binder mismatch: {name}"
      for name in protectedDefinitions do
        let some (.defnInfo expected) := challenge.constMap[name]?
          | throw <| IO.userError s!"Missing expected definition {name}"
        let some (.defnInfo actual) := solution.constMap[name]?
          | throw <| IO.userError s!"Missing solution definition {name}"
        if !(expected.type.equal actual.type) || !(expected.value.equal actual.value) then
          throw <| IO.userError s!"Exact protected definition mismatch: {name}"
      IO.ofExcept <| checkAxioms solution targets #[] axioms
      IO.ofExcept <| checkAxioms solution axiomFree #[] #[]
    let mut units := #[]
    for name in solution.constOrder do
      let some info := solution.constMap[name]?
        | throw <| IO.userError "Missing exported unit"
      let collect : StateM (Array String) Unit :=
        runForUsedConsts info fun n => modify (fun refs => refs.push n.toString)
      let refs := (collect.run #[]).2
      units := units.push <| Json.mkObj [
        ("name", toJson name.toString), ("references", toJson refs)]
    IO.println <| (Json.mkObj [
      ("targets", toJson (targets.map Name.toString)),
      ("definition_holes", toJson (#[] : Array String)),
      ("binder_annotations_checked", toJson (args.length == 3)),
      ("protected_definition_names", toJson (protectedDefinitions.map Name.toString)),
      ("permitted_axioms", toJson (axioms.map Name.toString)),
      ("axiom_free_controls", toJson (axiomFree.map Name.toString)),
      ("used_axioms", toJson ((usedAxioms solution).map (·.1.toString))),
      ("units", Json.arr units)]).compress
    return 0
  catch e =>
    IO.eprintln e.toString
    return 1
