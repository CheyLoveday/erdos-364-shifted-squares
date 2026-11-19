-- Runs only in the isolated build worker, before serialization.
-- The protected reference build uses reviewed owned source, never a candidate olean.
import Lean.Environment
import Lake.Check.Util
import Lean.Data.Json.FromToJson

open Lean Lake.Check

def primitives : Array Name := #[
  `Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd, `Nat.div, `Nat.mod,
  `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft,
  `Nat.shiftRight, `String.ofList, `Char.ofNat, `List, `eagerReduce,
  `Nat, `String, `String.mk, `Char, `optParam, `autoParam, `semiOutParam, `outParam]

def references (info : ConstantInfo) : Array Name :=
  ((runForUsedConsts info fun n => modify (fun refs : Array Name => refs.push n))
    : StateM (Array Name) Unit).run #[] |>.2

-- Safety comes from the imported declaration, never its spelling. Partial
-- compilation helpers and unsafe code are not logical module roots. If either
-- is explicitly selected or reached from a logical root, traversal refuses it.
def nonlogicalSafety? (info : ConstantInfo) : Option String :=
  if info.isUnsafe then some "unsafe"
  else if info.isPartial then some "partial"
  else none

def collectProjectInventory (cfg : Json) : IO Json := do
  initSearchPath (← findSysroot)
  let names ← IO.ofExcept <| cfg.getObjValAs? (Array String) "root_modules"
  let modules := names.map String.toName
  let env ← importModules (modules.map fun n => { module := n }) {}
  let moduleNames := env.header.moduleNames
  let mut roots := #[]
  let mut excluded := #[]
  let targets ← IO.ofExcept <| cfg.getObjValAs? (Array String) "target_declarations"
  let definitions ← IO.ofExcept <| cfg.getObjValAs? (Array String) "protected_definitions"
  let mut work : Array (Name × Option Name) :=
    (primitives ++ ((targets ++ definitions).map String.toName)).map (·, none)
  let mut recursors : Std.HashMap Name (Array Name) := {}
  for (_, info) in env.constants do
    if let .recInfo val := info then
      for n in val.all do
        recursors := recursors.insert n ((recursors[n]?.getD #[]).push val.name)
  for mod in modules do
    let mut declarations : Array Name := #[]
    for (name, info) in env.constants do
      if let some idx := env.getModuleIdxFor? name then
        if moduleNames[idx.toNat]! == mod then
          if let some safety := nonlogicalSafety? info then
            excluded := excluded.push <| Json.mkObj [
              ("module", toJson mod.toString), ("name", toJson name.toString),
              ("safety", toJson safety)]
          else
            declarations := declarations.push name
    declarations := declarations.qsort (fun a b => a.toString < b.toString)
    roots := roots.push <| Json.mkObj [
      ("name", toJson mod.toString),
      ("declarations", toJson (declarations.map Name.toString))]
    work := work ++ declarations.map (·, none)
  let mut visited : NameHashSet := {}
  let mut parents : Std.HashMap Name Name := {}
  let mut units := #[]
  while !work.isEmpty do
    let (name, parent) := work.back!
    work := work.pop
    if visited.contains name then continue
    visited := visited.insert name
    if let some parent := parent then
      parents := parents.insert name parent
    let some info := env.find? name
      | throw <| IO.userError s!"Missing dependency {name}"
    if let some safety := nonlogicalSafety? info then
      let mut path := [name]
      let mut cursor := name
      while let some parent := parents[cursor]? do
        path := parent :: path
        cursor := parent
      throw <| IO.userError s!"UNSUPPORTED_LOGICAL_DECLARATION ({safety}): {String.intercalate " -> " (path.map Name.toString)}"
    let refs := references info
    work := work ++ (refs ++ recursors[name]?.getD #[]).map (·, some name)
    if let .quotInfo _ := info then
      work := work ++ #[`Eq, `Quot, `Quot.mk, `Quot.lift, `Quot.ind].map (·, some name)
    units := units.push <| Json.mkObj [
      ("name", toJson name.toString), ("references", toJson (refs.map Name.toString))]
  return Json.mkObj [
    ("schema_version", toJson "LogicalInventoryV2"),
    ("modules", Json.arr roots), ("excluded", Json.arr excluded),
    ("units", Json.arr units)]

def main : IO Unit := do
  let input ← IO.FS.readFile "/inputs/project-config.json"
  let cfg ← IO.ofExcept <| Json.parse input
  IO.println (← collectProjectInventory cfg).compress
