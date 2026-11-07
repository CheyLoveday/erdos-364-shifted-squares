-- Trusted preparation utility. Reads data only; never imports Mathlib/candidate oleans.
import Lake.Build.Common

open Lean Lake System

def main : IO Unit := do
  let input ← IO.FS.readFile "/inputs/hash-inputs.json"
  let paths ← IO.ofExcept <| Json.parse input >>= fromJson? (α := Array (String × Bool))
  let mut rows : Array Json := #[]
  for (path, text) in paths do
    let hash ← Lake.computeFileHash (FilePath.mk path) text
    rows := rows.push <| Json.mkObj [("path", toJson path), ("hash", toJson hash.toString)]
  IO.println (Json.arr rows).compress
