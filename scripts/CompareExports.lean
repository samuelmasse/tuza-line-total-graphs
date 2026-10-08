module

import Lake.Check.Compare
import Lake.Check.Axioms
import Lean.Data.Json

/-! Local statement comparison of already generated exports using Lake's checker.
This does not run Palomar's sandboxed build or its full mechanical preflight.
Generate the exports with the pinned toolchain and all targets listed below.
-/

public def main (args : List String) : IO Unit := do
  let [configPath, challengePath, solutionPath] := args |
    throw <| IO.userError "Expected comparator.json, Challenge export, Solution export"
  let cfg ← IO.ofExcept <| Lean.Json.parse (← IO.FS.readFile configPath)
  let targets ← IO.ofExcept <| cfg.getObjValAs? (Array String) "theorem_names"
  let axioms ← IO.ofExcept <| cfg.getObjValAs? (Array String) "permitted_axioms"
  let targets := targets.map String.toName
  let axioms := axioms.map String.toName
  -- Same primitive boundary as Lake.CLI.Check.primitiveTargets in Lean 4.35.0-rc4.
  let primitives : Array Lean.Name := #[
    `Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd, `Nat.div, `Nat.mod,
    `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft,
    `Nat.shiftRight, `String.ofList, `Char.ofNat, `List, `eagerReduce, `Nat,
    `String, `String.mk, `Char, `optParam, `autoParam, `semiOutParam, `outParam]
  let challenge ← LeanExport.parseStream <|
    .ofHandle (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <|
    .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  IO.ofExcept <| Lake.Check.compareAt challenge solution (targets ++ axioms) #[] primitives
  IO.ofExcept <| Lake.Check.checkAxioms solution targets #[] axioms
  IO.println s!"Accepted {targets.size} target statements and their permitted axioms."
