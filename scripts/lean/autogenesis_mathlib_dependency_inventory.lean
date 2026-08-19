import Mathlib

/-!
Emit direct theorem-to-theorem dependency names for Nat/Int Mathlib theorems.

This is an evaluation-only extractor. It is the one Autogenesis source tool
allowed to inspect `TheoremVal.value`, and its output schema can contain only a
theorem name, defining module, and sorted dependency names. Candidate selection
and proof search must never execute it or receive the source proof values.
-/

open Lean Elab Command

private def selectedNamespace (name : Name) : Bool :=
  let rendered := name.toString
  rendered.startsWith "Nat." || rendered.startsWith "Int."

private def isTheorem (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.thmInfo _) => true
  | _ => false

elab "#axeyumMathlibDependencyInventory" : command => do
  let env ← getEnv
  let declarations := env.constants.toList.mergeSort fun left right =>
    left.1.toString < right.1.toString
  for (name, info) in declarations do
    match info with
    | .thmInfo theoremInfo =>
        if selectedNamespace name then
          let dependencies := theoremInfo.value.getUsedConstants
            |>.filter (fun dependency => dependency != name && isTheorem env dependency)
            |>.map (·.toString)
            |>.qsort (· < ·)
            |>.toList
            |>.eraseDups
            |>.toArray
          let moduleName :=
            (env.getModuleIdxFor? name).bind (env.header.modules[·]?)
              |>.map (·.module.toString) |>.getD ""
          let row := Json.mkObj [
            ("name", Json.str name.toString),
            ("module", Json.str moduleName),
            ("theorem_dependencies", Json.arr (dependencies.map Json.str))
          ]
          liftIO <| IO.println row.compress
    | _ => pure ()

#axeyumMathlibDependencyInventory
