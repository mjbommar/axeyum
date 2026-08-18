import Mathlib

/-!
Emit a statement-only inventory of Nat/Int Mathlib theorems as NDJSON.

Run this file from a pinned Mathlib checkout:

  lake env lean /path/to/axeyum/scripts/lean/autogenesis_mathlib_statement_inventory.lean

The output deliberately contains the declaration name, defining module, level
parameters, and theorem type, but never `TheoremVal.value`. It is candidate
source material, not an import stream and not evidence for an Axeyum fact.
-/

open Lean Elab Command

private def selectedNamespace (name : Name) : Bool :=
  let rendered := name.toString
  rendered.startsWith "Nat." || rendered.startsWith "Int."

elab "#axeyumMathlibStatementInventory" : command => do
  let env ← getEnv
  let declarations := env.constants.toList.mergeSort fun left right =>
    left.1.toString < right.1.toString
  for (name, info) in declarations do
    match info with
    | .thmInfo theoremInfo =>
        if selectedNamespace name then
          let prettyType ← liftTermElabM <| Meta.ppExpr theoremInfo.type
          let moduleName :=
            (env.getModuleIdxFor? name).bind (env.header.modules[·]?)
              |>.map (·.module.toString) |>.getD ""
          let row := Json.mkObj [
            ("name", Json.str name.toString),
            ("module", Json.str moduleName),
            ("level_params", Json.arr (theoremInfo.levelParams.toArray.map
              (fun value => Json.str value.toString))),
            ("type", Json.str prettyType.pretty),
            ("type_repr", Json.str (reprStr theoremInfo.type))
          ]
          liftIO <| IO.println row.compress
    | _ => pure ()

#axeyumMathlibStatementInventory
