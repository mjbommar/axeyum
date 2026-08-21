import autogenesis_div_add_mod_bounded_induction
import Lean

open Lean Elab Command

elab "#axeyumDivAddModBoundedTypeInventory" : command => do
  let env ← getEnv
  let name := `Axeyum.Autogenesis.divAddModBoundedInduction
  match env.find? name with
  | some (.thmInfo theoremInfo) =>
      let prettyType ← liftTermElabM <| Meta.ppExpr theoremInfo.type
      let row := Json.mkObj [
        ("name", Json.str name.toString),
        ("level_params", Json.arr (theoremInfo.levelParams.toArray.map
          (fun value => Json.str value.toString))),
        ("type", Json.str prettyType.pretty),
        ("type_repr", Json.str (reprStr theoremInfo.type))
      ]
      liftIO <| IO.println row.compress
  | _ => throwError "authored bounded-induction theorem is absent or not a theorem"

#axeyumDivAddModBoundedTypeInventory
