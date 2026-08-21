import autogenesis_div_add_mod_public_recursion
import Lean

open Lean Elab Command

elab "#axeyumDivAddModTypeInventory" : command => do
  let env ← getEnv
  let name := `Axeyum.Autogenesis.divAddModPublicRecursion
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
  | _ => throwError "authored public Euclidean theorem is absent or not a theorem"

#axeyumDivAddModTypeInventory
