/-
Replay an official `lean4export` NDJSON 3.1.0 stream into the **real Lean
kernel**.

Usage (needs only the pinned toolchain; no lake project, no network):

    lean --run scripts/lean/replay-lean4export.lean <stream.ndjson>

Why this exists: `lean file.lean` on a rendered module runs the *elaborator* —
implicit-argument inference, universe unification, coercion insertion, code
generation — none of which bear on whether a proof term is well typed. This
script bypasses all of it. It parses the export format, rebuilds each
declaration, and hands it to `Lean.Environment.addDeclCore`, which is Lean's own
kernel type checker. Nothing is elaborated and nothing is compiled.

It starts from `mkEmptyEnvironment`, so the stream must be self-contained and
nothing can be silently satisfied by Lean's own `Init` (in particular the
quotient package is added from the stream, never inherited — adding it twice is
a kernel error).

Recursors and constructors carried by an `inductive` record are deliberately
**not** replayed: Lean generates them itself from the family declaration, which
is the stronger check — our exported recursor must then agree with the one
Lean's kernel derives, or a later declaration that mentions it fails to check.
-/
import Lean
open Lean

private def jField (value : Json) (field : String) : IO Json :=
  IO.ofExcept (value.getObjVal? field)

private def jNat (value : Json) : IO Nat := IO.ofExcept value.getNat?
private def jStr (value : Json) : IO String := IO.ofExcept value.getStr?
private def jBool (value : Json) : IO Bool := IO.ofExcept value.getBool?
private def jArr (value : Json) : IO (Array Json) := IO.ofExcept value.getArr?

private def jFieldNat (value : Json) (field : String) : IO Nat := do
  jNat (← jField value field)

private def binderInfo : String → IO BinderInfo
  | "default" => pure .default
  | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit
  | "instImplicit" => pure .instImplicit
  | other => throw (IO.userError s!"unknown binderInfo {other}")

private structure Tables where
  names : Array Name := #[Name.anonymous]
  levels : Array Level := #[Level.zero]
  exprs : Array Expr := #[]

private def levelParams (tables : Tables) (value : Json) : IO (List Name) := do
  let entries ← jArr value
  let mut out := #[]
  for entry in entries do
    out := out.push tables.names[(← jNat entry)]!
  return out.toList

private def levelArgs (tables : Tables) (value : Json) : IO (List Level) := do
  let entries ← jArr value
  let mut out := #[]
  for entry in entries do
    out := out.push tables.levels[(← jNat entry)]!
  return out.toList

private def hints (value : Json) : IO ReducibilityHints := do
  match value with
  | .str "opaque" => pure .opaque
  | .str "abbrev" => pure .abbrev
  | _ => pure (.regular (UInt32.ofNat (← jFieldNat value "regular")))

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lean --run replay-lean4export.lean <stream.ndjson>"
      return 2
  let content ← IO.FS.readFile path
  let mut tables : Tables := {}
  let mut env ← mkEmptyEnvironment
  let mut pendingQuot := 0
  let mut declarations := 0
  let mut inductives := 0
  let mut lineNumber := 0
  for rawLine in content.splitOn "\n" do
    let line := rawLine.trimAscii.toString
    lineNumber := lineNumber + 1
    if line.isEmpty then continue
    let record ← IO.ofExcept (Json.parse line)
    if lineNumber == 1 then
      let header ← jField record "meta"
      let format ← jField header "format"
      let version ← jStr (← jField format "version")
      unless version == "3.1.0" do
        IO.eprintln s!"unsupported export format {version}"
        return 1
      continue
    -- Name, level, and expression records.
    if let .ok _ := record.getObjVal? "in" then
      let name ←
        if let .ok entry := record.getObjVal? "str" then
          pure (Name.mkStr tables.names[(← jFieldNat entry "pre")]! (← jStr (← jField entry "str")))
        else
          let entry ← jField record "num"
          pure (Name.mkNum tables.names[(← jFieldNat entry "pre")]! (← jFieldNat entry "i"))
      tables := { tables with names := tables.names.push name }
      continue
    if let .ok _ := record.getObjVal? "il" then
      let level ←
        if let .ok entry := record.getObjVal? "succ" then
          pure (Level.succ tables.levels[(← jNat entry)]!)
        else if let .ok entry := record.getObjVal? "max" then
          let pair ← jArr entry
          pure (Level.max tables.levels[(← jNat pair[0]!)]! tables.levels[(← jNat pair[1]!)]!)
        else if let .ok entry := record.getObjVal? "imax" then
          let pair ← jArr entry
          pure (Level.imax tables.levels[(← jNat pair[0]!)]! tables.levels[(← jNat pair[1]!)]!)
        else
          pure (Level.param tables.names[(← jFieldNat record "param")]!)
      tables := { tables with levels := tables.levels.push level }
      continue
    if let .ok _ := record.getObjVal? "ie" then
      let expr ←
        if let .ok entry := record.getObjVal? "bvar" then
          pure (Expr.bvar (← jNat entry))
        else if let .ok entry := record.getObjVal? "sort" then
          pure (Expr.sort tables.levels[(← jNat entry)]!)
        else if let .ok entry := record.getObjVal? "const" then
          pure (Expr.const tables.names[(← jFieldNat entry "name")]!
            (← levelArgs tables (← jField entry "us")))
        else if let .ok entry := record.getObjVal? "app" then
          pure (Expr.app tables.exprs[(← jFieldNat entry "fn")]!
            tables.exprs[(← jFieldNat entry "arg")]!)
        else if let .ok entry := record.getObjVal? "lam" then
          pure (Expr.lam tables.names[(← jFieldNat entry "name")]!
            tables.exprs[(← jFieldNat entry "type")]!
            tables.exprs[(← jFieldNat entry "body")]!
            (← binderInfo (← jStr (← jField entry "binderInfo"))))
        else if let .ok entry := record.getObjVal? "forallE" then
          pure (Expr.forallE tables.names[(← jFieldNat entry "name")]!
            tables.exprs[(← jFieldNat entry "type")]!
            tables.exprs[(← jFieldNat entry "body")]!
            (← binderInfo (← jStr (← jField entry "binderInfo"))))
        else if let .ok entry := record.getObjVal? "letE" then
          pure (Expr.letE tables.names[(← jFieldNat entry "name")]!
            tables.exprs[(← jFieldNat entry "type")]!
            tables.exprs[(← jFieldNat entry "value")]!
            tables.exprs[(← jFieldNat entry "body")]!
            (← jBool (← jField entry "nondep")))
        else if let .ok entry := record.getObjVal? "proj" then
          pure (Expr.proj tables.names[(← jFieldNat entry "typeName")]!
            (← jFieldNat entry "idx") tables.exprs[(← jFieldNat entry "struct")]!)
        else if let .ok entry := record.getObjVal? "natVal" then
          pure (Expr.lit (.natVal (← jStr entry).toNat!))
        else
          throw (IO.userError s!"line {lineNumber}: unsupported expression record")
      tables := { tables with exprs := tables.exprs.push expr }
      continue
    -- Declaration records.
    let declaration : Option Declaration ←
      if let .ok entry := record.getObjVal? "axiom" then
        pure (some (.axiomDecl {
          name := tables.names[(← jFieldNat entry "name")]!
          levelParams := (← levelParams tables (← jField entry "levelParams"))
          type := tables.exprs[(← jFieldNat entry "type")]!
          isUnsafe := false }))
      else if let .ok entry := record.getObjVal? "def" then
        let name := tables.names[(← jFieldNat entry "name")]!
        pure (some (.defnDecl {
          name := name
          levelParams := (← levelParams tables (← jField entry "levelParams"))
          type := tables.exprs[(← jFieldNat entry "type")]!
          value := tables.exprs[(← jFieldNat entry "value")]!
          hints := (← hints (← jField entry "hints"))
          safety := .safe
          all := [name] }))
      else if let .ok entry := record.getObjVal? "thm" then
        let name := tables.names[(← jFieldNat entry "name")]!
        pure (some (.thmDecl {
          name := name
          levelParams := (← levelParams tables (← jField entry "levelParams"))
          type := tables.exprs[(← jFieldNat entry "type")]!
          value := tables.exprs[(← jFieldNat entry "value")]!
          all := [name] }))
      else if let .ok entry := record.getObjVal? "opaque" then
        let name := tables.names[(← jFieldNat entry "name")]!
        pure (some (.opaqueDecl {
          name := name
          levelParams := (← levelParams tables (← jField entry "levelParams"))
          type := tables.exprs[(← jFieldNat entry "type")]!
          value := tables.exprs[(← jFieldNat entry "value")]!
          isUnsafe := false
          all := [name] }))
      else if let .ok _ := record.getObjVal? "quot" then
        pendingQuot := pendingQuot + 1
        if pendingQuot == 4 then pure (some .quotDecl) else pure none
      else if let .ok entry := record.getObjVal? "inductive" then
        let types ← jArr (← jField entry "types")
        let ctors ← jArr (← jField entry "ctors")
        let numParams ← jFieldNat types[0]! "numParams"
        let uparams ← levelParams tables (← jField types[0]! "levelParams")
        let mut families := #[]
        for family in types do
          let familyName := tables.names[(← jFieldNat family "name")]!
          let mut constructors := #[]
          for ctor in ctors do
            if tables.names[(← jFieldNat ctor "induct")]! == familyName then
              constructors := constructors.push {
                name := tables.names[(← jFieldNat ctor "name")]!
                type := tables.exprs[(← jFieldNat ctor "type")]! : Constructor }
          families := families.push {
            name := familyName
            type := tables.exprs[(← jFieldNat family "type")]!
            ctors := constructors.toList : InductiveType }
        inductives := inductives + 1
        pure (some (.inductDecl uparams numParams families.toList false))
      else
        throw (IO.userError s!"line {lineNumber}: unknown declaration record")
    if let some declaration := declaration then
      match env.addDeclCore 0 declaration none true with
      | .ok next =>
        env := next
        declarations := declarations + 1
      | .error exception =>
        let message ← (exception.toMessageData {}).toString
        IO.eprintln s!"line {lineNumber}: REAL LEAN KERNEL REJECTED the declaration: {message}"
        return 1
  IO.println s!"lean4export replay: the real Lean kernel accepted {declarations} declaration records \
({inductives} inductive groups), environment now holds {env.constants.toList.length} constants"
  return 0
