import Lean.Elab.Import

open Lean

structure FullHeaderResult where
  imports : Array Import
  isModule : Bool
  terminalLine : Nat
  terminalColumn : Nat
  messages : Array String
  deriving ToJson

structure FullFileResult where
  result? : Option FullHeaderResult := none
  errors : Array String := #[]
  deriving ToJson

structure FullParserResults where
  rows : Array FullFileResult
  deriving ToJson

def parseHeaderFile (fileName : String) : IO FullFileResult := do
  try
    let input ← IO.FS.readFile ⟨fileName⟩
    let inputCtx := Parser.mkInputContext input fileName
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (imports, terminalPos, importMessages) ← Elab.parseImports input (some fileName)
    let mut renderedMessages := #[]
    for message in messages.toList ++ importMessages.toList do
      renderedMessages := renderedMessages.push (← message.toString)
    return {
      result? := some {
        imports
        isModule := Elab.HeaderSyntax.isModule header
        terminalLine := terminalPos.line
        terminalColumn := terminalPos.column
        messages := renderedMessages
      }
    }
  catch error =>
    return { errors := #[error.toString] }

def main : IO UInt32 := do
  let fileNames ← (← IO.getStdin).lines
  let rows ← fileNames.mapM parseHeaderFile
  IO.println (toJson { rows : FullParserResults } |>.compress)
  return 0
