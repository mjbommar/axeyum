import Init.Prelude

structure ImportPair where
  left : Nat
  right : Nat

def importPairLeft (p : ImportPair) : Nat := p.left
def importNatLiteral : Nat := 37
def importStringLiteral : String := "axeyum"
