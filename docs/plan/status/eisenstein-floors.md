# Lane: eisenstein-floors

Status: IN PROGRESS (opened 2026-08-31)

Target: the floor-counting residue named as #1 in ADR-1260 -- naming the
rectangle-partition row counts as floors, i.e. bridging
`countRange (fun y => blt (mul p (succ y)) B) n` to `min n (div B p)`, and
deciding whether the family can EMIT constructor shapes or genuinely fights
`Nat.div`/`Nat.mod` being stuck at symbolic arguments.

Landed changes: (none yet -- initial checkpoint commit)
