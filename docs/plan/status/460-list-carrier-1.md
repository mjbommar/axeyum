# Lane: list-carrier-1 — `List` as a real prelude inductive (ADR-1495/1520/1577 follow-on)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, list-carrier-1, 2026-09-03).** Landing `List.{u}`
as an ordinary universe-polymorphic inductive (`nil`/`cons`), instantiated at
`u := 0` for its operations, in a new `list_prelude` module between `logic`
and `nat`. In progress: the inductive + recursor, `length`/`append`/`map`/
`foldr`/`reverse`, then theorems, then a bridge to `Nat.Multiset`. Details to
follow as work lands.

<!-- plan-section: landed-changes -->

| 2026-09-03 | list-carrier-1 | status stub opened |
