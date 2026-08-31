
The remaining two — `F:ml430-nat-factorial-dvd-ascfactorial-44a4e641` and
`F:ml430-nat-factorial-dvd-descfactorial-bbf6124f` — are left **open**.
`Nat.ascFactorial`/`Nat.descFactorial` do not exist in this kernel: no field on
`NatPrelude`, and `asc_factorial`/`desc_factorial`/`ascFactorial`/
`descFactorial` all grep to zero hits anywhere in
`crates/axeyum-lean-kernel/src/`. The prelude struct field list is the
authoritative registry here (every field is declared exactly once, at
construction), so this is a confirmed absence, not an unfound search — matches
the brief's expectation. Building the two ascending/descending factorial
definitions plus their base-case facts (`F-ml430-nat-ascfactorial-zero-…`,
`F-ml430-nat-descfactorial-zero-…`, etc. — eight open facts already sit in the
ledger for this family) is out of scope for an import-backlog lane and is the
next lane's task if picked up.
