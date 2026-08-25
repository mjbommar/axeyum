# Lane: string-recon — the string-length certificate had no kernel term behind it

<!-- plan-section: lane-status -->

**Two of the three string-length certificates now carry a Lean term real Lean 4
accepts; the third declines for two independent reasons, and the guard that was
supposed to catch the second admitted it** (`WIP`, string-recon, 2026-08-20).

`Evidence::UnsatStringLength` was rung 2 of the ladder — a certificate an
independent checker re-derives, with nothing kernel-checked behind it.
`reconstruct_string_length` builds the term for the **conjunctive** case over
the constructed integers (`try_new_over_integers`; `integer: axiom=0`), not
`AxReal` and not `CReal`: lengths and code points are integers, and `ℤ` models
every law a Farkas combination uses.

Detail moved to [`../notes/agent-string-recon.md`](../notes/agent-string-recon.md).

<!-- plan-section: landed-changes -->

| 2026-08-20 | `609417c9e` | `MAX_UNARY_TERMS` 4096 → 128: mutating the size guard away aborted the test binary rather than failing a test (cost 1026 overflows the stack; cost 514 renders a 13.2 MB module), so the budget admitted the crash it existed to prevent. Now pinned from both ends. The inequality sign re-check killed nothing and was deleted — positivity is enforced upstream by `checked_refutation` and downstream by both Farkas engines. The hypothesis-count check and the external `infer == False` re-gate also kill nothing and are kept, with the mutation pair that shows what the first one does (removing the equality registration kills 7 tests *through* it; removing both kills 1 and ships a quietly weaker module). New `lean_crosscheck` family `qf_s_string_length`: real Lean 4 accepts both modules, 173/173 in the full sweep. |
| 2026-08-20 | `b495a396e` | The string-length certificate reaches the kernel. `reconstruct_string_length` folds the certificate's own facts into a `False` over the constructed integers; `checked_refutation` is now the single derivation both `check_string_length_refutation` and the reconstruction read, so the exported view cannot drift from the validated one. An asserted **equality** enters as an equality — `LraReconstructCtx` grew `hyp_overrides` so the route mints `a = 0` and derives the `≤` half rather than assuming it, which is the one distinction the certificate's fact table turns on. A single-disjunct `(or A)` declines: the query states the disjunction, not the disjunct. Variables are named after their source (`len_xx`, `code_x`). `Evidence::UnsatStringLength` became a struct variant carrying `lean_module: Option<String>`, re-derived on `check` and never read back; a decline is `None`, not a weaker certificate. No `ProofFragment` variant — `scan_proof_fragment` is arena-based and a string script has no faithful arena. |
