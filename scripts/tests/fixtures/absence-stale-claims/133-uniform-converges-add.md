
- **`CReal.uniform_converges_add`** — does not exist. No `CRealPrelude`
  field, no `declare_uniform_converges_add`. Exists as a commit
  (`aa347788f`) on unmerged branch `worktree-agent-a2562e3631adc1bf2` only.
- **`Nat.even_or_odd`** — does not exist. Confirmed three ways: no source
  match, `theorem_dependency_inventory Nat.even_or_odd` exits 1, and
  `nat_prelude/fibonacci.rs`'s own doc comment says a parity case-split
  "is NOT attempted in this [declaration]... substantial new machinery".
  Exists as a commit (`88c516432`, "computed even/odd split") on unmerged
  branches `worktree-agent-a71ce0189ae2e5688` / `worktree-agent-aa7767a7d63d9446e`
  only.
- **`CReal.alternatingBracketUpper`**, **`CReal.alternatingLowerBound`**,
  **`CReal.alternatingUpperBound`** — none exist. `creal/alternating.rs` has
  exactly three `declare_*` functions (`neg_one_pow_double`,
  `alternating_e_le_o`, `alternating_bracket`); no dual/upper-bound variant
  anywhere in `creal/`.
