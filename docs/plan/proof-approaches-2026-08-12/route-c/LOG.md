# Route C lab notebook — machine-checked mathematics in axeyum's own Lean kernel

Append-only. Entries are timestamped with `date -Is`. Corrections are appended,
never edited into the original. Written for a reader who was not present.

Goal (from the orchestrator's brief): produce the first machine-checked
*mathematical theorem* in this project using `crates/axeyum-lean-kernel`, the
in-tree independent Rust Lean kernel, and report the kernel's real capability
boundary, the complete axiom list, and a negative control showing the checker
rejects a broken proof.

---

## 2026-08-12T19:07:00-04:00 — Entry 1: reconnaissance of the kernel (read-only)

Files read: `src/lib.rs` (module docs + `Kernel` API surface), `src/tests.rs`,
`src/env.rs` (`Declaration`, `Environment`), `src/tc.rs` (`add_declaration`,
`check_declaration`, `KernelError`), `src/prelude.rs` (`LogicPrelude`,
`build_logic_prelude`), `src/arith_prelude.rs` (`ArithPrelude`), `src/inductive.rs`
(`add_inductive` / `add_mutual_inductive` contract), `examples/prelude_axiom_inventory.rs`.

### What the trusted gates are

- `Kernel::add_declaration(Declaration) -> Result<(), KernelError>` is the
  ordinary gate. `check_declaration` (src/tc.rs:862) does exactly two things:
  (a) infers the declared type and requires its type to WHNF to a `Sort`,
  (b) if the declaration has a value, infers the value's type and requires
  `def_eq(value_ty, ty)`, else returns
  `KernelError::DeclarationValueMismatch { declared, inferred }`.
  So a `Declaration::Theorem { ty, value }` is admitted **iff** the kernel can
  itself type-check the proof term against the stated proposition. This is the
  gate every claim below is pushed through.
- `Kernel::add_inductive(name, uparams, num_params, ty, ctors)` is the trusted
  **inductive** gate (src/inductive.rs:239). It checks the parameter/index
  telescope, Lean-4.30 strict positivity on every constructor field, the
  constructor result shape, and then **generates the recursor itself** together
  with its ι-reduction `RecRule`s, `infer`-checking the generated recursor type.
  Admission is transactional (rollback on failure).

**Measured answer to the brief's critical question:** yes — a user can declare an
inductive type with a working recursor through the trusted gate, so genuine
induction is available. It is not merely re-exported for the prelude; the same
public entry point is what `build_logic_prelude` uses.

### What `build_logic_prelude` gives (src/prelude.rs)

All admitted through `add_inductive`/`add_declaration`, none of them axioms:
`True`, `False`, `And`, `Or`, `Iff`, `Eq` (indexed, with `Eq.rec`), `Exists`,
`Bool`, and — the important one — **`Nat : Type` as a genuine recursive
inductive** (`Nat.zero | Nat.succ (n : Nat)`) with a generated `Nat.rec` that
ι-computes `Nat.rec C z s Nat.zero ↦ z` and
`Nat.rec C z s (Nat.succ k) ↦ s k (Nat.rec C z s k)`, eliminating into an
arbitrary `Sort v` including `Prop` (src/prelude.rs:456-486). `Not` is a
`Definition`, not an axiom.

So **induction over ℕ is available with no axioms at all**. That is a much
stronger foundation than the brief anticipated.

### What `arith_prelude` gives — confirmed as the brief stated

`build_arith_prelude` declares an **axiomatized linear ordered field**: carrier
`R : Type` plus `add/mul/neg/zero/one/le/lt` and ~22 order/field axioms
(`le_refl`, `le_trans`, `lt_irrefl`, `add_comm`, `add_assoc`, `add_zero`,
`add_neg`, `mul_comm`, `mul_assoc`, `mul_one`, `mul_zero`, `left_distrib`,
`mul_nonneg`, `sq_nonneg`, …). Every one of these is a `Declaration::Axiom`.
`examples/prelude_axiom_inventory.rs` asserts the exact population:
**30 axioms for the real prelude, 34 for the integer prelude, 1 for the string
prelude**. There is no induction, no divisibility, no naturals in it.

Consequence for this task: proving the target identities over `R` would rest on
30 declared axioms. Proving them over the prelude's **inductive `Nat`** rests on
**zero**. I am therefore choosing the `Nat` route over the ordered-field route.
This is a deliberate strengthening of the brief's C1, not a substitution: the
Rado equation `a(x−y) = bz` lives over the naturals `x,y,z ∈ [1,n]` anyway, and
in ℕ it is written without subtraction as `a·x = a·y + b·z`.

### Existing in-tree proof idiom I am reusing

`crates/axeyum-solver/src/reconstruct/arithmetic.rs` builds `Eq.rec`-based
`symm`/`trans`/congruence combinators over the `R` carrier
(`eq_rec_transport_r` at line 395, `eq_symm_r` 420, `eq_trans_r` 438,
`congr_add_left` 454, …). I am porting that pattern to the `Nat` carrier. The
`Eq.rec` application order measured from that code is
`Eq.rec.{elim, u} α a motive refl_case b h`, with universe list
`[motive-level, carrier-level]`.

### Axioms so far

**Zero.** Nothing declared yet. Planned trusted base: the kernel + the
inductives `Nat` and `Eq` from `build_logic_prelude` + my own `Definition`s
(add, mul, pow, geometric sum, shell recurrence), all of which are definitions
with values, not assumptions.

### Plan (ambition level)

- **A.** `∀ a b : ℕ, a·(a·b² + 1) = a·1 + b·(a²·b)` — the closed-form defect
  family of the shell construction really is a solution of `E(a,b)`, for *all*
  `a,b` (an infinite family, not the 4 enumerated points).
- **B.** `∀ a k : ℕ, a·G(a,k) + 1 = G(a,k) + a^k` where `G(a,k) = Σ_{i<k} a^i` —
  the geometric-sum closed form, by induction on `k`.
- **C.** `∀ a m : ℕ, T(a,m) = a^{m+1} + 2·(a·G(a,m))` where `T` is the shell's
  *level-capacity recurrence* `T(a,0) = a`, `T(a,m+1) = a·T(a,m) + 2a` — i.e.
  the shell size `N = b·(a^{k-1} + 2(a^{k-2}+…+a))` from the brief equals what
  the level capacities actually sum to. Induction on `m`, using B in the step.
- **C'.** the same with the `b` factor, giving the brief's `N` formula verbatim.

If a step turns out not to be expressible, I log the exact error rather than
axiomatising around it.

---

## 2026-08-12T19:13:51-04:00 — Entry 2: the development compiles and the kernel accepts it

Wrote `crates/axeyum-lean-kernel/tests/rado_shell_arithmetic.rs` (public API only).
Structure: a `Dev` wrapper holding a `Kernel` + the logic prelude, with

- locally-nameless term construction (build with `fvar`s, then `abstract_fvars`
  + `lam`/`pi`), which avoids hand-computing de Bruijn indices entirely;
- `Eq.rec`-based `symm` / `trans` / `congr`-in-an-arbitrary-one-hole-context;
- `induct(p, base, step, target)` = `Nat.rec.{0} motive base step target`;
- `define_binary(name, …)` = a `Definition` whose value is
  `fun x y => Nat.rec.{1} (fun _ => Nat) (base x) (fun j ih => step x j ih) y`,
  i.e. structural recursion on the **second** argument. Consequence:
  `f x zero ≡ base x` and `f x (succ j) ≡ step x j (f x j)` hold **definitionally**
  (δ/β/ι), so no equation lemmas are needed and many steps are `Eq.refl`.

Definitions: `rado.add`, `rado.mul`, `rado.pow`, `rado.geo` (Σ_{i<k} aⁱ),
`rado.shellT` (the shell level-capacity recurrence T(a,0)=a, T(a,m+1)=a·T(a,m)+2a),
`rado.nshell a b m = b · shellT a m`.

Lemmas proved by `Nat.rec` induction (all admitted through `add_declaration`,
i.e. all kernel-checked): `zero_add`, `succ_add`, `add_comm`, `add_assoc`,
`add_right_comm`, `zero_mul`, `succ_mul`, `mul_comm`, `mul_one`, `one_mul`,
`left_distrib`, `mul_assoc`.

### Command and verbatim output (run 1)

```
$ export CARGO_BUILD_JOBS=1 && cargo test -p axeyum-lean-kernel --test rado_shell_arithmetic
running 6 tests
test definitions_compute_the_measured_shell_values ... ok
test kernel_checks_the_shell_size_closed_form ... ok
test kernel_checks_the_geometric_sum_closed_form ... ok
test kernel_checks_the_defect_family_identity ... ok
test the_development_declares_no_axioms ... ok
test kernel_rejects_broken_proof_terms ... ok

test result: ok. 6 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.25s
```

**6 tests, nonzero, all passing.** Everything compiled and checked on the first
kernel run — which this repo's CLAUDE.md explicitly says to distrust ("its tools
have lied more often than its solver has been weak"), so the rest of this entry
is the anti-vacuity evidence, not the green line.

### The statements the kernel actually admitted (verbatim `render_lean`)

Note `Nat` prints as `AxNat` (the pretty-printer renames it to avoid colliding
with Lean's builtin on export). `rado.*` are this development's definitions.

```
defect_identity : ((x0 : AxNat) -> ((x1 : AxNat) -> ((Eq.{1} AxNat)
  ((rado.mul x0) ((rado.add ((rado.mul x0) ((rado.mul x1) x1))) (AxNat.succ AxNat.zero))))
  ((rado.add ((rado.mul x0) (AxNat.succ AxNat.zero)))
   ((rado.mul x1) ((rado.mul ((rado.mul x0) x0)) x1)))))

geo_closed_form : ((x0 : AxNat) -> ((x1 : AxNat) -> ((Eq.{1} AxNat)
  ((rado.add ((rado.mul x0) ((rado.geo x0) x1))) (AxNat.succ AxNat.zero)))
  ((rado.add ((rado.geo x0) x1)) ((rado.pow x0) x1))))

shell_closed_form : ((x0 : AxNat) -> ((x1 : AxNat) -> ((Eq.{1} AxNat)
  ((rado.shellT x0) x1))
  ((rado.add ((rado.pow x0) (AxNat.succ x1)))
   ((rado.mul (AxNat.succ (AxNat.succ AxNat.zero))) ((rado.mul x0) ((rado.geo x0) x1))))))

nshell_closed_form : ((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> ((Eq.{1} AxNat)
  (((rado.nshell x0) x1) x2))
  ((rado.mul x1) ((rado.add ((rado.pow x0) (AxNat.succ x2)))
   ((rado.mul (AxNat.succ (AxNat.succ AxNat.zero))) ((rado.mul x0) ((rado.geo x0) x2))))))))
```

i.e. in ordinary notation, for all `a b k m : ℕ`:

- `a·(a·b·b + 1) = a·1 + b·(a·a·b)`
- `a·G(a,k) + 1 = G(a,k) + a^k`
- `T(a,m) = a^(m+1) + 2·(a·G(a,m))`
- `N(a,b,m) = b·(a^(m+1) + 2·(a·G(a,m)))`

These are universally quantified `Pi` telescopes over `AxNat` — infinite
families, not instances.

### Axiom population (measured, not asserted by me)

```
axiom population: []
```
Enumerated by walking `kernel.environment()` and filtering `Declaration::Axiom`.
**Zero axioms.** (Same query shape as `examples/prelude_axiom_inventory.rs`,
which reports 30 for the ordered-field prelude I chose not to use.)

### Negative controls — all five rejected (verbatim)

- **NC1** correct proof, FALSE statement (a factor of `b` dropped from `z`;
  false at a=b=2: 18 ≠ 10) →
  `DeclarationValueMismatch`, declared `… ((rado.mul x1) ((rado.mul x0) x0))`
  vs inferred `… ((rado.mul x1) ((rado.mul ((rado.mul x0) x0)) x1))`. Also
  asserted the rejected name never entered the environment.
- **NC2** swapped lemma arguments (`mul_assoc b a a` where `mul_assoc a a (b*b)`
  is required) → `TypeMismatch`
  expected `Eq AxNat ((a*a)*(b*b)) (a*(a*(b*b)))`
  got `Eq AxNat ((b*a)*a) (b*(a*a))`.
- **NC3** broken induction — the successor step returns the induction hypothesis
  itself (`P j` where `P (succ j)` is required) → `TypeMismatch`
  expected `Eq AxNat (add zero (succ _fvar.2)) (succ _fvar.2)`
  got `(fun x0 => Eq AxNat (add zero x0) x0) _fvar.2`.
- **NC4** false identity `mul a b = add a b` with an `Eq.refl` proof →
  `DeclarationValueMismatch` (declared `… (rado.add x0 x1)`, inferred
  `… (rado.mul x0 x1)`). This is also the control on `def_eq` itself: the
  kernel does *not* consider `mul` and `add` definitionally equal.
- **NC5** transposed conclusion (`pow + geo` instead of `geo + pow`) with the
  unmodified THEOREM B proof term → `DeclarationValueMismatch`. Note this
  statement is *mathematically true* (by `add_comm`) but is not what the proof
  term proves — the kernel is checking the term, not guessing the intent.

**5 deliberate breakages, 5 rejections, 0 acceptances.**

### Anti-vacuity: the definitions compute the brief's measured numbers

Checked with the kernel's own `def_eq` (δ/β/ι), not a Rust-side evaluator:
`pow 3 3 ≡ 27`, `geo 3 3 ≡ 13`, `shellT 3 1 ≡ 15`, `nshell 3 2 1 ≡ 30`
(so N+1 = 31 — the brief's measured row (3,2,3)), `nshell 4 3 1 ≡ 72`
(N+1 = 73 — the brief's row (4,3,3)), and the closed form ≡ 15 at (a=3,m=1).

### Capability boundary observed so far

Nothing has been rejected as *inexpressible* yet. Recorded facts:
- user-declared inductives with generated recursors: **supported** (`Nat`, `Eq`
  come through the same public gate);
- `Prop`-motive elimination out of a `Type`-valued inductive (`Nat.rec.{0}`):
  **supported**, no large-elimination restriction on `Nat`;
- definitional unfolding of user `Definition`s inside `def_eq`, including ι on
  `Nat.rec` with a constructor major: **supported**, and it carries a large part
  of the proof burden (every `f x zero`/`f x (succ j)` equation is `rfl`);
- what is *absent* and had to be built by hand: `Eq.symm`, `Eq.trans`,
  `congrArg`, and every arithmetic lemma. There is no tactic layer, no
  `simp`/`ring`, no unifier for implicit arguments — every argument, including
  every motive, is supplied explicitly.

---

## 2026-08-12T19:20:45-04:00 — Entry 3: pushing past C2 — paper-form N, and two capability probes

### Added after Entry 2

1. `rado.geo1 a m = Σ_{i=1..m} aⁱ` (a second definition, so the final statement
   can be written in the construction's own bracket `a^(k-2) + … + a` rather
   than in my induction-friendly `a·G(a,m)`), the lemma
   `geo_shift : ∀ a m, a·G(a,m) = geo1(a,m)` (induction on m), and
   **THEOREM D** `nshell_paper_form : ∀ a b m, N(a,b,m) = b·(a^(m+1) + 2·geo1(a,m))`
   — with `m = k−2` this is the brief's `N = b·(a^(k−1) + 2(a^(k−2) + … + a))`
   verbatim.
2. **THEOREM E** `solution_family : ∀ a b y t, a·(y + b·t) = a·y + b·(a·t)` —
   the *sufficiency* half of the brief's solution-form lemma (every
   `x = y + b·t`, `z = a·t` is a solution of `E(a,b)`). The converse
   (necessity, needing `gcd(a,b)=1`) is NOT proved and NOT assumed; see the
   boundary section.
3. More anti-vacuity numerics, including two **negative** `def_eq` controls
   (`nshell 3 2 2 ≢ 103`, `pow 3 3 ≢ 26`), plus `nshell 3 2 2 ≡ 102`
   (brief row (3,2,4): N+1 = 103) and `nshell 4 3 2 ≡ 312` (row (4,3,4): 313).

### Capability probe 1 — indexed `Prop` relation + its generated recursor

Question being measured: is the *kernel* the obstacle to a full correctness
proof, or is it the missing library? Declared, through the ordinary public
`add_inductive`, an order relation with one parameter and one index:

```
Le : AxNat → AxNat → Prop
Le.refl : Π (n), Le n n
Le.step : Π (n m), Le n m → Le n (succ m)
```

Admitted. The kernel generated (verbatim `render_lean`):

```
Le.rec : ((x0 : AxNat) -> ((motive : ((x1 : AxNat) -> ((x2 : (rado.Le x0) x1) -> Prop))) ->
         ((refl : (motive x0) (rado.Le.refl x0)) ->
          ((step : ((x3 : AxNat) -> ((x4 : (rado.Le x0) x3) ->
                    ((ih : (motive x3) x4) -> (motive (AxNat.succ x3)) (((rado.Le.step x0) x3) x4))))) ->
           ((x4 : AxNat) -> ((t : (rado.Le x0) x4) -> (motive x4) t))))))
```

Note the motive's codomain is fixed at `Prop` and the recursor carries **no**
universe parameter — the kernel applied the Prop/non-subsingleton
large-elimination restriction by itself, unprompted.

Proved with it: `zero_le : ∀ n, Le 0 n` (induction on `n`, constructors only)
and `le_succ_succ : ∀ n m, Le n m → Le (succ n) (succ m)` — **induction on the
derivation**, i.e. elimination with the generated `Le.rec`. Both accepted.

Negative control **NC6**: `∀ n, Le (succ n) n` with `Le.refl n` as the "proof" →
`DeclarationValueMismatch` (declared `Le (succ x0) x0`, inferred `Le x0 x0`).

### Capability probe 2 — existentials and divisibility

`dvd a n := ∃ q, n = a·q` as a `Definition` over the prelude's `Exists`
(`Exists.rec.{1}`, motive universe fixed at 0 — again the kernel's own
restriction). Proved:

```
dvd_mul : ∀ a q, a ∣ a·q                      (existential introduction)
dvd_add : ∀ a m n, a ∣ m → a ∣ n → a ∣ (m+n)  (double Exists.rec elimination
                                               + left_distrib)
```

Negative control **NC7**: the same proof term against the false conclusion
`a ∣ m·n` → `DeclarationValueMismatch`.

So the full chain "declare a relation → eliminate on a derivation → build and
destruct existentials → prove a closure lemma of divisibility" works. **The
kernel is not the bottleneck for C3.** What is missing is mathematics/library,
not expressiveness. Precisely what is still missing is in the report.

### Commands and verbatim counts

```
$ export CARGO_BUILD_JOBS=1 && cargo test -p axeyum-lean-kernel --test rado_shell_arithmetic
running 8 tests
test capability_probe_indexed_prop_relation_and_its_recursor ... ok
test kernel_checks_the_defect_family_identity ... ok
test capability_probe_existential_divisibility ... ok
test kernel_checks_the_geometric_sum_closed_form ... ok
test kernel_checks_the_shell_size_closed_form ... ok
test the_development_declares_no_axioms ... ok
test definitions_compute_the_measured_shell_values ... ok
test kernel_rejects_broken_proof_terms ... ok

test result: ok. 8 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.39s

$ cargo clippy -p axeyum-lean-kernel --test rado_shell_arithmetic -- -D warnings
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 1.71s      (clean)

$ cargo test -p axeyum-lean-kernel --lib
test result: ok. 199 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.81s
```

**8 tests in the new file (nonzero), 199 pre-existing crate unit tests still
green.** Note the first clippy pass emitted 7 `too_many_lines`/`type_complexity`
warnings, which under CI's `-D warnings` would have failed the gate; fixed with
a documented module-level `allow`, then re-verified clean. Recording this
because the run *before* the fix would have looked "fine" in a plain
`cargo test`.

### Axioms after Entry 3

Still **zero** (`axiom population: []`, measured by walking the environment).
Nothing in Entry 3 introduced an assumption: `geo1`, `dvd`, `Le` are a
definition, a definition, and an inductive declaration respectively.

### Considered and rejected (per the standing honesty rule)

- I considered proving the *necessity* half of the solution-form lemma
  (`gcd(a,b)=1 ∧ a(x−y)=bz ⟹ ∃t, x−y=bt ∧ z=at`) by **assuming** Gauss's lemma
  (`gcd(a,b)=1 ∧ a ∣ b·c ⟹ a ∣ c`) as an axiom. **Rejected**: that axiom is
  essentially the content of the statement, and an "unbounded proof" resting on
  it would be a fraud. It is therefore listed in the report as *not proved*,
  not as an assumption.
- I considered axiomatising `≤` (reflexivity/transitivity/antisymmetry) to state
  `x ≤ N`-style range facts. **Rejected**: probe 1 shows `≤` is *definable*
  inductively, so axiomatising it would have been laziness with a soundness
  cost.

---

## 2026-08-12T19:22:55-04:00 — Entry 4: export probe, and the final measurement

### Export probe (north-star relevance)

`Kernel::render_lean_module_compact_with_inductives("shell_closed_form", goal,
proof, &[Nat, Eq])` emits a **self-contained 42 146-byte Lean module**: real
`inductive AxNat`, real `inductive Eq.{u}`, then `def rado.add … := fun … =>
@AxNat.rec.{1} …` and so on down to `theorem shell_closed_form`. Head of the
file, verbatim:

```
-- Auto-generated by axeyum-lean-kernel: a self-contained re-check of a
-- reconstructed refutation. `prelude` avoids clashing with Lean core.
prelude
set_option linter.unusedVariables false

inductive AxNat : Sort (1) where
  | zero : AxNat
  | succ : ((x0 : AxNat) -> AxNat)
inductive Eq.{u} : ((x0 : Sort (u)) -> ((x1 : x0) -> ((x2 : x0) -> Prop))) where
  | refl : ((x0 : Sort (u)) -> ((x1 : x0) -> ((Eq.{u} x0) x1) x1))
def rado.add : ((x0 : AxNat) -> ((x1 : AxNat) -> AxNat)) :=
  fun (x0 : AxNat) => fun (x1 : AxNat) => (((@AxNat.rec.{1} (fun (x2 : AxNat) => AxNat)) x0) (fun (x2 : AxNat) => fun (x3 : AxNat) => AxNat.succ x3)) x1
```

and its last line is `#print axioms shell_closed_form` — i.e. the module carries
Lean's own axiom audit.

**HONESTY, IMPORTANT:** I did **not** run Lean on it. `command -v lean`,
`command -v lake`, `command -v elan`, and `~/.elan/bin` are all empty on this
box. The module is *emitted and structurally checked* (contains the theorem, the
inductives, no `sorry`, no `axiom `), **not** verified by Lean. Anyone with a
Lean toolchain can check it; the file is saved at
`route-c/shell_closed_form.lean` and the test writes it whenever
`AXEYUM_LEAN_EXPORT_DIR` is set.

### Final measurement

```
$ export CARGO_BUILD_JOBS=1
$ cargo clippy -p axeyum-lean-kernel --test rado_shell_arithmetic -- -D warnings
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.31s     (clean)
$ cargo test -p axeyum-lean-kernel --test rado_shell_arithmetic
running 9 tests
test capability_probe_indexed_prop_relation_and_its_recursor ... ok
test capability_probe_existential_divisibility ... ok
test kernel_checks_the_defect_family_identity ... ok
test kernel_checks_the_geometric_sum_closed_form ... ok
test export_probe_renders_a_real_lean_module ... ok
test kernel_checks_the_shell_size_closed_form ... ok
test the_development_declares_no_axioms ... ok
test definitions_compute_the_measured_shell_values ... ok
test kernel_rejects_broken_proof_terms ... ok

test result: ok. 9 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.47s
```

**9 tests, nonzero, all green. 7 negative controls (NC1–NC7), 7 rejections.
0 axioms.** Nothing was committed (per the brief); the single new file is
`crates/axeyum-lean-kernel/tests/rado_shell_arithmetic.rs`.

### Complete axiom ledger for this development (reconstructible from this log)

| # | Axiom | Where declared |
|---|-------|----------------|
| — | (none) | — |

Trusted base instead of axioms: (1) the `axeyum-lean-kernel` implementation
itself — its type checker, its strict-positivity gate, and its recursor
generator are trusted Rust code, not verified artefacts; (2) the inductive
declarations `AxNat`, `Eq`, `Exists` (from `build_logic_prelude`) and `Le`
(mine), each admitted through `add_inductive`; (3) my `Definition`s
`rado.{add,mul,pow,geo,geo1,shellT,nshell,dvd}`, which are definitions with
values, not assumptions. Everything else is a `Declaration::Theorem` whose proof
term the kernel re-checked.

### What is still NOT proved (so nobody reads more into this than is there)

- The shell colouring's **solution-freeness** — the actual conjecture. Not
  attempted; the colouring itself is not even formalised here.
- **Tightness** (`R_k = N+1`). Not attempted (and the brief records it fails at
  (3,2,5) anyway).
- The **necessity** half of the solution-form lemma (needs `gcd(a,b)=1` and
  Gauss's lemma). Explicitly not assumed.
- That the defect triple lies **in range** `[1,N]` and is **monochromatic** —
  the two facts that would turn `defect_identity` into a proof that the shell
  colouring is defective. Both need the colouring and an order.
