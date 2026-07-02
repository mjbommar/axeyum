# ADR-0052: The string `len`↔LIA link and the bounded-string `unsat` gate

Status: accepted
Date: 2026-07-01

## Context

P2.7 Phase A's exit criterion (Task A.2) is the **`str.len`-unsat gap**: the
bounded string front-end (ADR-0029) lowers `str.len` to `bv2nat(len_field)`, so a
string query's integer atoms cross into the `Int` theory while the packing
constraints stay in the BV theory. The two shared no propagation channel — the
exact integer refuters treat a raw `bv2nat` as opaque — so `(= s "ab") ∧
(= (str.len s) 3)` was `unknown` (the gap-analysis "Gap 10" marker,
`str_len_sat_direction_decides`).

Building the missing link surfaced something bigger. The bounded encoding
asserts `len(s) ≤ max_len` (`STRING_MAX_LEN = 8`) as a **well-formedness side
constraint** — an encoding artifact, not a user constraint. Any decision
procedure complete over the *lowered* query will therefore refute instances the
*real* (unbounded) string theory satisfies. Empirically confirmed **wrong-unsat
classes vs Z3 4.13.3**, all violating ADR-0029's own contract ("strings up to
`max_len` decide soundly; longer ones are `Unsupported`, never wrong"):

- **New (would have shipped with the naive A.2 link):** `(= (str.len s) 9)` —
  real theory `sat`; a complete BV+Int decision refutes it against the bound.
- **Pre-existing on HEAD, pure BV (no Int channel at all):**
  `(= s "abcde") ∧ (= t "fghij") ∧ (str.prefixof (str.++ s t) u)` — Z3 `sat`
  (`u` may be 10 chars; its encoding is capped at 8), axeyum answered `unsat`.
  The `str_differential_fuzz` never generated the class (length constants were
  capped at 5; literals at 3 chars).

So Task A.2 is really two coupled obligations: **(1)** the `len`↔LIA propagation
that closes Gap 10, and **(2)** a repair of the bounded-encoding verdict
contract so completeness gains can never surface bound-induced `unsat`s.

## Decision

Three cooperating pieces, all landed together:

### 1. `bv2nat`-linear blast (solver, `bv2nat_blast.rs`)

When **every** integer atom of a query is linear over `bv2nat` terms and
constants — no free `Int` symbols, `div`/`mod`, non-constant products, or
quantifiers — every integer value is provably bounded (`bv2nat(b) ∈ [0, 2^W−1]`),
so each atom rewrites to an **equivalent** pure-BV comparison at an
overflow-safe width (checked `u128` bounds; decline past 128 bits). Unlike the
bounded integer blast (ADR-0014, sat-only) this is an equivalence: the SAT path
decides **both** directions, `unsat` carries DRAT, `sat` a replayable model over
the unchanged symbols (still replay-guarded against the original assertions).
Dispatched in `check_auto` before the integer linear refuters, gated to
BV+Int-only feature sets.

### 2. The unbounded length abstraction (parser, `LenAbs` in `parse.rs`)

The parser is the only layer that still sees `str.*`/`seq.*` structure, so it
builds the abstraction as terms are lowered (threaded `&LenAbs`,
interior-mutable like `SeqInfo`):

- every string-valued term gets a shared **unbounded** `Int` length expression:
  `len(x ++ y) = len(x) + len(y)`, `len(literal) = |literal|`,
  `len(seq.unit e) = 1`, `len(seq.empty) = 0`, otherwise a fresh `≥ 0` variable;
- every hooked string atom `A` maps to `fresh_bool ∧ implied_fact(A)`
  (equality ⟹ equal lengths; `prefixof`/`suffixof` ⟹ `≤`; `contains` ⟹
  needle `≤` haystack) — a **relaxation faithful under any Boolean structure**
  (extend a real model by `B := value(A)`);
- every content bridge (`str.to_int`/`to_code`/`indexof`, `Int`-valued
  `seq.nth`) maps to a wholly-free integer;
- encoding bounds (`len(v) ≤ max_len`) are exported **separately** — they are
  true of the encoding only, never of the real theory.

Exported on `Script` as `len_abstraction_map` / `_facts` / `_bounds` +
`uses_bounded_strings`.

### 3. The bounded-string `unsat` gate (solver front door, `StringGate`)

Every script-solving entry point (`solve_smtlib`, incremental, `get-info`,
`unsat-core`) confirms an `unsat` on a bounded-string script:

1. **Confirm unbounded:** rewrite the active assertions through the abstraction
   map (+ facts, **no bounds**) and re-decide. This query has no encoding bound
   and relaxes the real semantics, so its `unsat` transfers — report `unsat`.
   *(This is the `len`↔LIA link itself: the abstraction is pure Bool+LIA, so the
   exact integer engines decide it — Gap 10 closes here for structural length
   conflicts, and via piece 1 for in-bound BV+Int interplay.)*
2. **Bound-bite detector:** the same length system **with** the encoding bounds
   being `unsat` (while step 1 could not refute unbounded) proves the recorded
   length facts force a length past the bound — the bounded `unsat` is an
   encoding artifact → honest `unknown`. This catches the pre-existing pure-BV
   class (the `prefixof` instance above). A downgrade is always sound.
3. **Content-driven check:** relax every `bv2nat`-crossing Boolean atom to a
   fresh Boolean; still-`unsat` means the bound-suspect integer channel was not
   needed — the pre-A.2 verdict surface — report `unsat`. Otherwise `unknown`.

Three guard refinements keep the gate itself sound:

- **Every symbolic string atom enters the map** — including fact-less ones
  (`str.<`/`str.<=` → a bare fresh Boolean; `str.in_re` even when the interval
  is trivial; the `distinct` arm's pairwise equalities). An atom kept verbatim
  would smuggle its *bounded* lowering into the "unbounded" abstraction and let
  step 1 wrongly confirm a bound-induced `unsat` (e.g. `"aaaaaaaa" < s <
  "aaaaaaab"` — real-`sat` only with `len(s) ≥ 9` — is packed-unsat).
- **Coarse-atom guard:** a symbolic `str.<`/`str.<=`/`str.in_re` atom carries
  no (or only interval-coarse) length facts, so the bite detector can miss its
  bound bite (the lexicographic gap above; a regex union gap like `ab | a⁹`).
  With such an atom present, **only a step-1-confirmed `unsat` passes**;
  steps 1.5/2 are skipped in favour of an honest `unknown`. Ground atoms (both
  operands literal, or constant-folded) are exact at every bound and are
  exempt — no decide-rate loss on the ground fragment.
- **Quantifier guard:** the map replaces atoms, and an atom under a quantifier
  may depend on the bound variable — one fresh Boolean cannot represent it per
  instantiation — so steps 1/1.5 are skipped when a quantifier is present
  (step 2 replaces quantified subformulas wholesale, which stays sound).

**Known theoretical residual (pending Phase B):** for the fact-carrying
fragment (equality/concat/prefixof/suffixof/contains + length atoms) the
`unsat` pass-through of steps 1.5/2 assumes a small-model property — that a
real model with bound-fitting *lengths* can be packed. Word-equation systems
that force long solutions do so through the concat length homomorphism (which
the bite detector sees), so no violating instance is known; the word-level
solver (Phase B) replaces this argument with a decision procedure. This is
exactly the residual ADR-0029 should have declared `Unsupported`.

## Consequences

- The Gap 10 marker decides: `(= s "ab") ∧ (= (str.len s) 3)` is `unsat`
  (confirmed by the abstraction), and `(= (str.len s) 9)` / `(> (str.len s) 8)`
  are honest `unknown` (real theory `sat`; bounded encoder cannot witness).
- The known wrong-unsat surface **shrank**: the length-visible bound-bite class
  (length atoms, cross-width comparisons whose facts are recorded) now
  downgrades. The **residual** class — atoms with no length facts yet (`str.in_re`
  with a long-forcing regex, `contains` content interplay, `substr`-family) —
  keeps the pre-A.2 surface and is tracked as the ADR-0029 contract-repair
  follow-up (P2.7 task list): the fix is richer per-atom length implications
  (regex Parikh min/max intervals) so step 1/2 confirm-or-downgrade covers them,
  plus width widening to recover the `sat` side.
- `str_differential_fuzz` now draws length constants past the bound (0..=11), so
  the class stays probed; DISAGREE=0 must hold (over-bound cases are axeyum
  `unknown` = SKIP vs Z3 `sat`).
- Cost: up to two extra solves, only on the (`unsat` ∧ bounded-strings) path.
- **Representation-fork resolution (ADR-0051 ↔ ADR-0029):** the bounded packed-BV
  encoder remains the default decision path for `(Seq E)`/`String` syntax, now
  behind this gate; the first-class `Sort::Seq` (ADR-0051) is the *unbounded*
  representation grown behind it (Phase B word-level solver). `parse_sort` is
  not re-routed until the word-level solver can decide what the bounded
  pre-check declines; the gate's `unknown`s delimit exactly the instances that
  route there. This closes the A.2 half of the fork question; the routing
  predicate ADR comes with Phase B.

## Alternatives rejected

- **Ship the blast without the gate** — measurably wrong (`len(s) = 9` → wrong
  `unsat` vs Z3). A complete engine over an under-approximating encoding is
  unsound at the front door, full stop.
- **Blanket-downgrade every bounded-string `unsat`** — throws away the large
  correct-unsat surface (content conflicts, ground refutations); the fuzz's
  unsat instances would collapse to `unknown`. The three-step confirm keeps
  them.
- **Build the abstraction in the solver by pattern-matching packed widths** —
  width heuristics misidentify genuine user bit-vectors; only the parser knows
  what is a string. (The `=`-hook does fire on width-shaped pairs, but its
  facts are sound for arbitrary BVs — equal BVs have equal decoded fields — and
  it never activates the gate.)

## Follow-up (2026-07-02): three residual recoveries

Measured against the committed `cvc5-regress-clean` baselines, 21 declared-`unsat`
instances downgraded to honest `unknown` at the gate. Three sound, bound-independent
recoveries were landed (5 of the 21 files: `str004`, `str005`, `re-comp/comp-all`,
`re-in-rewrite` ×2). Each is a strengthening of the abstraction or the gate that
adds confirmations without touching the pass-through invariant ("`unsat`
pass-through requires step-1 confirmation **or** (non-coarse ∧ no-bite ∧
content-only-`unsat`)"):

1. **Step-1a LIA projection (`StringGate`).** The bounded encoder emits
   per-string-variable well-formedness constraints (padding above the length field
   is zero) as pure `BitVec` assertions. Carried into the length abstraction they
   mix with the `Int` length facts, and the exact refuters decline the mixed
   `BitVec`+unbounded-`Int` combination (the free `BitVec` forces the sat-only
   bounded-integer path → `unknown` instead of the true `unsat`, e.g.
   `xx = xx ++ yy ∧ len(yy) > len(xx)`). When the **full** abstraction solve is
   `unknown`, the gate now retries a **projection** that drops every abstracted
   assertion carrying no `Int` subterm. Dropping constraints is a **sound
   weakening** (fewer constraints ⇒ *more* models), so an `unsat` of the subset
   still implies the full abstraction — hence the real theory — is `unsat`. The
   kept subset is pure `Bool`+`LIA`, which the length refuters decide. Only tried
   on an `unknown` full solve (a `sat` full abstraction can never yield an `unsat`
   subset).

2. **Empty-string exact equality (`LenAbs`).** `s = "" ⟺ len(s) = 0` — the empty
   string is the *unique* length-zero string — so an equality against `""` maps to
   the **exact** predicate `len(other) = 0` (no fresh Boolean), via
   `note_atom_exact`. Unlike the general `fresh_bool ∧ (len = 0)` relaxation (which
   `len(s) = 0 ∧ s ≠ ""` satisfies by picking the Boolean false), the exact form
   is truth-equivalent to the atom in every real model, so it is faithful under any
   Boolean structure and lets step 1 refute the conflict. (Only length 0 is
   length-determined; every longer length has multiple strings, so no other
   equality is strengthened.)

3. **Empty-language regex fold (`regex.rs`).** When no accepting state is reachable
   from the start through *any* path (unbounded graph reachability), `L(R) = ∅`, so
   `str.in_re s R` is `false` for a string of **any** length — `encode_in_re`
   returns the constant `false`. This is exact (not merely bounded-`false` like the
   structural `encode_match` term), and a `BoolConst` atom is a non-coarse ground
   atom, so a genuinely-empty regex (`re.comp re.all`, an `re.inter` of disjoint
   languages) no longer sets the coarse flag and no longer blocks the gate's
   content-`unsat` pass-through. **Soundness rests on *unbounded* reachability**: a
   non-empty regex whose shortest word merely exceeds the encoding bound still has a
   reachable accepting state, so it is *not* folded (it keeps its bounded encoding
   and downgrades honestly — the real theory is `sat`).

**Still `unknown` (Phase B / A.3, not length facts):** the remaining 16 files are
regex-*content* refutations (language inclusion/intersection emptiness across
*separate* `in_re` atoms — `re-include-union`, `regexp-strat-fix`, `re-agg-total1`,
`re-mod-eq`, `norn-31`, `re-neg-unfold-rev-a`, `username_checker_min`,
`a-in-comp-a`, `re.all`) and lexicographic (`str.<=`) reasoning
(`leq`, `strings-leq-trans-unsat`). These need the word-level / regex decision
procedure (a sound length fact cannot confirm them, and relaxing `in_re`/`str.<=`
coarseness is unsound — a fixed-prefix regex intersected with a fixed-suffix regex
can force a word longer than the bound with a contiguous length interval that the
bite detector cannot see). `unsat__update__distinct-elems` (seq `update` with
distinct values under a bound-safe `len = 1`) is content-driven but relaxed away by
step 2's blanket `bv2nat` relaxation; recovering it needs bound-safe-length-atom
handling in step 2 and is deferred with the rest.

## Revisited when

- P2.7 Phase B lands the word-level solver (the gate's `unknown`s become its
  routing signal; the fork ADR's routing predicate is written then).
- The residual fact-less bound-bite class is closed (regex Parikh intervals,
  `substr`-family length implications) — then ADR-0029's contract holds in full.
- The regex-content residual (inclusion/intersection emptiness across separate
  `in_re` atoms) is closed by a regex-automata decision (Phase A.3 / Phase B).
