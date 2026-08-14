# Lane `facts-number` -- extraction diary, 2026-08-14

Task: extract genuine propositions from the `S:number` and `S:arithmetic-structure`
strands of the math-education concept graph and land them as `fact` resources.

Result: **20 facts** written, `python3 scripts/validate-facts.py` at 0 errors
(25 total in the ledger with the 5 pre-existing seeds).

| status        | count | note                                                     |
| ------------- | ----: | -------------------------------------------------------- |
| `proved`      |    14 | kernel term type-checks, `axiom_footprint: []` (measured) |
| `open`        |     3 | empty evidence, reachable from proved facts               |
| `conjectured` |     3 | empty evidence, genuinely open mathematics                |

---

## What I actually ran

Nothing in the `proved` rows is asserted from a doc comment or a struct field name.

1. **The formal statements were extracted from the kernel, not transcribed.**
   I built an out-of-tree probe crate (in scratch, `[workspace]`-isolated, path
   dependency on `crates/axeyum-lean-kernel`) that calls `build_nat_prelude` and
   dumps `display_name` + `render_lean(ty)` for every `Declaration::Theorem`. It
   produced **119 theorem rows**, and each `proved` fact's `formal.statement` is
   one of those rows verbatim. This matters: had I written the statements from
   the `NatPrelude` doc comments I would have got the sort name wrong -- the
   declarations are rooted at `Nat` but the inductive renders as `AxNat`.
2. **Type-checking**: `cargo test -p axeyum-lean-kernel --lib nat_prelude` ->
   **28 passed** (nonzero, per the CLAUDE.md rule about inert filters).
   `build_nat_prelude` admits everything through the trusted
   `Kernel::add_declaration` gate, which re-checks the proof term against the
   stated type, so a green run *is* the proof.
3. **Axiom footprint**: `cargo run -q -p axeyum-lean-kernel --example nat_axiom_inventory`
   -> `nat: axiom=0 opaque=0 quotient=0 total_trusted=0`. Re-run by this lane
   after the coordinator's correction, not taken on report.

### The near-miss on `axiom_footprint`, recorded because it nearly shipped

My brief cited `--example prelude_axiom_inventory` as the measurement showing
zero Nat axioms. That example **never builds the Nat prelude** -- it builds
`real`, `integer` and `string` only. Zero Nat rows in its output means "never
enumerated", which looks identical to "axiom-free".

I had independently corroborated `axioms=0` with my own probe before the
correction arrived, so the *number* was never in doubt. But my probe had the
second half of the same bug: it matched `Declaration::Axiom` only, and would
have reported `0` for an environment full of `Opaque` (no proof body) or
`Quotient` (admits `Quot.sound`, one of Lean's three axioms) declarations. Two
independent measurements, same blind spot, agreeing with each other. The
committed `nat_axiom_inventory` counts all three; that is the command in
`checker_command`.

I also wrote the soundness argument into every footprint evidence row rather
than leaving it implicit, because the enumeration is **per-environment, not
per-theorem**: it is valid as a footprint precisely because a theorem cannot
depend on a trusted declaration the environment does not contain, so an empty
trusted surface bounds every individual footprint by `[]`. A per-theorem
footprint tool does not exist yet (see complaints).

---

## What I extracted

`proved` (all `fragment: Nat`, all `axiom_footprint: []`):

| fact | kernel theorem | concept |
| --- | --- | --- |
| `F:nat-mul-comm` | `Nat.mul_comm` | `C:commutativity` |
| `F:nat-add-assoc` | `Nat.add_assoc` | `C:associativity` |
| `F:nat-mul-assoc` | `Nat.mul_assoc` | `C:associativity` |
| `F:nat-left-distrib` | `Nat.left_distrib` | `C:distributivity` |
| `F:nat-add-zero` | `Nat.add_zero` | `C:identity-element` |
| `F:nat-mul-one` | `Nat.mul_one` | `C:identity-element` |
| `F:nat-add-sub-cancel-left` | `Nat.add_sub_cancel_left` | `C:inverse-operation` |
| `F:nat-div-mod-exists` | `Nat.div_mod_exists` | `C:division-algorithm` |
| `F:nat-div-mod-unique` | `Nat.div_mod_unique` | `C:division-algorithm` |
| `F:nat-dvd-add` | `Nat.dvd_add` | `C:divisibility` |
| `F:nat-dvd-gcd-iff` | `Nat.dvd_gcd_iff` | `C:greatest-common-divisor` |
| `F:nat-gcd-bezout` | `Nat.gcd_bezout` | `C:bezout-identity` |
| `F:nat-gcd-succ` | `Nat.gcd_succ` | `C:euclidean-algorithm` |
| `F:nat-mod-eq-mul` | `Nat.mod_eq_mul` | `C:congruence` |

`open` -- correct statement, empty evidence, all dependencies proved:

- `F:nat-pow-add` (`C:index-laws`) -- `a^(m+n) = a^m * a^n`. Deliberately the
  nearest target in the batch: `AxNat.pow`, `Nat.pow_zero` and `Nat.pow_succ`
  already exist and both dependencies are proved, so it should fall to induction
  on `n` with no new definitions. Measured: no index law is among the 119.
- `F:nat-euclid-lemma` (`C:fundamental-theorem-of-arithmetic`) -- reachable from
  `F:nat-gcd-bezout` + `F:nat-dvd-gcd-iff`.
- `F:nat-exists-prime-gt` (`C:infinitude-of-primes`) -- `open` means *not
  established in this ledger*, not mathematically open; the fact says so and
  cites Euclid in `prior_art`. Live target: the prelude already carries
  `Nat.not_dvd_one_add_mul_of_two_le`, literally the closing contradiction of
  Euclid's argument.

`conjectured` -- empty evidence:

- `F:goldbach-strong`, `F:twin-prime-unbounded`, `F:collatz-reaches-one`.

Three of the four unproved-but-expressible statements are written in the
**kernel's own core rendering** using only symbols `build_nat_prelude` declares,
checked against the 119-row inventory, so the loop can dispatch them without
inventing vocabulary. Primality is spelled out inline (`2 <= p and every divisor
is 1 or p`) since the prelude has no `Prime`.

---

## What I skipped, and why

- **Most of both strands.** `S:number` has 152 concepts and
  `S:arithmetic-structure` 81; I extracted from ~25. The rest are topics,
  notations, procedures or contexts, not propositions: `C:abacus`,
  `C:roman-numeral`, `C:thousands-separator`, `C:obelus`, `C:solidus`,
  `C:radical-sign`, `C:subscript`, `C:superscript`, `C:place-value`,
  `C:scientific-notation-large`, `C:multi-digit-addition-algorithm` and its
  three siblings, `C:mental-math`, `C:automaticity`, `C:fact-fluency`,
  `C:math-anxiety`, `C:back-of-envelope`, `C:fermi-estimate`, `C:budget`,
  `C:credit-card-interest`, `C:queue-waiting-time`, `C:getting-dressed`, ... A
  large slice of `S:arithmetic-structure` in particular is *applied contexts*
  (money, timetables, energy bills), which are pedagogy, not mathematics.
- **`C:order-of-operations`, `C:bracket-convention`, `C:equals-sign`,
  `C:minus-sign`, `C:plus-sign`, `C:division-sign`** -- notational conventions.
  A convention has no truth value; there is nothing to state.
- **`C:fundamental-theorem-of-arithmetic` as itself.** The kernel has no list,
  multiset or finite-product vocabulary, so "n is a product of primes, unique up
  to order" is **not writable in its language at all**. I extracted Euclid's
  lemma instead, which is the mathematical content of the uniqueness half and
  *is* expressible, and said so in the fact's `notes`. This is the sharpest
  capability gap I found.
- **`C:fermats-last-theorem`.** Skipped on purpose -- see complaint 1. The
  schema cannot express "a theorem, proved in the literature, not by us". Every
  available status would have been a lie.
- **Real/rational concepts** (`C:signed-rational-addition` and siblings,
  `C:floating-point-number`, `C:golden-ratio-fibonacci`, `C:complex-number`).
  Skipped: an Int or Real fact needs a *named* footprint drawn from the 34/30
  trusted declarations, and no tool reports which of them a given statement
  rests on. I would have had to guess. Guessing an axiom footprint is exactly
  the failure this ledger exists to prevent, so I stayed inside the axiom-free
  Nat layer where `[]` is measurable. **This leaves both `Int` and `Real`
  unrepresented in the fact ledger** -- a real coverage hole, and the fix is a
  tool, not more diligence.
- **`C:sequence`, `C:series`, `C:fibonacci-recurrence`, `C:arithmetic-sequence`,
  `C:geometric-sequence`.** `Nat.sumRange` exists and `Nat.mul_sumRange_pow` is
  a checked geometric-sum reindexing, but stating the closed forms these
  concepts are about needs subtraction/division that truncate on `Nat`. Doable
  later; the statements would have been ugly enough to be unreviewable.

---

## Friction and errors, in the order I hit them

1. The `NatPrelude` doc comments say things like ``add_comm : forall (n m : Nat),
   Eq Nat (add n m) (add m n)``. The kernel actually renders
   ``((x0 : AxNat) -> ((x1 : AxNat) -> Eq.{1} AxNat (AxNat.add x0 x1) (AxNat.add x1 x0)))``.
   Both are true statements about the same theorem, but only one is the artifact.
   Copying the doc comment would have produced 14 plausible-looking facts whose
   `formal.statement` names a sort that does not exist.
2. `grep -oP '\.theorem\(\s*"\K...'` returns **zero** matches -- the brief warned
   that theorems are declared via a `.theorem(...)` helper, but the helper takes
   an already-interned `NameId` field (`p.add_comm`), not a string literal. There
   is no way to get the theorem inventory by grepping; you have to build the
   environment. Cost: one wasted search, then the probe crate.
3. **The three seed facts' `formal.statement` and `checker_command` disagree.**
   `F:nat-add-comm` states `theorem rado.add_comm : ... (rado.add x0 x1) ...` but
   cites `cargo test -p axeyum-lean-kernel --lib nat_prelude`. `rado.add_comm`
   is declared in `crates/axeyum-lean-kernel/tests/rado_shell_arithmetic.rs`,
   a separate shell prelude with its own namespace; the `--lib nat_prelude`
   filter does not compile that integration test, so the cited command does not
   check the cited statement. The *proposition* is proved -- `Nat.add_comm` is in
   the 119 -- so the status is right and the evidence row points at the wrong
   thing. I did not edit another lane's seeds; flagging instead. Nothing in the
   validator can catch this, and it is the exact class of defect the ledger
   exists to prevent, appearing in the ledger's own seed data.
   `F:nat-succ-add` and `F:nat-zero-add` additionally carry a mangled
   `formal.statement` -- ``theorem rado.zero_add :  Nat:Eq AxNat (rado.add
   AxNat.zero x0) x0`` has a stray ``Nat:`` where the binder telescope should be,
   so it would not parse in any dialect -- truncated prose
   (`"succ a + b = succ (a + b) for all a b "`), and `F:nat-zero-add` declares
   `free_symbols: ["x0","x1"]` for a statement with one binder. Cheap to fix,
   worth fixing before the seeds get copied as a template.
4. Scratch-space isolation worked but needed a `[workspace]` stanza in the probe
   `Cargo.toml`; without it cargo walks up and refuses. Worth knowing for anyone
   else who wants to interrogate a crate without mutating a shared checkout.

---

## Feedback for the roadmap

### Complaint 1: there is no status for "known, but not by us"

`epistemic_status` has `proved | computed | empirical | conjectured | open |
refuted | axiom`. Fermat's Last Theorem is none of them from this repo's
position. `proved` is barred by the validator (no checked evidence, correctly).
`conjectured` is false. `open` is false as mathematics and only defensible as
"open in this ledger" -- which is a *different predicate* wearing the same name.
I used `open` for `F:nat-exists-prime-gt` with an explicit disclaimer in `notes`,
which is a workaround, not a fix.

This is not cosmetic. The self-extension loop is specified to consume `open`
facts. If `open` silently means two things -- "nobody knows" and "we have not
imported it yet" -- the loop's queue is polluted with problems it cannot
possibly close, and the ledger's headline "N open facts" number stops meaning
anything. Suggested fix: either add `established-elsewhere` (with
`bound-citation` evidence and `check_status: not-checked` permitted), or split
the field into `truth_status` (what mathematics knows) and `ledger_status`
(what we have established). The second is the honest shape; the first is one
enum entry and a validator rule.

### Complaint 2: `axiom_footprint` is per-fact, but nothing measures per-fact

The field is documented as "the axioms the establishing evidence rests on".
For the Nat layer I can only honestly justify `[]` by an *environment-level*
argument (the trusted surface is empty, therefore every footprint is empty).
That argument is sound and I wrote it into the evidence rows -- but it does not
scale one step. The moment a fact lands over `Int` or `Real`, `[]` is
unavailable and the correct answer is a *subset* of 34 or 30 declarations, and
there is no tool that computes the transitive constant-dependency closure of a
proof term. `#print axioms` is Lean's answer to exactly this.

The concrete consequence is measurable in this batch: **zero Int facts and zero
Real facts**, not because the propositions are uninteresting but because I
refuse to guess a footprint. A `Kernel::axiom_footprint(name) -> Vec<Name>`
walking the constant graph of the proof term is maybe a day's work and would
unlock the entire integer and real strands to fact extraction. I would put it
ahead of more extraction.

### Complaint 3: `formal.language: lean4` conflates two languages

`lean4` covers both the kernel's core rendering
(``((x0 : AxNat) -> Eq.{1} AxNat ...)``) and Lean surface syntax
(``forall n : Nat, ... ^[k] n = 1``). These are not interchangeable: the first
is dispatchable at the kernel and is what an admitted proof renders as, the
second needs elaboration and may reference symbols no axeyum prelude declares.
A consumer cannot tell which it is holding without parsing. 19 of my 20 facts
are core rendering and one (`F:collatz-reaches-one`) is surface, and the only
way I could flag that was English prose in `notes`. Suggest either splitting the
enum (`lean4-core` / `lean4-surface`) or adding a `dialect` field.

### Smaller notes

- **`depends_on` is ambiguous.** Is it the mathematical prerequisite or the
  measured proof-term dependency? The seed `F:nat-add-comm` uses the former.
  I followed suit and said so in `notes`, but a `relation` discriminator, or
  simply a sentence in the schema description, would remove the guess. Note it
  is also the field the loop's build order comes from, so the two readings give
  different orders.
- **No place to record a bounded verification.** For Goldbach, "checked for all
  n below 4e18" is genuine evidence *about a different, weaker proposition*.
  Today that needs a second fact with no link back. A `refines`/`weakens` edge
  (the mirror of `supersedes`) would let the strong statement point at what has
  actually been checked.
- **`concept_refs[].relation` is a free string.** I emitted `instance-of`,
  `about`, `related` and `key-lemma-of` with nothing to check them against.
  Either enumerate them or drop the field; an unvalidated vocabulary drifts.
- **The validator passed my batch first try, which is worth stating plainly
  rather than as praise.** It never fired, because I generated the files from a
  script that encoded its rules. That means it validated nothing about my work
  that I had not already assumed. Its error messages are well written and its
  semantic rules are the right ones; what it cannot see -- a `checker_command`
  that does not check the cited statement (item 3 of the friction list, present
  in the ledger's own seed data), an `axiom_footprint` asserted rather than
  measured, a `formal.statement` in a dialect nothing can parse -- is where the
  next validator work belongs. A cheap first step: have it shell out to the
  `checker_command` of every `checked` evidence row in a slow CI lane, and fail
  when the command exits nonzero or reports zero tests.
