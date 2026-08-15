# Diary — the geometry frontier (lane `geometry-frontier`), 2026-08-15

Three lanes met here. `geometry` built the corpus and named the pure lexicographic
monomial order as the structural suspect behind its two frontier theorems.
`mvpoly-bignum` added `MonomialOrder::DegRevLex`, measured it, found it reaches
`rhombus-diagonals-perpendicular` — and then deliberately *did not* switch the
default, because switching it could silently change what six proved facts claim.
This lane took that decision, with the evidence it needs.

Result: the default is `grevlex`, no fact's claim moved, the rhombus is the
seventh certified theorem, and `euler-line` is still on the frontier — but it is
no longer described by a stopwatch.

---

## 1. The decision, and the evidence that made it safe

The handover was precise about the danger, so it is worth restating exactly.
`certify` returns the certificate for the **smallest condition subset that
succeeds**, and "succeeds" is budget-relative: a subset whose reduction *declines*
is skipped rather than decided. A faster monomial order can therefore decide a
subset that used to decline, and the certificate lands on a **smaller** condition
set. Those conditions are hypotheses in each fact's `formal.statement`. So a
regenerated certificate can quietly redefine the theorem, and "the artifacts are
just re-rendered" would be a false description of the change.

`cargo run -p axeyum-cas --release --example geometry_order_audit` is the
measurement. It runs **every** condition subset of every corpus theorem under
both orders, prints the verdict for each, and then runs the full `certify` under
both and compares the condition set *and the serialized certificate byte for
byte*.

| theorem | subset | `lex` | `grevlex` |
|---|---|---|---|
| `varignon-midpoint-parallelogram` | `{}` | in ideal, 1.9 µs | in ideal, 0.2 µs |
| `thales-right-angle-in-semicircle` | `{}` | in ideal, 34.2 µs | in ideal, 24.0 µs |
| `orthocentre-altitudes-concurrent` | `{}` | in ideal, 5.9 ms | in ideal, 4.8 ms |
| `medians-concurrent` | `{}` | in ideal, 37.8 ms | in ideal, 15.5 ms |
| `centroid-divides-medians` | `{}` | **not in ideal**, 38.0 ms | **not in ideal**, 16.0 ms |
| `centroid-divides-medians` | `{abc-not-collinear}` | in ideal, 90.3 ms | in ideal, 46.5 ms |
| `parallelogram-diagonals-bisect` | `{}` | **not in ideal**, 5.2 ms | **not in ideal**, 4.2 ms |
| `parallelogram-diagonals-bisect` | `{abd-not-collinear}` | in ideal, 89.4 ms | in ideal, 72.3 ms |

**Six condition sets unchanged, zero moved, six certificates byte-identical.**
The emitter agrees independently: after the switch it reported *6 unchanged, 1
written* — the one being the rhombus. Not a single byte of the existing evidence
changed.

The audit was run **before** the rhombus joined the corpus, which is the right
order: the question it answers is whether the switch disturbs the facts that
already exist. Re-run afterwards it reports a seventh row, and that row is why
the tool now distinguishes three outcomes rather than two — see §2.

### The audit proved something stronger than "nothing moved"

The column that matters is not the timing, it is that **every subset is decided**.
Across all six, under *both* orders, not one declines. Ideal membership does not
depend on the monomial order — only whether a verdict is reached inside the
ceilings does — so once every subset of a theorem's conditions has been *decided*,
the reported condition set is smallest **absolutely**. No larger budget, no faster
order, and no better algorithm can shrink it.

That upgrades a claim the `geometry` lane was careful to scope. Its diary says the
minimality is "smallest by cardinality **among the subsets the budget decided**".
For these six theorems the qualifier is now discharged, and it is discharged by a
measurement rather than by the switch. Had any subset declined, the honest move
would have been to leave the default alone until it did not.

The property is per-order, and the rhombus in §2 is the case that shows why it has
to be: its saturated subset is decided under `grevlex` and **declines** under
`lex`. Minimality there is absolute on the strength of the `grevlex` run, which is
the run that produced the certificate — and the audit reports the two columns
separately rather than conjoining them, so that distinction cannot be lost.

The two conditions in the corpus are therefore not conservative padding: for
`centroid-divides-medians` and `parallelogram-diagonals-bisect` the empty subset
is decided **not in ideal**, so those theorems are genuinely conditional. And the
dangerous direction — claiming no condition is needed when one is — still cannot
arise, because it would require the empty-subset reduction to produce an identity
that the independent checker then re-derives.

### Scope of the switch

Only `geometry_limits()`. `Limits::fast()` and the solver's `ideal_limits()` still
say `Lex`, and this lane did not change them: they gate a latency-sensitive
dispatch path with its own corpus, and the same argument that made this switch
safe here — audit first, then flip — has not been run there. `grevlex` is very
likely right for them too (ideal membership needs no elimination anywhere), and it
is a measurement someone should make rather than inherit.

**No ADR, deliberately, and this is the reasoning rather than an omission.** The
reusable rule here — *a certificate's condition set is minimal absolutely iff
every subset was decided, so a search-parameter change is safe iff the audit shows
that* — is ADR-shaped. It is written into `geometry_limits()`'s doc comment
instead, for two reasons. The narrow one: the ADR index is generated by globbing
the filesystem, and while this lane worked, `docs/research/09-decisions/README.md`
was dirty with another lane's uncommitted row for an ADR that is not in the tree.
Regenerating would have swept it into this commit — the exact clobbering pattern
the repository has now recorded five times. The broader one: the order is a *cost*
knob whose order-independence is a unit test
(`the_monomial_order_changes_the_basis_but_not_the_verdict`), and the evidence it
touched is byte-identical, so nothing about the route's semantics moved. If a
future reader disagrees, the ADR to write is about the minimality rule, not about
`grevlex`.

---

## 2. The rhombus, promoted

`rhombus-diagonals-perpendicular` differs from `parallelogram-diagonals-bisect` by
exactly one hypothesis — the quadratic `|AB| = |BC|` — and by that one generator:

| | `lex` | `grevlex` |
|---|---|---|
| `{}` | 5.1 s, not in ideal | **0.9 s, not in ideal** |
| `{abd-not-collinear}` | **declined**, `ReductionSteps`, 301.8 s | **in ideal, 25.0 s**, 34 cofactor terms |

(This lane's own numbers, from `geometry_order_audit` on a loaded box; the
`mvpoly-bignum` lane measured 287.8 s and 23.6 s for the same two cells on an
idle one. Treat them as the same measurement.)

Both subsets are decided under `grevlex`, so the condition set is absolutely
minimal here too, on the same argument as §1. Under `lex` they are **not** — the
saturated subset declines — which is precisely the asymmetry the audit had to be
taught to report. Its verdict for this row is `REACH ONLY`, not `MOVED`: one
order certifies and the other does not, so the failing order's condition set is
*unknown* rather than different, and there is nothing to compare. Collapsing the
two would have raised an alarm about a change of claim where there is only a
change of reach.

The certificate is 8.7 kB, four generators, one conclusion, 34 cofactor terms —
still small enough to read, and in the signature Rabinowitsch shape: the cofactor
of the saturation generator is **exactly minus the conclusion**, verified
term-for-term from the committed file.

**Non-degeneracy, treated in full.** The counterexample is
`A = (0,0)`, `B = (1,0)`, `C = (2,0)`, `D = (5,0)`: four collinear points, so both
parallelism hypotheses hold vacuously, and `|AB| = |BC| = 1` holds honestly, while
`AC·BD = (2,0)·(4,0) = 8`. The theorem is false there, and the checker replays it
from the artifact.

Both controls the brief demanded are in place, and one of them had to be built
rather than inherited:

- **Deleting the counterexample rejects.** This control existed, but it ran
  against `first()` — the alphabetically first saturated certificate — so a newly
  promoted theorem would have inherited the *claim* that its counterexample is
  load-bearing without inheriting the test. Every saturation control now iterates
  over **every** saturated certificate, and asserts there are at least two of
  them, so the next promotion cannot quietly skip them either.
- **A configuration that violates the condition but does not break the theorem
  also rejects.** The pre-existing version of this substituted a *generic*
  configuration, which fails on two counts at once — it satisfies the conclusion
  *and* it does not annihilate the condition — so a checker that only tested the
  second would have passed it. The sharper control is now explicit:
  `A = (0,0)`, `B = (1,0)`, `C = (2,0)`, `D = (1,0)` is four collinear points, so
  `abd-not-collinear` genuinely fails, and yet the parallelogram's diagonals share
  the midpoint `(1,0)` and the rhombus's satisfy `AC·BD = (2,0)·(0,0) = 0`. The
  test asserts *both* halves of that description before tampering, so it cannot
  degrade into the weaker control by accident.

Sitting on the degeneracy locus is not enough. A counterexample has to falsify
something, and that is now checked as a property of the configuration, not
assumed from its name.

One scope note, because it is the kind of thing that gets quietly implied. Both
controls above run at the **checker**, against the committed artifact, and they
run against the rhombus. The matching control at the **certifier** — `certify`
returning `GeometryDecline::UnverifiedWitness` rather than emitting a certificate
whose negative control is decorative — is exercised on a cheap parallelogram
fixture, not on the rhombus, because the rhombus would have to complete its 25 s
reduction before reaching the refusal and that is not a unit test. It is the same
`verify_witnesses` code path either way, and the artifact the rhombus actually
ships is covered directly.

**The transcription was checked independently of the fact.** The SMT-LIB
`formal.statement` was cross-evaluated against the certificate's own polynomials
at 300 random rational configurations, 1500 comparisons, zero mismatches — because
a fact whose formal statement drifts from the artifact it cites is exactly the
failure this ledger exists to prevent, and prose review does not catch a
transposed sign.

`F:geometry-rhombus-diagonals-perpendicular`, `proof_route: cas-certificate`,
`validate-facts.py` 83 facts / 0 errors.

**Headroom, so the corpus is not one machine away from breaking.** The completed
reduction uses 253 S-pairs of 2 000, a 23-element basis of 200, a widest
intermediate polynomial of 1 678 monomials of 8 000, and 15 788 reduction steps of
50 000 — a factor of 3 to 9 on every axis.

---

## 3. `euler-line`: what actually obstructs it

Two lanes recorded this as "no verdict within 600 s" and "no verdict within
1200 s under either order". Both are true and neither says anything. A duration
names no obstruction — it is the same sentence you would write for an overflow, a
combinatorial explosion, or an infinite loop.

So `examples/geometry_obstruction.rs` runs the reduction under a **ladder** of
S-pair ceilings with every other ceiling set out of the way, and reports what the
computation was doing at each rung. The counters come from a new
`ReductionStats`, recorded on the success path too, so a theorem that finishes can
be used as a control against one that does not.

`euler-line`, `grevlex`, full condition set:

| S-pairs processed | still queued | reduced to zero | coprime leads | basis | widest polynomial |
|---|---|---|---|---|---|
| 9 | 66 | 2 | 2 | 12 | 41 |
| 17 | 120 | 6 | 4 | 16 | 278 |
| 33 | 210 | 17 | 12 | 21 | 278 |
| 65 | 528 | 37 | 18 | **33** | 477 |

`rhombus-diagonals-perpendicular`, same order, same conditions — the control,
because it **finishes**:

| S-pairs processed | still queued | reduced to zero | coprime leads | basis | widest polynomial |
|---|---|---|---|---|---|
| 9 | 36 | 4 | 4 | 9 | 71 |
| 17 | 105 | 6 | 7 | 15 | 71 |
| 33 | 171 | 18 | 14 | 19 | 273 |
| 65 | 253 | 46 | 27 | **23** | 733 |
| 129 | 253 | 110 | 55 | **23** | 733 |
| **253** | **253** | 234 | 117 | **23** | 1678 |

Read the two together and the obstruction is legible.

**It is not width.** At 65 pairs the rhombus — which finishes — is carrying a
**733**-monomial polynomial against `euler-line`'s **477**, and ends up at 1 678.
`euler-line` is not computing with bigger objects. Nor is it an arithmetic
failure: the rhombus decline under `lex` was `ReductionSteps`, never `Overflow`,
which the `mvpoly-bignum` lane established, and nothing here has reported an
overflow at all. Widening `MvPoly` past `i128` would not move this theorem.

**It is basis growth, and the quadratic backlog it creates.** The rhombus's basis
**saturates at 23 by pair 65** and does not grow again; the queue stops being
refilled and drains at pair 253, where the run completes. `euler-line`'s basis is
at 33 by pair 65 and is still climbing roughly one element per two pairs. Each new
basis element queues one pair against every existing one, so the backlog is
quadratic in a basis that has not stopped growing: 65 pairs processed leaves
**528** outstanding, and the ratio is getting worse, not better. The closure is not
near, and no rung of this ladder is going to reach it.

Changing the order does not change the shape, which is why `grevlex` moved the
rhombus and does not dent this. Under `lex` the same rung has 1 081 pairs queued,
a 47-element basis and a 2 522-monomial polynomial: four times worse on every
axis, same divergence. The `lex` run reached one rung further, and it is the
clearest single row in this whole investigation:

| S-pairs | queued | basis | widest | elapsed |
|---|---|---|---|---|
| 65 | 1 081 | 47 | 2 522 | 65.0 s |
| 129 | **3 403** | **83** | 5 856 | **635.4 s** |

Doubling the pairs processed **tripled the backlog**, added 36 basis elements,
and cost **ten times** the wall clock. The basis is growing at better than one
element per two pairs with no sign of slowing, so the queue it feeds is growing
faster than any ladder can walk. This is divergence, not slowness.

The rungs that did **not** land say the same thing from the other side, and they
are worth recording as lower bounds rather than discarded as incomplete. On an
otherwise idle 16-core host, killed after 27 minutes:

| run | last completed rung | next rung |
|---|---|---|
| `grevlex`, all conditions | 65 pairs in 15.8 s | 129: **> 27 min**, killed |
| `grevlex`, no conditions | 33 pairs in 3.0 s | 65: **> 27 min**, killed |

A rung that costs a hundred times its predecessor is not a budget away from
finishing. Note also that `grevlex`, the order that is four times *faster* than
`lex` at every rung up to 65, did not reach 129 in more than twice the 635 s
`lex` needed for it — the two orders do not even rank consistently once the basis
is this large, which is another way of saying the cost is not a property of the
order.

Memory, for completeness, is a non-issue: peak RSS across these runs is 117 MB
against a 6 GB cap. Nothing here is short of space; it is short of a smaller
basis.

### What would actually help, and how much — measured, not guessed

This `Buchberger` loop applies **no criteria**. Not the coprime-leading-term
(product) criterion, not the chain criterion. It processes every pair the queue
ever receives, including pairs that are known in advance to reduce to zero. The
`reduced to zero` column is the bill: on the completed rhombus run, **234 of 253
pairs (92%) reduced to zero** and taught the basis nothing.

So the missing lever is identified — and the counters also say it is **not
sufficient on its own**, which is the more useful half of the finding. The
`coprime leads` column counts exactly the pairs Buchberger's first criterion would
skip: 117 of 253 on the rhombus (46%), 18 of 65 on `euler-line` (28%). Removing
those is a constant factor of well under two on the theorem that needs it. The
chain criterion reaches more of the remaining wasted pairs, but the quantity that
has to change is the **basis size**, because the pair count is quadratic in it,
and no pair-skipping criterion makes the Gröbner basis smaller.

Stated plainly, so the next lane does not spend a session on the wrong thing:
implementing Buchberger's criteria is worth doing — it is a real speedup for the
whole crate, and a 92% waste rate is an embarrassment to leave measured and
unaddressed — but it will not by itself certify `euler-line`. The candidates that
change the exponent rather than the constant are a different algorithm (F4/F5
style linear algebra over the S-pair matrix), or exploiting the structure this
particular system has: all four hypotheses are **linear in the four unknowns**
`ox, oy, hx, hy`, with coefficients in `ℚ[ax..cy]`, so the natural derivation is
Cramer's rule over that coefficient ring, and Buchberger is being asked to
rediscover it by monomial reduction.

### What was not done, and why

**Frame normalisation is still refused.** Placing `A` at the origin and `B` on the
x-axis removes three coordinates and would very likely bring Euler's line into
range. The `geometry` lane declined it because the invariance it assumes is an
assumption *about the degenerate case* — the rigid motion taking a generic
`(A,B)` to `((0,0),(u,0))` does not exist when `A = B` — and trading a
soundness-relevant hypothesis for a speedup is the wrong trade in the one domain
whose characteristic failure is a hidden hypothesis. That judgement is correct and
this lane did not revisit it. Everything in the corpus remains in fully generic
coordinates: every point two free indeterminates, no WLOG anywhere.

**Simson (16 coordinates) and Pappus (18) were not attempted.** The gate on them
was `euler-line` at 10, and `euler-line` did not land. Attempting a 16-coordinate
system on a route whose 10-coordinate case diverges would produce a longer
timeout, not information.

**`euler-line` stays in `frontier()`, unproved rather than unchecked — and this
lane strengthened the second half.** Its two committed witnesses were still
replayed by `every_frontier_witness_is_consistent`, but *one* generic
configuration is a thin reading of "checked" for a theorem nothing else confirms.
So the corpus now also constructs the circumcentre and the orthocentre **exactly**
— Cramer's rule over the rationals — for a sweep of eight triangles (obtuse,
right, isosceles, generic), and asserts on each that the stated hypotheses vanish,
the stated non-degeneracy condition does not, and the stated conclusion holds.

That is not a proof; it is finitely many configurations, which is exactly why the
certifier exists. What it rules out is the specific way a frontier entry rots: a
mis-transcribed predicate sitting unnoticed because no search ever got far enough
to reject it.

The construction doubles as the evidence for §3's diagnosis — both systems are
linear in the unknown centre, and in both the determinant is (twice) the
collinearity polynomial named as the non-degeneracy condition.

And it carries its own control, which is the part that had to be *fixed* rather
than written. The first attempt perturbed the circumcentre by one unit in `x` and
required the conclusion to break; it **failed on the very first triangle**,
because `A=(0,0), B=(4,0), C=(1,3)` has `O=(2,1)`, `G=(5/3,1)`, `H=(1,1)` — a
*horizontal* Euler line, so a step along `x` slides `O` along the line and the
three points stay collinear. That is not a weakness of the control; it is the
theorem, caught by the control. The fix is to try both axes and require one to
break, which is always a real demand because a line cannot be both horizontal and
vertical. Without some such control the entire sweep would pass just as happily
against the zero polynomial.

A theorem we cannot prove must still be one whose statement survives its own
witnesses, and that distinction is the most valuable property this corpus has. It
was not blurred to show progress — it was made harder to satisfy.

---

## 4. The corpus now

| theorem | conditions | reduction (`grevlex`) |
|---|---|---|
| `varignon-midpoint-parallelogram` | — | 13 µs |
| `thales-right-angle-in-semicircle` | — | 56 µs |
| `orthocentre-altitudes-concurrent` | — | 5.6 ms |
| `medians-concurrent` | — | 18 ms |
| `centroid-divides-medians` | `abc-not-collinear` | 71 ms |
| `parallelogram-diagonals-bisect` | `abd-not-collinear` | 86 ms |
| **`rhombus-diagonals-perpendicular`** | `abd-not-collinear` | **21–26 s** |

Four of seven need no side condition at all, and the rule the `geometry` lane
found still holds with the rhombus added: a condition is needed exactly when the
theorem *locates* something. The rhombus does not locate a point, but its
conclusion is a *metric* relation between two constructed segments, and the flat
configuration satisfies every hypothesis while failing it — which is the same
failure mode as the parallelogram it extends, and it inherits the same condition.

`frontier()` holds one theorem: `euler-line`.

## Files

| path | what |
|---|---|
| `crates/axeyum-cas/src/geometry_certify.rs` | `geometry_limits()` now `DegRevLex`, with the audit written into the doc comment |
| `crates/axeyum-cas/src/geometry_corpus.rs` | rhombus promoted to `corpus()`; `frontier()` carries the `euler-line` measurement |
| `crates/axeyum-cas/src/groebner_cert.rs` | `ReductionStats` and `reduce_many_with_cofactors_traced` |
| `crates/axeyum-cas/examples/geometry_order_audit.rs` | the per-subset, per-order condition-set audit |
| `crates/axeyum-cas/examples/geometry_obstruction.rs` | the S-pair ladder that says what a non-returning reduction is doing |
| `crates/axeyum-cas/tests/geometry_certificate_artifacts.rs` | saturation controls over **every** saturated certificate, plus the on-locus-but-harmless counterexample control |
| `artifacts/geometry-certificates/rhombus-diagonals-perpendicular.json` | the seventh certificate |
| `artifacts/facts/F-geometry-rhombus-diagonals-perpendicular.json` | the seventh fact |

## The ranked next steps

1. **Buchberger's criteria in `groebner_cert.rs`** — the product criterion first
   (four lines, 28–46% of pairs by measurement), then the chain criterion. Worth
   it for the whole crate; will **not** by itself reach `euler-line`, and the
   counters above are there so nobody has to rediscover that.
2. **Audit and switch `Limits::fast()` / the solver's `ideal_limits()`** the same
   way this lane switched `geometry_limits()`: measure first, flip second.
3. **`euler-line` needs an algorithm, not a knob.** Either F4-style linear algebra
   over the S-pair matrix, or exploiting that its hypotheses are linear in the
   four unknown coordinates over `ℚ[ax..cy]`.
4. **Simson (16 coordinates) and Pappus (18)** remain gated on 3.
5. **A surface syntax for the corpus** — still open, twice recommended now.
