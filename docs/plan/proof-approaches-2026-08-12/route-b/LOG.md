# Route B lab notebook — append-only

Machine: 4 cores (`nproc` = 4), three agents sharing it. **All wall times in
this log are upper bounds on the true single-tenant cost**; the box was
contended for the whole session (`uptime` load average 1.74 at 19:07).

Convention: entries are appended with a `date -Is` stamp. Corrections are
appended as new entries, never edited into old ones.

---

## 2026-08-12T19:07:10-04:00 — notebook opened (retroactive preamble)

The notebook requirement arrived while the B1 build was running. Everything
below this heading up to the next `date -Is` stamp is a retroactive record of
work already done in this session, flagged as such. Everything after is
recorded live.

### Retroactive: what was done before the notebook existed (18:58–19:07)

**Step 1 — locate the precedent.** The brief claims the solution-form lemma
was discharged unbounded over ℤ. Searched the repo:

```sh
grep -rn "solution.form\|solution_form\|solution-form" --include=*.rs \
  --include=*.py --include=*.md --include=*.smt2 --include=*.txt .
```

One hit only:

```
docs/plan/claim-ledger-and-rado-frontier-2026-08-12.md:260:   solution-form lemma is separately machine-proved, bounded and unbounded
```

So the artefact is not in the repo. Found it in the session scratchpad at
`scratchpad/multilayer/` — a standalone cargo crate depending on the axeyum
crates by path. The relevant binary is
`multilayer/src/bin/layer2_lia.rs`, mode `param`, section "2b. The
parameterisation lemma".

**Step 2 — read what was actually posed.** `layer2_lia.rs:150`
`fn parameterisation(a, b, n, bounded)`. Confirmed by reading the source that
when `bounded == false` the function pushes **no** `in_range` constraints — the
three variables are plain `ar.int_var("x"/"y"/"z")` of `Sort::Int`, and the only
assertions are the equation and the negated claim. So the *encoding* is
genuinely unbounded. Whether the *solver* treats it as unbounded is a separate
question and is the whole point of B1; see below.

**Step 3 — reproduce.** Ran the already-built binary:

```sh
cd .../scratchpad/multilayer && time ./target/release/layer2_lia param
```

Output (verbatim, tail):

```
2b. PARAMETERISATION LEMMA  (x-y = b't, z = a't)
  a=1 b=1 (a'=1 b'=1) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=2 b=3 (a'=2 b'=3) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=3 b=2 (a'=3 b'=2) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=4 b=3 (a'=4 b'=3) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=6 b=4 (a'=3 b'=2) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=6 b=9 (a'=2 b'=3) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  -- unbounded (all of Z), expected to be harder --
  a=1 b=1 (a'=1 b'=1) over Z^3 (unbounded): a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=2 b=3 (a'=2 b'=3) over Z^3 (unbounded): a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=6 b=4 (a'=3 b'=2) over Z^3 (unbounded): a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)

real	0m0.023s
```

Reproduces exactly. **23 milliseconds for all 18 queries.**

### SUSPICION LOGGED AT 19:07, BEFORE ANY FURTHER MEASUREMENT

Two things smell wrong and I am recording them now so the record shows the
suspicion preceded the check:

1. **The unbounded queries are not slower than the bounded ones.** Both print
   `0.00s`. The source's own banner says "expected to be harder". A genuine
   ℤ-refutation of a divisibility fact is cheap if done by a gcd/congruence
   argument, so this is *consistent* with a real proof — but it is equally
   consistent with a route that decides the query by some shortcut that has
   nothing to do with ℤ.
2. **The precedent has NO unbounded false-variant control.** Reading
   `fn parameterisation_control` (`layer2_lia.rs:288`), every control is run at
   `n = 30`, i.e. **bounded**. `main` calls `parameterisation_control(a, b, 30)`
   only. So the claim "unsat unbounded over ℤ" rests on a gate that was never
   shown to be capable of returning `sat` in the unbounded configuration. Per
   this repo's own rule (a gate that never fires proves nothing), the unbounded
   result as it stands is **not yet evidence**. This is the single most
   important gap for B1 and it is what my `b1_audit` binary is built to close.

**Step 4 — build the audit harness.** Created `route-b/` as a standalone crate
(`Cargo.toml` depends on `axeyum-ir`, `axeyum-cas`, `axeyum-solver` with
`features = ["full"]`, by path, `[workspace]` empty table so it does not join
the main workspace). Wrote `route-b/src/bin/b1_audit.rs`. It differs from the
precedent in three ways that matter:

- uses `check_auto_explained` instead of `check_auto`, so the **dispatch route
  trace** is printed for every query — this answers "which route decided it,
  and was that route a finite-domain one";
- adds FALSE-variant controls **in the unbounded configuration**;
- adds anti-bounding controls: satisfiable unbounded queries whose only
  solutions have |z| ≈ 10^18, and ones forcing `z < 0 ∧ x < 0`. A silently
  bounded abstraction would return `unsat` or `unknown` on these.

Build:

```sh
cd route-b && export CARGO_BUILD_JOBS=1 \
  && export CARGO_TARGET_DIR=$PWD/target \
  && cargo build --release --bin b1_audit
```

```
    Finished `release` profile [optimized] target(s) in 5m 59s
real	5m59.409s
```

(Cold build of the whole axeyum dependency chain at `-j1` on a contended box.)

Not yet run. Next entry records the run.

---

## 2026-08-12T19:08:30-04:00 — B1 audit run. The precedent SURVIVES the audit.

```sh
cd route-b && ./target/release/b1_audit | tee b1_audit.out
real	0m0.014s
```

Full output in `route-b/b1_audit.out` (20 queries over 5 parameter pairs
(2,3),(3,2),(4,3),(6,4),(5,3)). Tally:

```
=== MISMATCH COUNT ===
0
=== verdict tally ===
     14 expect=sat        OK
      6 expect=unsat      OK
```

**Finding 1 — the deciding route is `lia-dpll`, not a bounded one.** Verbatim
trace for the headline query:

```
  TRUE  claim1: a(x-y)=bz /\ NOT(2 | z)                      -> unsat                        (0.002s)  expect=unsat      OK
      route| probe: fragment {int}
      route| dl-online: declined (not-applicable)
      route| lia-simplex: declined (unsupported)
      route| lia-dpll: decided unsat
```

`lia-dpll` is `crates/axeyum-solver/src/dpll_lia.rs`, whose module doc reads
"Boolean-structured linear arithmetic (`QF_LIA` …) by lazy-SMT / DPLL(T) over
the **exact-rational** simplices" and "A round budget bounds the search
(`unknown`, never wrong)". So the search is bounded, the *domain* is not: the
budget can only cost completeness (`unknown`), never soundness. No
bit-blasting, no finite-domain split, no bit-vector route appears in any trace.

**Finding 2 — the false-variant controls FIRE in the unbounded configuration.**
This is the gap in the precedent (which only ran controls at `n = 30`). Three
deliberately-false variants of the same query shape, unbounded:

```
  FALSE ctrlA: a(x-y)=bz /\ NOT(3 | z)                       -> sat    ... model| x=Some(6) y=Some(0) z=Some(4)
  FALSE ctrlB: ... /\ 2|z /\ x-y != 3*(z/2)+1                -> sat    ... model| x=Some(0) y=Some(0) z=Some(0)
  FALSE ctrlC: a(x-y)=bz /\ NOT(3 | z)                       -> sat    ... model| x=Some(6) y=Some(0) z=Some(4)
```

Hand-replay of ctrlA (a=2,b=3): 2(6−0) = 12 = 3·4 ✓, and 3∤4 ✓. A genuine
counterexample to the false claim. So the gate is not vacuous — it returns
`sat` when the claim is false and `unsat` when it is true, in the *same*
unbounded configuration.

**Finding 3 — anti-bounding controls pass; witnesses exceed any plausible box.**

```
  SAT   big: z=2*(1000000000000000000), x-y=3*(1000000000000000000), y=1 -> sat
      route| int-box-eval: decided sat
      model| x=Some(3000000000000000001) y=Some(1) z=Some(2000000000000000000)
  SAT   big: z=2*(-1000000000000000000), ...                             -> sat
      model| x=Some(-2999999999999999999) y=Some(1) z=Some(-2000000000000000000)
  SAT   negatives: a(x-y)=bz /\ z<0 /\ x<0                   -> sat
      model| x=Some(-1) y=Some(2) z=Some(-2)
```

Witnesses at ±3·10^18 and genuinely negative solutions. A silently-bounded or
wrapping abstraction could not produce these. Note the route for the big ones is
`int-box-eval`, a different route from the lemma's — worth noting but harmless
here (these are the controls, not the theorem).

**Verdict on B1: the precedent is real. It is NOT bit-vector-bounded.** The
paper's claim stands. Caveat recorded: I have not yet stressed `lia-dpll` on a
SAT query whose witness must be *searched for* rather than pinned by an
equation. Doing that next (`b1_hard`), because "returns sat only when the
answer is handed to it" would be a real weakness.

Suspicion from the 19:07 entry item 1 (unbounded no slower than bounded)
RESOLVED as benign: a congruence/gcd refutation genuinely is O(1) work for
DPLL(T)+simplex; the bounded version is not doing more work, it is doing the
same work with three redundant range atoms.
Suspicion item 2 (no unbounded control) RESOLVED by adding the controls above.

---

## 2026-08-12T19:14:00-04:00 — B2/B3 groundwork by enumeration (no solver)

Before encoding anything I re-derived the construction from the brief in
`route-b/shell_groundwork.py` and enumerated it. Full output in
`route-b/groundwork.out`. Command:

```sh
cd route-b && python3 shell_groundwork.py | tee groundwork.out
```

Three results that DIRECTLY shape the encodings:

**G2 — gcd(a,b)=1 cannot be dropped.** The brief invited me to check whether the
coprimality hypothesis could be avoided. It cannot:

```
  k=2 b<a gcd=1: 21/21 solution-free
  k=2 b<a gcd>1: 0/7 solution-free   DEFECTS: [(4, 2), (6, 2), (6, 3), (6, 4), (8, 2), (8, 4), (8, 6)]
  k=3 b<a gcd=1: 21/21 solution-free
  k=3 b<a gcd>1: 0/7 solution-free   DEFECTS: [(4, 2), (6, 2), (6, 3), (6, 4), (8, 2), (8, 4), (8, 6)]
```

Every single non-coprime `b<a` pair in range is defective, at both k. So the
gcd hypothesis is load-bearing and must appear in the encoding. **Decision:
encode gcd(a,b)=1 as Bezout, `∃u,v. a·u + b·v = 1`.** This is the right
direction: the theorem is posed as a *refutation* (an existential query), so an
existential hypothesis is just two more free variables — no quantifier
alternation, stays in QF_NIA. This is the single design choice that makes B3
tractable at all.

**G3 — the b=a+1 counterexample family, closed forms.** Verified a=2..11:

```
  a   b       N   x=ab^2+1   z=a^2 b  chi(x)  chi(1)  chi(z)   N-ab+1  in range
  2   3      24         19        12       2       2       2       19      True   eq=True mono=True  x==N-ab+1? True
  3   4      60         49        36       2       2       2       49      True   eq=True mono=True  x==N-ab+1? True
 ...
 11  12    1716       1585      1452       2       2       2     1585      True   eq=True mono=True  x==N-ab+1? True
```

with (asserted exactly for a=2..11)

```
    N        = 2ab + a^2 b = a(a+1)(a+2) = a^3+3a^2+2a
    x        = a b^2 + 1   = a(a+1)^2+1  = a^3+2a^2+a+1
    N-ab+1   = a^3+2a^2+a+1   == x   <-- x is EXACTLY the left endpoint of the
                                          right-hand shell
```

That `x = N − ab + 1` coincidence is the reason the family works, and it turns
B2 from "an identity" into a full theorem: not just `a(x−y)=bz`, but *in range
and monochromatic*, for all a.

**G4 — the k=2 refutation needs far less than I feared.** Worked the case
analysis by hand and cross-checked by brute force (`k=2, all coprime b<a with
2<=a<=9: NO monochromatic solution. OK`). Then noticed something the brief did
not claim: at k=2 the enumeration shows **every coprime pair is solution-free,
including b > a** — look at the k=2 rows, `(2,3) (2,5) (2,7) (3,4) (3,5) (3,7)
(3,8) (4,5) (4,7) (5,6) (5,7) (5,8) (6,7) (7,8)` are all FREE. So at k=2 the
`b<a` hypothesis appears unnecessary. Re-derived the proof and it is uniform:

    z = a·t ≤ N = a·b  ⇒  t ≤ b.
    CASE all-colour-1: a|x ∧ a|y ⇒ a | (x−y) = b·t ⇒ (Bezout) a|t ⇒ t = a·w
        ⇒ x−y = b·t = a·b·w = N·w ≥ N.  But x ≤ N and y ≥ 1 so x−y ≤ N−1.  ⊥
    CASE all-colour-2: a|z always, so colour 2 forces a²|z ⇒ a|t ⇒ t = a·q
        ⇒ x−y = b·t = N·q ≥ N > N−1 ≥ x−y.  ⊥

Both branches end at the *same* inequality and **neither uses b < a**. So I will
attempt the STRONGER k=2 theorem (no b<a hypothesis) and report which version
axeyum actually discharges.

**Encoding trick decided here (important for the paper).** Both `a | j` and its
negation `a ∤ j` must appear, and a negated divisibility is normally a universal
(`∀p. j ≠ a·p`), which would push the query out of QF. Avoided by witnessing the
remainder:

    a | j    ⟺  ∃p.       j = a·p
    a ∤ j    ⟺  ∃s,r.     j = a·s + r  ∧  1 ≤ r ≤ a−1

Both existential. Combined with Bezout for gcd, the ENTIRE colouring predicate
becomes quantifier-free NIA with extra free variables. No quantifier alternation
anywhere in route B.

**Control design fixed here, before running anything.** For k=2 the sharp
false-variant is *drop the Bezout hypothesis* — G2 says it must then be
satisfiable. Hand-checked a witness in advance so I can tell a real `sat` from a
lucky one: (a,b)=(4,2), t=2 ⇒ z=8, x−y=4, x=8, y=4; 4(8−4)=16=2·8 ✓; N=8;
v_4(4)=1, v_4(8)=1 so χ(8)=χ(4)=1 — all colour 1, a genuine defect of exactly
the parameterised shape. For k=3 the sharp false-variant is *drop b<a* (G1 shows
every coprime b>a row defects at k=3).

---

## 2026-08-12T19:18:10-04:00 — B2 first run. 17/20 matched, 3 informative FAILURES.

```sh
cd route-b && ./target/release/b2_family | tee b2_family.out
real	1m21.934s     # 81s of which 60s is ONE query's timeout; contended box
```

Full output in `route-b/b2_family.out`. Tally:

```
  [B2] matched=17 mismatched=3
      MISMATCH: iii.y1 -> unknown(Timeout)
      MISMATCH: iii.z2 -> unknown(Incomplete)
      MISMATCH: iii.x1 -> unknown(Incomplete)
```

### What WORKED (all with `a` a free unbounded Int, nothing sampled)

```
  TRUE  (i)  refute: a(x-y) != b*z                               unsat    0.00s
      via | int-real-relax: decided unsat
  TRUE  (i') refute: general b, a(x-y) != b*z                    unsat    0.00s
  TRUE  (ii) refute: NOT(x <= N)                                 unsat    0.00s
  TRUE  (ii) refute: NOT(z <= N)                                 unsat    0.00s
  TRUE  (ii) refute: NOT(x >= 1)                                 unsat    0.00s
  TRUE  (ii) refute: NOT(z >= 1)                                 unsat    0.00s
  TRUE  (iii.y2) refute: a*b < 1                                 unsat    0.00s
  TRUE  (iii.z1) refute: z != a^2*b                              unsat    0.00s
      via | term-identity-refuter: decided unsat
  TRUE  (iii.x2) refute: x < N-ab+1                              unsat    0.00s
  TRUE  (iii.x3) refute: x != N-ab+1                             unsat    0.00s
  TRUE  (iv) refute: NOT(identity /\ range /\ x in right shell)  unsat    0.14s
      via | int-real-relax: decided unsat
```

The deciding route for the polynomial facts is `int-real-relax`. Degree-3
polynomial identities and inequalities in one and two free integer variables are
discharged in milliseconds. `(iv)` is the whole arithmetic half of the theorem
as ONE query and it goes through.

**Every one of these is paired with a control that came back `sat`:**

```
  FALSE ctrl(i):     refute: a(x-y) != b*(z+1)          sat  0.01s  wit | a=2
  FALSE ctrl(ii):    refute: z < x                      sat  0.00s  wit | a=2
  FALSE ctrl(iii.z): refute: a^2 | z                    sat  0.02s  wit | a=2 pz=3
  FALSE ctrl(iii.x): refute: x != N-ab                  sat  0.00s  wit | a=2
  FALSE ctrl(iv):    conjunction + false conjunct z>=x  sat  0.01s  wit | a=2
```

`ctrl(iii.z)` returning `wit | a=2 pz=3` is a *correct* witness: a=2, b=3,
z = a^2 b = 12 = a^2 * 3, so pz = b = 3. The controls are not just firing, they
are firing with meaningful models.

### ENCODING FAILURE 1 (my bug, deliberately kept in the run)

I originally posed "a^2 | z" as `NOT(divides(a^2, z))` where `divides` witnesses
the quotient with a FREE variable `pz`. That is wrong: `pz` is implicitly
EXISTENTIAL at query level, so `not(z = a^2*pz)` says "there exists pz with
z != a^2*pz" — trivially satisfiable, and no evidence for anything. I caught
this by inspection BEFORE the first run and kept it in as a live demonstration:

```
  BUG   (iii.z1-bad) refute: NOT(a^2|z) -- negated existential   sat  0.00s
      wit | a=2 pz=1
```

Exactly as predicted (a=2, pz=1: z=12 != 4·1). **Rule extracted: a witnessed
existential predicate may only appear POSITIVELY in a refutation query.** Its
negation must be certified a different way.

### ENCODING FAILURE 2 (axeyum's reach — the real finding)

All three mismatches are the same shape: **refuting a divisibility to establish
a NON-divisibility.**

```
  TRUE  (iii.y1) refute: a | 1     unknown(Timeout)      60.00s
      via | int-blast-ladder: declined (budget: combined-theory timeout after scalar backend)
  TRUE  (iii.z2) refute: a^3 | z   unknown(Incomplete)   20.81s
      via | int-blast-ladder: declined (incomplete: no model within the bounded integer width 32; widen the bound)
  TRUE  (iii.x1) refute: a | x     unknown(Incomplete)    0.92s
      via | int-blast-ladder: declined (incomplete: no model within the bounded integer width 32; widen the bound)
```

`∃a,p. a ≥ 2 ∧ a·p = 1` — a fact a first-year student closes in one line —
routes to `int-blast-ladder`, which bit-blasts integers at a bounded width,
finds no model within width 32, and correctly declines as **`unknown`, never a
wrong `unsat`**. Soundness is intact; this is a *completeness* limit, and it is
the sharpest boundary of axeyum's arithmetic reach I have hit so far. Recorded
as a product finding.

### The fix, and why it is not a cheat

The three failures share a root cause that is MY encoding's fault, not only
axeyum's: I was trying to establish a *positive existential* fact
(`a ∤ j`, which by the remainder characterisation means "∃s,r. j = a·s+r ∧
1 ≤ r ≤ a−1") by *refuting its negation*, which is the hard direction. A
positive existential should be certified by **exhibiting the witness**, exactly
as `(iii.z1)` already does (witness p = b, decided by `term-identity-refuter` in
0.00s after the same claim in the wrong direction had failed).

Witnesses, all forced and none free-chosen:
  a ∤ 1        : s = 0, r = 1.  Need 1 ≤ 1 ≤ a−1, i.e. a ≥ 2.  LINEAR.
  a ∤ a·b²+1   : s = b², r = 1. Need 1 ≤ 1 ≤ a−1, i.e. a ≥ 2.  LINEAR.
  a³ ∤ a²(a+1) : z = a³ + a², so s = 1, r = a². Need 1 ≤ a² ≤ a³−1,
                 i.e. a²(a−1) ≥ 1.  Degree 3, one variable.

This is not weakening the theorem: `a ∤ j` is *defined* by the existence of such
an (s,r), so producing the witness and proving its side conditions IS the proof.
Rewriting `b2_family.rs` accordingly and re-running. Both the failed and the
fixed encodings stay in the file so the run shows both.
