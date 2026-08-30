# Notes: 307-brief-step0

Detail moved out of [`../status/307-brief-step0.md`](../status/307-brief-step0.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

That 0.89 row is the arrow-only, strictly weaker theorem whose distinctness from
the `Iff` takes a paragraph of prose in the fact's own notes. The tool separates
them from the types alone.

**The honest limit, printed on every PRESENT verdict**: a constant multiset
cannot see argument ORDER, so left/right variants collide -- `Int.add_assoc` and
`Int.add_left_comm` both score 1.00 against `a+b+c = a+(b+c)`. 1.00 is a
**candidate**, not a licence to flip a status; the rendered type is printed so
the reader decides. Where both variants exist the tool returns both
(`Nat.log_zero_left` *and* `Nat.log_zero_right`), which is the useful behaviour.

**2 -- Near misses.** Delegated to `examples/shape_search`, not reimplemented.
The operator head is qualified by the statement's carrier first (`Nat.le`, not
`le`) -- unqualified, `shape_search` answers UNANSWERABLE forever, which is
correct and useless -- and falls back to the unqualified spelling on exit 3.

**3 -- Modules to read.** 221 basenames indexed under
`crates/axeyum-lean-kernel/src`, **60 shared across directories**. A shared one
is flagged and **both** paths printed:

```
gcd.rs -> int_prelude/gcd.rs, nat_prelude/gcd.rs  <-- SHARED BASENAME, read BOTH
```

This is the `crt.rs` failure: three successive triages and one brief looked only
at `int_prelude/crt.rs` and concluded the Chinese Remainder machinery did not
transport, while `nat_prelude/crt.rs` carried exactly what was needed.

**4 -- Is the target blocked?** Delegated to `check-dispatchable-frontier.py` by
`importlib` -- held-out blind-evaluation population, mutation negative control,
divergence registry -- and prints the loaded sizes (107 / 12 / 4) as its own
positive control.

## 3. Speed

| | |
| --- | --- |
| a report against a warm snapshot | **0.23-0.48 s** |
| ranking all 141 open facts at once | 5.9 s |
| `--refresh` from an existing release binary | 34-37 s |
| `--refresh --build` cold in a fresh lane worktree | **1 m 50 s** (73 s build + 37 s read) |
| `shape_search` per near-miss query | 1 s, or 30 s with `--include-constructed` |

The snapshot exists precisely because the alternative fails the brief's first
constraint: a tool needing a fresh `--release` kernel build before every
dispatch would not get run, and not running it is the failure being fixed.

## 4. How staleness is surfaced -- and the bug the tool walked into itself

**The snapshot filename carries `git rev-parse HEAD:crates/axeyum-lean-kernel`.**
There is no in-band freshness field a reader can skip: a snapshot from another
kernel tree simply is not the file the current tree looks up.

Three states, and the middle one keeps the alarm meaningful:

* **EXACT** -- the snapshot's tree is HEAD's tree.
* **EQUIVALENT** -- behind HEAD, but no declaration-name leaf appears in today's
  sources that the snapshot lacks. Without this, every kernel commit (there are
  ~100 a day) would raise the alarm and the alarm would stop being read.
* **STALE** -- new leaves exist. Every ABSENT verdict is printed
  **PROVISIONAL**, the new leaves are named, and the process exits **4**.

The asymmetry is stated rather than implied: **a stale snapshot yields a false
ABSENT, never a false PRESENT.**

The leaf-name delta is derived from source text (`kernel.name_str(ns, "leaf")`
call sites, 2,013 distinct leaves) and is a heuristic. It decides *staleness*
only. No verdict is ever read from source text -- the standing rule is intact.

**The tool walked into its own hazard on its first run and that is why the
refusal exists.** `--refresh` used the prebuilt projection binary in the shared
checkout, 40 hours old, and stamped the resulting snapshot with **today's** tree
sha -- so the freshness check reported `EXACT` about an environment missing
**288 declarations** (1,998 against a true 2,286), including
`Nat.add_eq_zero_iff` and `Nat.gcd_comm`, both of which had landed that day. It
would have reported them ABSENT, confidently, from a snapshot labelled current.

So `--refresh` now **refuses** a projection binary older than the newest kernel
source, and `--allow-stale-binary` stamps the snapshot `snapshot-stale-binary-…`
-- structurally unable to match any tree sha, so it always reads STALE.

## 5. Every negative carries a positive control

Before any verdict the matcher is run against a built-in probe whose match
certainly exists (`∀ a b : ℕ, a + b = b + a` must retrieve `Nat.add_comm`). If
the probe fails the run is **UNANSWERABLE, exit 3, and prints no verdicts at
all** -- a broken snapshot must never read as "nothing exists". Section 3 pairs
its negative with the indexed-basename count; section 4 prints the partition
sizes it loaded; section 2 inherits `shape_search`'s own control line and its
exit-3 UNANSWERABLE distinction.

## 6. The loop-closing mechanism: `just brief`, and why not a gate

**Chosen: a `just` recipe.**

```
just brief F:ml430-nat-gcd-comm-…   # step 0, sub-second
just brief-refresh                  # re-read the environment (~2 min)
just brief-self-check               # the controls plus the snapshot self-check
```

The argument, in order of what actually decided it:

1. **It sits where the actor acts.** The dispatcher writes the brief and already
   types `just`. `just next` exists for exactly this reason -- its own comment
   says "a queue nobody can reach is a record, not a queue" -- and `just brief`
   is the next arrow along: `just next` picks the target, `just brief` sizes it.
2. **A check that a status doc records the step-0 result gates the wrong
   actor.** The lane writes the status doc, and R8's whole point is that the
   lane does nothing. Worse, such a check is satisfied by pasting a sentence:
   a checker whose exit status does not depend on what the run found is the
   defect this repository names as worse than no checker.
3. **Every gate that would genuinely check this needs the kernel environment,
   and therefore a build.** Wire it into the aggregate gate and it costs
   1m50s-plus per run -- the same cost that left `check-local-ci-freshness` red
   for 265 h. Make it skip when no snapshot exists and it reads green while
   checking nothing. Both branches are failures this repository has already
   paid for, so I did not build one.
4. **What I did instead of a gate is prevent the failure at the source rather
   than detect it afterwards.** A gate would catch "the dispatcher consumed a
   wrong retrieval answer". The tool cannot *produce* one: a snapshot that
   fails the probe exits 3 with no verdicts, and a stale snapshot exits 4 with
   every ABSENT marked provisional. The nine controls are what make that claim
   checkable, and they run in `scripts/check.sh` and `just check`.

**What would change my mind:** if `just brief` is measurably not run -- the
signal is the same one the retrospective used, mentions in status docs -- then
the next move is a gate on the *fact ledger*, not on status docs: "these open
facts have an exact-constant candidate in the environment; close them or record
why the candidate is not the proposition." That gate has a real finding to
report today (§7) and its cost problem is solved the moment a snapshot is
produced by something that already builds the kernel.

## 7. Finding, out of scope for this lane to act on

Ranking all 141 open facts that carry a `formal.statement` against the fresh
2,286-declaration snapshot:

| top score | open facts |
| --- | --- |
| >= 0.999 (exact constant multiset) | **14** |
| >= 0.75 | 20 |

Two verified by hand against the rendered types:

* `F:ml430-nat-dvd-antisymm-507f9026` -- `∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n`,
  and `Nat.dvd_antisymm` is admitted at exactly that type. Genuine.
* `F:ml430-int-add-assoc-749cb0ff` -- `Int.add_assoc` likewise. The run's second
  candidate at 1.00 is `Int.add_left_comm`, which is the order-collision caveat
  demonstrating itself.

The other twelve are candidates, not verdicts; several are `log_zero_left` /
`log_zero_right`-style pairs where both variants are returned and the reader
picks. Someone owning the ledger should walk them.

## 8. Controls

`scripts/tests/test-brief-step0.sh` -- ten cases, ~1 s, no cargo lock and no
kernel build (fixture snapshots via `AXEYUM_BRIEF_STEP0_CACHE`, a fixture binary
via `AXEYUM_BRIEF_STEP0_PROJECTION_BIN`). Nine guards, each deleted in a
`copytree`'d scratch root on `/data0` -- never a tracked source, `__pycache__`
cleared between iterations -- and each killed **exactly one** control:

| guard deleted | control that dies |
| --- | --- |
| `if not ok: return 3` (probe gate) | GUARD 1 vacuity |
| `state == "STALE"` → exit 4 | GUARD 2 |
| `if not resolved: return 1` | GUARD 3 |
| the `len(paths) > 1` SHARED BASENAME flag | GUARD 4 |
| the `fact_id in held` verdict | GUARD 5 |
| the `-mutation-` verdict | GUARD 6 |
| the stale-binary refusal in `--refresh` | GUARD 7 |
| the unmatchable `stale-binary-` restamp | GUARD 8 |
| the `is_rendered` dialect dispatch | GUARD 9 |

The tenth is the **false-positive control** -- a healthy run with a fresh
snapshot and a resolvable target exits 0 with no alarm word -- and it survived
all nine mutations, which is what distinguishes the guards from a subject that
refuses everything.

GUARD 9 came from a defect found in use, not from imagination: the ledger
carries **two statement dialects**, and some `formal.statement`s are kernel
rendered types (`theorem Int.gcd_comm : ((x0 : Int) -> …)`). Through the surface
normalizer, `->` became `sub` and `lt` (from `-` and `>`) and `x0`/`x1` became
constants, so `F:int-gcd-comm` scored **0.18 against its own declaration** and
printed a confident ABSENT. With the dispatch it is 1.00.

## 9. Gate status

```
scripts/tests/test-brief-step0.sh     10 pass, 0 fail
scripts/check-control-registration.sh controls=27 (was 26) orphans=0
                                      py_controls=387 py_orphans=0
python3 scripts/validate-facts.py     exit 0; 3341 evidence rows re-derived by 2+ checkers
python3 scripts/gen-plan.py --check   exit 0
scripts/check-aggregate-scope.sh      11 unrecorded divergences, ALL pre-existing;
                                      `brief-step0-controls` is on both sides
```

Registered in **both** `scripts/check.sh` and the `justfile`.

## 10. What this lane did not do

* No `crates/` change -- a sibling lane is in the nat prelude.
* No push.
* No fact status flipped. §7 is a report, not an edit.
* No gate built on top of the tool; §6 argues that, and names the signal that
  should reverse the decision.
