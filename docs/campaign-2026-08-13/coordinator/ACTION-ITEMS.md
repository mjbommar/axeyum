# Calibrated action items after the 2026-08-13 campaign

Synthesised from five agents' `FEEDBACK.md`, the coordinator's own measurements,
and a peer session's review. Every item cites what was measured; where a number
appears, an agent produced it today.

**The frame.** F-C3 is the strategic finding and it should order everything
else: a solo preprint author built the same *architecture* — SAT encoder, claim
ledger, Lean formalisation, axiom audit, public reproduction script — by March
2026. The architecture is not the moat. **The checked certificate is.** Their
SAT results enter Lean as `axiom lem_keypair_sat`; ours are now accepted by
Lean's own kernel. Every item below is ranked by how much it protects or
extends that difference.

---

## 1. Sweep the prose-guard class — the only wrong-answer generator on the list

**Three instances, three crates, one day**, and none was found by a test:

| where | form | found by |
|---|---|---|
| `axeyum-search` symmetry breaking | interchangeability assumed, unstated | agent-a, extending the trait |
| `axeyum-lean-kernel` `lean_pp` | "defensive guard" documented, never implemented | a peer reading the doc |
| `axeyum-rewrite` manifest | precondition is a `String`, presence-checked | coordinator reading the struct |

Only the first produced a demonstrated wrong answer — `S(3;3,4,5)` at `n = 41`
is **satisfiable** and the stock encoding calls it `unsat` — but all three have
the same shape, and a wrong `unsat` is certified happily by every downstream
tool because the proof is a valid proof of the wrong formula.

**Do:** (a) a mechanical sweep for comments asserting checks the code does not
perform, starting with `grep` for "guard", "only", "must be", "assumes" in
doc comments on public API; (b) generalise agent-f's `PreconditionGuard` so a
satisfiability-preserving transform carries its precondition **where it is
applied**; (c) every guard gets a control that fails without it.

**The trap to respect**, from agent-a: it tried five instances and only one
flipped. A control chosen carelessly passes while testing nothing.

## 2. File-backed backward DRAT checking — the hard limiter on what we can certify

**Measured: 6.6× blow-up**, 1.87 GB of text DRAT → 12.3 GiB resident (agent-c,
F-C7; its own prior estimate was 1.5×, so this is four times worse than
assumed). Consequence, stated plainly: **the repository ships certificates
(18.9 GB, 5.0 GB) it cannot re-check on half the hosts in this campaign.**
s5/s6/s7 have ~26 GiB and cannot carry a large check at all.

This is the single biggest constraint on the mathematics. agent-c had to run
duplicate insurance jobs on two hosts because it could not predict where a
check would fit, and killed a job at 2.95 GB of proof rather than discover the
answer at exit 137.

**Do now (hours, not weeks):** make the driver print the ratio and **refuse
with a typed exit code** rather than being OOM-killed — an OOM kill is
indistinguishable from a refuted claim, and that confusion has already cost
this project real work twice. **Then:** stream the backward pass from disk.

## 3. Package what is already proved — 25+ values and the `741` claim

agent-a: **20 of 45 decided cells** carry a ledger entry. agent-b's
`R_4(5(x-y)=4z) = 741` — a complete 6241-cube cover, every proof checked — was
not yet committed as a claim at last report.

A value with proofs on disk and no ledger entry is *"we computed this"*. A
packaged one is *"the system re-derives this on demand"*. Only the second
survives the session, and only the second is what a referee can use. This is
the cheapest high-value work available and it is already paid for.

Keep the honest form the checker already produces: today's run reports
`61 claims re-checked, 0 errors, 15 row(s) not re-checked here` — 46 re-derived,
15 regenerable-on-demand, each named with its regeneration command.

## 4. Make `axeyum-search` usable on an instance it has never seen

Three agent requests are one piece of work:

- **F-C2** — no supported front door for a new `ColouringFamily` instance.
  *Every agent rewrote the same driver.* `parse_family` already does the
  argument parsing.
- **F-C10** — nothing could check a *stored* proof without re-solving.
  `solve` bundles production with checking; `recertify_rado` always re-solves
  (`recertify_rado.rs:136`). agent-c built the missing `check` subcommand and
  it saved 113 minutes on one instance — but the real gain is that a
  certificate becomes **movable between machines**, converting the memory
  asymmetry from a nuisance into a scheduling parameter.
- **F-C5** — a checked `known_witness` hook. The satisfiable side of this whole
  family is a two-line construction; using it settled **eight parameter points
  in under a second** where search took tens of seconds and sometimes failed.
  Guard it through `verify_witness` — the previous session shipped an
  unguarded `predicted_lower_bound` that was wrong on 19/19 triples.

## 5. Novelty as an enforced field, not narrative

**Five of agent-a's claims shipped labelled NEW that had been published four
months earlier**, in a table one PDF extraction away. My audit caught it; an
audit is not a gate. `prior_art` is currently prose.

Cheap, and it is a correctness property of a claim rather than a nicety: a
value's meaning includes whether it is ours. Pair it with the standing rule
that earned its place today — **before any run that will produce a novelty
claim, extract the full text of the closest paper (not the abstract, not the
first table that answers the question) and `gh search repos` for its artifact
repository.** SSRN 403s; the Zenodo/GitHub artifacts do not.

## 6. One final pass over the paper against the measurements

The Lean paragraph has now been **wrong in both directions in a single day** —
first claiming the toolchain was absent and the export unchecked, then (my
correction) claiming it was rejected, when by evening Lean's own kernel accepts
it. Both corrections are committed, but the file has been rewritten three times
in twelve hours and deserves one careful read against the artifacts rather than
against anyone's memory.

Include agent-d's F-D6: the paper's Lean claim should be neither "works" nor
"does not exist" but the measured asymmetry — *an export path exists and is
exercised on 163 modules across 70 families; Lean's own kernel accepts the Rado
development from an empty environment; the inbound direction admits a measured
five-root fixture profile, with the dependency-closed population unstarted.*

## 7. Enumeration is the wall — and it is a modelling-layer problem

`S(3;4,4,12)` spends **164 s generating 633,107,771 multisets to keep 451,622
clauses**, which are then refuted in **0.1 s**. The subsumption reduction (up
to **1,402×**) is why we passed Song–Mao's published frontier — their search
stops about where the unreduced encoding stops fitting.

Two asks: generate the antichain directly rather than filtering it, and give
the framework a way to **size an instance without materialising it** (agent-a
#8). Related: `CnfFormula` as `Vec<Vec<CnfLit>>` costs 2.3 GB RSS for 330 MB of
**[CORRECTED 2026-08-14: agent-g measured the overhead against a flat arena at
2.13x, not the 7x this paragraph implies. Sizing the fix against 7x would make
a correct fix look like a failure. Cheaper first move: pack `CnfLit` to 4
bytes -- confined to `axeyum-cnf`, breaks no signature, half the win without a
113-call-site refactor.]**
literals.

## 8. Route A for adaptive covers, and branch-point selection

`compose_cover_proof` collapses a cover into a single DRAT proof of the
original formula, discharging the meta-argument entirely — and it **does not
generalise to trees** (agent-b #1). So the `741` result rests on four checked
obligations plus a meta-argument rather than one composed proof. That is sound
and honestly recorded, but it is the last place a reader has to trust an
argument rather than a certificate.

agent-b #5 is the companion: **branch-point selection is the whole game and
nothing chooses it.** For `a(x-y)=bz` a point `j` is a `z` only when `a | j`,
so multiples of `a` sit in ~1000 constraints where other points sit in ~300 —
which is why the 2026-08-12 probe, branching on 2,4,6,8,10,12, found the
subtree uniformly hard.

---

## Process items — small, and they each cost real work today

- **Commit by diff, never by copy.** Campaign rule 7 gave build isolation and I
  never thought through committing: agent-d's snapshot copy-back silently
  reverted another lane's refactor (repaired in `c33553e72`). My error.
- **`/tmp` is a 62 GiB tmpfs and it is RAM.** s0 sat at 80% with ~13 GiB of
  five-day-old artifacts from an unrelated project, cutting the headroom
  agent-c's memory-bound checks were scheduled against from 68 GiB to 55 GiB.
  `df` says disk; `free` says `shared`; neither view alone predicts the OOM.
- **A partial run must report where a reader looks for the positive.**
  `S(3;3,3,15)` was OOM-killed on the bracket's *upper* probe, so the raw
  transcript reads "sat at 100, then nothing" — a silent gap, not a failure.
  The `rc=137` annotation is the only thing distinguishing "out of memory" from
  "the lane moved on".

## What I would NOT do next

- **Chase more new values.** We have 18 new off-diagonal Schur numbers, a
  closed `741`, and two blank Table 10 cells in flight. The marginal value of
  a 19th is below the marginal value of packaging what exists.
- **Optimise the solver.** Every instance in agent-a's table is decided in
  under 2 seconds; enumeration and checking are the walls. Solver work would
  be optimising the part that is not slow.
- **Chase `w(2;3,20)` hard.** Fifteen years open, tiny formula, brutal search.
  Worth a bounded probe, not a campaign.
