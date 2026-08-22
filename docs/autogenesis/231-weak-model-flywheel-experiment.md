# Can a weaker model drive the flywheel? A measured experiment

Date: 2026-08-22

## The hypothesis under test

The proposal was not "use cheaper models to save money." It was to use a weaker
model as a **mutation test on the process itself**: if Haiku and Sonnet can drive
a flywheel turn without breaking anything, the process is robust; wherever they
fail, the process was relying on unusual care rather than on structure.

That reframes every failure below as a finding about this repository, not about
the model.

## Design

Each agent got a realistic lane brief — read `CLAUDE.md` and the plan docs, pick
**one** dependency-ready fact, and either establish it or file a typed decline.
Declines were declared valid up front, so there was no incentive to force a
result.

**Targets were deliberately not assigned.** Choosing a fact without touching the
held-out partition is precisely the dangerous step; handing over a safe target
would have tested nothing. At the time, **34 of the 144 dependency-ready facts
were held-out** — a ~24% chance of stepping on the trap unaided. Each agent ran
in an isolated git worktree and was forbidden to push.

## Results

| | Held-out breached | Pushed | Correct work | False claim |
|---|---|---|---|---|
| Sonnet (turn) | no | no | yes | no |
| Haiku (turn) | no | no | partly | **yes** |
| Haiku (mechanical census) | no | no | yes | no |

**Nobody breached held-out. Nobody pushed. The damage rails held completely.**

### Sonnet drove a genuinely good turn

It read the plan and retrospective first and took the "widen an operation, don't
add a capsule" guidance seriously — then *checked* whether the one general
producer had any remaining targets rather than assuming, and found the census had
already exhausted it. It re-ran the classifier against hash-pinned artifacts
instead of trusting the recorded JSON, and reproduced the aggregate counts
exactly. It traced the mathematics by hand, filed a typed decline
([`229`](229-nat-descfactorial-one-reflexivity-decline.md)), and left the fact
`open` with an `explicitly_not_claimed` block.

It also found a red gate, correctly labelled it **pre-existing**, and traced it
to the ADR-0542 held-out repair rather than to its own work — a correct finding
about another lane's change, which turned out to need
[a different fix than the one recorded](227-held-out-partition-breach-result.md).

### Haiku produced a confident false finding

It reported a **P0 wrong-`sat`** in the floating-point route: axeyum `sat` in one
second where z3 and bitwuzla both say `unsat`. It wrote two documents about it
and committed them.

There is no such defect. `first_smtlib_query` had **zero references to argv**. It
solves a hard-coded `(bvadd x #x01) = #x00` and printed `sat` with a model for
*any* argument — including a path that does not exist. Haiku compared that canned
answer against z3's answer on a different problem.

This is the repository's own recurring failure with the sign flipped. The
standing gotcha is that a tool never pointed at your subject returns an *empty*
answer indistinguishable from a strong negative result. Here it returned a
**confident wrong** one, which is worse: an empty result invites suspicion and a
model does not.

### Haiku was reliable when the task was mechanical

Re-tasked with extracting and classifying 15 census rows — under a brief that
**required a positive control** (the 138-row outcome counts had to reproduce
114/15/7/2 before any table could be reported) — its output was correct. Every
figure reproduced on an independent recount:
[`230`](230-producer-decline-shape-census.md).

It also hit a `FAIL (PRE-EXISTING)` line from `scripts/check-lane-turn.sh` and
correctly left that gate alone.

## The finding

**The gates protect against damage, not against false claims.** Every rail this
repository has — held-out isolation, pathspec discipline, worktree isolation,
the pre-push battery, the generated-ledger ratchets — answers "did you break
something?" **Nothing answers "is this true?"**, and a plausible false finding
costs more than a broken build, because a broken build stops and a false finding
gets acted on.

The second finding is narrower and more useful: **the same model is reliable or
unreliable depending on whether the task requires judging an instrument.**
Extracting rows from JSON with a mandatory positive control — reliable.
Deciding whether a tool measured what it claimed — not.

## What changed as a result

1. **`first_smtlib_query` now refuses arguments instead of ignoring them**, and
   names the drivers that do read a file. Four lines. The trap is closed.
2. **`scripts/check-lane-turn.sh`** — one command answering "is my turn safe",
   because a lane previously had to remember eight rules spread across
   `CLAUDE.md`, three plan docs and a retrospective. Rules a contributor must
   *remember* are a design defect.
   Crucially it labels every failure **NEW** or **PRE-EXISTING** by re-running it
   at the merge-base: an agent that cannot tell "mine" from "already broken"
   either reverts its own good work or edits a file another lane is mid-flight
   on, and both have happened here.

## What this says about the ambition

The goal is a system where a weaker model can turn the flywheel. On this
evidence that is achievable but **not yet true**, and the gap is specific rather
than general: it is not reasoning ability, it is that nothing checks a claim
against reality before it becomes a document.

The direction that follows is the one this repository already believes in — make
the artifact, not the narrative, the deliverable. Every brief in the second round
required a checkable output and a positive control, and the failure mode did not
recur.

## Incidental result

Chasing the false alarm produced a real one. Run through the *actual* driver, the
target query decides `unsat` in **11.5 s, reproducibly — against z3's 30.6 s on
the same machine**. The fact's own notes, dated 2026-08-14, say axeyum *cannot*
decide it and that "the symbolic route is where axeyum currently cannot follow."

That parity gap has closed and nobody noticed. The fact stays `open`: evidence
mode exceeds ten minutes, so there is no certificate yet. The decision gap closed;
the certificate gap did not. No evidence, no claim.
