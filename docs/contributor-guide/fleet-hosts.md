# Fleet hosts — what a machine needs before a lane can trust it

A lane that cannot run the gates its work depends on is not a parallel lane. It
is a queue entry waiting on whichever host happens to have the toolchain, and it
will report green from a gate that never examined its subject.

This document states the **capability baseline** for an axeyum host, how to
establish it, and how to verify it. It is deliberately separate from
[`multi-agent-operations.md`](multi-agent-operations.md), which owns the
*resource* discipline on those hosts (thermal envelope, bounded units, not
hammering another lane's worktree). Read that one before running anything heavy;
read this one before believing a gate.

## Why this exists

Measured 2026-08-16, before any provisioning:

| finding | measurement |
|---|---|
| `lean` and `just` present on | **exactly one host of five** (`s5`) |
| `cargo-deny` present on | **zero hosts** — so `cargo deny check` failed fleet-wide |
| Rust nightly spread | `2026-03-25` on s2, `2026-03-31` on s5/s6, `2026-07-11` on s4, `2026-07-12` on s7 — **109 days, 3.6 months** |
| `just` on the box agents actually work in (`s4`) | **absent**, while `CLAUDE.md` names `just check` as *the* gate |

Every one of those is the same defect wearing different clothes: **a gate's
scope silently depends on which machine it ran on.** The nightly spread is the
sharpest instance, because clippy's lint set changes between nightlies — so
"clippy clean" was a host-dependent claim, and one lane could hand another a red
tree it was unable to reproduce.

The s4 row is worse than a missing package. An agent following the session
protocol verbatim on s4 runs `just check`, gets "command not found", and falls
back to `./scripts/check.sh` — which
[`gate-divergence-2026-08-14.md`](../refactor-2026-08/gate-divergence-2026-08-14.md)
measured as **61 steps against 112**, each missing something the other has. The
fallback is not the gate, and nothing in the failure says so.

### State after the 2026-08-16 provisioning pass

Every row below was produced by **executing the binary**, not by `command -v`:

| host | role | rustc | just | cargo-deny | lean |
|---|---|---|---|---|---|
| `s4` | dev box, 16 c / 123 G — the shared multi-lane checkout | `2026-07-11` | 1.58.0 | 0.20.2 | 4.30.0 `d024af09` |
| `s5` | compute, 16 c | `2026-07-11` | 1.58.0 | 0.20.2 | 4.30.0 `d024af09` |
| `s6` | compute, 16 c | `2026-07-11` | 1.58.0 | 0.20.2 | 4.30.0 `d024af09` |
| `s7` | compute, 16 c, largest disk | `2026-07-11` | 1.58.0 | 0.20.2 | 4.30.0 `d024af09` |
| `s2` | compute, **4 c** — smallest; prefer it for Python/ledger/NAS-IO | `2026-07-11` | 1.58.0 | 0.20.2 | 4.30.0 `d024af09` |

**All five** hosts report the identical `clippy 0.1.99 (be8e82435e 2026-07-11)`
and `rustfmt 1.9.0-nightly (be8e82435e 2026-07-11)`, so a lint result is now
reproducible across the fleet. All five have `core.hooksPath=hooks`,
`/nas3/data` read-write, `~/.cargo/bin` on the non-interactive ssh `PATH`, and a
Lean the gate can discover.

> **s2 was network-isolated when first measured, and a reboot restored it.**
> Recorded rather than quietly overwritten, because the isolated case is real
> and will recur: it reached *nothing* external — not crates.io, GitHub, the
> Lean release host, nor the distribution archive — and was provisioned only
> after the reboot. Its 4 cores still make it the wrong host for a heavy build;
> that is a sizing judgement, not a capability limit.

## The baseline

A host is **gate-capable** when all of these hold. Anything less makes the host
usable for compute but not for verification, and a lane must say so when it
reports a result from one.

| requirement | why | verify |
|---|---|---|
| Rust nightly at the **fleet pin** | clippy lint sets differ between nightlies; an unpinned fleet cannot reproduce a lint failure | `rustc -vV \| grep commit-date` |
| `clippy`, `rustfmt`, `rust-src` components | `-D warnings` gate and `scripts/check-fmt-complete.sh` | `cargo clippy -V; rustfmt -V` |
| `just` | `just check` is the only full aggregate gate | `just --version` |
| `cargo-deny` | `cargo deny check` is a `just check` step | `cargo-deny --version` |
| Lean at the **repo pin** (`lean-toolchain`) | the axiom ledger, `check-lean-gate.sh`, and export verification all shell out to a real `lean` | run the binary — see the two layouts below |
| `core.hooksPath=hooks` in the checkout | `hooks/commit-msg` stamps the `Agent:` trailer; `hooks/pre-push` is the pre-merge gate | `git config --get core.hooksPath` |
| `/nas3/data` mounted read-write | shared artifacts, logs, staged binaries | `[ -w /nas3/data ]` |
| `loginctl enable-linger` | transient units must survive ssh disconnect | `loginctl show-user $USER -p Linger` |

The Rust pin lives in `AXEYUM_NIGHTLY` in the provisioning script. The Lean pin
lives in `lean-toolchain` at the repo root and is enforced by
`scripts/install-pinned-lean.sh`, which refuses a toolchain string it does not
recognise and checks the elan installer's SHA-256.

> **The two dates are off by one, and that is correct.** The fleet pin
> `nightly-2026-07-12` reports `commit-date 2026-07-11`, because a nightly dated
> *N* is built from the commit of *N−1*. Verify alignment by comparing hosts to
> **each other**, not by matching the channel name to the commit date — the
> latter never matches and reads like a failed pin.

> There is deliberately **no `rust-toolchain.toml`** in the repository. Adding
> one would pin every contributor and CI job as a side effect of a fleet
> decision, and CI runs stable plus MSRV 1.88 rather than nightly. The fleet pin
> is therefore an *operational* requirement enforced by provisioning, not a
> repository-wide one. If that trade is ever revisited, it needs an ADR.

## Provisioning

One idempotent script. The canonical copy is tracked in the repository; a
byte-identical mirror sits on the shared mount so a host with no checkout (or no
network) can still be provisioned:

```sh
scripts/provision-fleet-host.sh                  # canonical, version-controlled
/nas3/data/axeyum/bin/provision-fleet-host.sh    # staged mirror, for isolated hosts
```

Update the tracked file and re-copy the mirror; do not edit the mirror. A script
that exists only on a NAS is the same defect as a measurement whose evidence
lives only on a NAS — unreviewable, and gone when the mount is.

It installs the pinned nightly and sets it default, installs `just` and
`cargo-deny` (preferring a staged binary, else building and then **publishing
the result back to `/nas3/data/axeyum/bin/`**), installs the repo-pinned Lean,
and sets `core.hooksPath`. Re-running it is safe; it reports what it found as
well as what it did, because a provisioning script that prints nothing is
indistinguishable from one that did nothing.

Run it under a bounded transient unit on remote hosts so it survives
disconnection — see the recipe in
[`../refactor-2026-08/00-parallel-work.md`](../refactor-2026-08/00-parallel-work.md).

### Network-isolated hosts

A host that reaches nothing external — no crates.io, no GitHub, no Lean release
host, not even the distribution archive — is provisioned entirely from
`/nas3/data/axeyum/bin/`. That is why the script **publishes every binary it
builds back to the stage**: the first host to build `just` and `cargo-deny` pays
for all the others. Such a host can run Python gates, ledger validation and
NAS-side IO; it cannot download a Rust toolchain or install Lean, so those must
be copied from a sibling.

`s2` was in exactly this state on 2026-08-16 and a reboot restored its network,
so it was provisioned normally in the end — but the staged path was still
exercised and still earned its keep: `just` and `cargo-deny` were **installed
from the stage rather than rebuilt**, which on a 4-core box is the difference
between seconds and a long compile.

**Do not conclude a host is isolated from one failed probe, and re-probe after a
reboot.** Three separate
lanes on 2026-08-14 reported a resource unavailable after a single empty result:
`which lean` returned nothing while Lean 4.30.0 sat installed under `~/.elan`
merely off `PATH`; `/data0` was called the scratch disk without noticing it was
root-owned on that box; and `s5` was reported unreachable while `ssh s5` worked.
Probe several endpoints, and confirm the probe covers the subject before
believing its zero.

## Which gate needs which capability

This is the mapping that decides where a lane can run. A lane whose work touches
the left column must run on a host that satisfies the right one.

| work | gate | needs |
|---|---|---|
| anything | `cargo test`, `cargo check` | pinned nightly |
| anything merged | `hooks/pre-push` (corpus regression + solver `--lib`) | pinned nightly, hooks installed |
| lint-visible change | `scripts/check-clippy-complete.sh` | pinned nightly + clippy |
| the full aggregate | `just check` | **everything**, including `just`, `cargo-deny`, Lean |
| kernel / library / export | `scripts/check-lean-gate.sh`, the Lean axiom ledger | **Lean at the repo pin** |
| linear arithmetic | the z3 differential fuzzes (`--features z3`) | `GITHUB_TOKEN` for the `z3/gh-release` fetch |
| ledgers, claims, facts | `validate-facts.py`, `validate-claims.py`, `check-links.sh` | Python only — runs anywhere |

The Lean row is the one that shapes scheduling. Two of the three roadmap strands
are Lean-bound, so before this baseline existed they both serialised onto the
single host that had a `lean` binary.

## Verification

Provisioning is not the claim; the probe is. The script ends with a verification
block that checks each **artifact by running it** and exits non-zero if any is
absent, so re-running it is also the audit:

```sh
/nas3/data/axeyum/bin/provision-fleet-host.sh   # exits 1 if anything is missing
```

**Lean has two valid layouts, and knowing only one produces a false green.** The
first version of this script reported `lean: installed` and exited 0 on three
hosts that had no Lean, because it trusted the installer's exit status and then
globbed the wrong path:

```sh
$HOME/.elan/toolchains/*/bin/lean              # elan's own default layout
$HOME/.elan/elan-home/toolchains/*/bin/lean    # install-pinned-lean.sh's root
```

Both occur in this fleet. Probe both, and then execute the binary:

```sh
b=$(ls $HOME/.elan/elan-home/toolchains/*/bin/lean \
       $HOME/.elan/toolchains/*/bin/lean 2>/dev/null | head -1)
[ -x "$b" ] && "$b" --version || echo MISSING
```

`command -v` measures `PATH`, not the machine, and an installer's exit status
measures that it ran, not that it produced anything. Check the artifact.
