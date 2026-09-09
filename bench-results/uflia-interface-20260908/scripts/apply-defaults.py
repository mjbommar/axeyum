#!/usr/bin/env python3
"""Land the two defaults the 2026-09-08 measurement chose.

Kept as a script rather than applied by hand so the diff is one reviewable
object and so re-applying it after a merge cannot half-apply. Every anchor is
asserted to occur exactly once; a moved anchor aborts rather than editing the
wrong place.
"""

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]


def sub(path, old, new, count=1):
    p = ROOT / path
    s = p.read_text()
    assert s.count(old) == count, f"{path}: anchor occurs {s.count(old)} times, expected {count}"
    p.write_text(s.replace(old, new))


# 1. The Boolean-layer theory-atom ceiling.
sub(
    "crates/axeyum-solver/src/uflia_online.rs",
    """/// Hard ceiling on the number of distinct theory atoms in the Boolean skeleton.
/// Above it the layer declines (the propositional search space is too large to
/// enumerate soundly within budget).
///
/// This is deliberately above the current `QF_AUFLIA` fair-slice frontier
/// (`bug330` has 339 atoms) so the deadline-aware CDCL(T) spine, not admission,
/// decides whether that scalar abstraction is tractable.
const MAX_BOOLEAN_ATOMS: usize = 512;""",
    """/// Hard ceiling on the number of distinct theory atoms in the Boolean skeleton.
/// Above it the layer declines (the propositional search space is too large to
/// enumerate soundly within budget).
///
/// The intent has always been that **the deadline-aware CDCL(T) spine, not
/// admission, decides whether a scalar abstraction is tractable** — the previous
/// value, 512, was set above the `QF_AUFLIA` fair-slice frontier (`bug330`, 339
/// atoms) for exactly that reason. It had never been measured against a
/// population, and on 2026-09-08 it was:
///
/// - On the committed 200-file `QF_UFLIA` division list, this ceiling is the
///   **last thing 27 of the 50 files we lose** report, at atom counts of
///   **595 to 2,972** — one to six times the ceiling — each refused in
///   0.1–0.3 ms while the budget went to routes that could not decide them.
/// - Raised, the route **decides** files at 595–1,442 atoms and decides none
///   above 1,442 within a 24 s budget: above that the deadline stops it, which
///   is the behaviour the ceiling's own rationale asks for.
/// - Raised, it costs **nothing** on the same list: the arm that raised it
///   gained ten files and lost none, with zero disagreements against `cvc5`'s
///   committed verdicts.
///
/// So the value is now `8192` — the value the winning arm was measured at, and
/// above the whole observed range, so on this population admission no longer
/// decides anything and the deadline does. It is a ceiling on a
/// **deadline-aware** search (`CdclT::solve` carries the caller's deadline and
/// every route below re-derives it); the encoding stays bounded independently by
/// [`MAX_BOOLEAN_CLAUSES`], and the interface split by
/// [`crate::uflia_interface::MAX_INTERFACE_PAIRS`], so raising this one does not
/// uncap the others.
///
/// ADR-1801. Measurement:
/// `docs/research/12-performance/uflia-interface-caps-2026-09-08.md`.
const MAX_BOOLEAN_ATOMS: usize = 8192;""",
)

# 2. The opaque-application ceiling is NOT raised, and the isolation arm is why.
#    Raising the general ceiling ALONE decides the same ten files, and no run in
#    this lane — base, raised, or filtered — ever reported an opaque-ceiling
#    decline, so on this population the constant never fires. Its own doc warns
#    that the opaque path is the one place on this route where construction is
#    not deadline-aware; raising a bound that buys nothing measured and guards
#    the least deadline-aware code would be a change with a cost and no benefit.

# 3. The interface-pair proposal policy.
sub(
    "crates/axeyum-solver/src/uflia_interface.rs",
    """    /// Every unordered pair of atomic integer terms with at least one EUF
    /// endpoint, and a **decline** when there are more than the ceiling. The
    /// historical behaviour, kept as a named arm so the change is measured
    /// against it rather than only remembered.
    #[default]
    All,
    /// cvc5's care graph: keep only a pair that could fire a congruence —
    /// corresponding arguments of two applications of the same function at the
    /// same arity. Still declines when the filtered set is over the ceiling.
    CareGraph,
    /// The care graph, and when it is still over the ceiling, keep the first
    /// [`MAX_INTERFACE_PAIRS`] in the deterministic care order instead of
    /// declining. Sound in both directions (see the module docs); incomplete by
    /// construction, which is the trade being measured.
    CareGraphTruncate,""",
    """    /// Every unordered pair of atomic integer terms with at least one EUF
    /// endpoint, and a **decline** when there are more than the ceiling. The
    /// historical behaviour, kept as a named arm so the change is measured
    /// against it rather than only remembered.
    All,
    /// cvc5's care graph: keep only a pair that could fire a congruence —
    /// corresponding arguments of two applications of the same function at the
    /// same arity. Still declines when the filtered set is over the ceiling.
    CareGraph,
    /// The care graph, and when it is still over the ceiling, keep the first
    /// [`MAX_INTERFACE_PAIRS`] in the deterministic care order instead of
    /// declining. Sound in both directions (see the module docs); incomplete by
    /// construction, which is the trade being made.
    ///
    /// **The default since 2026-09-08 (ADR-1801).** On the committed 200-file
    /// `QF_UFLIA` list, with the Boolean-layer atom ceiling also raised, this arm
    /// decides 31 of the 50 files we lose against 14 for `All`, and loses none.
    /// On its own — atom ceiling unchanged — it decides one, because the atom
    /// ceiling refuses those queries before the interface layer is reached; the
    /// two changes are not independent and neither is sufficient.
    #[default]
    CareGraphTruncate,""",
)

sub(
    "crates/axeyum-solver/src/uflia_interface.rs",
    """    *RESOLVED.get_or_init(
        || match std::env::var("AXEYUM_UFLIA_INTERFACE_PAIRS").as_deref() {
            Ok("care") => UfliaInterfacePolicy::CareGraph,
            Ok("care-truncate") => UfliaInterfacePolicy::CareGraphTruncate,
            _ => UfliaInterfacePolicy::All,
        },
    )""",
    """    *RESOLVED.get_or_init(
        || match std::env::var("AXEYUM_UFLIA_INTERFACE_PAIRS").as_deref() {
            Ok("all") => UfliaInterfacePolicy::All,
            Ok("care") => UfliaInterfacePolicy::CareGraph,
            _ => UfliaInterfacePolicy::CareGraphTruncate,
        },
    )""",
)

sub(
    "crates/axeyum-solver/src/uflia_interface.rs",
    """        assert_eq!(UfliaInterfacePolicy::default(), UfliaInterfacePolicy::All);""",
    """        assert_eq!(
            UfliaInterfacePolicy::default(),
            UfliaInterfacePolicy::CareGraphTruncate,
            "the shipped default is the arm ADR-1801 measured, not the historical one"
        );""",
)

sub(
    "crates/axeyum-solver/src/uflia_interface.rs",
    """    fn policy_names_round_trip_and_the_default_is_the_historical_arm() {""",
    """    fn policy_names_round_trip_and_the_default_is_the_measured_arm() {""",
)

sub(
    "crates/axeyum-solver/src/uflia_interface.rs",
    """/// Which interface pairs the `QF_UFLIA` online combination proposes, and what it
/// does when the proposal exceeds the split ceiling.
///
/// Selected by `AXEYUM_UFLIA_INTERFACE_PAIRS` or, in-process, by
/// [`UfliaInterfacePolicyGuard`], so the arms can be A/B-ed on ONE binary rather
/// than on one build per arm.""",
    """/// Which interface pairs the `QF_UFLIA` online combination proposes, and what it
/// does when the proposal exceeds the split ceiling.
///
/// Selected by `AXEYUM_UFLIA_INTERFACE_PAIRS` (`all` / `care` / `care-truncate`)
/// or, in-process, by [`UfliaInterfacePolicyGuard`], so the arms can be A/B-ed on
/// ONE binary rather than on one build per arm. An unset or unrecognised value is
/// the default; `all` names the historical behaviour explicitly, so a bisect
/// against it is one environment variable rather than a build.""",
)

print("applied")
sys.exit(0)
