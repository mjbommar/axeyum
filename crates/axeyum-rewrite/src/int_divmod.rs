//! Eliminate integer Euclidean `div`/`mod` (by a **constant** divisor) and `abs`
//! into linear constraints, so the *complete* `QF_LIA` simplex/DPLL path decides
//! them (sound for both `sat` and `unsat`) — not only the bounded, sat-only
//! integer bit-blaster.
//!
//! For `q = (div a c)` and `r = (mod a c)` with `c ≠ 0` a constant, the
//! Euclidean pair is the unique `(q, r)` with `a = c·q + r` and `0 ≤ r < |c|`.
//! Replacing the terms with fresh variables `q, r` and adding those linear
//! constraints is therefore an **exact, equisatisfiable** encoding (not a
//! relaxation): a simplex `unsat` transfers soundly to the original. `c = 0`
//! (div/mod by a constant zero) is **UNDERSPECIFIED** in SMT-LIB — any
//! total-function value — so it maps to a **fresh unconstrained variable**,
//! never a fixed convention: committing to `div a 0 = 0` would be a valid
//! *witness* but an unsound *unsat* (a formula sat under a different free value
//! would be wrongly refuted — the P0 regressed by `a946f925`, fixed by
//! `52f3b1d1`). `abs a` becomes a
//! fresh `v` with `v ≥ a ∧ v ≥ −a ∧ (v = a ∨ v = −a)` (i.e. `v = |a|`); the
//! disjunction needs the Boolean-structured (DPLL) integer path.
//!
//! # What the caller is told, and why (ADR-1730)
//!
//! The pass used to return a bare `Vec<TermId>`, which ADR-1721 §4 named the
//! sharpest remaining preprocessing gap: no split index, no fresh-variable map,
//! and — the load-bearing one — **no signal when the zero-divisor congruence
//! closure is skipped**.
//!
//! ADR-1730 establishes the direction of that skip. The congruence lemmas are
//! *added conjuncts*, so omitting them above [`MAX_CONGRUENCE_GROUPS`] only
//! ENLARGES the model set. Therefore:
//!
//! - **`unsat` transfers soundly at every group count.** The cap can never
//!   produce a wrong `unsat`.
//! - **`sat` is the direction that degrades.** Above the cap the `_/0`
//!   relaxation is no longer congruence-closed, so a satisfying assignment need
//!   not induce a total `div(·, 0)` function and need not be a model of the
//!   original.
//!
//! That direction is live: `dispatch_int_linear_refuters` runs the LIA simplex
//! and DPLL routes on the eliminated form and returns their verdict — `Sat`
//! included — as the answer for the ORIGINAL query. So the mode is now carried
//! on [`IntDivModElimination`] as [`ZeroDivisorCongruence`], whose
//! [`ZeroDivisorCongruence::sat_transfers`] is `false` exactly when the lemmas
//! were skipped.
//!
//! # The faithfulness witness
//!
//! [`witness_int_divmod`] is the crate's second independent faithfulness
//! witness, in the shape ADR-1721 §7 proved on
//! [`crate::witness_read_over_write`]: it does **not** re-run the transform (a
//! re-derivation is not a discharge — a stably-wrong producer reproduces
//! identically). It interprets both sides under sampled concrete assignments,
//! deriving each fresh symbol's value from the ground evaluator's value of the
//! ORIGINAL term it replaced, and checks the two halves this pass owes:
//!
//! - the **replacement** half — each rewritten assertion denotes what the
//!   original assertion denoted;
//! - the **strengthening** half — each added constraint is *true* under that
//!   extension, i.e. is a consequence of the original rather than a spurious
//!   restriction that could turn a satisfiable query `unsat`.

use std::collections::{BTreeMap, HashMap};

use axeyum_ir::{
    Assignment, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval_with_memo,
};

use crate::replace_subterms;

/// Whether the zero-divisor Ackermann congruence lemmas were emitted, and how
/// many groups the decision was taken over.
///
/// This is the mode ADR-1730 makes observable. The lemmas are added conjuncts,
/// so skipping them is a **relaxation**: `unsat` transfers in every variant and
/// only [`Self::sat_transfers`] distinguishes the two.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ZeroDivisorCongruence {
    /// No `div`/`mod` by a constant zero occurred, so there was nothing to
    /// close. Not a weaker mode: the elimination is exact.
    NotApplicable,
    /// Every pair of zero-divisor groups received its congruence lemma, so the
    /// `_/0` relaxation is congruence-closed and a `sat` of the output induces a
    /// genuine total `div(·, 0)` / `mod(·, 0)`.
    Closed {
        /// Distinct syntactic zero-divisor dividends.
        groups: usize,
        /// Congruence implications appended.
        lemmas: usize,
    },
    /// More than `limit` zero-divisor groups, so the `O(k²)` pairwise pass was
    /// skipped entirely and **no** lemma was emitted.
    ///
    /// The output is a strictly weaker relaxation than [`Self::Closed`] would
    /// have been. `unsat` still transfers soundly; a `sat` of the output is
    /// **not** necessarily a model of the original, because two zero-divisor
    /// terms with provably equal dividends may be given different free values.
    Omitted {
        /// Distinct syntactic zero-divisor dividends.
        groups: usize,
        /// The bound that was crossed ([`MAX_CONGRUENCE_GROUPS`]).
        limit: usize,
    },
}

impl ZeroDivisorCongruence {
    /// `true` when a `sat` of the eliminated form transfers to the original.
    ///
    /// `false` **only** for [`Self::Omitted`]. An `unsat` transfers in every
    /// variant, which is why there is no dual accessor: the relaxation only ever
    /// enlarges the model set (ADR-1730).
    #[must_use]
    pub fn sat_transfers(&self) -> bool {
        !matches!(self, Self::Omitted { .. })
    }

    /// Distinct syntactic zero-divisor dividends the decision was taken over.
    #[must_use]
    pub fn groups(&self) -> usize {
        match self {
            Self::NotApplicable => 0,
            Self::Closed { groups, .. } | Self::Omitted { groups, .. } => *groups,
        }
    }

    /// Congruence implications actually appended (`0` unless [`Self::Closed`]).
    #[must_use]
    pub fn lemmas(&self) -> usize {
        match self {
            Self::Closed { lemmas, .. } => *lemmas,
            Self::NotApplicable | Self::Omitted { .. } => 0,
        }
    }
}

/// The result of [`eliminate_int_divmod`]: the linearized assertions plus the
/// metadata a checker (and a caller deciding whether to trust a `sat`) needs.
///
/// `assertions()` is `originals() ++ added_constraints()` — the same "snapshot,
/// then extend" tail-slice discipline `arrays.rs`, `functions.rs` and
/// `int_blast.rs` already use, so the size of the added set is a subtraction
/// rather than a separately-maintained count (ADR-1721 §5).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntDivModElimination {
    assertions: Vec<TermId>,
    original_count: usize,
    replacements: Vec<(TermId, SymbolId)>,
    congruence: ZeroDivisorCongruence,
}

impl IntDivModElimination {
    /// The full linearized assertion list: rewritten originals, then the added
    /// constraints.
    #[must_use]
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// Consumes the elimination, yielding the assertion list.
    #[must_use]
    pub fn into_assertions(self) -> Vec<TermId> {
        self.assertions
    }

    /// Number of leading entries of [`Self::assertions`] that are rewritten
    /// originals; equal to the caller's input length.
    #[must_use]
    pub fn original_count(&self) -> usize {
        self.original_count
    }

    /// The rewritten originals, positionally aligned with the caller's input.
    #[must_use]
    pub fn rewritten(&self) -> &[TermId] {
        &self.assertions[..self.original_count]
    }

    /// The appended defining constraints (Euclidean pairs, `abs`, and the
    /// zero-divisor congruence lemmas). Their count is the subtraction
    /// `assertions().len() - original_count()`.
    #[must_use]
    pub fn added_constraints(&self) -> &[TermId] {
        &self.assertions[self.original_count..]
    }

    /// Each eliminated `div`/`mod`/`abs` term paired with the fresh symbol that
    /// replaced it, in deterministic order.
    ///
    /// This is the producer's own record, so a checker must not use it as its
    /// reference for *what the value should be* — only for *which symbol stands
    /// for which original term*. [`witness_int_divmod`] derives the value itself,
    /// from the ground evaluator on the original term.
    #[must_use]
    pub fn replacements(&self) -> &[(TermId, SymbolId)] {
        &self.replacements
    }

    /// Whether the pass replaced anything at all. `false` means the assertions
    /// were returned unchanged and there is nothing to witness.
    #[must_use]
    pub fn eliminated_any(&self) -> bool {
        !self.replacements.is_empty()
    }

    /// The zero-divisor congruence mode this run produced (ADR-1730).
    #[must_use]
    pub fn congruence(&self) -> ZeroDivisorCongruence {
        self.congruence
    }

    /// Rebuilds an elimination from its parts, or `None` when `original_count`
    /// exceeds `assertions.len()`.
    ///
    /// This exists for the checker side, not the producer side: a checker reading
    /// a serialized artifact must be able to reconstruct the object, and — the
    /// reason it is public today — an adversarial fixture must be able to present
    /// a **wrong** elimination to [`witness_int_divmod`]. A witness that cannot be
    /// handed a wrong input cannot be shown to reject one, and a checker that
    /// cannot fail is worse than no checker.
    #[must_use]
    pub fn from_parts(
        assertions: Vec<TermId>,
        original_count: usize,
        replacements: Vec<(TermId, SymbolId)>,
        congruence: ZeroDivisorCongruence,
    ) -> Option<Self> {
        if original_count > assertions.len() {
            return None;
        }
        Some(Self {
            assertions,
            original_count,
            replacements,
            congruence,
        })
    }
}

/// Rewrites every `div`/`mod`-by-constant and `abs` in `assertions` into fresh
/// variables plus their defining linear constraints, returning the linearized
/// assertion list (the originals with the terms substituted, followed by the new
/// constraints) together with the metadata described on
/// [`IntDivModElimination`]. If none are present, the input is returned
/// unchanged with [`IntDivModElimination::eliminated_any`] `false`.
///
/// Group iteration is over [`BTreeMap`]s, not hash maps: the fresh symbol names
/// (`!divmod_0`, `!divmod_1`, …) and the order of the appended constraints are
/// public output, and determinism is a public API promise.
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders (e.g. a fresh-symbol conflict).
pub fn eliminate_int_divmod(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<IntDivModElimination, IrError> {
    let mut collector = Collector::default();
    for &a in assertions {
        collector.scan(arena, a);
    }
    if collector.divmod.is_empty() && collector.abs.is_empty() {
        return Ok(IntDivModElimination {
            assertions: assertions.to_vec(),
            original_count: assertions.len(),
            replacements: Vec::new(),
            congruence: ZeroDivisorCongruence::NotApplicable,
        });
    }

    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut replacements: Vec<(TermId, SymbolId)> = Vec::new();
    let mut constraints: Vec<TermId> = Vec::new();
    let mut fresh = 0u32;
    // Zero-divisor groups retained for the pairwise Ackermann congruence pass.
    let mut zero_groups: Vec<ZeroGroup> = Vec::new();

    // div/mod groups, keyed by (dividend, constant divisor).
    for ((dividend, divisor), terms) in collector.divmod {
        if divisor == 0 {
            // SMT-LIB leaves `div`/`mod` by zero UNDERSPECIFIED (any total-function
            // value). Folding to a fixed convention (`div a 0 = 0`, `mod a 0 = a`)
            // is sound for a *witness* but produces a WRONG UNSAT — a solver could
            // refute a formula that is satisfiable by some *other* choice of the
            // free value (e.g. `775 < mod(0,0)` is sat, not `775 < 0`). So each
            // div/mod-by-zero *group* (keyed by dividend) becomes a fresh
            // unconstrained variable — the underspecified free value.
            //
            // The free values are nevertheless kept **congruent** across groups
            // (see the pairwise pass after this loop): `div`/`mod` are total binary
            // functions, so `div a 0` and `div b 0` must be EQUAL when `a = b`, for
            // whatever the underspecified zero-divisor value is. Without that, the
            // fresh-per-group relaxation is unsound for *sat*: two zero-divisor
            // terms whose dividends are provably equal could be assigned different
            // values, yielding a model that is not a real SMT model (a WRONG SAT —
            // the `div (mod (2x) 3) 0 ≠ div (mod (3−x) 3) 0` shape, unsat because
            // `2x ≡ 3−x (mod 3)`). One fresh var per group (not per term) already
            // shares within a group; the congruence lemmas share across groups.
            let has_div = !terms.div.is_empty();
            let has_mod = !terms.mod_.is_empty();
            let q0 = if has_div {
                let (sym, v) = fresh_int(arena, &mut fresh)?;
                for t in terms.div {
                    map.insert(t, v);
                    replacements.push((t, sym));
                }
                Some(v)
            } else {
                None
            };
            let r0 = if has_mod {
                let (sym, v) = fresh_int(arena, &mut fresh)?;
                for t in terms.mod_ {
                    map.insert(t, v);
                    replacements.push((t, sym));
                }
                Some(v)
            } else {
                None
            };
            zero_groups.push(ZeroGroup {
                dividend,
                q: q0,
                r: r0,
            });
            continue;
        }
        let (q_sym, q) = fresh_int(arena, &mut fresh)?;
        let (r_sym, r) = fresh_int(arena, &mut fresh)?;
        for t in terms.div {
            map.insert(t, q);
        }
        for t in terms.mod_ {
            map.insert(t, r);
        }
        // a = c·q + r
        let c_const = arena.int_const(divisor);
        // BOTH fresh variables are recorded against the term they denote, whether or
        // not the query mentioned it. The Euclidean constraints below name `q` and
        // `r` together, so a group containing only `mod a c` still puts `q` into the
        // output — and a fresh symbol standing for no recorded term is one a checker
        // can only sample blindly, which makes a perfectly sound constraint look
        // false. (Measured: the negative-divisor fixture failed on exactly that.)
        // The arena is hash-consed, so these are the query's own terms when it had
        // them and are otherwise inert nodes that nothing asserts.
        let div_term = arena.int_div(dividend, c_const)?;
        let mod_term = arena.int_mod(dividend, c_const)?;
        replacements.push((div_term, q_sym));
        replacements.push((mod_term, r_sym));
        let cq = arena.int_mul(c_const, q)?;
        let cq_r = arena.int_add(cq, r)?;
        constraints.push(arena.eq(dividend, cq_r)?);
        // 0 ≤ r ≤ |c| − 1
        let zero = arena.int_const(0);
        constraints.push(arena.int_le(zero, r)?);
        let hi = arena.int_const(abs_minus_one(divisor));
        constraints.push(arena.int_le(r, hi)?);
    }

    // abs groups, keyed by the operand.
    for (operand, terms) in collector.abs {
        let (v_sym, v) = fresh_int(arena, &mut fresh)?;
        for t in terms {
            map.insert(t, v);
            replacements.push((t, v_sym));
        }
        let neg = arena.int_neg(operand)?;
        constraints.push(arena.int_ge(v, operand)?); // v ≥ a
        constraints.push(arena.int_ge(v, neg)?); // v ≥ −a
        let v_eq_a = arena.eq(v, operand)?;
        let v_eq_neg = arena.eq(v, neg)?;
        constraints.push(arena.or(v_eq_a, v_eq_neg)?); // v = a ∨ v = −a
    }

    // Pairwise Ackermann congruence over the zero-divisor groups. `div`/`mod` are
    // total binary functions and the divisor is the constant `0` in every group, so
    // for groups `(a, 0)` and `(c, 0)` the lemma `a = c → v_a = v_c` (the div
    // quotients, and separately the mod remainders) is a valid consequence for
    // whatever the underspecified `_/0` value is. This makes the fresh-per-group
    // relaxation sound for *sat* (a satisfying assignment now induces a consistent
    // total `_/0` function — no wrong sat) while remaining monotone (the true model
    // satisfies every lemma, so no wrong unsat, and a lone `mod(0,0)` with no
    // congruence partner stays free — the P0 `775 < mod(0,0)` is still not refuted).
    // Bounded by `MAX_CONGRUENCE_GROUPS` to keep the pass `O(k²)` small.
    //
    // ADR-1730: crossing the bound is a RELAXATION (added conjuncts are dropped),
    // so it can never break `unsat` and it is `sat` that degrades. The branch taken
    // is reported to the caller as `ZeroDivisorCongruence` rather than being
    // silent, which is the whole point of the mode being here at all.
    let congruence = if zero_groups.is_empty() {
        ZeroDivisorCongruence::NotApplicable
    } else if zero_groups.len() <= MAX_CONGRUENCE_GROUPS {
        let before = constraints.len();
        for i in 0..zero_groups.len() {
            for j in (i + 1)..zero_groups.len() {
                let (gi, gj) = (&zero_groups[i], &zero_groups[j]);
                let same_dividend = arena.eq(gi.dividend, gj.dividend)?;
                if let (Some(qi), Some(qj)) = (gi.q, gj.q) {
                    let q_eq = arena.eq(qi, qj)?;
                    constraints.push(arena.implies(same_dividend, q_eq)?);
                }
                if let (Some(ri), Some(rj)) = (gi.r, gj.r) {
                    let r_eq = arena.eq(ri, rj)?;
                    constraints.push(arena.implies(same_dividend, r_eq)?);
                }
            }
        }
        ZeroDivisorCongruence::Closed {
            groups: zero_groups.len(),
            lemmas: constraints.len() - before,
        }
    } else {
        ZeroDivisorCongruence::Omitted {
            groups: zero_groups.len(),
            limit: MAX_CONGRUENCE_GROUPS,
        }
    };

    // Substitute the eliminated terms throughout the assertions and constraints
    // (nested div/mod inside a dividend or constraint are handled too).
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len() + constraints.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo)?);
    }
    for c in constraints {
        out.push(replace_subterms(arena, c, &map, &mut memo)?);
    }
    Ok(IntDivModElimination {
        assertions: out,
        original_count: assertions.len(),
        replacements,
        congruence,
    })
}

/// `|c| − 1` without the `i128::MIN` overflow `c.abs()` would take.
///
/// `i128::MIN.abs()` has no `i128` representation: it panics in a debug build and
/// wraps in a release build, which would emit the bound `0 ≤ r ≤ i128::MAX` — a
/// silent weakening rather than a reported error. The checked form gives the true
/// value for every reachable divisor (`|i128::MIN| − 1 = i128::MAX` exactly) and
/// cannot trap.
fn abs_minus_one(divisor: i128) -> i128 {
    divisor.checked_abs().map_or(i128::MAX, |c| c - 1)
}

fn fresh_int(arena: &mut TermArena, counter: &mut u32) -> Result<(SymbolId, TermId), IrError> {
    let name = format!("!divmod_{counter}");
    *counter += 1;
    let sym = arena.declare_internal(&name, Sort::Int)?;
    Ok((sym, arena.var(sym)))
}

/// A zero-divisor `div`/`mod` group: the (shared) dividend and the fresh
/// quotient / remainder variables (each `None` when the group has no such term).
/// Retained for the pairwise Ackermann congruence pass over `_/0` terms.
struct ZeroGroup {
    dividend: TermId,
    q: Option<TermId>,
    r: Option<TermId>,
}

/// Upper bound on the number of *distinct zero-divisor dividends* over which the
/// `O(k²)` eager Ackermann congruence lemmas are emitted. Below it (every realistic
/// shape — a formula with >48 syntactically-distinct `_/0` dividends is
/// pathological) the relaxation is fully congruence-closed, so a relaxation `sat`
/// is a genuine model. This is a strict soundness improvement over the prior
/// fresh-per-term relaxation (which was *not* congruence-closed at any size and
/// could report a wrong `sat`); the follow-up to make it unconditional is to route
/// `_/0` through the lazy-CEGAR UF congruence path. `unsat` transfers soundly at
/// every size (the relaxation only enlarges the model space).
///
/// Crossing it is reported as [`ZeroDivisorCongruence::Omitted`], and
/// [`ZeroDivisorCongruence::sat_transfers`] is the caller's guard (ADR-1730).
pub const MAX_CONGRUENCE_GROUPS: usize = 48;

#[derive(Default)]
struct DivModTerms {
    div: Vec<TermId>,
    mod_: Vec<TermId>,
}

#[derive(Default)]
struct Collector {
    seen: std::collections::HashSet<TermId>,
    divmod: BTreeMap<(TermId, i128), DivModTerms>,
    abs: BTreeMap<TermId, Vec<TermId>>,
}

impl Collector {
    /// Pre-order scan over the assertion DAG.
    ///
    /// The walk is an explicit stack, not native recursion: its depth would
    /// otherwise be the term DAG's *depth*, which an SMT-LIB source controls
    /// directly with a left-associated `(+ (+ (+ n 1) 1) 1)` spine. A recursive
    /// walk **aborted** the process with a stack overflow there — strictly worse
    /// than an `unknown`, since the solver cannot then report a first-class
    /// `unknown` and a harness reads the exit as a crash (`fcc8760d`).
    /// Arguments are pushed in reverse so nodes are still visited left to right,
    /// keeping the collected `Vec` order — and hence the rewrite — unchanged.
    fn scan(&mut self, arena: &TermArena, term: TermId) {
        let mut work = vec![term];
        while let Some(term) = work.pop() {
            if !self.seen.insert(term) {
                continue;
            }
            let TermNode::App { op, args } = arena.node(term) else {
                continue;
            };
            let (op, args) = (*op, args.clone());
            match op {
                Op::IntDiv | Op::IntMod => {
                    if let TermNode::IntConst(c) = arena.node(args[1]) {
                        let entry = self.divmod.entry((args[0], *c)).or_default();
                        if op == Op::IntDiv {
                            entry.div.push(term);
                        } else {
                            entry.mod_.push(term);
                        }
                    }
                }
                Op::IntAbs => self.abs.entry(args[0]).or_default().push(term),
                _ => {}
            }
            work.extend(args.iter().rev().copied());
        }
    }
}

// ---------------------------------------------------------------------------
// The faithfulness witness (ADR-1730, in the shape of ADR-1721 §7)
// ---------------------------------------------------------------------------
//
// `ArrayElimUnsatCertificate::recheck` used to discharge read-over-write by
// re-running `eliminate_arrays` and comparing the results, and ADR-1721 §2
// measured what that is worth: a stably-wrong producer reproduces identically, so
// every step compares wrong to wrong. `eliminate_int_divmod` had not even that —
// no artifact of any kind.
//
// This witness does not re-run the transform. For one concrete assignment it
// binds every fresh symbol to the GROUND EVALUATOR'S value of the original
// `div`/`mod`/`abs` term that symbol replaced — the exact model extension
// ADR-1730's Claim 1 constructs — and then interprets both sides. The reference
// side never enters this module's rewriting code at all.
//
// Two halves are checked because neither subsumes the other:
//
//   * the REPLACEMENT half compares each rewritten assertion against its
//     original. It is blind to a consistent renaming (swap which fresh symbol
//     receives the quotient and which the remainder, and `replacements()` swaps
//     with it, so both sides still agree);
//   * the STRENGTHENING half requires every appended constraint to be TRUE under
//     that extension. That is where a swapped pair shows up — `a = c·q + r` is
//     false when `q` holds `a mod c` — and it is the direction that turns a
//     satisfiable query `unsat`, so it is the one that matters most.
//
// A disagreement is a hard finding. A sample that cannot be built or evaluated is
// counted as *unavailable*, never silently treated as agreement: the same
// honest-hole discipline `PreconditionAudit::denotation_unavailable` uses.

/// Number of sampled assignments [`witness_int_divmod`] is normally given.
///
/// Sample 0 is the all-zero corner and sample 1 the all-negative-one corner (the
/// Euclidean corner where a naive truncating implementation diverges); the rest
/// are seeded pseudorandom, so the sequence is deterministic (a public API
/// promise) and reproducible across runs and hosts.
pub const INT_DIVMOD_WITNESS_SAMPLES: usize = 8;

/// Magnitude bound on a sampled integer.
///
/// Small on purpose: the appended constraints multiply a sampled quotient by the
/// query's own (arbitrary) constant divisor, and an `i128` overflow there is
/// reported by the evaluator as an error, which the witness must count as
/// *unavailable* rather than compare. Keeping the samples small keeps the
/// coverage real.
const SAMPLED_INT_BOUND: i128 = 33;

/// What the witness found wrong, and where.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntDivModFinding {
    /// A rewritten assertion does not denote what the original denoted: the
    /// **replacement** half is unfaithful, so both directions are broken.
    Replacement {
        /// Index of the sampled assignment.
        sample: usize,
        /// Index of the assertion, into the caller's `assertions` slice.
        assertion: usize,
        /// Value of the original, `div`/`mod`/`abs`-using assertion.
        original: Value,
        /// Value of its rewritten form.
        rewritten: Value,
    },
    /// An appended constraint is **false** under the canonical model extension,
    /// so it is not a consequence of the original: the **strengthening** half is
    /// unsound and the elimination can turn a satisfiable query `unsat`.
    Constraint {
        /// Index of the sampled assignment.
        sample: usize,
        /// Index into [`IntDivModElimination::added_constraints`].
        constraint: usize,
        /// What the constraint evaluated to (any non-`Bool(true)` value).
        value: Value,
    },
}

/// Outcome of the `eliminate_int_divmod` faithfulness witness.
///
/// `compared`, `constraints_checked` and `unavailable` partition the work the
/// witness attempted, so a caller can report coverage instead of assuming it.
/// `compared == 0` is **not** a pass and [`Self::is_faithful`] does not treat it
/// as one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntDivModWitness {
    /// `(sample, assertion)` pairs where both sides evaluated and agreed.
    pub compared: usize,
    /// `(sample, constraint)` pairs where the appended constraint evaluated to
    /// `true` under the canonical extension.
    pub constraints_checked: usize,
    /// `(sample, term)` pairs skipped: a sort the sampler cannot build, or an
    /// evaluator refusal (an arithmetic overflow past the `i128` reference
    /// range). A coverage hole, not a pass.
    pub unavailable: usize,
    /// The first finding, if any. Its presence is a soundness alarm.
    pub finding: Option<IntDivModFinding>,
}

impl IntDivModWitness {
    /// `true` only when at least one assertion pair was compared and nothing
    /// disagreed.
    ///
    /// Deliberately `false` for an all-`unavailable` run: a witness that examined
    /// nothing has not witnessed anything. `constraints_checked` deliberately
    /// does **not** substitute for `compared`: a query whose constraints all hold
    /// but whose assertions were never compared has not had its replacement half
    /// examined.
    #[must_use]
    pub fn is_faithful(&self) -> bool {
        self.finding.is_none() && self.compared > 0
    }
}

/// Witnesses that `elim` is faithful to integer `div`/`mod`/`abs` semantics, by
/// evaluating the original assertions, their rewritten forms, and every appended
/// constraint under the same concrete assignments.
///
/// `arena` must be the arena the elimination ran on — the fresh `!divmod_*`
/// symbols live there — and `assertions` the ORIGINAL assertions it was given,
/// the same pair [`eliminate_int_divmod`] was called with.
///
/// For each sample the witness binds every symbol in the arena, then **overrides
/// each fresh symbol with the ground evaluator's value of the original term it
/// replaced**. Under that extension it requires
/// `⟦assertions[k]⟧ = ⟦elim.originals()[k]⟧` and requires every entry of
/// [`IntDivModElimination::added_constraints`] to be `true`.
///
/// Returns `compared == 0` with no finding when `elim` replaced nothing, or when
/// `assertions` and `elim.originals()` have different lengths. Both are "nothing
/// to witness" rather than a pass, and [`IntDivModWitness::is_faithful`] reports
/// them as such.
#[must_use]
pub fn witness_int_divmod(
    arena: &TermArena,
    assertions: &[TermId],
    elim: &IntDivModElimination,
    samples: usize,
) -> IntDivModWitness {
    let mut witness = IntDivModWitness {
        compared: 0,
        constraints_checked: 0,
        unavailable: 0,
        finding: None,
    };
    let rewritten_forms = elim.rewritten();
    if !elim.eliminated_any() || rewritten_forms.len() != assertions.len() {
        return witness;
    }
    let constraints = elim.added_constraints();
    let per_sample = assertions.len() + constraints.len();

    for sample in 0..samples {
        let Some(mut assignment) = sample_assignment(arena, sample) else {
            witness.unavailable += per_sample;
            continue;
        };
        // One memo per sample, shared across every evaluation. The assignment is
        // fixed within a sample, so a subterm's value is too, and the three
        // populations (originals, rewritten forms, constraints) share most of
        // their structure. Populating the fresh bindings first is safe for the
        // memo: an ORIGINAL term never mentions a fresh symbol, so nothing
        // memoized during the derivation pass can be invalidated by it.
        let mut memo: HashMap<TermId, Value> = HashMap::new();
        if !bind_fresh_symbols(arena, elim.replacements(), &mut assignment, &mut memo) {
            witness.unavailable += per_sample;
            continue;
        }

        for (index, (&original, &rewritten)) in
            assertions.iter().zip(rewritten_forms.iter()).enumerate()
        {
            let (Ok(lhs), Ok(rhs)) = (
                eval_with_memo(arena, original, &assignment, &mut memo),
                eval_with_memo(arena, rewritten, &assignment, &mut memo),
            ) else {
                witness.unavailable += 1;
                continue;
            };
            witness.compared += 1;
            if lhs != rhs && witness.finding.is_none() {
                witness.finding = Some(IntDivModFinding::Replacement {
                    sample,
                    assertion: index,
                    original: lhs,
                    rewritten: rhs,
                });
            }
        }

        for (index, &constraint) in constraints.iter().enumerate() {
            let Ok(value) = eval_with_memo(arena, constraint, &assignment, &mut memo) else {
                witness.unavailable += 1;
                continue;
            };
            witness.constraints_checked += 1;
            if value != Value::Bool(true) && witness.finding.is_none() {
                witness.finding = Some(IntDivModFinding::Constraint {
                    sample,
                    constraint: index,
                    value,
                });
            }
        }
    }
    witness
}

/// Builds one sampled assignment over every symbol in `arena`, or `None` if any
/// symbol has a sort this witness cannot sample.
///
/// The fresh `!divmod_*` symbols are `Int`, so they get a sampled placeholder
/// here and are overwritten by [`bind_fresh_symbols`]. Overwriting is deliberate:
/// a fresh symbol whose original term fails to evaluate must leave the whole
/// sample *unavailable* rather than silently keep an unrelated sampled value.
fn sample_assignment(arena: &TermArena, sample: usize) -> Option<Assignment> {
    let mut assignment = Assignment::new();
    let mut counter = 0u64;
    for (symbol, _name, sort) in arena.symbols() {
        counter += 1;
        let seed = mix(sample as u64, counter);
        let value = match sort {
            Sort::Bool => Value::Bool(sample_bit(sample, seed)),
            Sort::Int => Value::Int(sample_int(sample, seed)),
            Sort::BitVec(width) if width <= 128 => Value::Bv {
                width,
                value: sample_bits(sample, seed, width),
            },
            _ => return None,
        };
        assignment.set(symbol, value);
    }
    Some(assignment)
}

/// Binds each fresh symbol to the ground evaluator's value of the original term
/// it replaced — the canonical model extension.
///
/// The value comes from evaluating the ORIGINAL `div`/`mod`/`abs` term, which
/// the evaluator decides with its own integer semantics; nothing here consults
/// the constraints the pass emitted, so a wrong constraint cannot make itself
/// true. Returns `false` when any original term fails to evaluate, which makes
/// the whole sample *unavailable*.
fn bind_fresh_symbols(
    arena: &TermArena,
    replacements: &[(TermId, SymbolId)],
    assignment: &mut Assignment,
    memo: &mut HashMap<TermId, Value>,
) -> bool {
    for &(original, fresh) in replacements {
        let Ok(value) = eval_with_memo(arena, original, assignment, memo) else {
            return false;
        };
        assignment.set(fresh, value);
    }
    true
}

/// A sampled integer in `[-SAMPLED_INT_BOUND, SAMPLED_INT_BOUND]`, with sample 0
/// pinned to `0` and sample 1 to `-1` (the Euclidean corner).
fn sample_int(sample: usize, seed: u64) -> i128 {
    match sample {
        0 => 0,
        1 => -1,
        _ => {
            let span = (SAMPLED_INT_BOUND * 2 + 1) as u64;
            i128::from(seed % span) - SAMPLED_INT_BOUND
        }
    }
}

/// A sampled bit, with sample 0 the all-zero corner and sample 1 the all-ones
/// corner.
fn sample_bit(sample: usize, seed: u64) -> bool {
    match sample {
        0 => false,
        1 => true,
        _ => seed & 1 == 1,
    }
}

/// Sampled `width` bits, with sample 0 all-zero and sample 1 all-ones.
fn sample_bits(sample: usize, seed: u64, width: u32) -> u128 {
    let mask = if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    match sample {
        0 => 0,
        1 => mask,
        _ => (u128::from(mix(seed, 1)) | (u128::from(mix(seed, 2)) << 64)) & mask,
    }
}

/// `SplitMix64` finalizer over two inputs: a deterministic, well-mixed sample
/// seed that depends on nothing outside its arguments.
fn mix(a: u64, b: u64) -> u64 {
    let mut z = a
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .wrapping_add(b.wrapping_mul(0xbf58_476d_1ce4_e5b9));
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}
