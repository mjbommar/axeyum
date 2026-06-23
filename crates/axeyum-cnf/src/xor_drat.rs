//! Per-query DRAT refutation for an XOR-Gaussian UNSAT.
//!
//! This module narrows the lowest-assurance reduction in the stack: an
//! XOR (GF(2)) system found unsatisfiable by Gaussian elimination
//! ([`IncrementalXorMatrix`](crate::IncrementalXorMatrix)) is *search-only* —
//! the bare "UNSAT" carries no independently checkable certificate, so a wrong
//! XOR-UNSAT would be silently trusted. This module turns that into a
//! **per-query DRAT proof**: given the subset `S` of original XOR constraints
//! whose GF(2)-sum is the inconsistent row `0 = 1` (the Gaussian-elimination
//! certificate the matrix already tracks as a conflict *reason*), it emits a
//! DRAT refutation over the CNF encoding of those constraints, and that proof is
//! validated by the independent in-tree checker [`check_drat`](crate::check_drat).
//! A wrong XOR-UNSAT then surfaces as a `check_drat` rejection instead of a
//! trusted wrong answer.
//!
//! # The certificate
//!
//! A GF(2) Gaussian elimination that reaches `0 = 1` does so by XOR-summing a
//! subset `S = [c_0, …, c_{m-1}]` of the original constraints. Each constraint
//! `c_i = (vars_i, b_i)` asserts `(⊕ of vars_i) = b_i`. That `S` is exactly the
//! conflict *reason* an [`IncrementalXorMatrix`](crate::IncrementalXorMatrix)
//! conflict carries (its provenance `components` and the per-row source
//! tracking); the sum `⊕ S` has an **empty** left-hand side and parity `1`,
//! i.e. the contradiction `0 = 1`. The CNF encoding of `S` is therefore
//! unsatisfiable, and this module re-derives the empty clause from it.
//!
//! # The CNF encoding (shared with [`xor_propagate`](crate::xor_propagate))
//!
//! An XOR constraint `(⊕ of v_0..v_{k-1}) = b` is encoded by the `2^(k-1)`
//! clauses that forbid every assignment of those `k` variables whose parity is
//! `¬b`: for each such forbidden assignment, a clause with `v_j` negated iff its
//! bit is `1`. This is byte-identical to the encoding the `xor_propagate` tests
//! exercise and to what [`extract_xors`](crate::extract_xors) recognizes, so the
//! DRAT base CNF matches the formula the rest of the XOR path reasons over.
//!
//! # The DRAT proof (mirroring `CryptoMiniSat`'s Gauss → proof)
//!
//! `CryptoMiniSat` emits a proof for Gaussian elimination by recording, for each
//! reduced row, the subset of original XOR constraints that were summed to form
//! it (`gaussian.cpp`: `xor_reasons[row]`, the `reason_mat` chain, the FRAT
//! `implyclfromx`/`addx` records carrying each row's `xid` provenance). Its FRAT
//! format has *native XOR clauses*; our independent [`check_drat`](crate::check_drat)
//! is a plain RUP/RAT checker over ordinary CNF, so the proof must be ordinary
//! clause additions.
//!
//! The provenance subset `S` is what makes this tractable: rather than refute the
//! whole formula, we refute only `CNF(S)` — the encoding of the few constraints
//! the Gaussian elimination actually summed. `CNF(S)` is unsatisfiable (its XOR
//! constraints sum to `0 = 1`), and we obtain its DRAT proof from the in-tree
//! proof-producing CDCL core [`solve_with_drat_proof`](crate::solve_with_drat_proof)
//! (1-UIP conflict analysis, emits DRAT, ADR-0012). That proof is then handed,
//! together with `CNF(S)`, to the *independent* checker
//! [`check_drat`](crate::check_drat) — a different implementation — so the
//! certificate is validated end to end by a component that shares no code with
//! the producer. (A direct hand-rolled "sum of rows" resolution chain is *not*
//! RUP-checkable in general once shared variables cancel — e.g. two width-2 rows
//! summing straight to the empty clause give a non-RUP step — which is exactly
//! why we delegate to the CDCL core, whose 1-UIP learning materializes the
//! intermediate resolvents the empty-clause derivation needs.)
//!
//! Soundness rests only on `check_drat`: even if the CDCL core or `S` were buggy,
//! a proof that does not genuinely refute `CNF(S)` is *rejected*, so no wrong
//! XOR-UNSAT can be certified. And `CNF(S)` is built from the *original* XOR
//! constraints with the same parity encoding the rest of the XOR path uses, so a
//! refutation of `CNF(S)` is a refutation of (a subset of) the real formula.
//!
//! # Width boundary (honest scope)
//!
//! A width-`k` constraint encodes to `2^(k-1)` clauses, so per-row width drives
//! the base-CNF size. This module refuses (returns `None`) when any constraint in
//! `S` exceeds [`MAX_XOR_WIDTH`] variables. Small XOR systems (the `k ≤ 2`
//! width-2 systems the tests certify, and moderate widths within the cap) get a
//! checked certificate now; wider systems decline cleanly rather than build an
//! exponential clause set. Declining is *sound*: it produces no false
//! certificate, it simply leaves that query at the prior search-only assurance.

use crate::{
    CnfClause, CnfFormula, CnfLit, CnfVar, DratStep, ProofSolveOutcome, solve_with_drat_proof,
};

/// Maximum XOR width (variables in any single constraint of the conflict subset)
/// for which a DRAT certificate is emitted. A width-`k` constraint encodes to
/// `2^(k-1)` clauses, so this bounds per-constraint clause blow-up in the base
/// CNF. Above it, [`xor_gauss_drat_refutation`] declines (returns `None`) rather
/// than build an exponential clause set — declining is sound (no false
/// certificate).
pub const MAX_XOR_WIDTH: usize = 16;

/// A checkable DRAT refutation of an XOR-Gaussian UNSAT.
///
/// Holds the base CNF (the encoding of the conflict subset `S`) and a DRAT proof
/// that derives the empty clause from it. Feed both to
/// [`check_drat`](crate::check_drat): a valid certificate returns `Ok(true)`.
#[derive(Debug, Clone)]
pub struct XorGaussRefutation {
    /// CNF encoding of the conflict subset `S` (the base the proof refutes).
    formula: CnfFormula,
    /// DRAT proof deriving the empty clause from [`Self::formula`].
    proof: Vec<DratStep>,
}

impl XorGaussRefutation {
    /// The base CNF: the encoding of the conflict subset `S`.
    #[must_use]
    pub fn formula(&self) -> &CnfFormula {
        &self.formula
    }

    /// The DRAT proof deriving the empty clause from [`Self::formula`].
    #[must_use]
    pub fn proof(&self) -> &[DratStep] {
        &self.proof
    }

    /// Number of clause-addition steps in the proof (excludes deletions). A
    /// genuine refutation has at least one (the final empty clause), so this is
    /// the non-triviality signal for tests.
    #[must_use]
    pub fn addition_count(&self) -> usize {
        self.proof
            .iter()
            .filter(|step| matches!(step, DratStep::Add(_)))
            .count()
    }
}

/// A single XOR constraint: the variables `vars` and the right-hand-side parity
/// `b`, asserting `(⊕ of vars) = b`. The same `(Vec<usize>, bool)` shape
/// [`IncrementalXorMatrix`](crate::IncrementalXorMatrix) and
/// [`Gf2System`](crate::Gf2System) accept.
type XorConstraint = (Vec<usize>, bool);

/// Builds a DRAT refutation for an XOR-Gaussian UNSAT from the conflict subset.
///
/// `constraints` are the original XOR constraints; `subset` indexes the subset
/// `S ⊆ constraints` whose GF(2)-sum is the inconsistent row `0 = 1` (the
/// conflict reason an [`IncrementalXorMatrix`](crate::IncrementalXorMatrix)
/// conflict tracks). The result's [`XorGaussRefutation::formula`] is the CNF
/// encoding of `S` and [`XorGaussRefutation::proof`] is a DRAT proof of its
/// unsatisfiability, accepted by [`check_drat`](crate::check_drat).
///
/// Returns `None` (declines, soundly) when:
///
/// * `subset` is empty, or any index is out of range;
/// * the GF(2)-sum of the subset is **not** the contradiction `0 = 1` (so the
///   subset is not actually a refutation — we never fabricate one);
/// * any constraint in `S` exceeds [`MAX_XOR_WIDTH`] (the clause blow-up
///   boundary);
/// * a variable index does not fit the CNF variable space; or
/// * the proof-producing CDCL core does not return `unsat` for `CNF(S)` (it
///   never will for a genuine `0 = 1` subset, but declining is the safe response
///   to any unexpected `sat`/undecided verdict — we never emit an unchecked
///   proof).
///
/// Declining never produces a false certificate: the caller keeps its prior
/// (search-only) assurance for that query.
#[must_use]
pub fn xor_gauss_drat_refutation(
    constraints: &[XorConstraint],
    subset: &[usize],
    num_vars: usize,
) -> Option<XorGaussRefutation> {
    if subset.is_empty() {
        return None;
    }
    // Collect S, rejecting out-of-range indices and over-wide constraints.
    let mut s: Vec<XorConstraint> = Vec::with_capacity(subset.len());
    for &idx in subset {
        let (vars, parity) = constraints.get(idx)?;
        let canon = canonical_support(vars);
        if canon.len() > MAX_XOR_WIDTH {
            return None;
        }
        s.push((canon, *parity));
    }

    // Verify the subset truly sums to `0 = 1`. This is the soundness gate: a
    // subset whose sum is anything else is not a refutation, so we decline
    // rather than build a base CNF for it. (The DRAT check would also reject any
    // proof of a satisfiable CNF, but refusing up front means we never even
    // claim a certificate.)
    let (sum_support, sum_parity) = gf2_sum(&s);
    if !sum_support.is_empty() || !sum_parity {
        return None;
    }

    // Base CNF: the parity encoding of every constraint in S.
    let mut formula = CnfFormula::new(num_vars);
    for (vars, parity) in &s {
        for clause in xor_constraint_clauses(vars, *parity, num_vars)? {
            formula.add_clause(clause).ok()?;
        }
    }

    // The DRAT proof: refute CNF(S) with the in-tree proof-producing CDCL core.
    // A genuine `0 = 1` subset makes CNF(S) unsatisfiable, so the core returns a
    // DRAT proof; the independent `check_drat` then validates it. Any other
    // verdict (sat / undecided) means we decline rather than emit anything
    // unchecked — soundness rides entirely on `check_drat` accepting the result.
    match solve_with_drat_proof(&formula) {
        ProofSolveOutcome::Unsat(proof) => Some(XorGaussRefutation { formula, proof }),
        ProofSolveOutcome::Sat(_)
        | ProofSolveOutcome::ResourceOut
        | ProofSolveOutcome::Interrupted => None,
    }
}

/// The canonical support of a constraint: variables sorted ascending with
/// duplicate occurrences cancelled by parity (a variable appearing an even
/// number of times drops out, as GF(2) demands).
fn canonical_support(vars: &[usize]) -> Vec<usize> {
    let mut counts: Vec<usize> = vars.to_vec();
    counts.sort_unstable();
    let mut out = Vec::with_capacity(counts.len());
    let mut i = 0;
    while i < counts.len() {
        let v = counts[i];
        let mut run = 0;
        while i < counts.len() && counts[i] == v {
            run += 1;
            i += 1;
        }
        if run % 2 == 1 {
            out.push(v);
        }
    }
    out
}

/// XOR-adds two canonical constraints, returning the canonical sum `(support,
/// parity)`. The support is the symmetric difference; the parity is the XOR.
fn xor_constraints(
    a_support: &[usize],
    a_parity: bool,
    b_support: &[usize],
    b_parity: bool,
) -> (Vec<usize>, bool) {
    let mut support = Vec::with_capacity(a_support.len() + b_support.len());
    let (mut i, mut j) = (0, 0);
    while i < a_support.len() && j < b_support.len() {
        match a_support[i].cmp(&b_support[j]) {
            std::cmp::Ordering::Less => {
                support.push(a_support[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                support.push(b_support[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                // Shared variable cancels in GF(2).
                i += 1;
                j += 1;
            }
        }
    }
    support.extend_from_slice(&a_support[i..]);
    support.extend_from_slice(&b_support[j..]);
    (support, a_parity ^ b_parity)
}

/// The GF(2)-sum of all constraints in `s`, as a canonical `(support, parity)`.
fn gf2_sum(s: &[XorConstraint]) -> (Vec<usize>, bool) {
    let mut support: Vec<usize> = Vec::new();
    let mut parity = false;
    for (vars, p) in s {
        let (next, np) = xor_constraints(&support, parity, vars, *p);
        support = next;
        parity = np;
    }
    (support, parity)
}

/// The CNF clauses encoding `(⊕ of vars) = parity` (the parity encoding shared
/// with [`xor_propagate`](crate::xor_propagate)).
///
/// For a width-`k` support, emits the `2^(k-1)` clauses forbidding every
/// assignment of those variables whose parity is `¬parity`. An *empty* support
/// with `parity == true` is the contradiction `0 = 1`, encoded as the single
/// empty clause; an empty support with `parity == false` is the tautology
/// `0 = 0`, encoded as no clauses. Returns `None` if a variable does not fit
/// the CNF variable space.
fn xor_constraint_clauses(vars: &[usize], parity: bool, num_vars: usize) -> Option<Vec<CnfClause>> {
    let k = vars.len();
    if k == 0 {
        // 0 = 1 ⇒ the empty clause; 0 = 0 ⇒ no clause.
        return Some(if parity {
            vec![CnfClause::new(Vec::new())]
        } else {
            Vec::new()
        });
    }
    let k_u32 = u32::try_from(k).ok()?;
    let target_parity = !parity;
    let mut clauses = Vec::new();
    for assign in 0u32..(1u32 << k_u32) {
        if (assign.count_ones() & 1 == 1) != target_parity {
            continue;
        }
        let mut lits = Vec::with_capacity(k);
        for (j, &v) in vars.iter().enumerate() {
            if v >= num_vars {
                return None;
            }
            let var = CnfVar::new(v).ok()?;
            let lit = CnfLit::positive(var);
            // The clause forbids `assign`, so `v_j` is negated iff its bit is 1.
            lits.push(if (assign >> j) & 1 == 1 {
                lit.negated()
            } else {
                lit
            });
        }
        clauses.push(CnfClause::new(lits));
    }
    Some(clauses)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check_drat;

    /// Brute-force: is the XOR system over `num_vars` variables UNSAT?
    fn xor_system_is_unsat(s: &[XorConstraint], num_vars: usize) -> bool {
        assert!(num_vars <= 16, "brute force only for small systems");
        for assign in 0u32..(1u32 << num_vars) {
            let sat = s.iter().all(|(vars, parity)| {
                let p = vars
                    .iter()
                    .fold(false, |acc, &v| acc ^ ((assign >> v) & 1 == 1));
                p == *parity
            });
            if sat {
                return false;
            }
        }
        true
    }

    #[test]
    fn xor_gauss_unsat_emits_checkable_drat() {
        // The headline 3-variable system: a⊕b=1, b⊕c=1, a⊕c=1.
        // Sum of all three: (a⊕b)⊕(b⊕c)⊕(a⊕c) = 0 on the left, 1⊕1⊕1 = 1 on the
        // right ⇒ the inconsistent row 0 = 1.
        let constraints: Vec<XorConstraint> =
            vec![(vec![0, 1], true), (vec![1, 2], true), (vec![0, 2], true)];
        let num_vars = 3;
        assert!(
            xor_system_is_unsat(&constraints, num_vars),
            "guard: the system must truly be UNSAT"
        );

        let refutation = xor_gauss_drat_refutation(&constraints, &[0, 1, 2], num_vars)
            .expect("a 0 = 1 subset must produce a refutation");

        // check_drat ACCEPTS over the XOR-CNF and derives the empty clause.
        assert_eq!(
            check_drat(refutation.formula(), refutation.proof()),
            Ok(true),
            "independent check_drat must accept the XOR-Gauss refutation"
        );

        // Non-trivial: more than just the empty clause was derived (the
        // accumulator chain), and the proof genuinely reaches the empty clause.
        assert!(
            refutation.addition_count() >= 2,
            "proof must be a real chain, not a single empty-clause assertion: {} additions",
            refutation.addition_count()
        );
        assert!(
            refutation
                .proof()
                .iter()
                .any(|step| matches!(step, DratStep::Add(lits) if lits.is_empty())),
            "proof must reach the empty clause"
        );
    }

    #[test]
    fn xor_gauss_drat_tamper_is_rejected() {
        // Same UNSAT system, then corrupt one emitted clause: check_drat must
        // REJECT (the checker has teeth).
        let constraints: Vec<XorConstraint> =
            vec![(vec![0, 1], true), (vec![1, 2], true), (vec![0, 2], true)];
        let num_vars = 3;
        let refutation = xor_gauss_drat_refutation(&constraints, &[0, 1, 2], num_vars).unwrap();

        // Tamper 1: a premature empty clause as the SOLE step. The base CNF is
        // six width-2 clauses; nothing unit-propagates from the empty
        // assignment, so the empty clause is NOT RUP w.r.t. the base. A checker
        // with teeth must reject this unjustified jump to the contradiction.
        let premature = vec![DratStep::Add(Vec::new())];
        assert!(
            matches!(
                check_drat(refutation.formula(), &premature),
                Err(crate::DratError::StepNotVerified { .. })
            ),
            "a premature empty clause (no propagation justifies it) must be REJECTED"
        );

        // Tamper 2: corrupt the step that derives the empty clause by replacing
        // the WHOLE valid prefix with just that final unjustified empty-clause
        // addition stripped of its support — same as tamper 1 but proving the
        // valid proof's last step is load-bearing: drop every learned step and
        // keep only the empty clause.
        let only_empty: Vec<DratStep> = refutation
            .proof()
            .iter()
            .filter(|s| matches!(s, DratStep::Add(lits) if lits.is_empty()))
            .cloned()
            .collect();
        assert!(
            matches!(
                check_drat(refutation.formula(), &only_empty),
                Err(crate::DratError::StepNotVerified { .. })
            ),
            "the empty clause without its derived-clause prefix must be REJECTED"
        );

        // Tamper 3: drop the empty-clause step entirely — every remaining step
        // still verifies, but the proof no longer derives the empty clause, so
        // check_drat reports UNSAT *unestablished* rather than confirmed.
        let mut dropped = refutation.proof().to_vec();
        dropped.retain(|s| !matches!(s, DratStep::Add(lits) if lits.is_empty()));
        assert_eq!(
            check_drat(refutation.formula(), &dropped),
            Ok(false),
            "dropping the empty clause must leave UNSAT unestablished"
        );
    }

    #[test]
    fn sat_xor_system_declines_no_false_proof() {
        // A satisfiable XOR system: a⊕b=1, b⊕c=0. Its full sum is a⊕c=1, NOT
        // 0 = 1, so the emitter must DECLINE for any subset — never a false proof.
        let constraints: Vec<XorConstraint> = vec![(vec![0, 1], true), (vec![1, 2], false)];
        let num_vars = 3;
        assert!(
            !xor_system_is_unsat(&constraints, num_vars),
            "guard: the system is satisfiable"
        );
        // The whole-set subset does not sum to 0 = 1.
        assert!(xor_gauss_drat_refutation(&constraints, &[0, 1], num_vars).is_none());
        // Any singleton subset is a single constraint, not a contradiction.
        assert!(xor_gauss_drat_refutation(&constraints, &[0], num_vars).is_none());
        assert!(xor_gauss_drat_refutation(&constraints, &[1], num_vars).is_none());
    }

    #[test]
    fn width2_pair_contradiction_certified() {
        // The smallest non-trivial case: x0⊕x1 = 1 and x0⊕x1 = 0 contradict.
        // Sum: 0 = 1. This is the k=2 width-boundary the brief calls out first.
        let constraints: Vec<XorConstraint> = vec![(vec![0, 1], true), (vec![0, 1], false)];
        let num_vars = 2;
        assert!(xor_system_is_unsat(&constraints, num_vars));
        let refutation = xor_gauss_drat_refutation(&constraints, &[0, 1], num_vars).unwrap();
        assert_eq!(
            check_drat(refutation.formula(), refutation.proof()),
            Ok(true)
        );
    }

    #[test]
    fn out_of_range_or_empty_subset_declines() {
        let constraints: Vec<XorConstraint> = vec![(vec![0, 1], true), (vec![0, 1], false)];
        assert!(xor_gauss_drat_refutation(&constraints, &[], 2).is_none());
        assert!(xor_gauss_drat_refutation(&constraints, &[0, 5], 2).is_none());
    }

    #[test]
    fn duplicate_single_var_contradiction_certified() {
        // x0 ⊕ x0 = 1 canonicalizes to the empty support with parity 1 in ONE
        // constraint. The subset {0} sums to 0 = 1, so it is a valid refutation.
        let constraints: Vec<XorConstraint> = vec![(vec![0, 0], true)];
        let num_vars = 1;
        let refutation = xor_gauss_drat_refutation(&constraints, &[0], num_vars)
            .expect("x0 ⊕ x0 = 1 is the contradiction 0 = 1");
        assert_eq!(
            check_drat(refutation.formula(), refutation.proof()),
            Ok(true)
        );
    }

    /// A tiny deterministic LCG (no `rand` dependency), mirroring `xor_matrix`.
    struct Lcg(u64);
    impl Lcg {
        fn new(seed: u64) -> Self {
            Self(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1))
        }
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        fn below(&mut self, n: usize) -> usize {
            usize::try_from(self.next_u64() % (n as u64)).expect("modulus fits usize")
        }
        fn bool(&mut self) -> bool {
            self.next_u64() & 1 == 1
        }
    }

    /// Soundness fuzz: over many random small XOR systems, every contradictory
    /// whole-system sum (`0 = 1`) yields a `check_drat`-ACCEPTED refutation, and
    /// no satisfiable system ever yields one. Zero wrong UNSAT.
    #[test]
    fn soundness_fuzz_no_wrong_unsat() {
        let mut rng = Lcg::new(0x5A1D_F00D);
        let mut certified = 0usize;
        let mut declined_sat = 0usize;
        for _ in 0..4000 {
            let num_vars = 2 + rng.below(5); // 2..=6
            let num_constraints = 2 + rng.below(5); // 2..=6
            let mut constraints: Vec<XorConstraint> = Vec::with_capacity(num_constraints);
            for _ in 0..num_constraints {
                let width = 1 + rng.below(num_vars.min(MAX_XOR_WIDTH));
                let mut vars = Vec::with_capacity(width);
                for _ in 0..width {
                    vars.push(rng.below(num_vars));
                }
                constraints.push((vars, rng.bool()));
            }

            let all: Vec<usize> = (0..num_constraints).collect();
            let unsat = xor_system_is_unsat(&constraints, num_vars);
            let refutation = xor_gauss_drat_refutation(&constraints, &all, num_vars);

            match refutation {
                Some(r) => {
                    // A refutation was emitted: it MUST be accepted (no wrong
                    // UNSAT), and the underlying system MUST genuinely be UNSAT.
                    assert_eq!(
                        check_drat(r.formula(), r.proof()),
                        Ok(true),
                        "emitted refutation rejected by check_drat for {constraints:?}"
                    );
                    assert!(
                        unsat,
                        "refutation emitted for a SATISFIABLE system {constraints:?}"
                    );
                    certified += 1;
                }
                None => {
                    // Declining for a SAT system is correct. Declining for an
                    // UNSAT system is allowed (the whole-set sum need not be the
                    // 0 = 1 row — a proper subset might), but must never be a
                    // false claim, which is covered above.
                    if !unsat {
                        declined_sat += 1;
                    }
                }
            }
        }
        assert!(
            certified > 50,
            "fuzz certified too few systems to be meaningful: {certified}"
        );
        assert!(
            declined_sat > 50,
            "fuzz declined too few SAT systems to be meaningful: {declined_sat}"
        );
    }
}
