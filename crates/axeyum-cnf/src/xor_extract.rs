//! Sound XOR-gate extraction from CNF.
//!
//! This module is the second slice of the CDCL(XOR) path (see
//! `docs/research/05-algorithms/multiplier-sat-wall-and-algebraic-paths.md`,
//! path 2). The first slice landed the GF(2) Gaussian solver in [`crate::gf2`];
//! this slice recognizes sets of CNF clauses that *together* encode an XOR
//! constraint and exposes them as a populated [`Gf2System`] so the Gaussian
//! solver can derive implied units and equalities.
//!
//! Scope: extraction only. Wiring the recovered XOR constraints and their
//! derived facts into the SAT loop is a separate, later slice and is
//! intentionally not implemented here.
//!
//! # Soundness
//!
//! The whole point is that a recognized XOR constraint must be **logically
//! equivalent** to the clauses it was recovered from. A clause set that is not a
//! complete XOR gate is never recognized: false negatives are safe, false
//! positives would be a soundness bug. The recognition therefore demands an
//! *exact* match against the complete encoding (see [`extract_xors`]).
//!
//! # The encoding
//!
//! An XOR constraint `x_{i1} ⊕ x_{i2} ⊕ ... ⊕ x_{ik} = p` (`p ∈ {0, 1}`) over a
//! fixed set of `k` variables is logically equivalent to a specific set of
//! exactly `2^(k-1)` clauses over those `k` variables. The satisfying
//! assignments of the XOR are the `2^(k-1)` assignments whose popcount has
//! parity `p`; the *forbidden* assignments are the `2^(k-1)` of parity `1 - p`.
//! Each clause `(l_1 ∨ ... ∨ l_k)` rules out exactly one assignment: the one
//! that makes every literal false, i.e. `var_j = 1` iff `l_j` is negated. That
//! ruled-out assignment has popcount equal to the clause's negated-literal
//! count `n`, so its parity is `n mod 2`. For the clause to belong to the gate
//! it must forbid a parity-`(1 - p)` assignment, hence every gate clause shares
//! the same `n mod 2`, and `p = 1 - (n mod 2)`.
//!
//! Recognition therefore is: group candidate clauses by their (sorted,
//! repeat-free) variable set; for a set of size `k`, the group is an XOR gate
//! iff it contains exactly `2^(k-1)` distinct clauses whose forbidden
//! assignments are *exactly* the `2^(k-1)` assignments of one parity class. The
//! parity class fixes `p`. Anything short of an exact match recognizes nothing.
//!
//! # The gate table (roadmap item 2.2)
//!
//! Mining the clauses is what a solver has to do when it *receives* CNF.
//! `CaDiCaL`'s `congruence.cpp` is 7,925 lines of exactly that, recovering
//! AND/XOR/ITE structure someone else's Tseitin encoding destroyed. We are on
//! the other side of that boundary: we build the CNF, and the gate structure is
//! sitting in the AIG one layer up.
//!
//! [`XorGateTable`] carries it across. It is produced from the AIG and the
//! [`CnfEncoding`] the encoder already returns — no change to `tseitin_encode`,
//! no change to a single clause — and [`extract_xors_hinted`] consumes it to
//! decide which clause groups are worth grouping at all. The mining route stays
//! exactly where it was, as the route for CNF we did not encode.
//!
//! The table is a **hint**. Nothing reads a gate out of it; the consumer still
//! recognizes each group from the clauses. A corrupt entry can therefore only
//! cost a wasted lookup, and a missing entry only a missed gate — never a wrong
//! answer, and never a changed verdict, because extraction is an optimization
//! over a formula the table does not touch.
//!
//! ## What a congruence pass would need on top of this
//!
//! Deliberately out of scope here (item 2.2 is the interface; a congruence
//! closure over gates is its own item). What such a pass would need that this
//! table does not yet carry:
//!
//! * **The other gate kinds.** The encoder already plans NOT-ITE, NOT-AND and
//!   AND-tree gates and counts them in [`crate::CnfEncodingStats`]; only XOR is
//!   recorded here, because only XOR has a consumer today. The AND/ITE entries
//!   are the same three checks — the node holds a variable, the helpers do not,
//!   the operand variables are distinct.
//! * **A stable gate identity, not just a variable set.** Congruence merges two
//!   gates when their *inputs* become equivalent, so an entry needs its inputs
//!   as an ordered, polarity-carrying list keyed by output variable, not the
//!   unordered set that clause grouping needs. Both views come from the same
//!   `detect_*` result; the table stores the grouping view because that is what
//!   [`extract_xors_hinted`] filters on.
//! * **Survival across renumbering.** `compact` and the inprocessing
//!   passes renumber variables, and a table whose entries name pre-compaction
//!   variables silently stops matching. Since a stale table costs only speed
//!   that is safe, but a congruence pass wants it *rebuilt* or *remapped*
//!   through [`crate::CompactMap`] rather than dropped.
//! * **A proof obligation.** Merging two gates rewrites clauses, so unlike
//!   extraction it is not free: each substitution needs its RUP step, the same
//!   contract [`crate::ReductionLink`] already imposes on the other passes.

use crate::{CnfClause, CnfEncoding, CnfFormula, EncodedLit, Gf2System};
use axeyum_aig::{Aig, AigLit, AigNodeId, AigXorGate, detect_xor_gate};
use std::collections::{BTreeMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

/// Maximum XOR-gate width attempted, in variables.
///
/// A width-`k` gate is encoded by `2^(k-1)` clauses, so the work to confirm a
/// gate grows exponentially. Wider gates are rare in practice; `CryptoMiniSat`
/// caps the search the same way. Gates wider than this are simply not
/// recognized (a safe false negative).
const MAX_XOR_VARS: usize = 8;

/// A clause group's identity: its sorted, repeat-free variable set.
///
/// Stored as a fixed array plus a length so grouping allocates nothing per
/// clause. Unused entries are zero. Array order agrees with `Vec<usize>` order
/// for the sets this can hold: within a set the variables ascend and are
/// distinct, so a shorter key's first padding zero is compared against a
/// strictly positive variable of the longer key, which is exactly what
/// `Vec` ordering does when one is a prefix of the other. That agreement is
/// what keeps [`extract_xors`]'s output order unchanged by this
/// representation.
type GateKey = ([u32; MAX_XOR_VARS], u8);

/// Deterministic FNV-1a over a [`GateKey`]'s bytes.
///
/// `HashSet`'s default `RandomState` would be safe here — the set is only ever
/// probed, never iterated, so no output could depend on its order — but the
/// crate promises determinism and a seeded hasher makes that promise
/// structural rather than a comment.
struct GateKeyHasher(u64);

impl Default for GateKeyHasher {
    fn default() -> Self {
        Self(0xcbf2_9ce4_8422_2325)
    }
}

impl Hasher for GateKeyHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        let mut state = self.0;
        for &byte in bytes {
            state ^= u64::from(byte);
            state = state.wrapping_mul(0x0000_0100_0000_01b3);
        }
        self.0 = state;
    }
}

type GateKeySet = HashSet<GateKey, BuildHasherDefault<GateKeyHasher>>;

/// Result of extracting XOR gates from a CNF formula.
#[derive(Debug, Clone)]
pub struct ExtractedXors {
    /// A GF(2) system containing one constraint per recognized XOR gate, sized
    /// to the formula's variable count. Empty when no gate was recognized.
    pub system: Gf2System,
    /// Number of XOR gates recognized (equal to `system.num_constraints()`).
    pub num_recognized: usize,
}

/// Recognizes complete XOR gates in `cnf` and returns them as a [`Gf2System`].
///
/// The scan groups clauses by their variable set and recognizes a group as an
/// XOR gate only when it is *exactly* the complete `2^(k-1)`-clause encoding of
/// some `x ⊕ ... = p` constraint (see the module docs). One constraint is added
/// per recognized gate; the recovered variable set is added in ascending index
/// order, and gates are emitted in ascending order of their variable sets, so
/// the output is deterministic. Recognizing zero gates yields an empty system.
///
/// Only gates of width `2..=MAX_XOR_VARS` are attempted. Clauses with a
/// repeated variable (e.g. `x ∨ ¬x ∨ y`) cannot be part of a clean gate and are
/// skipped during grouping.
#[must_use]
pub fn extract_xors(cnf: &CnfFormula) -> ExtractedXors {
    extract_grouped(cnf, None)
}

/// Recognizes complete XOR gates in `cnf`, restricted to the variable sets a
/// [`XorGateTable`] says the encoder emitted a gate over.
///
/// Passing `None` is exactly [`extract_xors`] — the same call, not an
/// equivalent one — so a caller with no table, or whose CNF came from somewhere
/// else entirely (a DIMACS file, an inprocessed formula whose variables were
/// renumbered), keeps the full clause-mining route with no special case.
///
/// # What the table can and cannot do
///
/// Both routes run the *identical* grouping and the *identical*
/// [`recognize_gate`]. The table changes one thing: which clauses are grouped
/// at all. Every clause of a group shares that group's variable set by
/// definition, so a group is admitted whole or not at all — the table can never
/// hand [`recognize_gate`] a truncated group. Therefore:
///
/// * A **wrong or stale** table can only *add* variable sets to look at. Those
///   groups are then recognized on their own merits, exactly as mining would
///   have recognized them, or rejected. A corrupt table cannot invent a gate.
/// * A **missing** entry can only *drop* a gate from the result. That is a
///   performance loss, never an unsound one: extraction is an optimization and
///   the table does not touch the formula.
///
/// So the result is always a subset of [`extract_xors`]'s, and every element of
/// it is a genuine XOR consequence of `cnf`. Equality with mining is a
/// *completeness* property of the table, and is measured rather than assumed:
/// mining also finds gates no AIG node ever encoded, because two unrelated
/// binary clauses can add up to `a ≡ b`.
#[must_use]
pub fn extract_xors_hinted(cnf: &CnfFormula, table: Option<&XorGateTable>) -> ExtractedXors {
    extract_grouped(cnf, table.map(XorGateTable::keys))
}

/// Groups `cnf`'s clauses by variable set and recognizes each group.
///
/// `admit` is the only difference between the mined and table-driven routes:
/// `None` groups every clause, `Some(keys)` groups only clauses whose variable
/// set is one of `keys`. Everything after grouping is shared.
fn extract_grouped(cnf: &CnfFormula, admit: Option<&GateKeySet>) -> ExtractedXors {
    // Group clauses by their variable set. The key is the sorted, repeat-free
    // variable list; the value collects each clause's "negated-mask" — bit j
    // set iff the j-th variable (in sorted order) appears negated. A clause
    // with a repeated variable is dropped (it cannot be a clean gate clause).
    // We use a BTreeMap so iteration over groups is in sorted variable order,
    // keeping the output deterministic without a later sort.
    let mut groups: BTreeMap<GateKey, Vec<u32>> = BTreeMap::new();

    for clause in cnf.clauses() {
        let Some((key, mask)) = clause_key_and_mask(clause) else {
            continue;
        };
        if let Some(admit) = admit
            && !admit.contains(&key)
        {
            continue;
        }
        groups.entry(key).or_default().push(mask);
    }

    let mut system = Gf2System::new(cnf.variable_count());
    let mut num_recognized = 0usize;

    for ((vars, len), masks) in &groups {
        let k = usize::from(*len);
        if let Some(rhs) = recognize_gate(k, masks) {
            let vars: Vec<usize> = vars[..k].iter().map(|&var| var as usize).collect();
            system.add_constraint(&vars, rhs);
            num_recognized += 1;
        }
    }

    ExtractedXors {
        system,
        num_recognized,
    }
}

/// Builds a clause's group key and negated-mask, or `None` when the clause
/// cannot belong to a clean gate (wrong width, or a repeated variable).
fn clause_key_and_mask(clause: &CnfClause) -> Option<(GateKey, u32)> {
    let lits = clause.lits();
    let k = lits.len();
    if !(2..=MAX_XOR_VARS).contains(&k) {
        return None;
    }
    let mut pairs = [(0u32, false); MAX_XOR_VARS];
    for (slot, lit) in pairs[..k].iter_mut().zip(lits) {
        *slot = (u32::try_from(lit.var().index()).ok()?, lit.is_negated());
    }
    pairs[..k].sort_unstable_by_key(|&(var, _)| var);
    if pairs[..k].windows(2).any(|w| w[0].0 == w[1].0) {
        // A variable repeats in the clause; not a clean gate clause.
        return None;
    }
    let mut vars = [0u32; MAX_XOR_VARS];
    let mut mask = 0u32;
    for (bit, &(var, negated)) in pairs[..k].iter().enumerate() {
        vars[bit] = var;
        if negated {
            mask |= 1u32 << bit;
        }
    }
    Some(((vars, u8::try_from(k).ok()?), mask))
}

/// One XOR gate the Tseitin encoder emitted, in CNF variable space.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct XorGateHint {
    /// Distinct CNF variable indices, ascending.
    pub vars: Vec<usize>,
    /// Right-hand side `p` of `(⊕ vars) = p`.
    pub rhs: bool,
}

/// Gate structure carried across the AIG-to-CNF boundary.
///
/// `CaDiCaL` spends thousands of lines *recovering* AND/XOR/ITE structure
/// from clauses because it never saw the circuit. We build the CNF,
/// so the structure is one layer up and nearly free: an AIG XOR node is two
/// `node()` lookups ([`detect_xor_gate`]) and the encoding's own variable
/// bindings say which of those nodes actually reached the formula as a complete
/// clause group. This is that table — an *interface*, not a recovery algorithm.
///
/// # It is a hint, never a source of truth
///
/// Nothing downstream may trust an entry. [`extract_xors_hinted`] uses the
/// table only to decide which clause groups to look at, and then recognizes
/// each group from the clauses themselves, exactly as [`extract_xors`] does.
/// See that function for what a corrupt or incomplete table can and cannot do.
#[derive(Debug, Clone, Default)]
pub struct XorGateTable {
    hints: Vec<XorGateHint>,
    keys: GateKeySet,
}

impl XorGateTable {
    /// Records the XOR gates `encoding` emitted for `aig`.
    ///
    /// `aig` must be the graph `encoding` was produced from. A different graph
    /// yields a table whose entries do not describe the formula, which
    /// [`extract_xors_hinted`] tolerates — it recognizes every group from the
    /// clauses — but which carries no benefit.
    ///
    /// # Which XOR nodes reach the CNF, and as what
    ///
    /// Recognizing the shape ([`detect_xor_gate`]) is not enough: what matters
    /// is whether the encoder emitted its clauses, and over which variables.
    /// Three cases produce a complete clause group, and they are told apart by
    /// two things the encoding already reports — the variable bindings and the
    /// root list.
    ///
    /// * **Its own variable.** All four clauses are there:
    ///   `out ^ v_lhs ^ v_rhs = inversions`. Holding a variable also settles
    ///   clause *direction*: a node loses its variable to
    ///   `plan_direct_root_nodes` exactly when its root polarity is fixed, and
    ///   a fixed polarity is exactly the condition under which only half the
    ///   equivalence is emitted. A node that still has a variable carries all
    ///   four clauses, not two.
    /// * **Asserted directly as a root.** No variable; the encoder folded the
    ///   constant output into the clauses. Half of an equivalence with a
    ///   constant output is the whole gate: two clauses over the two inputs,
    ///   `v_lhs ^ v_rhs = asserted ^ inversions`. Which roots those are is read
    ///   off `encoding.roots()` — `assert_root` reports a constant-true CNF
    ///   literal for exactly the roots it distributed — rather than re-derived.
    /// * **The top of a flattened chain.** The AND-tree planner collapses a
    ///   chain of variable-less XOR nodes into one parity leaf and emits the
    ///   chain's clauses as a whole. It plans a parity leaf only under a
    ///   positively asserted root, whose output is the constant true, so those
    ///   clauses are again the leaf's whole gate — over the flattened literals,
    ///   capped at three. The chain's inner links own no clauses and are left
    ///   out.
    ///
    /// In every case the two helper AND nodes must be subsumed (no variable of
    /// their own). The encoder subsumes them only when it planned a compound
    /// gate over them, and XOR is the first plan it tries, so a recognized XOR
    /// shape with private helpers is not confusable with the ITE, NOT-AND or
    /// AND-tree plans that skip helpers under the same privacy rule. The
    /// variables of an entry must also be pairwise distinct and none of them
    /// the constant node, since the four clauses otherwise collapse under
    /// tautology and duplicate filtering into something that is not a group of
    /// that width.
    ///
    /// Anything else is left out. A missing entry costs a gate, never a wrong
    /// one — and `every_recorded_entry_is_implied_by_the_clauses_it_names`
    /// checks each entry against the clauses by brute force, so an entry that
    /// named a group the encoder never emitted would fail rather than sit there
    /// as a plausible-looking lie.
    #[must_use]
    pub fn from_encoding(aig: &Aig, encoding: &CnfEncoding) -> Self {
        let node_var = encoded_node_variables(aig, encoding);
        let direct_root = direct_root_polarities(aig, encoding);
        let recognized = recognized_xor_gates(aig, &node_var);
        let fused = fused_chain_links(aig, &node_var, &recognized);

        let mut hints = Vec::new();
        for (node_id, _) in aig.nodes() {
            if let Some(hint) =
                xor_hint_for_node(node_id, &node_var, &direct_root, &recognized, &fused)
            {
                hints.push(hint);
            }
        }
        Self::from_hints(hints)
    }

    /// Builds a table from explicit hints, for tests and for producers other
    /// than the one-shot Tseitin encoder.
    ///
    /// Entries are sorted and deduplicated; nothing else is checked, because
    /// nothing downstream trusts an entry.
    #[must_use]
    pub fn from_hints(mut hints: Vec<XorGateHint>) -> Self {
        hints.sort();
        hints.dedup();
        let mut keys = GateKeySet::default();
        for hint in &hints {
            if let Some(key) = hint_key(hint) {
                keys.insert(key);
            }
        }
        Self { hints, keys }
    }

    /// Recorded gates, ascending by variable set.
    #[must_use]
    pub fn hints(&self) -> &[XorGateHint] {
        &self.hints
    }

    /// Number of recorded gates.
    #[must_use]
    pub fn len(&self) -> usize {
        self.hints.len()
    }

    /// Whether the table recorded no gate at all.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.hints.is_empty()
    }

    fn keys(&self) -> &GateKeySet {
        &self.keys
    }
}

fn hint_key(hint: &XorGateHint) -> Option<GateKey> {
    let k = hint.vars.len();
    if !(2..=MAX_XOR_VARS).contains(&k) {
        return None;
    }
    let mut vars = [0u32; MAX_XOR_VARS];
    for (slot, &var) in vars[..k].iter_mut().zip(&hint.vars) {
        *slot = u32::try_from(var).ok()?;
    }
    vars[..k].sort_unstable();
    if vars[..k].windows(2).any(|w| w[0] == w[1]) {
        return None;
    }
    Some((vars, u8::try_from(k).ok()?))
}

/// CNF variable held by each AIG node, indexed by `AigNodeId::index`.
///
/// `None` means the encoder allocated no variable for that node: it subsumed
/// the node into a compound gate, distributed it straight into root clauses, or
/// never reached it.
fn encoded_node_variables(aig: &Aig, encoding: &CnfEncoding) -> Vec<Option<u32>> {
    let mut node_var: Vec<Option<u32>> = vec![None; aig.node_count()];
    for binding in encoding.variable_bindings() {
        let index = binding.aig_literal.node().index();
        if let Some(slot) = node_var.get_mut(index) {
            *slot = u32::try_from(binding.variable.index()).ok();
        }
    }
    node_var
}

/// Which nodes the encoder asserted straight into clauses, and at which
/// polarity.
///
/// Read off the encoding's own root list rather than re-derived: `assert_root`
/// reports a constant-true CNF literal for exactly the roots it distributed.
fn direct_root_polarities(aig: &Aig, encoding: &CnfEncoding) -> Vec<Option<bool>> {
    let mut direct_root: Vec<Option<bool>> = vec![None; aig.node_count()];
    for root in encoding.roots() {
        let index = root.aig_literal.node().index();
        if index == 0 || root.cnf_lit != EncodedLit::Const(true) {
            continue;
        }
        let polarity = !root.aig_literal.is_inverted();
        match direct_root.get(index).copied().flatten() {
            Some(existing) if existing != polarity => direct_root[index] = None,
            _ => direct_root[index] = Some(polarity),
        }
    }
    direct_root
}

/// Every XOR shape whose two helper AND nodes the encoder subsumed.
///
/// The encoder subsumes a helper only when it planned a compound gate over it,
/// and XOR is the first plan it tries, so a recognized shape with private
/// helpers is an XOR the encoder planned.
fn recognized_xor_gates(aig: &Aig, node_var: &[Option<u32>]) -> Vec<Option<AigXorGate>> {
    let mut recognized: Vec<Option<AigXorGate>> = vec![None; aig.node_count()];
    for (node_id, node) in aig.nodes() {
        if let Some(gate) = detect_xor_gate(aig, node)
            && gate
                .helper_nodes
                .iter()
                .all(|helper| node_var[helper.index()].is_none())
        {
            recognized[node_id.index()] = Some(gate);
        }
    }
    recognized
}

/// Nodes that are inner links of a flattened XOR chain.
///
/// A variable-less XOR feeding another variable-less XOR is flattened INTO its
/// parent: the AND-tree planner turns the chain into one parity leaf and emits
/// clauses for the chain as a whole, so only the top of the chain owns clauses.
fn fused_chain_links(
    aig: &Aig,
    node_var: &[Option<u32>],
    recognized: &[Option<AigXorGate>],
) -> Vec<bool> {
    let mut fused = vec![false; aig.node_count()];
    for (node_id, _) in aig.nodes() {
        if node_var[node_id.index()].is_some() {
            continue;
        }
        let Some(gate) = recognized[node_id.index()] else {
            continue;
        };
        for input in [gate.lhs, gate.rhs] {
            let index = input.node().index();
            if node_var[index].is_none() && recognized[index].is_some() {
                fused[index] = true;
            }
        }
    }
    fused
}

/// The entry `node_id` contributes, if the encoder emitted a complete clause
/// group for it. The three cases are documented on
/// [`XorGateTable::from_encoding`].
fn xor_hint_for_node(
    node_id: AigNodeId,
    node_var: &[Option<u32>],
    direct_root: &[Option<bool>],
    recognized: &[Option<AigXorGate>],
    fused: &[bool],
) -> Option<XorGateHint> {
    let index = node_id.index();
    let gate = recognized[index]?;
    // The recognized node equals `gate.lhs ^ gate.rhs` over AIG literals, so a
    // variable-level constraint carries the input inversions on its right-hand
    // side.
    let inversions = gate.lhs.is_inverted() ^ gate.rhs.is_inverted();

    if let Some(out) = node_var[index] {
        // Its own variable, so all four clauses are there.
        let lhs = input_variable(gate.lhs, node_var)?;
        let rhs = input_variable(gate.rhs, node_var)?;
        return ascending_hint(&[out, lhs, rhs], inversions);
    }

    if let Some(asserted) = direct_root[index] {
        // Asserted as a root with the constant output folded in: two clauses
        // over the two inputs. A direct-root XOR is encoded from its immediate
        // inputs, never flattened, so those inputs carry variables.
        let lhs = input_variable(gate.lhs, node_var)?;
        let rhs = input_variable(gate.rhs, node_var)?;
        return ascending_hint(&[lhs, rhs], asserted ^ inversions);
    }

    if fused[index] {
        // An inner link of a flattened chain: its clauses belong to the top.
        return None;
    }

    // The top of a flattened chain. The AND-tree planner accepts a parity leaf
    // only under a positively asserted root, whose output is the constant true,
    // so the emitted clauses are the leaf's whole gate over the flattened
    // literals.
    let mut leaves = Vec::new();
    let mut inverted = false;
    if !flatten_xor_chain(
        AigLit::positive(node_id),
        node_var,
        recognized,
        &mut leaves,
        &mut inverted,
    ) {
        return None;
    }
    // The planner caps a parity leaf at three literals; a longer chain is not
    // planned as one, so there is nothing to record.
    if !(2..=3).contains(&leaves.len()) {
        return None;
    }
    let mut vars = Vec::with_capacity(leaves.len());
    let mut leaf_inversions = false;
    for leaf in &leaves {
        let var = input_variable(*leaf, node_var)?;
        leaf_inversions ^= leaf.is_inverted();
        vars.push(var);
    }
    // The leaf constrains its literals to parity `!inverted`; moving to
    // variables absorbs each leaf literal's own inversion.
    ascending_hint(&vars, !inverted ^ leaf_inversions)
}

/// Builds a hint over `vars` if they are pairwise distinct, ascending.
fn ascending_hint(vars: &[u32], rhs: bool) -> Option<XorGateHint> {
    let mut sorted = vars.to_vec();
    sorted.sort_unstable();
    if sorted.windows(2).any(|w| w[0] == w[1]) {
        return None;
    }
    Some(XorGateHint {
        vars: sorted.iter().map(|&var| var as usize).collect(),
        rhs,
    })
}

/// Expands a chain of variable-less XOR nodes into its literal leaves, the way
/// the AND-tree planner's parity leaf does.
///
/// `inverted` accumulates the inversion of each expanded XOR literal; a leaf
/// keeps its own inversion in the literal itself. Returns `false` when the
/// chain grows past what a parity leaf can hold, so the caller records nothing.
fn flatten_xor_chain(
    lit: AigLit,
    node_var: &[Option<u32>],
    recognized: &[Option<AigXorGate>],
    leaves: &mut Vec<AigLit>,
    inverted: &mut bool,
) -> bool {
    if leaves.len() > 3 {
        return false;
    }
    let index = lit.node().index();
    if node_var[index].is_none()
        && let Some(gate) = recognized[index]
    {
        *inverted ^= lit.is_inverted();
        return flatten_xor_chain(gate.lhs, node_var, recognized, leaves, inverted)
            && flatten_xor_chain(gate.rhs, node_var, recognized, leaves, inverted);
    }
    leaves.push(lit);
    true
}

fn input_variable(lit: AigLit, node_var: &[Option<u32>]) -> Option<u32> {
    if lit.node().index() == 0 {
        // The constant node: the encoder folds it into the clause instead of
        // giving it a variable, so the group is not width 3.
        return None;
    }
    node_var.get(lit.node().index()).copied().flatten()
}

/// Decides whether the negated-masks of a `k`-variable clause group form a
/// complete XOR gate, returning the gate's right-hand-side parity `p` if so.
///
/// `masks` carries, for each clause in the group, the bitmask (over the `k`
/// sorted variable positions) of which literals are negated. A clause with
/// negated-mask `m` rules out the single assignment `var_j = bit_j(m)`, whose
/// popcount is `m.count_ones()`. The group is a complete gate for parity `p`
/// iff the masks are *exactly* the set of all `2^(k-1)` masks of one popcount
/// parity, each appearing once.
fn recognize_gate(k: usize, masks: &[u32]) -> Option<bool> {
    debug_assert!((2..=MAX_XOR_VARS).contains(&k));
    let expected = 1usize << (k - 1);
    if masks.len() != expected {
        // Wrong number of clauses (too few — a near-miss — or too many — an
        // extra clause in the group). Either way it cannot be the exact gate.
        return None;
    }

    // The full mask range over k variables is 0..2^k. Each mask in the group
    // must be in range, distinct, and share one popcount parity. We record the
    // parity from the first clause and require every clause to match it, then
    // confirm we covered *every* mask of that parity (no missing, no duplicate).
    let parity = (masks[0].count_ones() & 1) == 1;
    let full = 1u32 << k;
    let mut seen = vec![false; full as usize];
    for &mask in masks {
        if mask >= full {
            // A bit outside the k-variable range was set — impossible given how
            // masks are built, but check defensively rather than index OOB.
            return None;
        }
        if (mask.count_ones() & 1 == 1) != parity {
            // Mixed parity: not a single parity class, so not an XOR gate.
            return None;
        }
        if seen[mask as usize] {
            // Duplicate clause: cannot complete the parity class to 2^(k-1)
            // distinct masks.
            return None;
        }
        seen[mask as usize] = true;
    }

    // Confirm full coverage of the parity class: every mask of this parity is
    // present. (Count already equals 2^(k-1) and all are distinct of this
    // parity, so this is guaranteed; assert it as a soundness backstop.)
    for m in 0..full {
        if (m.count_ones() & 1 == 1) == parity {
            debug_assert!(seen[m as usize], "parity class not fully covered");
            if !seen[m as usize] {
                return None;
            }
        }
    }

    // A clause forbids a parity-`parity` assignment; the XOR's forbidden
    // assignments are those of parity `1 - p`, so `parity == 1 - p`, giving
    // `p = !parity`.
    Some(!parity)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CnfClause, CnfLit, CnfVar};

    /// Builds a clause from `(var_index, negated)` pairs.
    fn clause(lits: &[(usize, bool)]) -> CnfClause {
        let lits = lits
            .iter()
            .map(|&(v, neg)| {
                let lit = CnfLit::positive(CnfVar::new(v).expect("var fits u32"));
                if neg { lit.negated() } else { lit }
            })
            .collect();
        CnfClause::new(lits)
    }

    fn formula(num_vars: usize, clauses: &[Vec<(usize, bool)>]) -> CnfFormula {
        let mut f = CnfFormula::new(num_vars);
        for c in clauses {
            f.add_clause(clause(c)).expect("valid clause");
        }
        f
    }

    /// Generates the complete clause set encoding `(⊕ of `vars`) = p`.
    ///
    /// A clause forbids an assignment of parity `1 - p`; the clause's negated
    /// literals are exactly the variables set to 1 in that forbidden assignment.
    /// So we enumerate every parity-`(1 - p)` assignment over `vars` and emit
    /// one clause per assignment with `literal_j` negated iff `var_j` is 1.
    fn xor_clauses(vars: &[usize], p: bool) -> Vec<Vec<(usize, bool)>> {
        let k = vars.len();
        let target_parity = !p; // forbidden assignments have parity 1 - p.
        let mut clauses = Vec::new();
        for assign in 0u32..(1u32 << k) {
            let parity = (assign.count_ones() & 1) == 1;
            if parity != target_parity {
                continue;
            }
            let lits: Vec<(usize, bool)> = vars
                .iter()
                .enumerate()
                .map(|(j, &v)| (v, (assign >> j) & 1 == 1))
                .collect();
            clauses.push(lits);
        }
        clauses
    }

    /// Brute-force: returns every assignment over `vars` (as a popcount-indexed
    /// truth table value, `var_j` = bit j) that satisfies all `clauses` restricted
    /// to those vars. Used to confirm the recognized constraint matches the
    /// intended XOR exactly.
    fn clause_models(vars: &[usize], clauses: &[Vec<(usize, bool)>]) -> Vec<u32> {
        let k = vars.len();
        let mut models = Vec::new();
        for assign in 0u32..(1u32 << k) {
            let value = |v: usize| -> bool {
                let j = vars.iter().position(|&x| x == v).expect("var in set");
                (assign >> j) & 1 == 1
            };
            let all = clauses.iter().all(|c| {
                c.iter()
                    .any(|&(v, neg)| if neg { !value(v) } else { value(v) })
            });
            if all {
                models.push(assign);
            }
        }
        models
    }

    /// XOR truth table: assignments over `vars` with `⊕ x = p`, as a bit-packed
    /// mask matching `clause_models`' encoding (`var_j` = bit j).
    fn xor_models(vars: &[usize], p: bool) -> Vec<u32> {
        let k = vars.len();
        (0u32..(1u32 << k))
            .filter(|a| ((a.count_ones() & 1) == 1) == p)
            .collect()
    }

    #[test]
    fn round_trip_k2_parity_zero() {
        // x0 ⊕ x1 = 0.
        let f = formula(2, &xor_clauses(&[0, 1], false));
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
        // x0 == x1, exposed by the GF(2) solver as an equality.
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                assert_eq!(sol.implied_equalities(), &[(0, 1, false)]);
            }
            crate::Gf2Outcome::Unsat => panic!("gate system should be SAT"),
        }
    }

    #[test]
    fn round_trip_k2_parity_one() {
        // x0 ⊕ x1 = 1.
        let f = formula(2, &xor_clauses(&[0, 1], true));
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                assert_eq!(sol.implied_equalities(), &[(0, 1, true)]);
            }
            crate::Gf2Outcome::Unsat => panic!("gate system should be SAT"),
        }
    }

    #[test]
    fn round_trip_k3_parity_zero() {
        // x0 ⊕ x1 ⊕ x2 = 0 ⇒ 4 clauses.
        let clauses = xor_clauses(&[0, 1, 2], false);
        assert_eq!(clauses.len(), 4);
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
        // Every satisfying assignment of the recovered system must satisfy the XOR.
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                let xor = sol.value(0) ^ sol.value(1) ^ sol.value(2);
                assert!(!xor, "solution must satisfy x0 ⊕ x1 ⊕ x2 = 0");
            }
            crate::Gf2Outcome::Unsat => panic!("gate system should be SAT"),
        }
    }

    #[test]
    fn round_trip_k3_parity_one() {
        let clauses = xor_clauses(&[0, 1, 2], true);
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                let xor = sol.value(0) ^ sol.value(1) ^ sol.value(2);
                assert!(xor, "solution must satisfy x0 ⊕ x1 ⊕ x2 = 1");
            }
            crate::Gf2Outcome::Unsat => panic!("gate system should be SAT"),
        }
    }

    #[test]
    fn parity_matches_truth_table_k2_k3_k4() {
        // For each width and parity, the recognized gate's models (brute force
        // over the clauses) must equal exactly the XOR truth table.
        for k in 2usize..=4 {
            let vars: Vec<usize> = (0..k).collect();
            for &p in &[false, true] {
                let clauses = xor_clauses(&vars, p);
                let f = formula(k, &clauses);
                let extracted = extract_xors(&f);
                assert_eq!(
                    extracted.num_recognized, 1,
                    "k={k} p={p} should recognize one gate"
                );
                // The clauses are UNSAT exactly on assignments violating the XOR.
                let mut models = clause_models(&vars, &clauses);
                let mut expected = xor_models(&vars, p);
                models.sort_unstable();
                expected.sort_unstable();
                assert_eq!(models, expected, "clause models must equal XOR k={k} p={p}");
            }
        }
    }

    #[test]
    fn no_false_positive_missing_one_clause() {
        // Drop one clause of a k=3 gate ⇒ not recognized.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        clauses.pop();
        assert_eq!(clauses.len(), 3);
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn no_false_positive_extra_clause_in_group() {
        // The complete k=3 even gate plus an extra clause over the same vars
        // (an odd-parity clause) ⇒ 5 clauses in the group, not 4 ⇒ not a gate.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        // Add the all-positive clause (x0 ∨ x1 ∨ x2), which is odd parity (0
        // negated literals → forbids 000, parity 0... actually it belongs to
        // the OTHER gate). Adding it makes 5 clauses over the same var set.
        clauses.push(vec![(0, false), (1, false), (2, false)]);
        assert_eq!(clauses.len(), 5);
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn no_false_positive_duplicate_clause() {
        // Right count (4) but a duplicate ⇒ parity class not fully covered.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        clauses.pop();
        clauses.push(clauses[0].clone()); // duplicate the first
        assert_eq!(clauses.len(), 4);
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn no_false_positive_mixed_parity() {
        // Four clauses over {0,1,2} but mixing both parity classes ⇒ not a gate.
        let even = xor_clauses(&[0, 1, 2], false); // even-parity clauses
        let odd = xor_clauses(&[0, 1, 2], true); // odd-parity clauses
        let clauses = vec![
            even[0].clone(),
            even[1].clone(),
            odd[0].clone(),
            odd[1].clone(),
        ];
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn no_false_positive_plain_clauses() {
        // Ordinary non-XOR CNF ⇒ nothing recognized.
        let f = formula(
            4,
            &[
                vec![(0, false), (1, true)],
                vec![(1, false), (2, false), (3, true)],
                vec![(0, true)],
            ],
        );
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn two_independent_gates_both_recognized() {
        // x0 ⊕ x1 = 1 and x2 ⊕ x3 ⊕ x4 = 0 over disjoint variables.
        let mut clauses = xor_clauses(&[0, 1], true);
        clauses.extend(xor_clauses(&[2, 3, 4], false));
        let f = formula(5, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 2);
        // Confirm consistency: every model satisfies both XORs.
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                assert!(sol.value(0) ^ sol.value(1));
                assert!(!(sol.value(2) ^ sol.value(3) ^ sol.value(4)));
            }
            crate::Gf2Outcome::Unsat => panic!("two independent gates should be SAT"),
        }
    }

    #[test]
    fn near_miss_with_unrelated_clause_does_not_block_gate() {
        // A complete k=3 gate over {0,1,2} plus an unrelated clause over {3,4}.
        // The unrelated clause is a different variable group, so it neither
        // joins nor blocks the gate.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        clauses.push(vec![(3, false), (4, true)]);
        let f = formula(5, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
    }

    #[test]
    fn clause_with_repeated_variable_is_skipped() {
        // A "clause" with a repeated variable can't be a clean gate clause; it
        // is dropped during grouping, so the otherwise-complete gate is broken.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        // Replace one clause with one having a repeated variable over {0,1,2}.
        clauses[0] = vec![(0, false), (0, true), (1, false)];
        let f = formula(3, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn empty_formula_recognizes_nothing() {
        let f = CnfFormula::new(4);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
        assert_eq!(extracted.system.num_constraints(), 0);
        assert_eq!(extracted.system.num_vars(), 4);
    }

    #[test]
    fn unit_clauses_are_not_gates() {
        // Single-literal clauses (k=1) are below the k>=2 threshold.
        let f = formula(2, &[vec![(0, false)], vec![(1, true)]]);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }

    #[test]
    fn determinism_constraints_in_sorted_order() {
        // Two gates added out of natural order; constraints come back grouped by
        // sorted variable set. Build gate over {2,3} after gate over {0,1}.
        let mut clauses = xor_clauses(&[2, 3], false);
        clauses.extend(xor_clauses(&[0, 1], true));
        let f = formula(4, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 2);
        // Running extraction again must yield an identical system shape.
        let again = extract_xors(&f);
        assert_eq!(again.num_recognized, extracted.num_recognized);
        assert_eq!(
            again.system.num_constraints(),
            extracted.system.num_constraints()
        );
    }

    #[test]
    fn k4_round_trip() {
        // A wider gate to exercise the 2^(k-1) = 8 clause case.
        let clauses = xor_clauses(&[0, 1, 2, 3], true);
        assert_eq!(clauses.len(), 8);
        let f = formula(4, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 1);
        match extracted.system.solve() {
            crate::Gf2Outcome::Sat(sol) => {
                assert!(sol.value(0) ^ sol.value(1) ^ sol.value(2) ^ sol.value(3));
            }
            crate::Gf2Outcome::Unsat => panic!("k4 gate should be SAT"),
        }
    }

    #[test]
    fn gate_wider_than_cap_not_recognized() {
        // A complete gate of width MAX_XOR_VARS + 1: every clause exceeds the
        // per-clause width cap, so all are skipped during grouping.
        let vars: Vec<usize> = (0..=MAX_XOR_VARS).collect();
        let clauses = xor_clauses(&vars, false);
        let f = formula(MAX_XOR_VARS + 1, &clauses);
        let extracted = extract_xors(&f);
        assert_eq!(extracted.num_recognized, 0);
    }
}

/// The gate table carried across the AIG-to-CNF boundary (roadmap item 2.2).
///
/// These tests are the whole reason the table is allowed to exist. They pin
/// four things:
///
/// 1. The table-driven route finds the same XOR set as clause mining on a
///    curated XOR corpus (the exit criterion), compared constraint by
///    constraint rather than by count.
/// 2. Building the table does not change one byte of the CNF.
/// 3. A **corrupt** table cannot change the answer.
/// 4. **Dropping** the table leaves mining intact, which is what keeps foreign
///    CNF working — and, so that (1) is not vacuous, an *incomplete* table
///    demonstrably makes the equality check fail.
#[cfg(test)]
mod gate_table_tests {
    use super::*;
    use crate::{CnfEncoding, parse_dimacs, tseitin_encode};
    use axeyum_aig::{Aig, AigLit};
    use axeyum_bv::lower_terms;
    use axeyum_ir::{Sort, TermArena};
    use std::fmt::Write as _;

    /// One curated instance: a name and the AIG plus roots handed to the
    /// encoder.
    struct Instance {
        name: &'static str,
        aig: Aig,
        roots: Vec<AigLit>,
    }

    /// Lowers one `QF_BV` term through `axeyum-bv`, the production route into
    /// AIG. These are the instances whose gate structure is *not* hand-placed:
    /// whatever XOR nodes exist are the ones bit-blasting actually produced.
    fn lowered(
        name: &'static str,
        build: impl Fn(&mut TermArena) -> axeyum_ir::TermId,
    ) -> Instance {
        let mut arena = TermArena::new();
        let root = build(&mut arena);
        let lowering = lower_terms(&arena, &[root]).expect("fixture lowers");
        let roots = lowering.roots()[0].bits().to_vec();
        Instance {
            name,
            aig: lowering.aig().clone(),
            roots,
        }
    }

    fn bv(arena: &mut TermArena, name: &str, width: u32) -> axeyum_ir::TermId {
        let sym = arena
            .declare(name, Sort::BitVec(width))
            .expect("fresh symbol");
        arena.var(sym)
    }

    /// The curated XOR corpus.
    ///
    /// Bit-blasted adders and multipliers are the natural home of XOR gates (a
    /// full adder's sum bit *is* a three-input XOR), so most of these are
    /// arithmetic. The last few are deliberately XOR-poor or XOR-free, which is
    /// the other half of the check: a table that recorded gates there would be
    /// wrong, and a mining route that found none there must be matched by the
    /// table route finding none either.
    fn curated_corpus() -> Vec<Instance> {
        let mut corpus = vec![
            lowered("bvxor8", |a| {
                let x = bv(a, "x", 8);
                let y = bv(a, "y", 8);
                a.bv_xor(x, y).unwrap()
            }),
            lowered("bvxor_chain4x8", |a| {
                let x = bv(a, "x", 8);
                let y = bv(a, "y", 8);
                let z = bv(a, "z", 8);
                let w = bv(a, "w", 8);
                let xy = a.bv_xor(x, y).unwrap();
                let zw = a.bv_xor(z, w).unwrap();
                a.bv_xor(xy, zw).unwrap()
            }),
            lowered("bvadd16", |a| {
                let x = bv(a, "x", 16);
                let y = bv(a, "y", 16);
                a.bv_add(x, y).unwrap()
            }),
            lowered("bvadd_three12", |a| {
                let x = bv(a, "x", 12);
                let y = bv(a, "y", 12);
                let z = bv(a, "z", 12);
                let xy = a.bv_add(x, y).unwrap();
                a.bv_add(xy, z).unwrap()
            }),
            lowered("bvmul8", |a| {
                let x = bv(a, "x", 8);
                let y = bv(a, "y", 8);
                a.bv_mul(x, y).unwrap()
            }),
            lowered("bvxor_eq", |a| {
                let x = bv(a, "x", 8);
                let y = bv(a, "y", 8);
                let z = bv(a, "z", 8);
                let xy = a.bv_xor(x, y).unwrap();
                a.eq(xy, z).unwrap()
            }),
            lowered("bvadd_eq_mul", |a| {
                let x = bv(a, "x", 8);
                let y = bv(a, "y", 8);
                let sum = a.bv_add(x, y).unwrap();
                let product = a.bv_mul(x, y).unwrap();
                a.eq(sum, product).unwrap()
            }),
            lowered("bvand8_no_xor", |a| {
                let x = bv(a, "x", 8);
                let y = bv(a, "y", 8);
                a.bv_and(x, y).unwrap()
            }),
            lowered("bvult16_no_xor", |a| {
                let x = bv(a, "x", 16);
                let y = bv(a, "y", 16);
                a.bv_ult(x, y).unwrap()
            }),
        ];
        corpus.push(parity_chain(24));
        corpus.push(mixed_xor_and_or());
        corpus
    }

    /// A hand-built parity chain: `p0 ^ p1 ^ ... ^ p(n-1)`, the densest XOR
    /// shape there is.
    fn parity_chain(inputs: usize) -> Instance {
        let mut aig = Aig::new();
        let mut acc = aig.input("p0");
        for index in 1..inputs {
            let next = aig.input(format!("p{index}"));
            acc = aig.xor(acc, next);
        }
        Instance {
            name: "parity_chain24",
            aig,
            roots: vec![acc],
        }
    }

    /// XOR nodes interleaved with AND/OR, so the recognizer has to reject the
    /// non-XOR shapes sitting next to the ones it must find.
    fn mixed_xor_and_or() -> Instance {
        let mut aig = Aig::new();
        let in0 = aig.input("a");
        let in1 = aig.input("b");
        let in2 = aig.input("c");
        let in3 = aig.input("d");
        let first_xor = aig.xor(in0, in1);
        let conjunction = aig.and(in2, in3);
        let disjunction = aig.or(first_xor, conjunction);
        let second_xor = aig.xor(disjunction, in2);
        let selected = aig.mux(in0, second_xor, conjunction);
        let root = aig.and(selected, first_xor);
        Instance {
            name: "mixed_xor_and_or",
            aig,
            roots: vec![root, second_xor, first_xor],
        }
    }

    fn encode(instance: &Instance) -> CnfEncoding {
        tseitin_encode(&instance.aig, &instance.roots).expect("fixture encodes")
    }

    /// THE EXIT CRITERION, correctness half.
    ///
    /// For every curated instance: the constraints recovered through the table
    /// equal, element for element, the constraints recovered by mining the
    /// clauses. Compared as full `(vars, rhs)` tuples in emission order, not as
    /// counts — two different gate sets of the same size would pass a count
    /// check.
    #[test]
    fn table_finds_the_same_xor_set_as_clause_mining_on_the_curated_corpus() {
        let mut instances_with_gates = 0usize;
        let mut total_gates = 0usize;
        let mut report = String::new();
        let mut mismatches = Vec::new();
        for instance in curated_corpus() {
            let encoding = encode(&instance);
            let formula = encoding.formula();
            let table = XorGateTable::from_encoding(&instance.aig, &encoding);

            let mined = extract_xors(formula);
            let hinted = extract_xors_hinted(formula, Some(&table));
            let agree = hinted.system.constraints() == mined.system.constraints();

            let _ = writeln!(
                report,
                "  {:<20} vars {:>6} clauses {:>7} entries {:>5} mined {:>5} hinted {:>5} {}",
                instance.name,
                formula.variable_count(),
                formula.clauses().len(),
                table.len(),
                mined.num_recognized,
                hinted.num_recognized,
                if agree { "SAME" } else { "DIFFERENT" },
            );
            if !agree {
                let mined_set = mined.system.constraints();
                let hinted_set = hinted.system.constraints();
                let missing: Vec<_> = mined_set
                    .iter()
                    .filter(|c| !hinted_set.contains(c))
                    .take(4)
                    .cloned()
                    .collect();
                let extra: Vec<_> = hinted_set
                    .iter()
                    .filter(|c| !mined_set.contains(c))
                    .take(4)
                    .cloned()
                    .collect();
                let _ = writeln!(report, "      missing from the table route: {missing:?}");
                let _ = writeln!(report, "      found ONLY by the table route: {extra:?}");
                mismatches.push(instance.name);
            }
            if mined.num_recognized > 0 {
                instances_with_gates += 1;
                total_gates += mined.num_recognized;
            }
        }
        println!("gate-table vs clause mining on the curated XOR corpus:\n{report}");
        assert!(
            mismatches.is_empty(),
            "the table route and the mining route must recover the SAME XOR set;              they differ on {mismatches:?}\n{report}"
        );
        // A corpus on which nothing is ever recognized would make the equality
        // above vacuous. Pin that it is not.
        assert!(
            instances_with_gates >= 6,
            "the curated corpus must actually contain XOR gates; only \
             {instances_with_gates} instances recognized any\n{report}"
        );
        assert!(
            total_gates >= 200,
            "expected a few hundred gates across the corpus, found \
             {total_gates}\n{report}"
        );
    }

    /// Constraint 2: building the table does not change the CNF.
    ///
    /// `from_encoding` takes `&Aig` and `&CnfEncoding`, so it *cannot* mutate
    /// either — but "cannot mutate" is a claim about this revision, and the
    /// measurement downstream of item 2.2 is only valid if the clauses are the
    /// ones that were there before. So: encode, snapshot the DIMACS text, build
    /// the table, re-encode, and require the text to be byte-identical.
    #[test]
    fn building_the_table_leaves_the_cnf_byte_identical() {
        for instance in curated_corpus() {
            let before = encode(&instance).formula().to_dimacs();
            let encoding = encode(&instance);
            let table = XorGateTable::from_encoding(&instance.aig, &encoding);
            let during = encoding.formula().to_dimacs();
            let after = encode(&instance).formula().to_dimacs();
            assert_eq!(
                before, during,
                "{}: table build changed the CNF",
                instance.name
            );
            assert_eq!(before, after, "{}: re-encoding differs", instance.name);
            // Consume the table so it cannot be optimized away.
            assert!(table.len() <= before.len());
        }
    }

    /// NEGATIVE CONTROL 1: a corrupt table cannot change the answer.
    ///
    /// Three corruptions, all of the "claims a gate that is not there" kind:
    /// a variable set that carries no clause at all, a set that carries clauses
    /// but is not a complete gate, and every three-variable set of a small
    /// prefix of the formula. Each is a lie the table tells the consumer; none
    /// may move the result, because the consumer recognizes each group from the
    /// clauses rather than believing the entry.
    #[test]
    fn a_corrupt_table_cannot_change_the_recovered_xor_set() {
        for instance in curated_corpus() {
            let encoding = encode(&instance);
            let formula = encoding.formula();
            let honest = XorGateTable::from_encoding(&instance.aig, &encoding);
            let expected = extract_xors_hinted(formula, Some(&honest))
                .system
                .constraints();
            let vars = formula.variable_count();
            if vars < 6 {
                continue;
            }

            let mut corrupt = honest.hints().to_vec();
            // (a) A set of variables past the end of the formula.
            corrupt.push(XorGateHint {
                vars: vec![vars + 1, vars + 2, vars + 3],
                rhs: true,
            });
            // (b) Every 3-subset of the first six variables, flagged with both
            //     parities. Almost none of these is a gate; any that is, mining
            //     found too.
            for i in 0..6 {
                for j in (i + 1)..6 {
                    for k in (j + 1)..6 {
                        corrupt.push(XorGateHint {
                            vars: vec![i, j, k],
                            rhs: false,
                        });
                        corrupt.push(XorGateHint {
                            vars: vec![i, j, k],
                            rhs: true,
                        });
                    }
                }
            }
            // (c) Flip the recorded parity of every honest entry. The parity is
            //     the part of an entry a naive consumer would copy straight
            //     into the GF(2) system.
            for hint in &mut corrupt {
                hint.rhs = !hint.rhs;
            }

            let corrupted = XorGateTable::from_hints(corrupt);
            let got = extract_xors_hinted(formula, Some(&corrupted))
                .system
                .constraints();
            let mined = extract_xors(formula).system.constraints();
            assert_eq!(
                got, expected,
                "{}: a corrupt table moved the result",
                instance.name
            );
            assert_eq!(
                got, mined,
                "{}: a corrupt table must still agree with mining",
                instance.name
            );
        }
    }

    /// NEGATIVE CONTROL 2: dropping the table leaves the mining route intact.
    ///
    /// This is the property that keeps foreign CNF working. `None` is not an
    /// "equivalent" path, it is the same call, and this pins that on both
    /// encoder-produced CNF and on a DIMACS file that no AIG ever produced.
    #[test]
    fn dropping_the_table_falls_back_to_mining() {
        for instance in curated_corpus() {
            let encoding = encode(&instance);
            let formula = encoding.formula();
            assert_eq!(
                extract_xors_hinted(formula, None).system.constraints(),
                extract_xors(formula).system.constraints(),
                "{}: the no-table route must be the mining route",
                instance.name
            );
        }

        // Foreign CNF: a DIMACS file with two XOR gates and no AIG behind it.
        // The mining route finds both; an unrelated table finds nothing, and
        // that is a slower answer, never a wrong one.
        let foreign = parse_dimacs(
            "p cnf 5 6\n\
             1 2 0\n\
             -1 -2 0\n\
             3 4 5 0\n\
             3 -4 -5 0\n\
             -3 4 -5 0\n\
             -3 -4 5 0\n",
        )
        .expect("valid DIMACS");
        let mined = extract_xors(&foreign);
        assert_eq!(mined.num_recognized, 2, "the foreign file has two gates");
        // A table built for a DIFFERENT graph is the honest model of foreign
        // CNF: there is no encoding behind this formula at all.
        assert!(XorGateTable::default().is_empty());
        assert_eq!(
            extract_xors_hinted(&foreign, Some(&XorGateTable::default())).num_recognized,
            0,
            "an empty table admits no group, which is slower, not wrong"
        );
        assert_eq!(
            extract_xors_hinted(&foreign, None).system.constraints(),
            mined.system.constraints()
        );
        let unrelated = XorGateTable::from_hints(vec![XorGateHint {
            vars: vec![0, 1, 2],
            rhs: false,
        }]);
        let with_unrelated = extract_xors_hinted(&foreign, Some(&unrelated));
        assert!(
            with_unrelated.num_recognized <= mined.num_recognized,
            "a table can only ever narrow the search"
        );
    }

    /// The equality check in
    /// `table_finds_the_same_xor_set_as_clause_mining_on_the_curated_corpus`
    /// must be able to FAIL. Drop one honest entry and require the result to
    /// shrink by exactly that gate.
    ///
    /// Without this, "the table agrees with mining" could be true because the
    /// comparison is blind — for instance if `extract_xors_hinted` quietly fell
    /// back to mining whenever a table was supplied.
    #[test]
    fn an_incomplete_table_visibly_loses_exactly_the_dropped_gate() {
        let mut checked = 0usize;
        for instance in curated_corpus() {
            let encoding = encode(&instance);
            let formula = encoding.formula();
            let honest = XorGateTable::from_encoding(&instance.aig, &encoding);
            let full = extract_xors_hinted(formula, Some(&honest));
            if full.num_recognized == 0 {
                continue;
            }

            // Find an entry whose group mining actually recognizes, drop it,
            // and require the recovered set to lose exactly that constraint.
            let recognized = full.system.constraints();
            let dropped = honest
                .hints()
                .iter()
                .find(|hint| recognized.iter().any(|(vars, _)| *vars == hint.vars))
                .expect("a recognized gate came from some entry")
                .clone();
            let thinned: Vec<XorGateHint> = honest
                .hints()
                .iter()
                .filter(|hint| hint.vars != dropped.vars)
                .cloned()
                .collect();
            let partial = extract_xors_hinted(formula, Some(&XorGateTable::from_hints(thinned)));
            assert_eq!(
                partial.num_recognized + 1,
                full.num_recognized,
                "{}: dropping one entry must lose exactly one gate",
                instance.name
            );
            assert!(
                !partial
                    .system
                    .constraints()
                    .iter()
                    .any(|(vars, _)| *vars == dropped.vars),
                "{}: the dropped gate must be gone",
                instance.name
            );
            checked += 1;
        }
        assert!(
            checked >= 6,
            "only {checked} instances exercised this control"
        );
    }

    /// Every entry the table records must be a real logical consequence of the
    /// clauses — checked by brute force over the three variables, not by
    /// re-running the recognizer that produced it.
    #[test]
    fn every_recorded_entry_is_implied_by_the_clauses_it_names() {
        let mut checked = 0usize;
        let mut widths = std::collections::BTreeSet::new();
        for instance in curated_corpus() {
            let encoding = encode(&instance);
            let formula = encoding.formula();
            let table = XorGateTable::from_encoding(&instance.aig, &encoding);
            for hint in table.hints() {
                let k = hint.vars.len();
                assert!(
                    (2..=3).contains(&k),
                    "{}: AIG XOR entries are width 2 or 3, got {k}",
                    instance.name
                );
                assert!(
                    hint.vars.windows(2).all(|w| w[0] < w[1]),
                    "{}: entry variables must ascend",
                    instance.name
                );
                widths.insert(k);
                // Brute force over the entry's variables: collect every clause
                // whose variable set is exactly this one, and require its models
                // to be exactly the XOR's models. This checks the CLAUSES, not
                // the recognizer that produced the entry.
                let key = hint_key(hint).expect("entry has a key");
                let mut models = Vec::new();
                for assign in 0u32..(1u32 << k) {
                    let satisfied =
                        formula
                            .clauses()
                            .iter()
                            .all(|clause| match clause_key_and_mask(clause) {
                                Some((clause_key, _)) if clause_key == key => {
                                    clause.lits().iter().any(|lit| {
                                        let slot = hint
                                            .vars
                                            .iter()
                                            .position(|&var| var == lit.var().index())
                                            .expect("clause var is in the key");
                                        (((assign >> slot) & 1) == 1) != lit.is_negated()
                                    })
                                }
                                _ => true,
                            });
                    if satisfied {
                        models.push(assign);
                    }
                }
                let expected: Vec<u32> = (0u32..(1u32 << k))
                    .filter(|a| ((a.count_ones() & 1) == 1) == hint.rhs)
                    .collect();
                assert_eq!(
                    models, expected,
                    "{}: entry {:?} rhs={} does not match the clauses over its variables",
                    instance.name, hint.vars, hint.rhs
                );
                checked += 1;
            }
        }
        assert!(checked >= 200, "only {checked} entries were checked");
        assert_eq!(
            widths,
            std::collections::BTreeSet::from([2, 3]),
            "the corpus must exercise BOTH shapes the encoder emits: the \
             width-3 group of a gate with its own variable, and the width-2 \
             group of a gate the encoder asserted directly as a root"
        );
    }

    /// Clause mining exactly as it stood on `main` at `6dd85fc78`, before this
    /// change: a `BTreeMap` keyed by a heap-allocated `Vec<usize>`, with a
    /// second `Vec` allocated per clause to sort the (variable, negated) pairs.
    ///
    /// Kept for one reason — it is the **before** side of the measurement. A
    /// ratio quoted against the post-change mining route would understate the
    /// change, because sharing one allocation-free grouping between the two
    /// routes sped the mining route up too. Its own test pins it against the
    /// shipped mining route so it cannot drift into measuring something else.
    fn mine_as_of_main(cnf: &CnfFormula) -> ExtractedXors {
        let mut groups: BTreeMap<Vec<usize>, Vec<u32>> = BTreeMap::new();
        for clause in cnf.clauses() {
            let lits = clause.lits();
            let k = lits.len();
            if !(2..=MAX_XOR_VARS).contains(&k) {
                continue;
            }
            let mut pairs: Vec<(usize, bool)> = lits
                .iter()
                .map(|lit| (lit.var().index(), lit.is_negated()))
                .collect();
            pairs.sort_unstable_by_key(|&(var, _)| var);
            if pairs.windows(2).any(|w| w[0].0 == w[1].0) {
                continue;
            }
            let vars: Vec<usize> = pairs.iter().map(|&(var, _)| var).collect();
            let mut mask = 0u32;
            for (bit, &(_, negated)) in pairs.iter().enumerate() {
                if negated {
                    mask |= 1u32 << bit;
                }
            }
            groups.entry(vars).or_default().push(mask);
        }
        let mut system = Gf2System::new(cnf.variable_count());
        let mut num_recognized = 0usize;
        for (vars, masks) in &groups {
            if let Some(rhs) = recognize_gate(vars.len(), masks) {
                system.add_constraint(vars, rhs);
                num_recognized += 1;
            }
        }
        ExtractedXors {
            system,
            num_recognized,
        }
    }

    /// The measurement baseline must still be the thing it claims to be.
    #[test]
    fn baseline_agrees_with_the_shipped_mining_route() {
        for instance in curated_corpus() {
            let encoding = encode(&instance);
            let formula = encoding.formula();
            assert_eq!(
                mine_as_of_main(formula).system.constraints(),
                extract_xors(formula).system.constraints(),
                "{}: the pre-change baseline and the shipped mining route must \
                 recover the same set, or the measurement compares two \
                 different things",
                instance.name
            );
        }
    }

    /// MEASUREMENT, the performance half of the exit criterion.
    ///
    /// Not a ratchet — a wall-clock ratio inside a test on a shared box is not
    /// reproducible, and asserting one would be a gate that fails for reasons
    /// unrelated to this code. This runs three routes on two instances of very
    /// different XOR density, asserts they agree, and PRINTS the timings, so a
    /// number can be quoted from an actual run (`--release -- --nocapture`)
    /// with the host and load stated alongside it.
    #[test]
    fn measure_table_route_against_mining() {
        for (label, instance) in [
            (
                "xor-dense (mul+add+eq)",
                lowered("dense", |a| {
                    let x = bv(a, "x", 16);
                    let y = bv(a, "y", 16);
                    let z = bv(a, "z", 16);
                    let product = a.bv_mul(x, y).unwrap();
                    let sum = a.bv_add(product, z).unwrap();
                    a.eq(sum, x).unwrap()
                }),
            ),
            (
                "xor-sparse (and + ult)",
                lowered("sparse", |a| {
                    let x = bv(a, "x", 32);
                    let y = bv(a, "y", 32);
                    let masked = a.bv_and(x, y).unwrap();
                    a.bv_ult(masked, y).unwrap()
                }),
            ),
        ] {
            let encoding = encode(&instance);
            let formula = encoding.formula();
            let table = XorGateTable::from_encoding(&instance.aig, &encoding);

            let rounds = 50;
            let mut results = Vec::new();
            let mut timings = Vec::new();
            for (route, run) in [
                (
                    "mining as of main (before)",
                    Box::new(|| mine_as_of_main(formula)) as Box<dyn Fn() -> ExtractedXors>,
                ),
                ("mining, shipped", Box::new(|| extract_xors(formula))),
                (
                    "table route (after)",
                    Box::new(|| extract_xors_hinted(formula, Some(&table))),
                ),
            ] {
                let start = std::time::Instant::now();
                let mut last = None;
                for _ in 0..rounds {
                    last = Some(run());
                }
                timings.push((route, start.elapsed() / rounds));
                results.push(last.expect("ran at least once").system.constraints());
            }
            let start = std::time::Instant::now();
            for _ in 0..rounds {
                let built = XorGateTable::from_encoding(&instance.aig, &encoding);
                std::hint::black_box(built.len());
            }
            let build = start.elapsed() / rounds;

            assert!(
                results.windows(2).all(|w| w[0] == w[1]),
                "{label}: the three routes must agree"
            );
            println!(
                "gate-table measurement [{label}]: {} vars / {} clauses / {} \
                 gates / {} entries",
                formula.variable_count(),
                formula.clauses().len(),
                results[0].len(),
                table.len(),
            );
            for (route, elapsed) in &timings {
                println!("    {route:<28} {elapsed:?}");
            }
            println!("    {:<28} {build:?}", "table build (once)");
        }
    }

    /// The table route must examine strictly fewer clause groups than mining on
    /// XOR-poor formulas — the mechanism behind the performance half of the
    /// exit criterion. This asserts the MECHANISM (fewer groups), not a
    /// wall-clock ratio, which is not reproducible inside a test.
    #[test]
    fn the_table_narrows_the_clause_scan() {
        let instance = lowered("bvmul8_scan", |a| {
            let x = bv(a, "x", 8);
            let y = bv(a, "y", 8);
            a.bv_mul(x, y).unwrap()
        });
        let encoding = encode(&instance);
        let formula = encoding.formula();
        let table = XorGateTable::from_encoding(&instance.aig, &encoding);

        let mut mined_groups = std::collections::BTreeSet::new();
        let mut hinted_groups = std::collections::BTreeSet::new();
        for clause in formula.clauses() {
            if let Some((key, _)) = clause_key_and_mask(clause) {
                mined_groups.insert(key);
                if table.keys().contains(&key) {
                    hinted_groups.insert(key);
                }
            }
        }
        assert!(!hinted_groups.is_empty(), "the multiplier has XOR gates");
        assert!(
            hinted_groups.len() * 2 < mined_groups.len(),
            "the table must cut the group count well below half: {} of {}",
            hinted_groups.len(),
            mined_groups.len()
        );
    }
}
