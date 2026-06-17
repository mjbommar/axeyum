//! Alethe proof **emission** for a first slice of general `QF_BV` `unsat`
//! refutations — the **variable/constant predicate fragment** (Track 3, the
//! producer counterpart to the bitblast-step emitter [`crate::bitblast_step`]
//! and the EUF/LRA emitters [`crate::prove_qf_uf_unsat_alethe`] /
//! [`crate::prove_lra_unsat_alethe`]).
//!
//! [`prove_qf_bv_unsat_alethe`] builds a complete, **Carcara-checkable** Alethe
//! proof closing to the empty clause `(cl)` for a `QF_BV` conjunction whose every
//! assertion is a *predicate over bit-vector variables/constants*:
//!
//! - a positive predicate `(= x y)`, `(bvult x y)`, or `(bvslt x y)`, or
//! - a negated predicate `(not (= x y))`, `(not (bvult x y))`, `(not (bvslt x y))`,
//!
//! where each operand is a bit-vector **variable or constant** (a
//! [`TermNode::Symbol`] or [`TermNode::BvConst`]) — **no compound bit-vector
//! subterms** like `(bvand a b)`. Anything outside that fragment (a compound
//! operand, an unsupported predicate, a non-bit-vector operand, a non-predicate
//! Boolean assertion) yields [`None`], as does a query that is **not** genuinely
//! `unsat`.
//!
//! ## How the proof is built
//!
//! 1. **Confirm `unsat`.** The conjunction is run through the pure-Rust
//!    [`crate::SatBvBackend`]; a non-`unsat` (or undecided) result returns [`None`].
//! 2. **Per assertion `φ`:** `assume φ`, then `bitblast_step` the underlying
//!    predicate to `(= pred B)`, then derive the *Boolean form* of the assertion as
//!    a unit clause — `(cl B)` for a positive assertion, `(cl (not B))` for a
//!    negated one — via `equiv1`/`equiv2` + `resolution` (exactly the committed
//!    template `tests/carcara_crosscheck.rs::full_qf_bv_unsat_proof_is_accepted_by_carcara`).
//! 3. **Refute the bit-level Boolean problem.** Each Boolean form `B` is a
//!    propositional formula over **bit atoms** `((_ @bit_of i) v)` (leaves, since
//!    operands are vars/consts). The forms are Tseitin-encoded into clauses, where a
//!    compound subterm is used directly as its own gate variable so the Carcara
//!    CNF-introduction rules match structurally. Every Tseitin defining clause is
//!    justified by a premise-free CNF-introduction step — `and_pos`/`and_neg` for a
//!    conjunction, `or_pos`/`or_neg` for a disjunction, `equiv_pos1`/`equiv_pos2`/
//!    `equiv_neg1`/`equiv_neg2` for a Boolean `=`, `xor_pos1`/`xor_pos2`/`xor_neg1`/
//!    `xor_neg2` for an `xor`; a `not` folds into the literal polarity (with the
//!    syntactic `(not …)` nesting kept in the emitted clause, which Carcara
//!    resolution collapses by parity). The clause set is refuted by the in-tree
//!    proof-producing SAT core (`solve_with_drat_proof` → `elaborate_drat_to_lrat`),
//!    whose LRAT resolution chain is replayed as Alethe `resolution` steps to `(cl)`.
//!
//! Every returned proof has been built deterministically (stable ids, sorted
//! variable maps — no hash-map iteration in the output); the soundness gate is the
//! external Carcara binary, exercised by the gated cross-check tests.

use std::collections::BTreeMap;

use axeyum_cnf::{
    AletheClause, AletheCommand, AletheLit, AletheTerm, CnfClause, CnfFormula, CnfLit, CnfVar,
    LratStep, ProofSolveOutcome, elaborate_drat_to_lrat, solve_with_drat_proof,
};
use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};

use crate::backend::{CheckResult, SolverBackend, SolverConfig};
use crate::bitblast_step;
use crate::sat_bv_backend::SatBvBackend;

/// Emits a complete, Carcara-checkable Alethe refutation for an `unsat` `QF_BV`
/// conjunction in the **variable/constant predicate fragment**, or [`None`] when
/// the query is outside that fragment or is not genuinely `unsat`.
///
/// The supported fragment (v1): every assertion is one of
///
/// - `(= x y)`, `(bvult x y)`, `(bvslt x y)` — a positive predicate, or
/// - `(not (= x y))`, `(not (bvult x y))`, `(not (bvslt x y))` — its negation,
///
/// where each operand `x`, `y` is a bit-vector **variable** ([`TermNode::Symbol`])
/// or **constant** ([`TermNode::BvConst`]) of the same width — there are **no
/// compound bit-vector subterms**. The returned proof closes to the empty clause
/// `(cl)` and is accepted by the external Carcara checker (see the gated tests in
/// `tests/carcara_crosscheck.rs`).
///
/// Returns [`None`] when:
///
/// - the conjunction is `sat` or undecided (so there is no refutation to emit);
/// - any assertion is outside the fragment — a compound bit-vector operand
///   (`(= (bvand a b) c)`), an unsupported predicate (`bvule`, `bvugt`, …), a
///   non-bit-vector operand, or a non-predicate Boolean assertion; or
/// - the bit-level Boolean problem cannot be closed to `(cl)` (defensive — does not
///   occur for a genuinely `unsat` instance in the fragment).
///
/// The emission is deterministic: assume/step ids and the atom→variable map are
/// assigned in a stable order, with no hash-map iteration in the output.
///
/// # Panics
///
/// Does not panic for any input; arena access is total over well-formed terms.
#[must_use]
pub fn prove_qf_bv_unsat_alethe(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // 1. Parse every assertion into the supported fragment up front; bail on any
    //    out-of-fragment assertion before doing any solving.
    let parsed: Vec<Asserted> = assertions
        .iter()
        .map(|&t| classify_assertion(arena, t))
        .collect::<Option<Vec<_>>>()?;
    if parsed.is_empty() {
        return None;
    }

    // 2. Confirm the conjunction is genuinely unsat with the pure-Rust SAT-BV path.
    if !is_unsat(arena, assertions) {
        return None;
    }

    // 3. Emit the proof.
    let mut builder = Builder::new();

    // The propositional refutation collects each assertion's Boolean form as a
    // CNF clause over the bit atoms, keyed by the canonical atom text.
    let mut tseitin = Tseitin::new();
    // (clause-id-in-formula → Alethe step id) for the input clauses fed to the SAT
    // core; the LRAT bridge resolves learned clauses against these.
    let mut input_clause_ids: Vec<(Vec<CnfLit>, String)> = Vec::new();

    // Emit every `assume` first (Alethe convention; some checkers warn otherwise).
    let assume_ids: Vec<String> = parsed
        .iter()
        .map(|item| -> Option<String> {
            let pred_alethe = predicate_to_alethe(arena, item.predicate)?;
            Some(builder.assume(vec![AletheLit {
                atom: pred_alethe,
                negated: item.negated,
            }]))
        })
        .collect::<Option<Vec<_>>>()?;

    for (k, item) in parsed.iter().enumerate() {
        let pred = item.predicate;
        let negated = item.negated;
        let assume_id = assume_ids[k].clone();
        let pred_alethe = predicate_to_alethe(arena, pred)?;

        // bitblast_step the predicate → (= pred B).
        let bb_id = format!("bb{k}");
        let bb = bitblast_step(arena, pred, &bb_id)?;
        let boolean_form = bitblast_boolean_form(&bb)?;
        builder.push(bb);

        // Derive the Boolean form of the assertion as a unit clause.
        // Positive: equiv1 (= pred B) → (cl (not pred) B), resolve with (cl pred) → (cl B).
        // Negated: equiv2 (= pred B) → (cl pred (not B)), resolve with (cl (not pred)) → (cl (not B)).
        let bool_unit = if negated {
            let e_id = builder.step(
                vec![pos(pred_alethe.clone()), neg(boolean_form.clone())],
                "equiv2",
                &[&bb_id],
            );
            builder.step(
                vec![neg(boolean_form.clone())],
                "resolution",
                &[&e_id, &assume_id],
            )
        } else {
            let e_id = builder.step(
                vec![neg(pred_alethe.clone()), pos(boolean_form.clone())],
                "equiv1",
                &[&bb_id],
            );
            builder.step(
                vec![pos(boolean_form.clone())],
                "resolution",
                &[&e_id, &assume_id],
            )
        };

        // Tseitin-encode B and register the top-level unit `(cl B)` / `(cl (not B))`
        // as an input clause for the SAT refutation, justified by `bool_unit`.
        let root_lit = tseitin.encode(&mut builder, &boolean_form)?;
        let root_lit = if negated {
            root_lit.wrap_not()
        } else {
            root_lit
        };
        input_clause_ids.push((vec![root_lit.to_cnf(&tseitin)], bool_unit));
    }

    // Add every Tseitin defining clause (each already an emitted Alethe step) as an
    // input clause for the SAT core.
    for gate in &tseitin.gate_clauses {
        input_clause_ids.push((
            gate.lits.iter().map(|l| l.to_cnf(&tseitin)).collect(),
            gate.step_id.clone(),
        ));
    }

    // 4. Build the propositional formula and refute it.
    refute(&mut builder, &tseitin, &input_clause_ids)
}

/// A parsed in-fragment assertion: the (possibly inner) predicate term and whether
/// the assertion negated it.
struct Asserted {
    predicate: TermId,
    negated: bool,
}

/// Classifies an assertion into the supported fragment, returning the inner
/// predicate and its polarity, or [`None`] if out of fragment.
fn classify_assertion(arena: &TermArena, term: TermId) -> Option<Asserted> {
    // Peel a single `not`.
    if let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    {
        let inner = *args.first()?;
        let pred = supported_predicate(arena, inner)?;
        return Some(Asserted {
            predicate: pred,
            negated: true,
        });
    }
    let pred = supported_predicate(arena, term)?;
    Some(Asserted {
        predicate: pred,
        negated: false,
    })
}

/// Returns `term` if it is a supported predicate (`=`, `bvult`, `bvslt`) over two
/// bit-vector **variable/constant** operands, else [`None`].
fn supported_predicate(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    if !matches!(op, Op::Eq | Op::BvUlt | Op::BvSlt) {
        return None;
    }
    let [a, b] = &args[..] else {
        return None;
    };
    // Operands must be bit-vector vars/consts (no compound subterms).
    if !is_leaf_bv(arena, *a) || !is_leaf_bv(arena, *b) {
        return None;
    }
    Some(term)
}

/// Whether `term` is a bit-vector **variable** or **constant** (a leaf operand the
/// fragment permits — no compound bit-vector subterm).
fn is_leaf_bv(arena: &TermArena, term: TermId) -> bool {
    if !matches!(arena.sort_of(term), Sort::BitVec(_)) {
        return false;
    }
    matches!(
        arena.node(term),
        TermNode::Symbol(_) | TermNode::BvConst { .. }
    )
}

/// Renders the supported predicate `term` as the Alethe atom Carcara expects for the
/// `assume` (matching the bitblast step's LHS): `(= x y)`, `(bvult x y)`, `(bvslt x y)`.
fn predicate_to_alethe(arena: &TermArena, term: TermId) -> Option<AletheTerm> {
    let TermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    let head = match op {
        Op::Eq => "=",
        Op::BvUlt => "bvult",
        Op::BvSlt => "bvslt",
        _ => return None,
    };
    let rendered = args
        .iter()
        .map(|&a| leaf_to_alethe(arena, a))
        .collect::<Option<Vec<_>>>()?;
    Some(AletheTerm::App(head.to_owned(), rendered))
}

/// Renders a leaf bit-vector operand (variable or constant) as an Alethe term, the
/// same way [`crate::bitblast_step`] renders it (so the `assume` matches the step).
fn leaf_to_alethe(arena: &TermArena, term: TermId) -> Option<AletheTerm> {
    match arena.node(term) {
        TermNode::Symbol(symbol) => {
            let (name, _sort) = arena.symbol(*symbol);
            Some(AletheTerm::Const(name.to_owned()))
        }
        TermNode::BvConst { width, value } => {
            Some(AletheTerm::Const(bv_const_literal(*width, *value)))
        }
        _ => None,
    }
}

/// Renders a bit-vector constant as the SMT-LIB `#b…` binary literal (MSB-first),
/// matching the bitblast emitter's rendering.
fn bv_const_literal(width: u32, value: u128) -> String {
    let mut out = String::with_capacity(2 + width as usize);
    out.push_str("#b");
    for i in (0..width).rev() {
        out.push(if (value >> i) & 1 == 1 { '1' } else { '0' });
    }
    out
}

/// Pulls the Boolean form `B` out of a predicate bitblast step's conclusion
/// `(= pred B)`. Returns [`None`] if the step is not the expected predicate shape.
fn bitblast_boolean_form(step: &AletheCommand) -> Option<AletheTerm> {
    let AletheCommand::Step { clause, .. } = step else {
        return None;
    };
    let [lit] = clause.as_slice() else {
        return None;
    };
    if lit.negated {
        return None;
    }
    let AletheTerm::App(head, args) = &lit.atom else {
        return None;
    };
    if head != "=" || args.len() != 2 {
        return None;
    }
    // For a predicate the RHS is a plain Boolean (no @bbterm wrapper).
    Some(args[1].clone())
}

/// Confirms the conjunction is `unsat` via the pure-Rust SAT-BV backend.
fn is_unsat(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    matches!(
        backend.check(arena, assertions, &config),
        Ok(CheckResult::Unsat)
    )
}

// --- Alethe command builder -------------------------------------------------

/// Builds the proof command list with deterministic step ids.
struct Builder {
    commands: Vec<AletheCommand>,
    next_assume: usize,
    next_step: usize,
}

impl Builder {
    fn new() -> Self {
        Self {
            commands: Vec::new(),
            next_assume: 0,
            next_step: 0,
        }
    }

    fn assume(&mut self, clause: AletheClause) -> String {
        let id = format!("h{}", self.next_assume);
        self.next_assume += 1;
        self.commands.push(AletheCommand::Assume {
            id: id.clone(),
            clause,
        });
        id
    }

    /// Pushes an already-built command (e.g. a `bitblast_*` step from the emitter).
    fn push(&mut self, command: AletheCommand) {
        self.commands.push(command);
    }

    /// Emits a step with a fresh `s<n>` id, no `:args`; returns the id.
    fn step(&mut self, clause: AletheClause, rule: &str, premises: &[&str]) -> String {
        self.step_args(clause, rule, premises, Vec::new())
    }

    /// Emits a step with a fresh `s<n>` id and the given `:args`; returns the id.
    fn step_args(
        &mut self,
        clause: AletheClause,
        rule: &str,
        premises: &[&str],
        args: Vec<AletheTerm>,
    ) -> String {
        let id = format!("s{}", self.next_step);
        self.next_step += 1;
        self.commands.push(AletheCommand::Step {
            id: id.clone(),
            clause,
            rule: rule.to_owned(),
            premises: premises.iter().map(|p| (*p).to_owned()).collect(),
            args,
        });
        id
    }
}

fn pos(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: false,
    }
}

fn neg(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: true,
    }
}

// --- Tseitin encoding of the bit-level Boolean forms ------------------------

/// A propositional literal in the Tseitin encoding.
///
/// `view` is the **verbatim** subterm as it appears as an operand of a gate —
/// possibly `(not …)`-wrapped — so the Carcara CNF-introduction rules (which match
/// each operand `φi` structurally against the gate term) see the exact syntax. For
/// the CNF/SAT layer we normalize: `base` is `view` with all leading `not`s peeled,
/// and `parity` is `true` when an **odd** number of `not`s were peeled (the literal
/// is the negation of `base`). The two views agree semantically; only the
/// negation **nesting** differs (Carcara resolution collapses it by parity).
#[derive(Clone)]
struct PLit {
    /// The operand term exactly as written (for Alethe emission).
    view: AletheTerm,
    /// `view` with all leading `not`s removed (the CNF/SAT atom).
    base: AletheTerm,
    /// Whether `view` negates `base` (odd negation count).
    parity: bool,
}

impl PLit {
    /// A leaf/gate literal whose `view` and `base` coincide (no leading `not`).
    fn positive(term: AletheTerm) -> PLit {
        PLit {
            view: term.clone(),
            base: term,
            parity: false,
        }
    }

    /// The literal for the operand `(not view)` — wraps `view` in a syntactic
    /// `not` and flips the CNF parity.
    fn wrap_not(&self) -> PLit {
        PLit {
            view: AletheTerm::App("not".to_owned(), vec![self.view.clone()]),
            base: self.base.clone(),
            parity: !self.parity,
        }
    }

    /// The Alethe literal that asserts the operand itself: the positive literal
    /// `view`. (`view` already carries any `not` nesting syntactically.)
    fn lit_view(&self) -> AletheLit {
        AletheLit {
            atom: self.view.clone(),
            negated: false,
        }
    }

    /// The Alethe literal that asserts the **negation** of the operand: the
    /// syntactic `(not view)`.
    fn lit_not_view(&self) -> AletheLit {
        AletheLit {
            atom: AletheTerm::App("not".to_owned(), vec![self.view.clone()]),
            negated: false,
        }
    }

    fn to_cnf(&self, tseitin: &Tseitin) -> CnfLit {
        let var = tseitin.var_of(&self.base);
        let base = CnfLit::positive(var);
        if self.parity { base.negated() } else { base }
    }
}

/// One emitted Tseitin defining clause: its propositional literals and the Alethe
/// step id that justifies it.
struct GateClause {
    lits: Vec<PLit>,
    step_id: String,
}

/// The Tseitin encoder: walks a Boolean form, introducing a fresh gate atom for
/// each compound subterm, emitting the defining clauses (each a Carcara
/// CNF-introduction step), and recording an atom→`CnfVar` map for the SAT core.
struct Tseitin {
    /// Canonical atom key → [`CnfVar`] (deterministic by insertion order).
    var_of: BTreeMap<String, CnfVar>,
    /// [`CnfVar`] index → the atom term it represents (the inverse of `var_of`, used
    /// to render learned-clause atoms — kept verbatim so no key reparse is needed).
    atom_terms: Vec<AletheTerm>,
    /// Memo of already-encoded compound subterms (by key) → their gate literal.
    memo: BTreeMap<String, PLit>,
    /// Emitted defining clauses.
    gate_clauses: Vec<GateClause>,
}

impl Tseitin {
    fn new() -> Self {
        Self {
            var_of: BTreeMap::new(),
            atom_terms: Vec::new(),
            memo: BTreeMap::new(),
            gate_clauses: Vec::new(),
        }
    }

    /// The `CnfVar` for `atom`, allocating one on first sight (deterministic).
    fn var_of(&self, atom: &AletheTerm) -> CnfVar {
        *self
            .var_of
            .get(&atom.key())
            .expect("atom registered before lowering")
    }

    fn register(&mut self, atom: &AletheTerm) {
        let key = atom.key();
        if !self.var_of.contains_key(&key) {
            let index = self.var_of.len();
            let var = CnfVar::new(index).expect("variable index fits");
            self.var_of.insert(key, var);
            self.atom_terms.push(atom.clone());
        }
    }

    fn total_vars(&self) -> usize {
        self.var_of.len()
    }

    /// Encodes `term` (a Boolean formula), returning the literal equivalent to it.
    /// Leaves (bit projections) return themselves; a `(not …)` wraps its inner
    /// literal syntactically (no new variable); compound gates introduce the gate
    /// term as a variable and emit the defining clauses.
    fn encode(&mut self, builder: &mut Builder, term: &AletheTerm) -> Option<PLit> {
        match term {
            AletheTerm::Indexed { .. } | AletheTerm::Const(_) => {
                self.register(term);
                Some(PLit::positive(term.clone()))
            }
            AletheTerm::App(head, args) => {
                let key = term.key();
                if let Some(lit) = self.memo.get(&key) {
                    return Some(lit.clone());
                }
                let lit = match (head.as_str(), args.len()) {
                    ("not", 1) => {
                        // Syntactic negation: wrap the inner literal's view in `not`
                        // and flip its CNF parity; do NOT allocate a fresh variable.
                        let inner = self.encode(builder, &args[0])?;
                        inner.wrap_not()
                    }
                    ("and", _) => self.encode_gate(builder, term, GateKind::And, args)?,
                    ("or", _) => self.encode_gate(builder, term, GateKind::Or, args)?,
                    ("=", 2) => self.encode_gate(builder, term, GateKind::Equiv, args)?,
                    ("xor", 2) => self.encode_gate(builder, term, GateKind::Xor, args)?,
                    _ => return None,
                };
                // Memoize compound gates (a `not` is cheap and view-dependent, so it
                // is recomputed; gates carry emitted clauses, so memoize them).
                if !matches!(head.as_str(), "not") {
                    self.memo.insert(key, lit.clone());
                }
                Some(lit)
            }
        }
    }

    /// Introduces the gate term `g = term` as a propositional variable, encodes each
    /// operand to a literal, and emits the Tseitin defining clauses `g ↔ op(operands)`
    /// as Carcara CNF-introduction steps (no premises — pure tautologies). Returns the
    /// positive gate literal. Each emitted Alethe clause uses the operand **verbatim**
    /// (`operand.lit_view`) or its syntactic negation (`operand.lit_not_view`), so the
    /// rules match structurally; the recorded CNF clause normalizes the negation parity.
    fn encode_gate(
        &mut self,
        builder: &mut Builder,
        term: &AletheTerm,
        kind: GateKind,
        args: &[AletheTerm],
    ) -> Option<PLit> {
        let operands: Vec<PLit> = args
            .iter()
            .map(|a| self.encode(builder, a))
            .collect::<Option<Vec<_>>>()?;

        self.register(term);
        let gate = PLit::positive(term.clone());

        match kind {
            GateKind::And => self.encode_and(builder, &gate, &operands),
            GateKind::Or => self.encode_or(builder, &gate, &operands),
            GateKind::Equiv => self.encode_binary(builder, &gate, &operands, GateKind::Equiv)?,
            GateKind::Xor => self.encode_binary(builder, &gate, &operands, GateKind::Xor)?,
        }
        Some(gate)
    }

    /// Emits one CNF-introduction step (`rule`/`args`) and records its CNF clause.
    /// `lits` pairs the emitted Alethe literal with its normalized CNF literal.
    fn emit(
        &mut self,
        builder: &mut Builder,
        rule: &str,
        args: Vec<AletheTerm>,
        lits: Vec<(AletheLit, PLit)>,
    ) {
        let (clause, plits): (Vec<AletheLit>, Vec<PLit>) = lits.into_iter().unzip();
        let id = builder.step_args(clause, rule, &[], args);
        self.gate_clauses.push(GateClause {
            lits: plits,
            step_id: id,
        });
    }

    /// The `and` defining clauses: `and_pos` per conjunct (`g → ti`) and one
    /// `and_neg` (`(⋀ ti) → g`).
    fn encode_and(&mut self, builder: &mut Builder, gate: &PLit, operands: &[PLit]) {
        let term = gate.view.clone();
        for (i, operand) in operands.iter().enumerate() {
            self.emit(
                builder,
                "and_pos",
                vec![AletheTerm::Const(i.to_string())],
                vec![
                    (neg(term.clone()), gate.wrap_not()),
                    (operand.lit_view(), operand.clone()),
                ],
            );
        }
        let mut lits = vec![(pos(term), gate.clone())];
        for operand in operands {
            lits.push((operand.lit_not_view(), operand.wrap_not()));
        }
        self.emit(builder, "and_neg", Vec::new(), lits);
    }

    /// The `or` defining clauses: one `or_pos` (`g → (⋁ ti)`) and `or_neg` per
    /// disjunct (`ti → g`).
    fn encode_or(&mut self, builder: &mut Builder, gate: &PLit, operands: &[PLit]) {
        let term = gate.view.clone();
        let mut lits = vec![(neg(term.clone()), gate.wrap_not())];
        for operand in operands {
            lits.push((operand.lit_view(), operand.clone()));
        }
        self.emit(builder, "or_pos", Vec::new(), lits);
        for (i, operand) in operands.iter().enumerate() {
            self.emit(
                builder,
                "or_neg",
                vec![AletheTerm::Const(i.to_string())],
                vec![
                    (pos(term.clone()), gate.clone()),
                    (operand.lit_not_view(), operand.wrap_not()),
                ],
            );
        }
    }

    /// The four defining clauses for a binary `=` (`Equiv`) or `xor` gate.
    fn encode_binary(
        &mut self,
        builder: &mut Builder,
        gate: &PLit,
        operands: &[PLit],
        kind: GateKind,
    ) -> Option<()> {
        let [a, b] = operands else {
            return None;
        };
        let term = gate.view.clone();
        // Per row: (rule, gate polarity wraps `term`, a's negation, b's negation).
        // `equiv`/`xor` differ only in which (a,b) polarity combinations land in the
        // positive vs negative `term` rows.
        let rows: [(&str, bool, bool, bool); 4] = match kind {
            GateKind::Equiv => [
                ("equiv_pos1", true, false, true),
                ("equiv_pos2", true, true, false),
                ("equiv_neg1", false, true, true),
                ("equiv_neg2", false, false, false),
            ],
            GateKind::Xor => [
                ("xor_pos1", true, false, false),
                ("xor_pos2", true, true, true),
                ("xor_neg1", false, false, true),
                ("xor_neg2", false, true, false),
            ],
            _ => return None,
        };
        for (rule, gate_neg, a_neg, b_neg) in rows {
            let gate_lit = if gate_neg {
                (neg(term.clone()), gate.wrap_not())
            } else {
                (pos(term.clone()), gate.clone())
            };
            let a_lit = if a_neg {
                (a.lit_not_view(), a.wrap_not())
            } else {
                (a.lit_view(), a.clone())
            };
            let b_lit = if b_neg {
                (b.lit_not_view(), b.wrap_not())
            } else {
                (b.lit_view(), b.clone())
            };
            self.emit(builder, rule, Vec::new(), vec![gate_lit, a_lit, b_lit]);
        }
        Some(())
    }
}

/// The Boolean connective a Tseitin gate encodes.
#[derive(Clone, Copy)]
enum GateKind {
    And,
    Or,
    Equiv,
    Xor,
}

// --- Propositional refutation: SAT core → LRAT → Alethe resolution ----------

/// Refutes the collected input clauses (each already an emitted Alethe step) with
/// the proof-producing SAT core, replaying the LRAT resolution chain as Alethe
/// `resolution` steps down to `(cl)`. Returns the full command list, or [`None`] if
/// the formula is unexpectedly not refuted.
fn refute(
    builder: &mut Builder,
    tseitin: &Tseitin,
    input_clause_ids: &[(Vec<CnfLit>, String)],
) -> Option<Vec<AletheCommand>> {
    let mut formula = CnfFormula::new(tseitin.total_vars());
    // clause index in formula → Alethe step id of its (cl …) form.
    let mut clause_step: BTreeMap<u64, String> = BTreeMap::new();
    for (i, (lits, step_id)) in input_clause_ids.iter().enumerate() {
        formula.add_clause(CnfClause::new(lits.clone())).ok()?;
        // LRAT numbers input clauses 1..=N.
        clause_step.insert(i as u64 + 1, step_id.clone());
    }

    let ProofSolveOutcome::Unsat(drat) = solve_with_drat_proof(&formula) else {
        return None;
    };
    let lrat = elaborate_drat_to_lrat(&formula, &drat).ok()?;

    // Replay each LRAT addition as an Alethe resolution step over the antecedent
    // clauses' Alethe ids. The learned clause is RUP from its hints, so the
    // resolution entailment holds; the final empty clause closes the proof.
    for step in &lrat {
        let LratStep::Add { id, clause, hints } = step else {
            continue;
        };
        let alethe_clause = cnf_clause_to_alethe(tseitin, clause)?;
        let premises: Vec<String> = hints
            .iter()
            .map(|h| clause_step.get(h).cloned())
            .collect::<Option<Vec<_>>>()?;
        let premise_refs: Vec<&str> = premises.iter().map(String::as_str).collect();
        let step_id = builder.step(alethe_clause, "resolution", &premise_refs);
        clause_step.insert(*id, step_id);
    }

    Some(builder.commands_snapshot())
}

/// Maps a CNF clause back to an Alethe clause over the original bit/gate atoms,
/// inverting the `Tseitin` variable map.
fn cnf_clause_to_alethe(tseitin: &Tseitin, clause: &[CnfLit]) -> Option<AletheClause> {
    clause
        .iter()
        .map(|lit| {
            let atom = tseitin.atom_of_var(lit.var())?;
            Some(AletheLit {
                atom,
                negated: lit.is_negated(),
            })
        })
        .collect()
}

impl Tseitin {
    /// The Alethe atom for a `CnfVar` (inverse of [`Tseitin::var_of`]); returns the
    /// verbatim term recorded at registration, with no key reparse.
    fn atom_of_var(&self, var: CnfVar) -> Option<AletheTerm> {
        self.atom_terms.get(var.index()).cloned()
    }
}

impl Builder {
    fn commands_snapshot(&self) -> Vec<AletheCommand> {
        self.commands.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::prove_qf_bv_unsat_alethe;
    use axeyum_cnf::AletheCommand;
    use axeyum_ir::{Sort, TermArena, TermId};

    fn bv(arena: &mut TermArena, name: &str, width: u32) -> TermId {
        let s = arena.declare(name, Sort::BitVec(width)).expect("declare");
        arena.var(s)
    }

    /// The emitted proof must end in an empty-clause `resolution` step (`(cl)`),
    /// regardless of the external checker.
    fn closes_to_empty(proof: &[AletheCommand]) -> bool {
        matches!(
            proof.last(),
            Some(AletheCommand::Step { clause, rule, .. })
                if clause.is_empty() && rule == "resolution"
        )
    }

    #[test]
    fn template_instance_emits_a_closing_proof() {
        // (= a b) ∧ (bvult a b), 1-bit — the committed template, reproduced.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 1);
        let b = bv(&mut arena, "b", 1);
        let eq = arena.eq(a, b).unwrap();
        let ult = arena.bv_ult(a, b).unwrap();
        let proof = prove_qf_bv_unsat_alethe(&arena, &[eq, ult]).expect("unsat proof");
        assert!(closes_to_empty(&proof), "proof must close to (cl)");
    }

    #[test]
    fn negated_equality_emits_a_closing_proof() {
        // (= a b) ∧ (not (= a b)) over width 2.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let eq = arena.eq(a, b).unwrap();
        let neq = arena.not(eq).unwrap();
        let proof = prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("unsat proof");
        assert!(closes_to_empty(&proof));
    }

    #[test]
    fn deterministic_emission() {
        // The driver is deterministic: two runs over the same query emit identical
        // command lists (no hash-map iteration in the output).
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let ab = arena.bv_ult(a, b).unwrap();
        let ba = arena.bv_ult(b, a).unwrap();
        let p1 = prove_qf_bv_unsat_alethe(&arena, &[ab, ba]).expect("unsat proof");
        let p2 = prove_qf_bv_unsat_alethe(&arena, &[ab, ba]).expect("unsat proof");
        assert_eq!(p1, p2);
    }

    #[test]
    fn sat_instance_is_none() {
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let ult = arena.bv_ult(a, b).unwrap();
        assert!(prove_qf_bv_unsat_alethe(&arena, &[ult]).is_none());
    }

    #[test]
    fn compound_operand_is_none() {
        // (= (bvand a b) a) ∧ (not …) is unsat, but the compound operand is out of fragment.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let and = arena.bv_and(a, b).unwrap();
        let eq = arena.eq(and, a).unwrap();
        let neq = arena.not(eq).unwrap();
        assert!(prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).is_none());
    }

    #[test]
    fn unsupported_predicate_is_none() {
        // bvule is not in the v1 predicate set, even when the instance is unsat.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let le = arena.bv_ule(a, b).unwrap();
        let lt = arena.bv_ult(b, a).unwrap();
        // a <= b ∧ b < a is unsat, but bvule is unsupported → None.
        assert!(prove_qf_bv_unsat_alethe(&arena, &[le, lt]).is_none());
    }

    #[test]
    fn empty_assertions_is_none() {
        let arena = TermArena::new();
        assert!(prove_qf_bv_unsat_alethe(&arena, &[]).is_none());
    }
}
