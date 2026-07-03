//! Alethe proof **emission** for independently re-checked **word-level**
//! (string/sequence) refutations — the producer counterpart to the T-B.7
//! [`axeyum_strings::refute_word_equations`] checker and the missing external
//! artifact the 4th review's Lean ledger demanded.
//!
//! [`axeyum_strings`] already ships word-level `unsat` only behind an independent
//! re-derivation ([`axeyum_strings::check_conflict`] / [`axeyum_strings::check_fact`] /
//! [`axeyum_strings::check_cycle_constant_conflict`], ADR-0053). That check runs **in process** and
//! computes a minimal premise set, but produces no checkable *artifact*, so a word
//! `unsat` could not carry a certificate (`is_certified` stayed `false`). This
//! module closes that gap: it emits a self-validating Alethe proof for a
//! re-checked word refutation.
//!
//! # The proof mapping (design)
//!
//! A certified word conflict, in the [`axeyum_strings`] taxonomy, is one of:
//!
//! - **(a) aligned constant clash** — two members joined into one equivalence
//!   class by a chain of premise equalities, whose normalized component vectors
//!   clash at an equal-length-aligned position on two distinct constant blocks
//!   ([`axeyum_strings::check_conflict`] / `augmented_constant_clash`);
//! - **(b) self-loop constant contradiction** — `x ≈ "a" ++ x` and kin: a cycle
//!   forcing a nonempty constant to `ε` ([`axeyum_strings::check_cycle_constant_conflict`]);
//! - **(c) contradicted disequality** — `a ≠ b` whose two sides a premise
//!   equality-chain places in one class ([`axeyum_strings::check_equality`]).
//!
//! The ideal Alethe rendering is a two-part proof:
//!
//! 1. **assumptions** — the cited premise equalities `(= aᵢ bᵢ)` and, for the
//!    disequality shape, the contradicting `(not (= s t))`, over SMT-LIB
//!    string terms (`str.++` / `seq.unit` / `seq.empty` / character literals);
//! 2. **equality-joining** — `trans`/`symm`/`cong` chains over the premise
//!    equalities that carry the two clashing terms into one derived equality
//!    `(= M_a M_b)` (Carcara-valid EUF); then
//! 3. **the clash** — a theory-tautology step closing `(= M_a M_b)` against the
//!    fact that two clashing normal forms cannot be equal.
//!
//! Alethe has **no native string-clash rule**, so — exactly as `la_generic` /
//! `lia_generic` do for arithmetic — step (3) uses a dedicated rule
//! [`WORD_CLASH_RULE`] (`axeyum_word_clash`) validated by a **pluggable callback**
//! (the [`axeyum_cnf::check_alethe_with`] `extra` hook) that re-derives the clash
//! with the **independent** [`axeyum_strings`] checker
//! ([`refute_word_equations`], itself gated by `check_derivation`). Nothing in the
//! clause is trusted: the callback rebuilds the string system from the clause's own
//! literals in a fresh arena and demands [`RefuteOutcome::Unsat`].
//!
//! ## What this slice actually emits
//!
//! The public refutation API ([`refute_word_equations`]) exposes only the **premise
//! index set** of a conflict — *not* the internal member/position/constant
//! witnesses that a targeted `trans` chain to a specific `(= M_a M_b)` would need.
//! So, rather than trust an un-witnessed reconstruction, this emitter folds the
//! whole equality-joining into the single theory-tautology step — the direct
//! parallel of the `la_generic` emitter, which likewise emits **one** tautology
//! clause `(cl ¬φ₁ … ¬φₙ)` rather than sub-derivations:
//!
//! ```text
//! (assume h_i (= a_i b_i))                       ; each cited premise equality
//! (assume d_j (not (= s_j t_j)))                 ; each contradicting disequality
//! (step clash (cl (not (= a_i b_i)) … (= s_j t_j) …) :rule axeyum_word_clash)
//! (step empty (cl) :rule resolution :premises (clash h_i … d_j …))
//! ```
//!
//! The `clash` clause is precisely the **negation of the assumed premise
//! conjunction**; it is valid iff that conjunction is word-`unsat`, which the
//! callback re-verifies. The final `resolution` ties the clause to the actual
//! assumptions (an independently-checked entailment via `check_alethe`'s SAT core),
//! so a tampered clause that no longer negates the assumes fails to derive `(cl)`.
//!
//! # The custom-rule hole (disclosed)
//!
//! [`WORD_CLASH_RULE`] is **not** a rule Carcara knows, so a third-party Alethe
//! checker will reject the `clash` step — the same, documented, `lia_generic`-class
//! hole. What we guarantee is the *self-check*: every certificate this module
//! returns has passed [`axeyum_cnf::check_alethe_with`] under the word-clash
//! callback and derives the empty clause (verify-before-record: a construction bug
//! is an `Err`, never a bogus certificate). The assumptions and the final
//! resolution are ordinary Carcara-valid Alethe; only the one clash step is the
//! plugged theory rule.

use std::collections::BTreeSet;

use axeyum_cnf::{AletheClause, AletheCommand, AletheLit, AletheTerm, check_alethe_with};
use axeyum_ir::{ArraySortKey, Op, Sort, TermArena, TermId, TermNode};
use axeyum_strings::{RefuteOutcome, SearchBudget, refute_word_equations};

/// The dedicated clash rule name (parallels `la_generic` / `lia_generic`): a
/// tautology clause `(cl (not (= a b)) …)` whose validity is the word-`unsat` of
/// the assumed premise conjunction, re-checked by the plugged callback.
pub const WORD_CLASH_RULE: &str = "axeyum_word_clash";

/// A self-validated Alethe certificate for a word-level (string/sequence)
/// refutation.
///
/// The [`commands`](Self::commands) have passed [`Self::check`] (an
/// [`axeyum_cnf::check_alethe_with`] run under the word-clash callback that derives
/// the empty clause). [`premises`](Self::premises) records the cited **original**
/// equality-premise indices (an unsat core); [`disequality_driven`](Self::disequality_driven)
/// says whether the contradiction needed the disequalities.
#[derive(Debug, Clone)]
pub struct WordClashCertificate {
    /// The self-validated Alethe commands refuting the word system.
    pub commands: Vec<AletheCommand>,
    /// The cited original equality-premise indices (an unsat core).
    pub premises: BTreeSet<usize>,
    /// Whether the refutation used the disequalities (shape (c)) rather than a
    /// pure equality contradiction (shapes (a)/(b)).
    pub disequality_driven: bool,
    /// The sequence element sort key, needed to rebuild terms when re-checking.
    elem: ArraySortKey,
}

impl WordClashCertificate {
    /// Re-checks the embedded proof exactly as emission did: runs
    /// [`axeyum_cnf::check_alethe_with`] with the word-clash callback and requires
    /// it to derive the empty clause. A tampered proof (mutated clause, premise,
    /// constant, or rule) fails here.
    #[must_use]
    pub fn check(&self) -> bool {
        let elem = self.elem;
        matches!(
            check_alethe_with(&self.commands, &move |rule: &str, clause: &[AletheLit]| {
                word_clash_extra(rule, clause, elem)
            }),
            Ok(true)
        )
    }
}

/// Why word-conflict Alethe emission declined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WordAletheError {
    /// The system is not refuted by the independent T-B.7 checker (first-class
    /// `unknown` — never a claim of `sat`).
    NotRefuted,
    /// A premise term is outside the sequence fragment the emitter can render as
    /// an Alethe string term (a nested sequence element, a non-bit-vector element,
    /// or a non-sequence operand).
    UnsupportedTerm,
    /// The assembled proof failed its own [`WordClashCertificate::check`]
    /// (an emitter bug — never returned as a certificate).
    SelfCheckFailed,
}

/// A generous, deadline-free budget: refutation is non-recursive, so this only
/// bounds the internal fixpoint (which is itself hard-bounded).
fn budget() -> SearchBudget {
    SearchBudget::new(50_000_000)
}

/// Emits a self-validated [`WordClashCertificate`] for `equalities ∧ ¬disequalities`
/// over unbounded `Seq`-sorted terms when the independent T-B.7 refutation
/// ([`refute_word_equations`]) certifies it `unsat`, or a [`WordAletheError`]
/// otherwise.
///
/// The certificate is **verify-before-record**: the assembled proof is run through
/// the word-clash callback (which re-derives the clash with the independent
/// [`axeyum_strings`] checker) and returned only if it derives the empty clause —
/// so an emitter bug yields [`WordAletheError::SelfCheckFailed`], never a wrong
/// certificate. Never claims `sat`; a non-refuted system is
/// [`WordAletheError::NotRefuted`].
///
/// # Errors
///
/// - [`WordAletheError::NotRefuted`] — the system is not word-`unsat` (or the
///   cited core does not independently re-refute);
/// - [`WordAletheError::UnsupportedTerm`] — a premise term is outside the
///   renderable sequence fragment;
/// - [`WordAletheError::SelfCheckFailed`] — the proof failed its own re-check.
pub fn word_conflict_alethe(
    arena: &mut TermArena,
    equalities: &[(TermId, TermId)],
    disequalities: &[(TermId, TermId)],
) -> Result<WordClashCertificate, WordAletheError> {
    // (1) Establish the refutation and its minimal premise core through the
    // independent checker. This is the sole `unsat` gate — a hint we then render.
    let RefuteOutcome::Unsat { premises } =
        refute_word_equations(arena, equalities, disequalities, &budget())
    else {
        return Err(WordAletheError::NotRefuted);
    };

    // The element sort key: every renderable term is `Seq(elem)`. Take it from a
    // cited premise (or, failing that, any equality) so `check` can rebuild terms.
    let elem = element_key(arena, equalities, &premises).ok_or(WordAletheError::UnsupportedTerm)?;

    let cited_eqs: Vec<(TermId, TermId)> = premises.iter().map(|&i| equalities[i]).collect();

    // (2) Decide whether the disequalities are actually needed: if the cited
    // equalities alone re-refute, this is a pure equality contradiction (shapes
    // (a)/(b)) and the proof carries no disequality; otherwise it is
    // disequality-driven (shape (c)) and every disequality is assumed.
    let eq_only = matches!(
        refute_word_equations(arena, &cited_eqs, &[], &budget()),
        RefuteOutcome::Unsat { .. }
    );
    let diseqs_used: &[(TermId, TermId)] = if eq_only { &[] } else { disequalities };

    // (3) Render assumptions + the clash tautology + the closing resolution.
    let commands =
        build_proof(arena, &cited_eqs, diseqs_used).ok_or(WordAletheError::UnsupportedTerm)?;

    let cert = WordClashCertificate {
        commands,
        premises,
        disequality_driven: !eq_only,
        elem,
    };

    // (4) Verify-before-record.
    if cert.check() {
        Ok(cert)
    } else {
        Err(WordAletheError::SelfCheckFailed)
    }
}

/// The sequence element sort key of the cited system, or `None` if no cited
/// endpoint is a `Seq`. Prefers a cited premise; falls back to any equality.
fn element_key(
    arena: &TermArena,
    equalities: &[(TermId, TermId)],
    premises: &BTreeSet<usize>,
) -> Option<ArraySortKey> {
    let from = |t: TermId| match arena.sort_of(t) {
        Sort::Seq(k) => Some(k),
        _ => None,
    };
    for &i in premises {
        let (a, b) = *equalities.get(i)?;
        if let Some(k) = from(a).or_else(|| from(b)) {
            return Some(k);
        }
    }
    for &(a, b) in equalities {
        if let Some(k) = from(a).or_else(|| from(b)) {
            return Some(k);
        }
    }
    None
}

/// Builds the assumption / clash / resolution commands, or `None` if any term is
/// outside the renderable sequence fragment.
fn build_proof(
    arena: &TermArena,
    cited_eqs: &[(TermId, TermId)],
    diseqs: &[(TermId, TermId)],
) -> Option<Vec<AletheCommand>> {
    let mut commands = Vec::with_capacity(cited_eqs.len() + diseqs.len() + 2);
    let mut premise_ids: Vec<String> = Vec::with_capacity(cited_eqs.len() + diseqs.len());
    // The clash clause: the negation of the assumed premise conjunction.
    let mut clash: AletheClause = Vec::with_capacity(cited_eqs.len() + diseqs.len());

    // Each equality premise `(= a b)`: assume `(cl (= a b))`, negate it in `clash`.
    for (i, &(a, b)) in cited_eqs.iter().enumerate() {
        let atom = eq_atom(arena, a, b)?;
        let id = format!("h{i}");
        commands.push(AletheCommand::Assume {
            id: id.clone(),
            clause: vec![AletheLit {
                atom: atom.clone(),
                negated: false,
            }],
        });
        premise_ids.push(id);
        clash.push(AletheLit {
            atom,
            negated: true,
        });
    }

    // Each disequality premise `(not (= s t))`: assume `(cl (not (= s t)))`, and
    // put the *positive* `(= s t)` in `clash` (the literal that negates it).
    for (j, &(s, t)) in diseqs.iter().enumerate() {
        let atom = eq_atom(arena, s, t)?;
        let id = format!("d{j}");
        commands.push(AletheCommand::Assume {
            id: id.clone(),
            clause: vec![AletheLit {
                atom: atom.clone(),
                negated: true,
            }],
        });
        premise_ids.push(id);
        clash.push(AletheLit {
            atom,
            negated: false,
        });
    }

    // The theory-tautology clash step.
    commands.push(AletheCommand::Step {
        id: "clash".to_owned(),
        clause: clash,
        rule: WORD_CLASH_RULE.to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });

    // Resolve the clash clause against every assumption to the empty clause.
    let mut resolution_premises = vec!["clash".to_owned()];
    resolution_premises.extend(premise_ids);
    commands.push(AletheCommand::Step {
        id: "empty".to_owned(),
        clause: Vec::new(),
        rule: "resolution".to_owned(),
        premises: resolution_premises,
        args: Vec::new(),
    });

    Some(commands)
}

/// The Alethe atom `(= a b)` over two rendered sequence terms.
fn eq_atom(arena: &TermArena, a: TermId, b: TermId) -> Option<AletheTerm> {
    Some(AletheTerm::App(
        "=".to_owned(),
        vec![seq_to_alethe(arena, a)?, seq_to_alethe(arena, b)?],
    ))
}

// ----- forward rendering: IR sequence term -> Alethe term --------------------

/// Renders an IR `Seq`-sorted term as an [`AletheTerm`] over the invertible
/// string vocabulary, or `None` outside that fragment:
///
/// - a `Seq` **variable** → `Const(name)` (a seq-level name);
/// - `str.++ a b` → `App("str.++", [.., ..])`;
/// - `seq.empty` → `App("seq.empty", [])`;
/// - `seq.unit e` → `App("seq.unit", [elem])`, where `elem` is either a character
///   literal `App("char", [Const(width), Const(value)])` or an element variable
///   `Const(name)`.
///
/// The `char` head keeps constant characters unambiguous from element variables so
/// the reverse converter is sort-directed and exact.
fn seq_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    match arena.node(t) {
        TermNode::Symbol(s) => {
            // Only a `Seq`-sorted symbol is a seq-level term here.
            if matches!(arena.sort_of(t), Sort::Seq(_)) {
                let (name, _sort) = arena.symbol(*s);
                Some(AletheTerm::Const(name.to_owned()))
            } else {
                None
            }
        }
        TermNode::App { op, args } => match op {
            Op::SeqConcat if args.len() == 2 => Some(AletheTerm::App(
                "str.++".to_owned(),
                vec![
                    seq_to_alethe(arena, args[0])?,
                    seq_to_alethe(arena, args[1])?,
                ],
            )),
            Op::SeqEmpty(_) if args.is_empty() => {
                Some(AletheTerm::App("seq.empty".to_owned(), Vec::new()))
            }
            Op::SeqUnit if args.len() == 1 => Some(AletheTerm::App(
                "seq.unit".to_owned(),
                vec![elem_to_alethe(arena, args[0])?],
            )),
            _ => None,
        },
        _ => None,
    }
}

/// Renders a scalar element term (inside `seq.unit`): a bit-vector constant as
/// `App("char", [width, value])`, a bit-vector variable as `Const(name)`, else
/// `None`.
fn elem_to_alethe(arena: &TermArena, e: TermId) -> Option<AletheTerm> {
    match arena.node(e) {
        TermNode::BvConst { width, value } => Some(AletheTerm::App(
            "char".to_owned(),
            vec![
                AletheTerm::Const(width.to_string()),
                AletheTerm::Const(value.to_string()),
            ],
        )),
        TermNode::Symbol(s) => {
            let (name, _sort) = arena.symbol(*s);
            Some(AletheTerm::Const(name.to_owned()))
        }
        _ => None,
    }
}

// ----- the plugged clash callback + reverse rebuild --------------------------

/// The [`axeyum_cnf::check_alethe_with`] `extra` callback for [`WORD_CLASH_RULE`].
///
/// Returns `None` for any other rule (so the host reports it unsupported). For the
/// clash rule it rebuilds the string system **from the clause's own literals** in a
/// fresh arena — a negated `(= a b)` literal is an assumed equality, a positive one
/// an assumed disequality — and demands the independent [`refute_word_equations`]
/// return [`RefuteOutcome::Unsat`]. Any parse failure, empty system, or non-`Unsat`
/// verdict yields `Some(false)` — an unvalidatable clash is rejected, never blessed
/// (the sound default). This is the theory-tautology re-derivation: nothing in the
/// clause is trusted.
fn word_clash_extra(rule: &str, clause: &[AletheLit], elem: ArraySortKey) -> Option<bool> {
    if rule != WORD_CLASH_RULE {
        return None;
    }
    Some(word_clash_valid(clause, elem))
}

/// Re-derives the clash: rebuilds `equalities` / `disequalities` from `clause` and
/// returns whether they are jointly word-`unsat` per [`refute_word_equations`].
fn word_clash_valid(clause: &[AletheLit], elem: ArraySortKey) -> bool {
    let mut arena = TermArena::new();
    let mut equalities: Vec<(TermId, TermId)> = Vec::new();
    let mut disequalities: Vec<(TermId, TermId)> = Vec::new();
    for lit in clause {
        let AletheTerm::App(head, args) = &lit.atom else {
            return false;
        };
        if head != "=" || args.len() != 2 {
            return false;
        }
        let (Some(l), Some(r)) = (
            alethe_to_seq(&mut arena, elem, &args[0]),
            alethe_to_seq(&mut arena, elem, &args[1]),
        ) else {
            return false;
        };
        if lit.negated {
            equalities.push((l, r));
        } else {
            disequalities.push((l, r));
        }
    }
    if equalities.is_empty() && disequalities.is_empty() {
        return false;
    }
    matches!(
        refute_word_equations(&mut arena, &equalities, &disequalities, &budget()),
        RefuteOutcome::Unsat { .. }
    )
}

/// Rebuilds an IR `Seq`-sorted term from its rendered [`AletheTerm`] in `arena`
/// (the inverse of [`seq_to_alethe`]). `None` if the shape is not a rendered
/// sequence term or a name cannot be declared with the expected sort.
fn alethe_to_seq(arena: &mut TermArena, elem: ArraySortKey, at: &AletheTerm) -> Option<TermId> {
    match at {
        AletheTerm::Const(name) => {
            let sym = arena.declare(name, Sort::Seq(elem)).ok()?;
            Some(arena.var(sym))
        }
        AletheTerm::App(head, args) => match head.as_str() {
            "str.++" if args.len() == 2 => {
                let a = alethe_to_seq(arena, elem, &args[0])?;
                let b = alethe_to_seq(arena, elem, &args[1])?;
                arena.seq_concat(a, b).ok()
            }
            "seq.empty" if args.is_empty() => Some(arena.seq_empty(elem)),
            "seq.unit" if args.len() == 1 => {
                let e = alethe_to_elem(arena, elem, &args[0])?;
                arena.seq_unit(e).ok()
            }
            _ => None,
        },
        AletheTerm::Indexed { .. } => None,
    }
}

/// Rebuilds a scalar element term (the inverse of [`elem_to_alethe`]). A `char`
/// application is a bit-vector constant; a bare `Const(name)` is a bit-vector
/// variable of the element width. `None` outside that or on a bad width.
fn alethe_to_elem(arena: &mut TermArena, elem: ArraySortKey, at: &AletheTerm) -> Option<TermId> {
    match at {
        AletheTerm::App(head, args) if head == "char" && args.len() == 2 => {
            let (AletheTerm::Const(w), AletheTerm::Const(v)) = (&args[0], &args[1]) else {
                return None;
            };
            let width: u32 = w.parse().ok()?;
            let value: u128 = v.parse().ok()?;
            arena.bv_const(width, value).ok()
        }
        AletheTerm::Const(name) => {
            let width = elem.bv_width()?;
            arena.bv_var(name, width).ok()
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests;
