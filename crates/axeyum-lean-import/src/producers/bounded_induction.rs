//! Untrusted, bounded general producer: `Eq.refl`, and where that gets stuck,
//! a bounded structural induction over a naturally-shaped (zero/succ) binder,
//! plus one or more congruence rewrites driven by the induction hypothesis —
//! including, where a single rewrite is not enough, a self-contained
//! auxiliary arithmetic lemma discovered and proved by the SAME mechanism and
//! spliced in with `Eq.trans`.
//!
//! This is deliberately target-agnostic: it never dispatches on a fact id, a
//! declaration name, or a hand-supplied proof plan. It discovers the
//! "zero/succ"-shaped inductive, its recursor, and the ambient `Eq`/`Eq.refl`/
//! `Eq.rec` primitives structurally from whatever kernel it is handed, and it
//! only ever emits a candidate that the SAME independent kernel then
//! re-type-checks through `Kernel::add_declaration`. Every budget below is an
//! explicit constant; exhausting one is a decline, never a hang.
//!
//! Known reach, measured against the seven frozen `natural-factorial` goals
//! that reach the kernel and have their plain-`Eq.refl` candidate rejected
//! (see `docs/autogenesis/226-production-measurement-and-general-producer-plan.md`
//! and `docs/autogenesis/232-first-general-producer-result.md`): it closes
//! `descFactorial n 1 = n`, `ascFactorial n 0 = 1`, and `descFactorial n 0 =
//! 1` (single induction, one congrArg-with-hypothesis rewrite bridges the
//! `succ`-case); and, via the residual-lemma extension
//! ([`Search::try_residual_lemma`]), `ascFactorial 0 k.succ = 0` (the
//! step-case's second factor multiplies out to `0` regardless of the first,
//! closed by [`kabstract_occurrences`] finding the induction hypothesis
//! occurrence behind a `brecOn`/`below` structure *projection* — a shape
//! spine-argument matching alone could not see into) and `ascFactorial 1 k =
//! k!` (the step-case bridge needs the auxiliary identity `1 + n = n.succ`,
//! proved as its own nested, budget-sharing induction and composed with the
//! primary congruence via `Eq.trans`). It declines `descFactorial n n = n!`
//! (the induction variable occurs in two positions at once — a genuinely
//! diagonal recursion where the induction hypothesis's shape does not
//! directly relate `descFactorial (n+1) n` back to `descFactorial n n`,
//! needing more than a rewrite chain). Every decline above is a real `Err`,
//! checked against the same kernel, never a silent skip.
//!
//! ## Absurd elimination
//!
//! `n < k -> descFactorial n k = 0` used to decline the same way: the search
//! reaches a base case whose only hypothesis is `n < 0` (`Nat.lt` unfolds to
//! the indexed `Nat.le (succ n) 0`), and closing a Prop-headed goal from a
//! hypothesis it never inspects is not something the congruence-rewrite
//! machinery above can do at all. [`Search::local_hyps`] now retains every
//! ordinary (non-induction) Pi-bound hypothesis introduced along the current
//! derivation, and when a terminal goal is otherwise stuck,
//! [`Search::try_absurd_elimination`] looks for one whose type unfolds to an
//! application of a [`LeShape`]-shaped indexed family (discovered
//! structurally — nothing here names `Nat.le`, `Nat.lt`, or any target
//! declaration) at index `zero`, with its parameter structurally
//! `succ`-shaped. That hypothesis can never be inhabited, and its OWN
//! recursor, instantiated with a motive that depends only on the index (not
//! on the hypothesis itself — the "vacuous motive" the module-level search
//! above never needed), produces a proof of the CURRENT goal directly, no
//! matter what that goal is — without any reference to `descFactorial`,
//! `n`, or `k` in the mechanism itself. This genuinely closes the induction's
//! *base* case (`n < 0 -> descFactorial n 0 = 0`, for both the literal `n =
//! 0` and a fully generic `n`), exactly the shape the decline above named.
//!
//! It does not, by itself, close `descFactorial_of_lt` as a whole: the
//! induction's non-vacuous *step* case needs `n < succ k' -> descFactorial n
//! (succ k') = 0`, and the search's only route to that is its own induction
//! hypothesis `n < k' -> descFactorial n k' = 0` — usable only once `n <
//! succ k'` is turned into `n < k'`, which is false whenever `n = k'`. That
//! needs a genuine case split (`n < succ k' -> n < k' ∨ n = k'`, via the
//! SAME [`LeShape`] recursor, this time consuming both constructors rather
//! than ruling one out) whose `n = k'` branch then needs `n - n = 0`
//! (`Nat.sub_self`) — itself not a single-step induction, since `Nat.sub`
//! recurses on its second argument and `pred (n - m)` at `m = succ m'` needs
//! `n - m'` already equal to something `pred` can act on, not `n - n`
//! directly. Both pieces are real, bounded, shape-general capabilities in
//! the same spirit as this one — but they are additional capabilities, not
//! a corollary of absurd elimination, and are not implemented here. Also
//! fixed alongside this capability, because building it exposed the gap
//! directly: [`instantiate_hypothesis`] previously applied an induction
//! hypothesis's proof to a goal binder's fresh variable without checking
//! that the two binders' domains actually agree, which a hypothesis whose
//! own type depends on the induction variable (like `n < k`) makes false at
//! the step case — silently building an ILL-TYPED term that only the FINAL
//! kernel re-check caught, turning a declinable shape mismatch into a hard
//! kernel rejection of the whole candidate instead of a clean decline.
//!
//! ## Case-split elimination and diagonal generalization
//!
//! [`Search::try_case_split_elimination`] supplies the genuine case split
//! the previous section named: for a stuck goal it looks for a retained
//! hypothesis whose type unfolds to a [`LeShape`]-shaped family at a
//! SUCC-shaped (not zero-shaped) index, and consumes both of that family's
//! constructors — the "at-param" branch recovers `n = k'` (via the family's
//! `refl` shape) and transports a proof of the goal's own predecessor
//! instance along it; the "step" branch recovers a strictly smaller
//! instance of the outer family and re-applies whichever induction
//! hypothesis was stuck waiting for exactly that predecessor
//! ([`Search::stuck_hyps`]). This closes `descFactorial_of_lt`'s step case
//! down to needing `n - n = 0` at the `n = k'` branch, exactly as
//! diagnosed — and does so as its own nested, budget-sharing proof
//! obligation, not a corollary of absurd elimination.
//!
//! `Nat.sub_self` itself needs two further, independently-motivated
//! generalizations of the residual mechanism, because its own step case is
//! NOT a single congruence rewrite: `succ n' - succ n' = 0` from IH `n' -
//! n' = 0` has no occurrence of the IH's LHS anywhere in the goal's
//! reduced form at all (`Nat.sub` recurses on its SECOND argument, so
//! `succ n' - succ n'` unfolds to `pred (succ n' - n')` — a term about
//! `succ n'`, never `n'` alone).
//!
//! - [`Search::try_split_congruence`] closes the gap this leaves in
//!   [`Search::try_residual_lemma`]: when a congruence wrap's residual
//!   `Eq(candidate, expected)` has the SAME head applied to the SAME
//!   arguments on both sides but collapsed onto ONE occurrence site (`n' -
//!   n'` vs `succ n' - succ n'` — the same `n'` at every position), the
//!   existing narrowing can only re-pose the identical diagonal goal one
//!   level down, self-similar under induction and never simpler.
//!   Generalizing the two occurrence SITES independently, rather than by
//!   shared free-variable identity, poses the STRICTLY MORE GENERAL `∀ n m,
//!   n - m = succ n - succ m` — provable by ordinary induction on `m` alone
//!   (`n` stays fixed) — and re-specializing both fresh variables back to
//!   the one original value closes the specific diagonal instance. Always
//!   sound: the general statement is independently kernel-checked before
//!   ever being instantiated, so an attempted split that happens to be
//!   FALSE (e.g. `descFactorial y0 y1 = descFactorial (succ y0) (succ
//!   y1)`, tried and declined when this fires from an unrelated degenerate
//!   match) simply fails to prove, never fabricates a wrong witness.
//! - [`Search::try_absorbing_argument`] supplies the hypothesis-INDEPENDENT
//!   half: once `n - n = 0` and `0 * x = 0` are each real but unrelated
//!   facts, closing `(succ q - succ q) * descFactorial (succ q) (succ q) =
//!   0` needs BOTH chained by congruence with NEITHER ever occurring in the
//!   induction hypothesis at all (the recursive call's own first argument
//!   has already moved past it) — a shape the single IH-driven rewrite in
//!   [`Search::try_congr_rewrite`] cannot reach regardless of how the
//!   residual it poses is generalized. It tries each top-level argument
//!   position of the goal's own (WHNF-reduced) application spine as an
//!   independent target for `Eq(arg, goal.rhs)`, and on success asks for
//!   the OPERATOR's plain fact about every OTHER position generalized to a
//!   fresh, opaque variable — `0 * x = 0`, never `0 * (this specific
//!   term's other operand) = 0`.
//!
//! Measured 2026-08-22 against `F:ml430-nat-descfactorial-of-lt-fbcf5d26`
//! (`∀ n k, n < k -> descFactorial n k = 0`): both new mechanisms close
//! their own instances — `n - n = 0` (with the `∀ n m, n - m = succ n -
//! succ m` generalization proved en route) and, separately, `0 - x = 0` via
//! `try_absorbing_argument` — but the theorem as a whole still declines.
//! The remaining gap is precise and NOT a budget shortfall: once `succ q -
//! succ q = 0` closes the first factor, the second half of the chain needs
//! `0 * descFactorial (succ q) (succ q) = 0`, and this kernel compiles
//! `descFactorial`'s course-of-values recursion so that WHNF-reducing the
//! goal to expose that multiplication's SECOND operand as a separable
//! top-level argument requires ALSO forcing the (still `succ q`-generic,
//! un-inducted) recursive value's own `brecOn`/`below` structure — which
//! entangles the operand with the very `q` this producer is still
//! generalizing, so [`Search::generalize_opaque_operands`]'s re-`whnf`
//! attempt reproduces the SAME entangled expression rather than a clean
//! `HMul.hMul 0 B`. Separating that operand without already knowing
//! `descFactorial`'s specific recursive shape needs a genuinely different
//! introspection strategy than WHNF-then-`app_spine`, and is not
//! implemented here.

use std::collections::BTreeSet;

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, Kernel, LevelId, LocalContext, LocalDecl, NameId,
};

/// Maximum number of leading `Pi` binders this producer will peel (shared
/// budget across plain generalization and structural induction).
pub const MAX_BINDERS: usize = 8;
// Raised to 12 on 2026-08-22 and REVERTED the same hour. The two mechanisms added
// with it -- `try_split_congruence` and `try_absorbing_argument` -- need the
// deeper search to engage, but they did not close their target, and 12 changes
// the reproduction contract of five ALREADY-ESTABLISHED facts: every
// `mathlib-bounded-induction-family-*` manifest pins `max_binders: 8` as part of
// its receipt, and `check-autogenesis-bounded-induction-family.py` correctly
// refused the mismatch even though every `proof_sha256` was byte-identical.
//
// Perturbing a settled fact's contract to enable a capability that has not yet
// produced a theorem is the wrong trade. Raise it again in the same change that
// makes it pay, and update the five manifests in that change.

/// Maximum number of structural inductions this producer will perform while
/// building one candidate. Bounded so the search cannot recurse without limit
/// over nested zero/succ-shaped binders.
pub const MAX_INDUCTIONS: usize = 2;

/// Maximum number of residual auxiliary-lemma attempts
/// ([`Search::try_residual_lemma`]) one derivation may make in total,
/// decremented on every attempt regardless of outcome. A congruence rewrite
/// whose final check fails only up to an arithmetic identity between two
/// zero/succ-shaped terms (e.g. `1 + n = n.succ`, needed when a course-of-
/// values-compiled operator's recursion argument is itself a sum rather than
/// a bare variable) is generalized back into its own standalone `Pi` goal
/// and proved via a nested, budget-sharing call to [`Search::attempt`] —
/// this bounds how many such side quests one derivation may spawn, so the
/// capability cannot turn a single decline into unbounded extra search.
pub const MAX_RESIDUAL_LEMMAS: usize = 300;

/// Minimum number of structural inductions guaranteed to a nested residual
/// proof ([`Search::prove_universal_identity_with`]'s own call to
/// [`Search::attempt`]), regardless of how much of the OUTER derivation's
/// shared [`MAX_INDUCTIONS`] budget is already "in flight" — permanently
/// consumed for as long as the successful outer branch that used it keeps
/// executing (`Search::attempt`'s Pi-branch only ever releases a consumed
/// induction slot when `try_induction` returns `Err`, i.e. on backtrack; a
/// SUCCESSFUL outer induction several levels up keeps its slot spent for
/// every nested call made while it is still on the stack). A residual lemma
/// is a self-contained side quest about a DIFFERENT statement than whatever
/// the outer derivation is proving, so its own single induction should not
/// be hostage to how deep the outer derivation happened to nest before
/// asking for it: closing `Nat.sub_self` as a residual three inductions deep
/// into an unrelated derivation needs exactly one induction of its own,
/// no matter how many the surrounding context already spent. Applied as a
/// FLOOR (`.max`), never a reduction — a healthy outer budget is never made
/// worse by this constant, and the boosted amount is always restored to
/// its exact pre-boost value afterward, so it can never leak into a SIBLING
/// call the way a permanent bump to [`MAX_INDUCTIONS`] itself would.
const MIN_RESIDUAL_INDUCTIONS: usize = 1;

/// As [`MIN_RESIDUAL_INDUCTIONS`], for [`MAX_BINDERS`]: a residual goal
/// needs enough leading `Pi`s peeled to reach its own induction variable
/// and close the base/step goals that induction produces (each of which may
/// itself carry a further ordinary hypothesis binder, e.g. a case split's
/// own recovered equality).
const MIN_RESIDUAL_BINDERS: usize = 4;

/// Maximum nesting depth of [`Search::prove_universal_identity_with`] calls
/// ([`Search::residual_depth`]). This is a DEPTH bound, deliberately
/// separate from [`MAX_RESIDUAL_LEMMAS`]'s COUNT bound: the
/// [`MIN_RESIDUAL_INDUCTIONS`]/[`MIN_RESIDUAL_BINDERS`] floors mean a
/// residual attempt that would otherwise decline immediately (no budget
/// left to induct) now gets just enough rope to try its own induction and
/// pose a FURTHER nested residual from its own stuck step case — sound
/// either way (nothing is accepted without the kernel re-checking it), but
/// an unproductive chain of these (e.g. repeatedly re-deriving a false
/// shifted-argument identity) can still be within `MAX_RESIDUAL_LEMMAS`'s
/// total-count budget while nesting the native call stack (`attempt` ->
/// `try_induction` -> `attempt` -> `close_terminal` -> `try_congr_rewrite`
/// -> `try_residual_lemma` -> `prove_universal_identity_with` -> `attempt`
/// -> …) far enough to overflow it — measured directly: without this bound,
/// closing `F:ml430-nat-descfactorial-of-lt-fbcf5d26` crashed with a stack
/// overflow. Six is enough for the deepest CORRECT chain this producer
/// needs (case-split's own predecessor proof, nested inside which is the
/// absorbing-argument split, nested inside which is the sub-self instance,
/// nested inside which is the split-congruence generalization) with one
/// level of slack; exhausting it is an ordinary decline, never a hang or a
/// crash.
const MAX_RESIDUAL_CHAIN_DEPTH: usize = 6;

/// Maximum number of [`LeShape`] "step" constructor applications
/// [`Search::ascend_le`] will chain from a known starting point (either
/// `refl(param)` or a hypothesis's own proof) while looking for the
/// terminal order goal's index. This is NOT a search over arbitrary
/// derivations — every step is forced (there is exactly one way to grow a
/// `family(param, ·)` proof by one `succ`), so this only ever closes a goal
/// whose index is a SMALL, LITERAL number of `succ`s past the starting
/// index (covering both literal base-case gaps like `0 < 1` and a
/// hypothesis whose index already equals the goal's up to a small constant
/// offset); a genuinely unbounded or non-literal gap correctly falls
/// through to [`Search::try_order_absorbing_argument`] instead. Bounded so
/// this can never loop; exhausting it is a decline, never a hang.
const MAX_LE_ASCENT_STEPS: usize = 16;

/// First free-variable id this producer mints. Chosen far above anything an
/// import stream or the kernel's own `LocalContext` would use, so this
/// producer's free variables cannot collide with either.
const FVAR_BASE: u64 = 9_000_000;

/// One fully constructed candidate, plus the search shape that produced it —
/// reported so a caller can distinguish "closed by plain reflexivity" from
/// "closed by induction" without re-deriving it from the proof term.
#[derive(Debug)]
pub struct Candidate {
    /// The proposed proof term, valid only in the kernel that produced it.
    ///
    /// Untrusted until that same kernel re-checks it through
    /// `Kernel::add_declaration`.
    pub proof: ExprId,
    /// How many leading `Pi` binders the search peeled, out of
    /// [`MAX_BINDERS`].
    pub binders_used: usize,
    /// How many structural inductions the search performed, out of
    /// [`MAX_INDUCTIONS`]. Zero means the goal closed by plain reflexivity.
    pub inductions_used: usize,
}

/// Why the bounded search declined, tagged by stage so a caller can report a
/// precise, typed reason rather than a free-form string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclineReason {
    /// The goal has more leading `Pi` binders than [`MAX_BINDERS`] allows.
    BinderBudgetExceeded,
    /// The terminal, non-`Pi` goal is not an exact `Eq` application, so none
    /// of this producer's equality machinery applies to it.
    NotEqualityGoal,
    /// The terminal goal is not definitionally equal and no applicable
    /// induction-hypothesis rewrite closed the remaining gap.
    TerminalNotDefEqNoRewrite,
    /// A structural primitive this producer needs (the named declaration)
    /// occurs in the kernel's environment a number of times other than one —
    /// either absent, or ambiguous.
    RequiredDeclarationUnavailable(String),
    /// The discovered recursor has a shape this producer cannot drive; the
    /// payload describes which expectation failed.
    UnsupportedRecursorShape(String),
}

impl std::fmt::Display for DeclineReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BinderBudgetExceeded => {
                write!(f, "binder budget exceeded: maximum {MAX_BINDERS}")
            }
            Self::NotEqualityGoal => write!(f, "terminal goal is not an exact Eq application"),
            Self::TerminalNotDefEqNoRewrite => write!(
                f,
                "terminal goal is not definitionally equal and no applicable induction-hypothesis rewrite closed the gap"
            ),
            Self::RequiredDeclarationUnavailable(name) => {
                write!(
                    f,
                    "required declaration {name:?} occurs a number of times other than one"
                )
            }
            Self::UnsupportedRecursorShape(detail) => {
                write!(f, "unsupported recursor shape: {detail}")
            }
        }
    }
}

fn exact_name(kernel: &Kernel, rendered: &str) -> Result<NameId, DeclineReason> {
    let matches: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(name, _)| {
            (kernel.display_name(*name).to_string() == rendered).then_some(*name)
        })
        .collect();
    match matches.as_slice() {
        [name] => Ok(*name),
        _ => Err(DeclineReason::RequiredDeclarationUnavailable(
            rendered.to_owned(),
        )),
    }
}

/// Whether `rendered` occurs in `kernel`'s environment exactly ZERO times —
/// as opposed to `exact_name`'s "exactly one", this distinguishes "genuinely
/// absent" from "ambiguous" (`> 1`), which `propose_bounded_induction` needs
/// to treat differently: a purely order-headed statement's minimal import
/// closure legitimately never needs `Eq` at all (zero occurrences, a common
/// and correct shape, not a malformed kernel), while more than one match is
/// still the same hard ambiguity `discover_eq_primitives` already declines
/// on today — this helper only ever WIDENS what is tolerated, never narrows
/// it.
fn declaration_absent(kernel: &Kernel, rendered: &str) -> bool {
    !kernel
        .environment()
        .iter()
        .any(|(name, _)| kernel.display_name(*name).to_string() == rendered)
}

fn app_spine(kernel: &Kernel, mut expression: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut arguments = Vec::new();
    while let ExprNode::App(function, argument) = kernel.expr_node(expression) {
        arguments.push(*argument);
        expression = *function;
    }
    arguments.reverse();
    (expression, arguments)
}

/// Maximum number of beta-reduction steps [`beta_whnf`] will perform.
/// Generous but finite — the only thing it ever reduces is a literal
/// `(fun x => body) arg` redex left behind by this producer's own
/// congruence wraps, which cannot chain more than a handful deep.
const MAX_BETA_STEPS: usize = 64;

/// Reduce `e` at its head by BETA ALONE, repeatedly, never unfolding any
/// constant's own definition — unlike [`Kernel::whnf`], which aggressively
/// delta/iota-unfolds through a STUCK recursive definition (e.g. `Nat.sub`
/// applied to a non-literal argument) even though doing so cannot make
/// progress toward a literal constructor, because whnf's job is "reduce as
/// far as possible", not "reduce only if it helps."
///
/// That distinction matters for [`Search::try_split_congruence`]: given
/// `candidate = (fun x0 => x0) (n - n)` and `expected = succ n - succ n`,
/// `Kernel::whnf` unfolds `n - n` (stuck on the generic `n`) all the way
/// into its raw `brecOn`/`below` recursor encoding, while `succ n - succ n`
/// unfolds ONE further iota step (its outer argument IS literally
/// `succ`-shaped) into a DIFFERENT recursor-encoded shape — so the two
/// sides never end up sharing a comparable head/arity, even though the
/// ORIGINAL, unreduced applications (`HSub.hSub … n n` vs `HSub.hSub …
/// (succ n) (succ n)`) obviously do. Reducing by beta only leaves the
/// `HSub.hSub` application spine completely intact on both sides — it only
/// ever strips the congruence wrap's own identity/name lambda — so
/// `app_spine` sees the same head and arity it would see on the source
/// term directly.
fn beta_whnf(kernel: &mut Kernel, mut e: ExprId) -> ExprId {
    let mut budget = MAX_BETA_STEPS;
    loop {
        if budget == 0 {
            return e;
        }
        budget -= 1;
        let ExprNode::App(f, a) = kernel.expr_node(e).clone() else {
            return e;
        };
        let ExprNode::Lam(_, _, body, _) = kernel.expr_node(f).clone() else {
            return e;
        };
        e = kernel.instantiate(body, &[a]);
    }
}

/// Maximum number of sub-expression nodes [`kabstract_occurrences`] will
/// visit while searching for occurrences of a hypothesis side inside a goal
/// side. Bounded so a pathologically large `brecOn`/`below` unfolding cannot
/// hang the search; exhausting it makes the search report "not found",
/// never a panic or an unbounded loop.
const MAX_KABSTRACT_NODES: usize = 4_096;

/// Maximum number of sub-expression nodes [`collect_fvars`] will visit while
/// finding which free variables occur in a residual gap's two sides. Same
/// role as [`MAX_KABSTRACT_NODES`] — bounds a recursive term walk so it
/// reports an (under-approximate, never wrong) partial result instead of
/// hanging on a pathologically large term.
const MAX_FVAR_COLLECT_NODES: usize = 4_096;

/// Maximum recursion depth [`find_diff`] will descend while narrowing a
/// residual gap to its actual point of difference. Bounded the same way as
/// [`MAX_KABSTRACT_NODES`]/[`MAX_FVAR_COLLECT_NODES`]: exhausting it makes
/// the search fall back to the coarser, whole-term pair rather than hang or
/// panic.
const MAX_DIFF_NODES: usize = 256;

/// Find the point where `a` and `b` — known not to be definitionally equal —
/// actually diverge, by descending through matching `App` spines wherever
/// the function part still matches exactly (so the shared context is kept
/// intact) but the trailing argument does not. Returns `None` only if `a`/`b`
/// turn out definitionally equal at some recursion step (never at the top,
/// since the caller already knows they are not); returns `Some((a, b))`
/// unchanged when no further descent is possible, which is the correct,
/// maximally-conservative answer for "the whole pair is the diff" — this
/// function only ever narrows, never fabricates a diff that does not truly
/// separate the two sides.
///
/// Deliberately does **not** descend into the function position when only
/// the *trailing* arguments happen to coincide (the symmetric case): two
/// differently-curried applications can share a final argument by
/// coincidence (e.g. `n.succ` vs a 6-argument `HAdd.hAdd … 1 n` both ending
/// in the same `n`) while the "remaining" function-position comparison
/// after stripping it is a bare constant against a partial application —
/// not a meaningful pointwise identity, and one this producer has no
/// business trying to prove (it would need function extensionality, not
/// induction). Keeping only the shared-context direction means every
/// diff this returns is a genuine same-shape divergence.
fn find_diff(
    kernel: &mut Kernel,
    a: ExprId,
    b: ExprId,
    budget: &mut usize,
) -> Option<(ExprId, ExprId)> {
    if *budget == 0 {
        return Some((a, b));
    }
    *budget -= 1;
    if kernel.def_eq(a, b) {
        return None;
    }
    if let (ExprNode::App(f1, x1), ExprNode::App(f2, x2)) =
        (kernel.expr_node(a).clone(), kernel.expr_node(b).clone())
        && kernel.def_eq(f1, f2)
    {
        return find_diff(kernel, x1, x2, budget).or(Some((a, b)));
    }
    Some((a, b))
}

/// Collect every free-variable id occurring anywhere in `e` (including under
/// `Lam`/`Pi`/`Let`, since — unlike [`kabstract_occurrences`] — there is no
/// binder-crossing hazard in merely recording that an id occurs) into `out`.
/// Bounded by `budget`; exhausting it stops the walk early rather than
/// hanging, which can only under-report occurrences, never fabricate one —
/// a caller that then fails to find a variable's type simply declines.
fn collect_fvars(
    kernel: &Kernel,
    e: ExprId,
    out: &mut std::collections::BTreeSet<u64>,
    budget: &mut usize,
) {
    if *budget == 0 {
        return;
    }
    *budget -= 1;
    match kernel.expr_node(e) {
        ExprNode::FVar(id) => {
            out.insert(*id);
        }
        ExprNode::App(f, a) => {
            let (f, a) = (*f, *a);
            collect_fvars(kernel, f, out, budget);
            collect_fvars(kernel, a, out, budget);
        }
        ExprNode::Proj(_, _, inner) => {
            let inner = *inner;
            collect_fvars(kernel, inner, out, budget);
        }
        ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
            let (ty, body) = (*ty, *body);
            collect_fvars(kernel, ty, out, budget);
            collect_fvars(kernel, body, out, budget);
        }
        ExprNode::Let(_, ty, val, body) => {
            let (ty, val, body) = (*ty, *val, *body);
            collect_fvars(kernel, ty, out, budget);
            collect_fvars(kernel, val, out, budget);
            collect_fvars(kernel, body, out, budget);
        }
        _ => {}
    }
}

/// Abstract every occurrence of `needle` inside `haystack` (compared up to
/// definitional equality, so it finds occurrences regardless of how they are
/// currently folded/unfolded) into the given `placeholder` free variable,
/// recursing through `App`, `Proj`, and a binder's own type annotation —
/// never into a `Lam`/`Pi`/`Let` *body*, since those are expressed with de
/// Bruijn indices relative to a binder this function does not open, and a
/// closed `needle` can never actually occur there matched against `whole`'s
/// own bound variables. Returns the rewritten term and whether any
/// occurrence was found; finding none returns `haystack` unchanged, not an
/// error — the caller decides what a lack of match means.
///
/// This is the same operation Lean's own `rw` tactic calls `kabstract`: the
/// generalization from the previous single-spine-position search this
/// producer used, needed because a course-of-values (`brecOn`/`below`)
/// compiled recursive definition routes a nested recursive call through a
/// structure *projection* before it reaches an argument slot of the outer
/// operator — a shape `App`-only spine peeling cannot see into.
fn kabstract_occurrences(
    kernel: &mut Kernel,
    haystack: ExprId,
    needle: ExprId,
    placeholder: ExprId,
    budget: &mut usize,
) -> (ExprId, bool) {
    if *budget == 0 {
        return (haystack, false);
    }
    *budget -= 1;
    if kernel.def_eq(haystack, needle) {
        return (placeholder, true);
    }
    match kernel.expr_node(haystack).clone() {
        ExprNode::App(f, a) => {
            let (f2, found_f) = kabstract_occurrences(kernel, f, needle, placeholder, budget);
            let (a2, found_a) = kabstract_occurrences(kernel, a, needle, placeholder, budget);
            if found_f || found_a {
                (kernel.app(f2, a2), true)
            } else {
                (haystack, false)
            }
        }
        ExprNode::Proj(type_name, field_index, inner) => {
            let (inner2, found) = kabstract_occurrences(kernel, inner, needle, placeholder, budget);
            if found {
                (kernel.proj(type_name, field_index, inner2), true)
            } else {
                (haystack, false)
            }
        }
        ExprNode::Lam(name, ty, body, info) => {
            let (ty2, found) = kabstract_occurrences(kernel, ty, needle, placeholder, budget);
            if found {
                (kernel.lam(name, ty2, body, info), true)
            } else {
                (haystack, false)
            }
        }
        ExprNode::Pi(name, ty, body, info) => {
            let (ty2, found) = kabstract_occurrences(kernel, ty, needle, placeholder, budget);
            if found {
                (kernel.pi(name, ty2, body, info), true)
            } else {
                (haystack, false)
            }
        }
        ExprNode::Let(name, ty, val, body) => {
            let (ty2, found_ty) = kabstract_occurrences(kernel, ty, needle, placeholder, budget);
            let (val2, found_val) = kabstract_occurrences(kernel, val, needle, placeholder, budget);
            if found_ty || found_val {
                (kernel.let_(name, ty2, val2, body), true)
            } else {
                (haystack, false)
            }
        }
        _ => (haystack, false),
    }
}

/// `fun (name : ty) => body`, abstracting the free variable `fv` in `body`.
/// A free function (not a `Search` method) since it only ever touches its
/// own arguments.
fn lam_fv(
    kernel: &mut Kernel,
    name: NameId,
    fv: u64,
    ty: ExprId,
    body: ExprId,
    info: BinderInfo,
) -> ExprId {
    let abstracted = kernel.abstract_fvars(body, &[fv]);
    kernel.lam(name, ty, abstracted, info)
}

/// `fun (name : ty) => partial_rec name`, where `partial_rec` was built at
/// this same scope using the free variable `major_fv` as the induction
/// target's stand-in; closes `major_fv` and applies the recursor to the
/// binder actually being introduced.
fn lam_fv_apply_major(
    kernel: &mut Kernel,
    name: NameId,
    major_fv: u64,
    ty: ExprId,
    info: BinderInfo,
    partial_rec: ExprId,
) -> ExprId {
    let major = kernel.fvar(major_fv);
    let applied = kernel.app(partial_rec, major);
    lam_fv(kernel, name, major_fv, ty, applied, info)
}

/// A parsed `Eq.{level} carrier lhs rhs` goal.
#[derive(Debug, Clone, Copy)]
struct EqGoal {
    level: LevelId,
    carrier: ExprId,
    lhs: ExprId,
    rhs: ExprId,
}

fn parse_eq_goal(kernel: &Kernel, eq_name: NameId, goal: ExprId) -> Result<EqGoal, DeclineReason> {
    let (head, arguments) = app_spine(kernel, goal);
    let ExprNode::Const(name, levels) = kernel.expr_node(head) else {
        return Err(DeclineReason::NotEqualityGoal);
    };
    if *name != eq_name || arguments.len() != 3 || levels.len() != 1 {
        return Err(DeclineReason::NotEqualityGoal);
    }
    Ok(EqGoal {
        level: levels[0],
        carrier: arguments[0],
        lhs: arguments[1],
        rhs: arguments[2],
    })
}

/// A terminal goal (or a live hypothesis, once peeled down) headed by a
/// [`LeShape`]-shaped family applied to exactly two arguments — the ORDER
/// counterpart of [`EqGoal`], parsed the same "exact application" way. This
/// is a genuinely different terminal shape than [`EqGoal`], never a
/// generalization of it: an order goal's two positions are `param` (fixed
/// throughout one [`LeShape`] recursor elimination) and `idx` (the one that
/// varies), not two freely-interchangeable sides of an equation.
#[derive(Debug, Clone)]
struct OrderGoal {
    family: NameId,
    levels: Vec<LevelId>,
    shape: LeShape,
    param: ExprId,
    idx: ExprId,
}

/// Parse `expr` as an [`OrderGoal`], UNLIKE [`parse_eq_goal`] first reducing
/// it to WHNF — `<`/`≤` surface syntax is typeclass notation (`LT.lt`,
/// `LE.le`) that only unfolds down to the underlying [`LeShape`] inductive
/// (`Nat.lt`, itself `Nat.le (succ _) _`, then `Nat.le` itself) through
/// delta/iota reduction, which [`parse_eq_goal`] deliberately never performs
/// on an already-exact `Eq` application. Structural throughout: `family` is
/// whatever [`detect_le_shape`] confirms has the right constructor/recursor
/// shape, never a name this producer already knows.
fn parse_order_goal(search: &mut Search, kernel: &mut Kernel, expr: ExprId) -> Option<OrderGoal> {
    let expr_whnf = kernel.whnf(expr);
    let (head, args) = app_spine(kernel, expr_whnf);
    if args.len() != 2 {
        return None;
    }
    let ExprNode::Const(family, levels) = kernel.expr_node(head).clone() else {
        return None;
    };
    let shape = detect_le_shape(search, kernel, family)?;
    Some(OrderGoal {
        family,
        levels,
        shape,
        param: args[0],
        idx: args[1],
    })
}

/// Build `order.shape.refl_ctor(order.param) : family(order.param,
/// order.param)` — the base value [`Search::ascend_le`] starts a chain from
/// when no hypothesis is available (or none applies).
fn build_le_refl(kernel: &mut Kernel, order: &OrderGoal) -> ExprId {
    let c = kernel.const_(order.shape.refl_ctor, order.levels.clone());
    kernel.app(c, order.param)
}

/// The ambient equality primitives, discovered by exact display name (never
/// hand-supplied), plus the exact universe-parameter arity each one needs —
/// checked rather than assumed, so a kernel with a different `Eq` shape
/// declines instead of building a term the kernel would reject anyway.
struct EqPrimitives {
    eq: NameId,
    eq_refl: NameId,
    eq_rec: NameId,
}

fn discover_eq_primitives(kernel: &Kernel) -> Result<EqPrimitives, DeclineReason> {
    let eq = exact_name(kernel, "Eq")?;
    let eq_refl = exact_name(kernel, "Eq.refl")?;
    let eq_rec = exact_name(kernel, "Eq.rec")?;
    let Some(Declaration::Recursor { uparams, .. }) = kernel.environment().get(eq_rec) else {
        return Err(DeclineReason::UnsupportedRecursorShape(
            "Eq.rec is not a Recursor declaration".to_owned(),
        ));
    };
    if uparams.len() != 2 {
        return Err(DeclineReason::UnsupportedRecursorShape(format!(
            "Eq.rec has {} universe parameters, expected 2",
            uparams.len()
        )));
    }
    Ok(EqPrimitives {
        eq,
        eq_refl,
        eq_rec,
    })
}

fn build_eq(
    kernel: &mut Kernel,
    eq: NameId,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let head = kernel.const_(eq, vec![level]);
    let with_carrier = kernel.app(head, carrier);
    let with_x = kernel.app(with_carrier, x);
    kernel.app(with_x, y)
}

fn build_eq_refl(
    kernel: &mut Kernel,
    eq_refl: NameId,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
) -> ExprId {
    let head = kernel.const_(eq_refl, vec![level]);
    let with_carrier = kernel.app(head, carrier);
    kernel.app(with_carrier, x)
}

/// A zero/succ-shaped inductive: exactly two constructors, no parameters, no
/// indices — one nullary ("zero"), one with exactly one field recursive on
/// the family itself ("succ") — plus its generated recursor, discovered by
/// inspecting `Kernel::environment()`, never by name.
#[derive(Debug, Clone, Copy)]
struct NatShape {
    zero_ctor: NameId,
    succ_ctor: NameId,
    rec_name: NameId,
}

fn ctor_is_zero_shaped(kernel: &Kernel, ctor: NameId) -> bool {
    matches!(
        kernel.environment().get(ctor),
        Some(Declaration::Constructor { num_fields: 0, .. })
    )
}

fn ctor_is_succ_shaped(kernel: &Kernel, ctor: NameId, family: NameId) -> bool {
    let Some(Declaration::Constructor {
        ty, num_fields: 1, ..
    }) = kernel.environment().get(ctor)
    else {
        return false;
    };
    let ExprNode::Pi(_, field_ty, body, _) = kernel.expr_node(*ty) else {
        return false;
    };
    let field_is_family =
        matches!(kernel.expr_node(*field_ty), ExprNode::Const(n, _) if *n == family);
    let result_is_family = matches!(kernel.expr_node(*body), ExprNode::Const(n, _) if *n == family);
    field_is_family && result_is_family
}

fn detect_nat_shape(kernel: &Kernel, family: NameId) -> Option<NatShape> {
    let Some(Declaration::Inductive {
        num_params,
        num_indices,
        ctor_names,
        ..
    }) = kernel.environment().get(family)
    else {
        return None;
    };
    if *num_params != 0 || *num_indices != 0 || ctor_names.len() != 2 {
        return None;
    }
    let (c0, c1) = (ctor_names[0], ctor_names[1]);
    let (zero_ctor, succ_ctor) =
        if ctor_is_zero_shaped(kernel, c0) && ctor_is_succ_shaped(kernel, c1, family) {
            (c0, c1)
        } else if ctor_is_zero_shaped(kernel, c1) && ctor_is_succ_shaped(kernel, c0, family) {
            (c1, c0)
        } else {
            return None;
        };
    for (name, decl) in kernel.environment().iter() {
        let Declaration::Recursor {
            rec_rules,
            num_motives,
            num_minors,
            num_params: rp,
            num_indices: ri,
            uparams,
            ..
        } = decl
        else {
            continue;
        };
        if *rp != 0 || *ri != 0 || *num_motives != 1 || *num_minors != 2 || uparams.len() != 1 {
            continue;
        }
        let rule_ctors: BTreeSet<NameId> = rec_rules.iter().map(|rule| rule.ctor_name).collect();
        if rule_ctors == BTreeSet::from([zero_ctor, succ_ctor]) {
            return Some(NatShape {
                zero_ctor,
                succ_ctor,
                rec_name: *name,
            });
        }
    }
    None
}

/// A singly-parametrized, singly-indexed two-constructor inductive family
/// shaped like `Nat.le`: one constructor concluding at the index equal to
/// the (fixed) parameter itself ("refl"), and one constructor with a
/// recursive occurrence at index `m` concluding at index `succ m` ("step"),
/// where the index's own type is itself zero/succ-shaped ([`NatShape`]).
///
/// Discovered structurally from [`Kernel::environment`] — never by name,
/// exactly like [`NatShape`] is for the goal's own binders. This happens to
/// be the shape behind `Nat.le`/`Nat.lt` in an imported Lean kernel
/// (`Nat.lt a b` unfolds to `Nat.le (Nat.succ a) b`), but nothing in its
/// detection mentions `Nat.le`, `Nat.lt`, or any target fact: it fires for
/// whatever inductive a hypothesis's type happens to unfold to, provided it
/// has this shape.
#[derive(Debug, Clone, Copy)]
struct LeShape {
    idx_ty: ExprId,
    idx_shape: NatShape,
    rec_name: NameId,
    /// `family`'s "at-param" constructor (`refl : family p p`), retained
    /// (never just discarded after detection, as it used to be) so
    /// [`Search::close_order_terminal`]'s new order-goal closers can build
    /// actual `family` VALUES — not just inspect the shape — the same way
    /// [`Search::try_induction`] already does for a plain [`NatShape`].
    refl_ctor: NameId,
    /// `family`'s "step" constructor (`step : family p m -> family p
    /// (succ m)`), retained for the same reason as `refl_ctor`.
    step_ctor: NameId,
}

/// Try `(refl_ctor, step_ctor)` as the "at-param"/"step" pair for a
/// [`LeShape`] over `family` (already known to have exactly 2 constructors,
/// 1 parameter, 1 index). Returns `None` (never a hard error) on any shape
/// mismatch, including a family whose recursor does not eliminate directly
/// into `Prop` (this producer only builds the Prop-restricted application) —
/// the caller tries the other constructor ordering, or gives up.
#[allow(clippy::similar_names)]
fn try_le_shape_pair(
    search: &mut Search,
    kernel: &mut Kernel,
    family: NameId,
    refl_ctor: NameId,
    step_ctor: NameId,
) -> Option<LeShape> {
    // `refl_ctor : Π (p : P), family p p` — no fields beyond the parameter.
    let Some(Declaration::Constructor {
        ty: refl_ty,
        num_fields: 0,
        ..
    }) = kernel.environment().get(refl_ctor).cloned()
    else {
        return None;
    };
    let ExprNode::Pi(_, _param_ty, refl_body, _) = kernel.expr_node(refl_ty).clone() else {
        return None;
    };
    let p_fv = search.fresh_fvar();
    let p = kernel.fvar(p_fv);
    let refl_body_inst = kernel.instantiate(refl_body, &[p]);
    let (rh, ra) = app_spine(kernel, refl_body_inst);
    let ExprNode::Const(rf, _) = kernel.expr_node(rh).clone() else {
        return None;
    };
    if rf != family || ra.len() != 2 || !kernel.def_eq(ra[0], p) || !kernel.def_eq(ra[1], p) {
        return None;
    }

    // `step_ctor : Π (p : P) (m : Q) (_ : family p m), family p (succ m)` —
    // exactly 2 fields beyond the parameter (the index `m` and the
    // recursive occurrence).
    let Some(Declaration::Constructor {
        ty: step_ty,
        num_fields: 2,
        ..
    }) = kernel.environment().get(step_ctor).cloned()
    else {
        return None;
    };
    let ExprNode::Pi(_, _param_ty2, step_body1, _) = kernel.expr_node(step_ty).clone() else {
        return None;
    };
    let p2_fv = search.fresh_fvar();
    let p2 = kernel.fvar(p2_fv);
    let step_body1_inst = kernel.instantiate(step_body1, &[p2]);
    let ExprNode::Pi(_, idx_ty, step_body2, _) = kernel.expr_node(step_body1_inst).clone() else {
        return None;
    };
    let m_fv = search.fresh_fvar();
    let m = kernel.fvar(m_fv);
    let step_body2_inst = kernel.instantiate(step_body2, &[m]);
    let ExprNode::Pi(_, proof_ty, step_body3, _) = kernel.expr_node(step_body2_inst).clone() else {
        return None;
    };
    let (ph, pa) = app_spine(kernel, proof_ty);
    let ExprNode::Const(pf, _) = kernel.expr_node(ph).clone() else {
        return None;
    };
    if pf != family || pa.len() != 2 || !kernel.def_eq(pa[0], p2) || !kernel.def_eq(pa[1], m) {
        return None;
    }
    let h_fv = search.fresh_fvar();
    let h = kernel.fvar(h_fv);
    let concl = kernel.instantiate(step_body3, &[h]);
    let (ch, ca) = app_spine(kernel, concl);
    let ExprNode::Const(cf, _) = kernel.expr_node(ch).clone() else {
        return None;
    };
    if cf != family || ca.len() != 2 || !kernel.def_eq(ca[0], p2) {
        return None;
    }

    // The index type must itself be zero/succ-shaped, and the step
    // constructor's own conclusion index must be exactly its successor of
    // `m` — the structural fact that makes "step always lands past zero".
    let idx_ty_whnf = kernel.whnf(idx_ty);
    let ExprNode::Const(idx_family, _) = kernel.expr_node(idx_ty_whnf).clone() else {
        return None;
    };
    let idx_shape = detect_nat_shape(kernel, idx_family)?;
    let succ_ctor_e = kernel.const_(idx_shape.succ_ctor, vec![]);
    let succ_m = kernel.app(succ_ctor_e, m);
    if !kernel.def_eq(ca[1], succ_m) {
        return None;
    }

    let rec_name = find_le_recursor(kernel, refl_ctor, step_ctor)?;
    Some(LeShape {
        idx_ty,
        idx_shape,
        rec_name,
        refl_ctor,
        step_ctor,
    })
}

/// Recursor discovery for [`LeShape`], mirroring the search loop in
/// [`detect_nat_shape`]: match by `rec_rules`' constructor set, never by
/// name. Restricted to a Prop-only eliminator (`uparams` empty) — the shape
/// this producer's construction actually builds; a large-eliminating
/// recursor over the same family is simply not matched here.
fn find_le_recursor(kernel: &Kernel, refl_ctor: NameId, step_ctor: NameId) -> Option<NameId> {
    for (name, decl) in kernel.environment().iter() {
        let Declaration::Recursor {
            rec_rules,
            num_motives,
            num_minors,
            num_params,
            num_indices,
            uparams,
            ..
        } = decl
        else {
            continue;
        };
        if *num_params != 1
            || *num_indices != 1
            || *num_motives != 1
            || *num_minors != 2
            || !uparams.is_empty()
        {
            continue;
        }
        let rule_ctors: BTreeSet<NameId> = rec_rules.iter().map(|rule| rule.ctor_name).collect();
        if rule_ctors == BTreeSet::from([refl_ctor, step_ctor]) {
            return Some(*name);
        }
    }
    None
}

/// Detect a [`LeShape`] over `family`, trying both constructor orderings.
fn detect_le_shape(search: &mut Search, kernel: &mut Kernel, family: NameId) -> Option<LeShape> {
    let Some(Declaration::Inductive {
        num_params,
        num_indices,
        ctor_names,
        ..
    }) = kernel.environment().get(family).cloned()
    else {
        return None;
    };
    if num_params != 1 || num_indices != 1 || ctor_names.len() != 2 {
        return None;
    }
    let (c0, c1) = (ctor_names[0], ctor_names[1]);
    try_le_shape_pair(search, kernel, family, c0, c1)
        .or_else(|| try_le_shape_pair(search, kernel, family, c1, c0))
}

/// A live induction hypothesis available while closing a subgoal: a proof of
/// `stmt`. `stmt` may still carry leading `Pi`s of its own (when further
/// binders follow the induction variable in the original goal) — it is
/// peeled in lockstep with the goal by [`instantiate_hypothesis`] as
/// `Search::attempt` generalizes each further binder, and parsed into an
/// [`EqGoal`] only once [`Search::close_terminal`] actually needs it.
#[derive(Debug, Clone, Copy)]
struct Hypothesis {
    proof: ExprId,
    stmt: ExprId,
}

/// Peel one `Pi` off `hypothesis.stmt`, applying its proof to `x` (of
/// declared type `x_ty`) to match the goal's own generalization of the same
/// binder. Returns `None` (dropping the hypothesis rather than failing the
/// search) if `stmt` is not a `Pi` here, OR if the peeled `Pi`'s own domain
/// is not definitionally equal to `x_ty` — a genuine shape mismatch between
/// the induction hypothesis and the goal, which should cost this one
/// rewrite opportunity, not the whole candidate.
///
/// The second check matters whenever a hypothesis Pi's domain itself
/// depends on the variable being inducted (e.g. `n < k -> …` inducted on
/// `k`): the goal's OWN binder at the step case has domain `P(succ k')`
/// while the induction hypothesis's leading binder has domain `P(k')` —
/// different types — so applying the IH's proof to the goal's fresh
/// variable without this check silently builds an ILL-TYPED application
/// (`hyp.proof : Pi _:P(k') -> _` applied to a value of type `P(succ k')`)
/// that only the FINAL kernel re-check would ever catch, turning a
/// declinable shape mismatch into a hard rejection of the whole candidate.
fn instantiate_hypothesis(
    kernel: &mut Kernel,
    hypothesis: Hypothesis,
    x: ExprId,
    x_ty: ExprId,
) -> Option<Hypothesis> {
    let ExprNode::Pi(_, domain_ty, body, _) = kernel.expr_node(hypothesis.stmt).clone() else {
        return None;
    };
    if !kernel.def_eq(domain_ty, x_ty) {
        return None;
    }
    let stmt = kernel.instantiate(body, &[x]);
    let proof = kernel.app(hypothesis.proof, x);
    Some(Hypothesis { proof, stmt })
}

/// A `Pi` binder mid-descent, bundled to keep `try_induction`'s arity small.
#[derive(Debug, Clone, Copy)]
struct Binder {
    name: NameId,
    ty: ExprId,
    info: BinderInfo,
    body: ExprId,
}

struct Search {
    eqp_eq: NameId,
    eqp_refl: NameId,
    eqp_rec: NameId,
    /// Whether `eqp_eq`/`eqp_refl`/`eqp_rec` name REAL declarations in this
    /// kernel, as opposed to an inert placeholder ([`kernel.anon()`],
    /// `propose_bounded_induction`'s own choice when
    /// [`discover_eq_primitives`] fails because the minimal import closure
    /// for a purely order-headed statement (e.g. `n ≤ n.factorial`) never
    /// needed `Eq` at all — a real, common shape, not a malformed kernel.
    /// Every consumer of the `eqp_*` fields for anything other than a
    /// pass-through struct MUST check this first: `false` means those
    /// fields are meaningless and must never be dereferenced (built into a
    /// term, or compared against as a real name) — only ever gates whether
    /// the `Eq`-shaped terminal route ([`Search::close_terminal`] and
    /// everything reachable from it, including the two call sites in
    /// [`Search::close_order_terminal`] that reuse [`Search::try_absurd_elimination`]
    /// for its OWN internal `Eq`-shaped filler construction) is attempted
    /// at all. When `true`, behavior is BYTE-IDENTICAL to before this field
    /// existed — `eq_available` is set from `discover_eq_primitives`
    /// SUCCEEDING, unchanged.
    eq_available: bool,
    next_fvar: u64,
    binders_left: usize,
    inductions_left: usize,
    binders_used: usize,
    inductions_used: usize,
    /// The type recorded for every free variable minted through
    /// [`Search::fresh_fvar_typed`] — every induction target, induction
    /// predecessor, and plain-generalized binder the search has introduced
    /// so far. Consulted only by the residual-lemma path
    /// ([`Search::try_residual_lemma`]): to generalize a stuck subterm back
    /// into a standalone universally-quantified auxiliary goal, the search
    /// needs the ORIGINAL binder type for each free variable occurring in
    /// it, not just the variable's numeric id.
    fvar_types: std::collections::BTreeMap<u64, ExprId>,
    /// How many residual auxiliary-lemma attempts
    /// ([`Search::try_residual_lemma`]) this whole derivation may still make,
    /// decremented on every attempt regardless of outcome. Bounds the total
    /// extra search this capability can spend, independent of — and on top
    /// of — [`MAX_BINDERS`]/[`MAX_INDUCTIONS`], which the residual attempt
    /// also shares and is bound by.
    residual_budget: usize,
    /// Current nesting depth of [`Search::prove_universal_identity_with`]
    /// calls — incremented on entry, decremented on exit regardless of
    /// outcome. Distinct from [`Search::residual_budget`], which bounds the
    /// TOTAL number of residual attempts across the whole derivation but
    /// not how deep any one CHAIN of them nests: the [`MIN_RESIDUAL_…`]
    /// floors guarantee every residual its own minimum induction/binder
    /// capability regardless of how exhausted the outer derivation's shared
    /// budget already is, which is exactly what lets an unproductive
    /// recursive chain (e.g. repeatedly re-posing a false auxiliary
    /// statement that itself induces yet another residual) keep making
    /// just enough apparent progress to recurse again — bounded in COUNT by
    /// `residual_budget`, but not in native call-stack DEPTH, and a bounded
    /// count reached through unbounded depth still overflows the stack.
    /// [`Search::MAX_RESIDUAL_CHAIN_DEPTH`] bounds depth directly.
    residual_depth: usize,
    /// Every ordinary (non-induction) Pi-bound hypothesis introduced along
    /// the CURRENT derivation path: `(free variable, its type)`. Pushed by
    /// the plain-generalization branch of [`Search::attempt`] right before
    /// recursing, and truncated back to its pre-push length immediately
    /// after — regardless of that recursive call's outcome — so a
    /// hypothesis from one branch (e.g. an induction's base case) never
    /// leaks into a sibling branch (e.g. that induction's step case, or an
    /// entirely different candidate reached after a failed nested
    /// induction). Consulted only by [`Search::try_absurd_elimination`].
    local_hyps: Vec<(u64, ExprId)>,
    /// Induction hypotheses that [`instantiate_hypothesis`] could not carry
    /// forward past a plain-generalization step because the newly
    /// introduced binder's domain was NOT the same type as the hypothesis's
    /// own leading `Pi` domain (a genuine shape mismatch, e.g. the
    /// hypothesis's domain still names the induction's own predecessor
    /// while the goal's fresh binder names the successor) — retained
    /// UNAPPLIED, still carrying its own leading `Pi`, rather than dropped.
    /// Consulted only by [`Search::try_case_split_elimination`]: once a
    /// case split recovers a value at exactly the predecessor the
    /// hypothesis's domain names, the hypothesis becomes applicable again.
    /// Pushed by the plain-generalization branch of [`Search::attempt`]
    /// right before recursing and truncated back immediately after —
    /// regardless of outcome — with the exact same per-branch scoping
    /// discipline as [`Search::local_hyps`], so a stuck hypothesis from one
    /// branch never leaks into a sibling.
    stuck_hyps: Vec<Hypothesis>,
}

impl Search {
    fn fresh_fvar(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    /// [`Search::fresh_fvar`], additionally recording `ty` as that
    /// variable's type for the residual-lemma generalizer.
    fn fresh_fvar_typed(&mut self, ty: ExprId) -> u64 {
        let fv = self.fresh_fvar();
        self.fvar_types.insert(fv, ty);
        fv
    }

    /// Try to close `goal` (already peeled of every leading binder) via
    /// `Eq.refl`, or via one congruence rewrite driven by `hypothesis`.
    fn close_terminal(
        &mut self,
        kernel: &mut Kernel,
        goal: EqGoal,
        hypothesis: Option<Hypothesis>,
    ) -> Result<ExprId, DeclineReason> {
        if std::env::var("BIS_DEBUG").is_ok() {
            eprintln!(
                "close_terminal: lhs={} rhs={} hyp={}",
                kernel.render_lean(goal.lhs),
                kernel.render_lean(goal.rhs),
                hypothesis.map_or_else(|| "<none>".to_string(), |h| kernel.render_lean(h.stmt))
            );
        }
        if kernel.def_eq(goal.lhs, goal.rhs) {
            return Ok(build_eq_refl(
                kernel,
                self.eqp_refl,
                goal.level,
                goal.carrier,
                goal.lhs,
            ));
        }
        // The hypothesis is only usable once its (possibly still-Pi-headed)
        // statement has been peeled down to the same `Eq` shape as `goal` —
        // by the same number of `Search::attempt` generalization steps. A
        // hypothesis that is present but does not (yet, or ever) parse this
        // way is simply unavailable for this rewrite, not a hard error.
        let Some((hyp_proof, hyp_goal)) = hypothesis.and_then(|hyp| {
            parse_eq_goal(kernel, self.eqp_eq, hyp.stmt)
                .ok()
                .map(|g| (hyp.proof, g))
        }) else {
            let target = build_eq(
                kernel,
                self.eqp_eq,
                goal.level,
                goal.carrier,
                goal.lhs,
                goal.rhs,
            );
            return self
                .try_absurd_elimination(kernel, target)
                .or_else(|| self.try_case_split_elimination(kernel, goal))
                .or_else(|| {
                    self.try_absorbing_argument(kernel, goal, std::env::var("BIS_DEBUG").is_ok())
                })
                .ok_or(DeclineReason::TerminalNotDefEqNoRewrite);
        };
        // Try deriving the rewrite "wrap" `f` by abstracting every occurrence
        // of the hypothesis's RHS anywhere inside the (whnf-reduced) goal RHS
        // — not only at a spine-argument position. A course-of-values
        // (`brecOn`/`below`) compiled definition routes a recursive call
        // through a structure *projection* (`(below-pack).1`) before it ever
        // reaches an argument slot of the outer operator, so restricting the
        // search to `App` spine positions missed exactly the shape a second
        // arithmetic operator (e.g. multiplication consuming a `descFactorial`
        // recursive call as its own recursion scrutinee) produces. Searching
        // every subterm reachable through `App`/`Proj`/a binder's own type
        // finds the occurrence regardless of how deep the projection nesting
        // goes, while still building exactly one `congrArg`-shaped rewrite —
        // never more than the single hypothesis already in hand.
        let debug = std::env::var("BIS_DEBUG").is_ok();
        let rhs_whnf = kernel.whnf(goal.rhs);
        if debug {
            eprintln!("  rhs_whnf={}", kernel.render_lean(rhs_whnf));
        }
        if let Some(proof) = self.try_congr_rewrite(
            kernel,
            rhs_whnf,
            hyp_goal.rhs,
            hyp_goal.lhs,
            goal.lhs,
            true,
            hyp_proof,
            hyp_goal,
            goal,
            debug,
        ) {
            return Ok(proof);
        }
        // Symmetric attempt: derive the wrap from the (whnf-reduced) LHS.
        let lhs_whnf = kernel.whnf(goal.lhs);
        if debug {
            eprintln!("  lhs_whnf={}", kernel.render_lean(lhs_whnf));
        }
        if let Some(proof) = self.try_congr_rewrite(
            kernel,
            lhs_whnf,
            hyp_goal.lhs,
            hyp_goal.rhs,
            goal.rhs,
            false,
            hyp_proof,
            hyp_goal,
            goal,
            debug,
        ) {
            return Ok(proof);
        }
        let target = build_eq(
            kernel,
            self.eqp_eq,
            goal.level,
            goal.carrier,
            goal.lhs,
            goal.rhs,
        );
        self.try_absurd_elimination(kernel, target)
            .or_else(|| self.try_case_split_elimination(kernel, goal))
            .or_else(|| self.try_absorbing_argument(kernel, goal, debug))
            .ok_or(DeclineReason::TerminalNotDefEqNoRewrite)
    }

    /// Maximum number of retained local hypotheses ([`Search::local_hyps`])
    /// [`Search::try_absurd_elimination`] will try, most-recently-introduced
    /// first, for one stuck terminal goal. Bounded independently of
    /// [`MAX_BINDERS`] (which already bounds how many can even exist) so
    /// this loop is visibly finite on its own; exhausting it is a decline,
    /// never a hang.
    const MAX_ABSURD_HYPOTHESES: usize = MAX_BINDERS;

    /// Try to close `target` (an arbitrary Prop-valued goal — not
    /// necessarily anything to do with the induction currently in progress)
    /// from an outright contradiction in one of the ordinary Pi-bound
    /// hypotheses collected so far ([`Search::local_hyps`]),
    /// most-recently-introduced first.
    ///
    /// This is "absurd elimination": when a hypothesis's type unfolds to an
    /// application of a [`LeShape`]-shaped indexed family at index `zero`,
    /// with its parameter structurally `succ`-shaped, that hypothesis can
    /// never be inhabited (`Nat.lt a b` unfolds to exactly this shape, and
    /// `a < 0` is impossible for every `a`) — its OWN recursor, instantiated
    /// with a motive that depends only on the index (never on the
    /// hypothesis, nor on `target`'s own head symbol), produces a proof of
    /// `target` directly, without first isolating a standalone `False` and
    /// without any reference to what `target` actually says. Purely
    /// shape-driven: nothing here names `Nat.lt`, `Nat.le`, or any target
    /// declaration. Returns `None` (never a hard error) when no retained
    /// hypothesis matches — the caller declines as before.
    fn try_absurd_elimination(&mut self, kernel: &mut Kernel, target: ExprId) -> Option<ExprId> {
        if std::env::var("BIS_DEBUG").is_ok() {
            eprintln!(
                "  [absurd] try_absurd_elimination: {} local hyps, target={}",
                self.local_hyps.len(),
                kernel.render_lean(target)
            );
        }
        let mut budget = Self::MAX_ABSURD_HYPOTHESES;
        for i in (0..self.local_hyps.len()).rev() {
            if budget == 0 {
                break;
            }
            budget -= 1;
            let (fv, ty) = self.local_hyps[i];
            if let Some(proof) = self.try_absurd_from_hypothesis(kernel, fv, ty, target) {
                return Some(proof);
            }
        }
        None
    }

    /// One candidate hypothesis for [`Search::try_absurd_elimination`]; see
    /// that method's doc for the shape being matched. Builds the candidate
    /// and then independently confirms its INFERRED type is exactly
    /// `target` before returning it — declining (`None`) rather than
    /// risking a malformed candidate reaching the caller's `add_declaration`
    /// and turning a graceful decline into a hard kernel rejection.
    #[allow(clippy::too_many_lines)]
    fn try_absurd_from_hypothesis(
        &mut self,
        kernel: &mut Kernel,
        hyp_fv: u64,
        hyp_ty: ExprId,
        target: ExprId,
    ) -> Option<ExprId> {
        let debug = std::env::var("BIS_DEBUG").is_ok();
        let hyp_whnf = kernel.whnf(hyp_ty);
        let (head, args) = app_spine(kernel, hyp_whnf);
        let ExprNode::Const(family, levels) = kernel.expr_node(head).clone() else {
            if debug {
                eprintln!(
                    "  [absurd] head not Const: {}",
                    kernel.render_lean(hyp_whnf)
                );
            }
            return None;
        };
        if args.len() != 2 {
            if debug {
                eprintln!(
                    "  [absurd] args.len()={} (want 2): {}",
                    args.len(),
                    kernel.render_lean(hyp_whnf)
                );
            }
            return None;
        }
        let Some(le_shape) = detect_le_shape(self, kernel, family) else {
            if debug {
                eprintln!(
                    "  [absurd] no LeShape for family {}",
                    kernel.display_name(family)
                );
            }
            return None;
        };
        let (param, idx_val) = (args[0], args[1]);

        // The hypothesis's own index must BE `zero` -- the one instance
        // this family can never actually inhabit once the parameter is
        // `succ`-shaped.
        let zero_e = kernel.const_(le_shape.idx_shape.zero_ctor, vec![]);
        if !kernel.def_eq(idx_val, zero_e) {
            if debug {
                eprintln!(
                    "  [absurd] idx_val {} not defeq zero",
                    kernel.render_lean(idx_val)
                );
            }
            return None;
        }
        // The parameter must be STRUCTURALLY `succ _` (any predecessor) --
        // this is what makes the family's `refl` constructor unreachable at
        // this index (`refl : family p p`, so `p` would have to be `zero`
        // too, contradicting `succ`-shaped).
        let param_whnf = kernel.whnf(param);
        let (phead, pargs) = app_spine(kernel, param_whnf);
        let ExprNode::Const(psucc, _) = kernel.expr_node(phead).clone() else {
            if debug {
                eprintln!(
                    "  [absurd] param head not Const: {}",
                    kernel.render_lean(param_whnf)
                );
            }
            return None;
        };
        if psucc != le_shape.idx_shape.succ_ctor || pargs.len() != 1 {
            if debug {
                eprintln!(
                    "  [absurd] param not succ-shaped: {}",
                    kernel.render_lean(param_whnf)
                );
            }
            return None;
        }
        let pred_a = pargs[0];

        // The carrier level for equalities between two index-typed values --
        // read off the index type's OWN inferred sort, never assumed.
        let Ok(idx_sort) = kernel.infer(le_shape.idx_ty) else {
            if debug {
                eprintln!("  [absurd] infer(idx_ty) failed");
            }
            return None;
        };
        let idx_sort_whnf = kernel.whnf(idx_sort);
        let ExprNode::Sort(idx_level) = kernel.expr_node(idx_sort_whnf).clone() else {
            if debug {
                eprintln!(
                    "  [absurd] idx_ty sort not Sort: {}",
                    kernel.render_lean(idx_sort_whnf)
                );
            }
            return None;
        };

        let anon = kernel.anon();
        let level_zero = kernel.level_zero();
        let level_one = kernel.level_succ(level_zero);
        let eqp_eq = self.eqp_eq;
        let eqp_refl = self.eqp_refl;

        // `motive_over_idx := fun (idx : idx_ty) (_ : family param idx) =>
        //     idx_shape.rec{level_one} (fun _ => Sort level_zero)
        //         target
        //         (fun pred _ih => Eq idx_ty pred pred)
        //         idx`
        // -- a Prop-VALUED (not proof-valued) case split on `idx`: at
        // `zero` this reduces by iota to exactly `target`; at any `succ
        // pred` it reduces to the trivially-inhabited `Eq idx_ty pred pred`.
        let idx_fv = self.fresh_fvar();
        let idx_e = kernel.fvar(idx_fv);
        let sort0 = kernel.sort(level_zero);
        let motive2 = kernel.lam(anon, le_shape.idx_ty, sort0, BinderInfo::Default);
        let succ_pred_fv = self.fresh_fvar();
        let succ_pred = kernel.fvar(succ_pred_fv);
        let succ_case_body = build_eq(
            kernel,
            eqp_eq,
            idx_level,
            le_shape.idx_ty,
            succ_pred,
            succ_pred,
        );
        let succ_ih_fv = self.fresh_fvar();
        let succ_ih_ty = kernel.sort(level_zero);
        let succ_case = lam_fv(
            kernel,
            anon,
            succ_ih_fv,
            succ_ih_ty,
            succ_case_body,
            BinderInfo::Default,
        );
        let succ_case = lam_fv(
            kernel,
            anon,
            succ_pred_fv,
            le_shape.idx_ty,
            succ_case,
            BinderInfo::Default,
        );
        let idx_rec = kernel.const_(le_shape.idx_shape.rec_name, vec![level_one]);
        let case_generic = kernel.app(idx_rec, motive2);
        let case_generic = kernel.app(case_generic, target);
        let case_generic = kernel.app(case_generic, succ_case);
        let case_generic = kernel.app(case_generic, idx_e);

        let fam_c = kernel.const_(family, levels.clone());
        let fam_applied_p = kernel.app(fam_c, param);
        let fam_applied_idx = kernel.app(fam_applied_p, idx_e);
        let h2_fv = self.fresh_fvar();
        let motive_inner = lam_fv(
            kernel,
            anon,
            h2_fv,
            fam_applied_idx,
            case_generic,
            BinderInfo::Default,
        );
        let motive_over_idx = lam_fv(
            kernel,
            anon,
            idx_fv,
            le_shape.idx_ty,
            motive_inner,
            BinderInfo::Default,
        );

        // `refl` minor premise: `motive_over_idx param (refl param)`
        // reduces (since `param` is literally `succ pred_a`) to
        // `Eq idx_ty pred_a pred_a`.
        let refl_proof = build_eq_refl(kernel, eqp_refl, idx_level, le_shape.idx_ty, pred_a);

        // `step` minor premise: `fun m a ih => Eq.refl idx_ty m`, which has
        // type `motive_over_idx (succ m) (step param m a) = Eq idx_ty m m`
        // regardless of `m`, `a`, or the unused `ih`.
        let m_fv = self.fresh_fvar();
        let m = kernel.fvar(m_fv);
        let a_fv = self.fresh_fvar();
        let fam_c2 = kernel.const_(family, levels.clone());
        let fam_applied_p2 = kernel.app(fam_c2, param);
        let fam_applied_m = kernel.app(fam_applied_p2, m);
        let a_val = kernel.fvar(a_fv);
        let ih_fv = self.fresh_fvar();
        let ih_ty = kernel.app(motive_over_idx, m);
        let ih_ty = kernel.app(ih_ty, a_val);
        let refl_m = build_eq_refl(kernel, eqp_refl, idx_level, le_shape.idx_ty, m);
        let step_body = lam_fv(kernel, anon, ih_fv, ih_ty, refl_m, BinderInfo::Default);
        let step_body = lam_fv(
            kernel,
            anon,
            a_fv,
            fam_applied_m,
            step_body,
            BinderInfo::Default,
        );
        let step_minor = lam_fv(
            kernel,
            anon,
            m_fv,
            le_shape.idx_ty,
            step_body,
            BinderInfo::Default,
        );

        let le_rec = kernel.const_(le_shape.rec_name, vec![]);
        let applied = kernel.app(le_rec, param);
        let applied = kernel.app(applied, motive_over_idx);
        let applied = kernel.app(applied, refl_proof);
        let applied = kernel.app(applied, step_minor);
        let applied = kernel.app(applied, idx_val);
        let hyp_e = kernel.fvar(hyp_fv);
        let applied = kernel.app(applied, hyp_e);

        // `applied` mentions `hyp_fv` freely (it is only abstracted once
        // this proof is returned all the way up to the plain generalization
        // branch of `Search::attempt` that introduced it) AND every
        // outer-scope induction/generalization variable `param`/`idx_val`
        // were themselves built from (`n`, `k`, a predecessor, …) — plain
        // `Kernel::infer`, used elsewhere in this file only for CLOSED
        // candidates, would reject any of them as an unbound fvar. Every one
        // of those is already typed in `self.fvar_types` (every
        // `fresh_fvar_typed` call, in both `Search::try_induction` and the
        // plain-generalization branch, records it there), so build a
        // `LocalContext` from the whole map rather than trying to track
        // which subset `applied` actually touches.
        let mut local_ctx = LocalContext::new();
        for (&fv, &ty) in &self.fvar_types {
            local_ctx.push(LocalDecl {
                fvar: fv,
                name: anon,
                ty,
                info: BinderInfo::Default,
            });
        }
        let inferred = match kernel.infer_in(applied, &mut local_ctx) {
            Ok(t) => t,
            Err(e) => {
                if debug {
                    eprintln!("  [absurd] infer(applied) failed: {e:?}");
                }
                return None;
            }
        };
        if !kernel.def_eq(inferred, target) {
            if debug {
                eprintln!(
                    "  [absurd] inferred {} not defeq target {}",
                    kernel.render_lean(inferred),
                    kernel.render_lean(target)
                );
            }
            return None;
        }
        if debug {
            eprintln!("  [absurd] SUCCESS");
        }
        Some(applied)
    }

    /// `Eq.rec`-based transport: given `p_at_base : P(base)` — where
    /// `p_body` is the de-Bruijn-abstracted body of `P`, i.e. exactly what
    /// [`Kernel::abstract_fvars`] produces — and `h : Eq carrier base
    /// target_point`, build a proof of `P(target_point)`. The generic form
    /// of [`Search::build_eq_trans`]/[`Search::build_eq_symm`]/
    /// [`Search::build_congr_arg`]: those all specialize `P` to another
    /// `Eq`; this one takes an arbitrary abstracted predicate, which
    /// [`Search::try_case_split_elimination`] needs to move a proof between
    /// the two predecessor-shaped positions a case split produces.
    #[allow(clippy::too_many_arguments)]
    fn build_transport(
        &mut self,
        kernel: &mut Kernel,
        level: LevelId,
        carrier: ExprId,
        base: ExprId,
        target_point: ExprId,
        p_body: ExprId,
        p_at_base: ExprId,
        h: ExprId,
    ) -> ExprId {
        let anon = kernel.anon();
        let x_fv = self.fresh_fvar();
        let x = kernel.fvar(x_fv);
        let p_at_x = kernel.instantiate(p_body, &[x]);
        let hyp_ty = build_eq(kernel, self.eqp_eq, level, carrier, base, x);
        let inner = kernel.lam(anon, hyp_ty, p_at_x, BinderInfo::Default);
        let motive = lam_fv(kernel, anon, x_fv, carrier, inner, BinderInfo::Default);
        let z = kernel.level_zero();
        let rec = kernel.const_(self.eqp_rec, vec![z, level]);
        let with_carrier = kernel.app(rec, carrier);
        let with_base = kernel.app(with_carrier, base);
        let with_motive = kernel.app(with_base, motive);
        let with_minor = kernel.app(with_motive, p_at_base);
        let with_target = kernel.app(with_minor, target_point);
        kernel.app(with_target, h)
    }

    /// Maximum number of retained local hypotheses ([`Search::local_hyps`])
    /// [`Search::try_case_split_elimination`] will try, most-recently-
    /// introduced first, for one stuck terminal goal. Same bound and
    /// rationale as [`Search::MAX_ABSURD_HYPOTHESES`].
    const MAX_CASE_SPLIT_HYPOTHESES: usize = MAX_BINDERS;

    /// Try to close `goal` via a genuine case split on a local hypothesis
    /// whose type unfolds to a [`LeShape`]-shaped indexed family at a
    /// SUCC-shaped index — as opposed to [`Search::try_absurd_elimination`]'s
    /// zero-shaped index, where the family is provably uninhabited. Here the
    /// family CAN be inhabited either way, so both of its own constructors
    /// are consumed rather than one being ruled out: `family param (succ
    /// k)` came either from the family's own "at-param" constructor
    /// (forcing `param`'s own predecessor to equal `k`) or its "step"
    /// constructor (handing back `family param k` directly, one index
    /// smaller). Purely shape-driven — nothing here names `Nat.lt`,
    /// `Nat.le`, or any target declaration; the only target-shaped
    /// ingredient consulted is [`Search::stuck_hyps`], itself populated
    /// structurally by [`Search::attempt`] whenever a live induction
    /// hypothesis could not be carried forward past a plain generalization
    /// step because its domain still names a different index.
    fn try_case_split_elimination(&mut self, kernel: &mut Kernel, goal: EqGoal) -> Option<ExprId> {
        if std::env::var("BIS_DEBUG").is_ok() {
            eprintln!(
                "  [case-split] try_case_split_elimination: {} local hyps, {} stuck hyps",
                self.local_hyps.len(),
                self.stuck_hyps.len()
            );
        }
        let mut budget = Self::MAX_CASE_SPLIT_HYPOTHESES;
        for i in (0..self.local_hyps.len()).rev() {
            if budget == 0 {
                break;
            }
            budget -= 1;
            let (fv, ty) = self.local_hyps[i];
            if let Some(proof) = self.try_case_split_from_hypothesis(kernel, fv, ty, goal) {
                return Some(proof);
            }
        }
        None
    }

    /// One candidate hypothesis for [`Search::try_case_split_elimination`];
    /// see that method's doc for the shape being matched. Builds the
    /// candidate and then independently confirms its INFERRED type is
    /// exactly `goal` before returning it — same discipline as
    /// [`Search::try_absurd_from_hypothesis`].
    #[allow(clippy::too_many_lines, clippy::similar_names)]
    fn try_case_split_from_hypothesis(
        &mut self,
        kernel: &mut Kernel,
        hyp_fv: u64,
        hyp_ty: ExprId,
        goal: EqGoal,
    ) -> Option<ExprId> {
        let debug = std::env::var("BIS_DEBUG").is_ok();
        let hyp_whnf = kernel.whnf(hyp_ty);
        let (head, args) = app_spine(kernel, hyp_whnf);
        let ExprNode::Const(family, levels) = kernel.expr_node(head).clone() else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let le_shape = detect_le_shape(self, kernel, family)?;
        let (param, idx_val) = (args[0], args[1]);

        // The hypothesis's own index must be STRUCTURALLY succ-shaped —
        // exactly the case left open once try_absurd_elimination's
        // zero-index case has already been tried (by the caller) and
        // failed.
        let idx_whnf = kernel.whnf(idx_val);
        let (idx_head, idx_args) = app_spine(kernel, idx_whnf);
        let ExprNode::Const(idx_succ, _) = kernel.expr_node(idx_head).clone() else {
            return None;
        };
        if idx_succ != le_shape.idx_shape.succ_ctor || idx_args.len() != 1 {
            return None;
        }
        let k_pred = idx_args[0];

        // The parameter must ALSO be structurally succ-shaped — the same
        // requirement try_absurd_elimination makes of it, and for the same
        // reason: it is what makes the family's own "at-param" constructor
        // type reduce to something usable via idx_shape's recursor rather
        // than getting stuck on an opaque parameter.
        let param_whnf = kernel.whnf(param);
        let (param_head, param_args) = app_spine(kernel, param_whnf);
        let ExprNode::Const(param_succ, _) = kernel.expr_node(param_head).clone() else {
            return None;
        };
        if param_succ != le_shape.idx_shape.succ_ctor || param_args.len() != 1 {
            return None;
        }
        let n_pred = param_args[0];

        // Find a retained stuck hypothesis ([`Search::stuck_hyps`]) whose
        // own leading `Pi` domain is exactly `family param k_pred` — the
        // predecessor this case split actually recovers.
        let target_domain = {
            let fam_c = kernel.const_(family, levels.clone());
            let with_param = kernel.app(fam_c, param);
            kernel.app(with_param, k_pred)
        };
        let mut matched_ih = None;
        for stuck in self.stuck_hyps.iter().rev() {
            let ExprNode::Pi(_, domain_ty, body, _) = kernel.expr_node(stuck.stmt).clone() else {
                continue;
            };
            if kernel.def_eq(domain_ty, target_domain) {
                matched_ih = Some((stuck.proof, body));
                break;
            }
        }
        let Some((ih_proof, ih_body)) = matched_ih else {
            if debug {
                eprintln!("  [case-split] no matching stuck hypothesis for predecessor");
            }
            return None;
        };

        // The carrier level for equalities between two index-typed values —
        // read off the index type's own inferred sort, never assumed.
        let Ok(idx_sort) = kernel.infer(le_shape.idx_ty) else {
            if debug {
                eprintln!("  [case-split] infer(idx_ty) failed");
            }
            return None;
        };
        let idx_sort_whnf = kernel.whnf(idx_sort);
        let ExprNode::Sort(idx_level) = kernel.expr_node(idx_sort_whnf).clone() else {
            if debug {
                eprintln!(
                    "  [case-split] idx_ty sort not Sort: {}",
                    kernel.render_lean(idx_sort_whnf)
                );
            }
            return None;
        };

        let anon = kernel.anon();
        let level_zero = kernel.level_zero();
        let level_one = kernel.level_succ(level_zero);
        let eqp_eq = self.eqp_eq;
        let eqp_refl = self.eqp_refl;

        let target = build_eq(kernel, eqp_eq, goal.level, goal.carrier, goal.lhs, goal.rhs);

        // Narrow `target` to its point of dependence on `n_pred`: abstract
        // every occurrence of `n_pred` inside `target` into a placeholder,
        // giving a reusable de-Bruijn body `p_body` such that
        // `p_body[x := n_pred]` is `target` again and `p_body[x := k_pred]`
        // is the same statement at the predecessor the case split recovers.
        let placeholder_fv = self.fresh_fvar();
        let placeholder = kernel.fvar(placeholder_fv);
        let mut kb = MAX_KABSTRACT_NODES;
        let (replaced, found) = kabstract_occurrences(kernel, target, n_pred, placeholder, &mut kb);
        if !found {
            if debug {
                eprintln!("  [case-split] n_pred does not occur in target");
            }
            return None;
        }
        let p_body = kernel.abstract_fvars(replaced, &[placeholder_fv]);
        let p_at_k_pred = kernel.instantiate(p_body, &[k_pred]);
        let Ok(p_at_k_pred_goal) = parse_eq_goal(kernel, self.eqp_eq, p_at_k_pred) else {
            if debug {
                eprintln!("  [case-split] predecessor statement is not an Eq application");
            }
            return None;
        };

        // Prove the predecessor-shaped statement as its own self-contained
        // side quest via [`Search::prove_universal_identity`] — critically,
        // that re-GENERALIZES `k_pred` (and anything else free in it) back
        // into a fresh `Pi`, which is what lets the nested search induct on
        // it; calling `attempt` directly on the already-fixed `k_pred`
        // could never induct (there would be no leading `Pi` left to
        // peel). Shares, never adds to, the outer derivation's
        // binder/induction budget. The currently-being-processed hypothesis
        // is temporarily removed from `local_hyps` so this nested search
        // cannot re-select it and recurse into case-splitting on itself.
        let removed_at = self.local_hyps.iter().position(|&(fv, _)| fv == hyp_fv);
        if let Some(pos) = removed_at {
            self.local_hyps.remove(pos);
        }
        let result = self.prove_universal_identity(
            kernel,
            p_at_k_pred_goal.level,
            p_at_k_pred_goal.carrier,
            p_at_k_pred_goal.lhs,
            p_at_k_pred_goal.rhs,
            false,
            debug,
        );
        if let Some(pos) = removed_at {
            self.local_hyps.insert(pos, (hyp_fv, hyp_ty));
        }
        let Some(aux_proof) = result else {
            if debug {
                eprintln!("  [case-split] predecessor statement FAILED");
            }
            return None;
        };

        // refl branch: `fun (heq : Eq idx_ty n_pred k_pred) => <target, by
        // transporting aux_proof along heq.symm>`.
        let heq_fv = self.fresh_fvar();
        let heq = kernel.fvar(heq_fv);
        let heq_ty = build_eq(kernel, eqp_eq, idx_level, le_shape.idx_ty, n_pred, k_pred);
        let heq_symm = self.build_eq_symm(kernel, idx_level, le_shape.idx_ty, n_pred, k_pred, heq);
        let refl_value = self.build_transport(
            kernel,
            idx_level,
            le_shape.idx_ty,
            k_pred,
            n_pred,
            p_body,
            aux_proof,
            heq_symm,
        );
        let refl_case_full = lam_fv(
            kernel,
            anon,
            heq_fv,
            heq_ty,
            refl_value,
            BinderInfo::Default,
        );

        // step branch: `fun (m)(a : family param m)(heq2 : Eq idx_ty m
        // k_pred) => <target, by transporting `a` to `family param k_pred`,
        // applying the matched stuck induction hypothesis, and bridging via
        // `close_terminal` exactly as if the domains had matched directly>`.
        let m_fv = self.fresh_fvar();
        let m = kernel.fvar(m_fv);
        let a_fv = self.fresh_fvar();
        let fam_c2 = kernel.const_(family, levels.clone());
        let fam_p = kernel.app(fam_c2, param);
        let fam_p_m = kernel.app(fam_p, m);
        let a_val = kernel.fvar(a_fv);
        let heq2_fv = self.fresh_fvar();
        let heq2 = kernel.fvar(heq2_fv);
        let heq2_ty = build_eq(kernel, eqp_eq, idx_level, le_shape.idx_ty, m, k_pred);

        let fam_body = {
            let x_fv = self.fresh_fvar();
            let x = kernel.fvar(x_fv);
            let fam_c3 = kernel.const_(family, levels.clone());
            let fam_p3 = kernel.app(fam_c3, param);
            let fam_p3_x = kernel.app(fam_p3, x);
            kernel.abstract_fvars(fam_p3_x, &[x_fv])
        };
        let a2 = self.build_transport(
            kernel,
            idx_level,
            le_shape.idx_ty,
            m,
            k_pred,
            fam_body,
            a_val,
            heq2,
        );
        let ih_applied = kernel.app(ih_proof, a2);
        let ih_applied_stmt = kernel.instantiate(ih_body, &[a2]);
        let removed_at2 = self.local_hyps.iter().position(|&(fv, _)| fv == hyp_fv);
        if let Some(pos) = removed_at2 {
            self.local_hyps.remove(pos);
        }
        let step_result = self.close_terminal(
            kernel,
            goal,
            Some(Hypothesis {
                proof: ih_applied,
                stmt: ih_applied_stmt,
            }),
        );
        if let Some(pos) = removed_at2 {
            self.local_hyps.insert(pos, (hyp_fv, hyp_ty));
        }
        let step_value = match step_result {
            Ok(proof) => proof,
            Err(reason) => {
                if debug {
                    eprintln!("  [case-split] step branch FAILED: {reason}");
                }
                return None;
            }
        };
        let step_body = lam_fv(
            kernel,
            anon,
            heq2_fv,
            heq2_ty,
            step_value,
            BinderInfo::Default,
        );
        let step_body = lam_fv(kernel, anon, a_fv, fam_p_m, step_body, BinderInfo::Default);
        let step_case_full = lam_fv(
            kernel,
            anon,
            m_fv,
            le_shape.idx_ty,
            step_body,
            BinderInfo::Default,
        );

        // Index-level case split selecting which of the two branches above
        // applies, purely as a function of the OUTER application's actual
        // index (mirroring [`Search::try_absurd_from_hypothesis`] exactly,
        // except the succ-branch here carries a genuine, non-vacuous
        // payload rather than a trivially-provable filler).
        let sq_fv = self.fresh_fvar();
        let sq = kernel.fvar(sq_fv);
        let heq_at_sq_ty = build_eq(kernel, eqp_eq, idx_level, le_shape.idx_ty, sq, k_pred);
        let succ_case_body = kernel.pi(anon, heq_at_sq_ty, target, BinderInfo::Default);
        let succ_ih_fv = self.fresh_fvar();
        let succ_ih_ty = kernel.sort(level_zero);
        let succ_case = lam_fv(
            kernel,
            anon,
            succ_ih_fv,
            succ_ih_ty,
            succ_case_body,
            BinderInfo::Default,
        );
        let succ_case = lam_fv(
            kernel,
            anon,
            sq_fv,
            le_shape.idx_ty,
            succ_case,
            BinderInfo::Default,
        );

        // The zero branch of `idx_shape`'s own recursor is never invoked
        // (`param` is succ-shaped), so any well-typed filler works — the
        // same choice [`Search::try_absurd_from_hypothesis`] makes for its
        // own off-target branch.
        let zero_dummy = build_eq(kernel, eqp_eq, idx_level, le_shape.idx_ty, k_pred, k_pred);

        let idx_fv = self.fresh_fvar();
        let idx_e = kernel.fvar(idx_fv);
        let sort0 = kernel.sort(level_zero);
        let motive2 = kernel.lam(anon, le_shape.idx_ty, sort0, BinderInfo::Default);
        let idx_rec = kernel.const_(le_shape.idx_shape.rec_name, vec![level_one]);
        let case_generic = kernel.app(idx_rec, motive2);
        let case_generic = kernel.app(case_generic, zero_dummy);
        let case_generic = kernel.app(case_generic, succ_case);
        let case_generic = kernel.app(case_generic, idx_e);

        let fam_c4 = kernel.const_(family, levels.clone());
        let fam_applied_p = kernel.app(fam_c4, param);
        let fam_applied_idx = kernel.app(fam_applied_p, idx_e);
        let h2_fv = self.fresh_fvar();
        let motive_inner = lam_fv(
            kernel,
            anon,
            h2_fv,
            fam_applied_idx,
            case_generic,
            BinderInfo::Default,
        );
        let motive_over_idx = lam_fv(
            kernel,
            anon,
            idx_fv,
            le_shape.idx_ty,
            motive_inner,
            BinderInfo::Default,
        );

        let le_rec = kernel.const_(le_shape.rec_name, vec![]);
        let applied = kernel.app(le_rec, param);
        let applied = kernel.app(applied, motive_over_idx);
        let applied = kernel.app(applied, refl_case_full);
        let applied = kernel.app(applied, step_case_full);
        let applied = kernel.app(applied, idx_val);
        let hyp_e = kernel.fvar(hyp_fv);
        let applied = kernel.app(applied, hyp_e);

        // `applied : motive_over_idx idx_val hyp_e`, which reduces (`idx_val`
        // is literally `succ k_pred`) to `Pi(_: Eq idx_ty k_pred k_pred),
        // target)`; apply it to `Eq.refl` to get `target` itself.
        let refl_k_pred = build_eq_refl(kernel, eqp_refl, idx_level, le_shape.idx_ty, k_pred);
        let applied = kernel.app(applied, refl_k_pred);

        // Independently confirm the INFERRED type before returning — same
        // discipline as `try_absurd_from_hypothesis`: a malformed candidate
        // declines here, never reaches the caller's `add_declaration`.
        let mut local_ctx = LocalContext::new();
        for (&fv, &ty) in &self.fvar_types {
            local_ctx.push(LocalDecl {
                fvar: fv,
                name: anon,
                ty,
                info: BinderInfo::Default,
            });
        }
        let inferred = match kernel.infer_in(applied, &mut local_ctx) {
            Ok(t) => t,
            Err(e) => {
                if debug {
                    eprintln!("  [case-split] infer(applied) failed: {e:?}");
                }
                return None;
            }
        };
        if !kernel.def_eq(inferred, target) {
            if debug {
                eprintln!(
                    "  [case-split] inferred {} not defeq target {}",
                    kernel.render_lean(inferred),
                    kernel.render_lean(target)
                );
            }
            return None;
        }
        if debug {
            eprintln!("  [case-split] SUCCESS");
        }
        Some(applied)
    }

    /// Maximum number of top-level argument positions of the WHNF-reduced
    /// goal LHS's application spine [`Search::try_absorbing_argument`] will
    /// try as an independent, hypothesis-free rewrite target. Ordinary
    /// arithmetic operators are binary (once typeclass/instance arguments
    /// are counted too), so this is a generous, still-finite ceiling.
    const MAX_ABSORB_ARGS: usize = 8;

    /// Rebuild `expr`'s own top-level application spine, generalizing every
    /// argument position of carrier type `carrier` that is NOT (up to
    /// `def_eq`) `fixed_value` to a fresh, OPAQUE variable — never
    /// decomposing an argument's own internal structure, and never
    /// generalizing `fixed_value` itself (the value
    /// [`Search::try_absorbing_argument`] just proved some other position
    /// equals, e.g. the literal `0` a subtraction was rewritten to; treating
    /// it as opaque too would ask for the operator's identity to hold at
    /// EVERY value there, not just the one already established).
    ///
    /// Returns the rebuilt expression (using the fresh variables) alongside
    /// the map from each fresh variable back to the ORIGINAL argument it
    /// replaced, in the exact shape
    /// [`Search::prove_universal_identity_with`]'s `reinstantiate_as`
    /// expects. An argument whose type cannot be inferred, or is not
    /// `carrier`-typed, is left untouched (literal) — still sound, only
    /// loses generality if that literal form is not itself provable.
    fn generalize_opaque_operands(
        &mut self,
        kernel: &mut Kernel,
        carrier: ExprId,
        fixed_value: ExprId,
        expr: ExprId,
        local_ctx: &mut LocalContext,
    ) -> (ExprId, std::collections::BTreeMap<u64, ExprId>) {
        let (head, args) = app_spine(kernel, expr);
        let mut reinstantiate_as = std::collections::BTreeMap::new();
        let mut rebuilt = head;
        for arg in &args {
            if kernel.def_eq(*arg, fixed_value) {
                rebuilt = kernel.app(rebuilt, *arg);
                continue;
            }
            let generalized = match kernel.infer_in(*arg, local_ctx) {
                Ok(ty) if kernel.def_eq(ty, carrier) => {
                    let fresh = self.fresh_fvar_typed(ty);
                    reinstantiate_as.insert(fresh, *arg);
                    Some(kernel.fvar(fresh))
                }
                _ => None,
            };
            rebuilt = kernel.app(rebuilt, generalized.unwrap_or(*arg));
        }
        (rebuilt, reinstantiate_as)
    }

    /// Close a terminal `Eq(goal.lhs, goal.rhs)` when the induction
    /// hypothesis is no help at all — not even through the degenerate match
    /// [`Search::try_congr_rewrite`] takes when the hypothesis's own RHS
    /// happens to equal `goal.rhs` — because the fact actually needed has
    /// NOTHING to do with the induction currently in progress.
    ///
    /// `(succ q - succ q) * descFactorial (succ q) (succ q) = 0` is exactly
    /// this shape: the induction hypothesis (`descFactorial q (succ q) =
    /// 0`) never occurs in the goal at all (the recursive call's own first
    /// argument has already moved on to `succ q`), yet the goal is true via
    /// TWO facts that are each independent of that induction — `succ q -
    /// succ q = 0` and `0 * x = 0` — chained by ordinary congruence.
    ///
    /// Tries each top-level argument position `i` of the WHNF-reduced
    /// `goal.lhs`'s application spine, in turn: if `Eq(arg_i, goal.rhs)` is
    /// itself provable via a nested, hypothesis-INDEPENDENT
    /// [`Search::prove_universal_identity`] call (its own bounded,
    /// budget-sharing side quest — this is where `succ q - succ q = 0`
    /// gets proved, with no reference to the surrounding multiplication),
    /// the remaining gap is `Eq(head(..., goal.rhs, ...), goal.rhs)` — the
    /// SAME operator with position `i` now fixed at the target value and
    /// every OTHER top-level argument position generalized to a fresh,
    /// OPAQUE variable (never decomposed further), so what gets asked for
    /// is the plain operator fact (`0 * x = 0`), never a claim tied to
    /// whatever this specific term's other argument happens to be built
    /// from (`0 * descFactorial n n = 0`, which is not simpler and may not
    /// even be true of the general shape reached by re-deriving it). Both
    /// steps chain via `Eq.trans`.
    #[allow(clippy::too_many_lines)]
    fn try_absorbing_argument(
        &mut self,
        kernel: &mut Kernel,
        goal: EqGoal,
        debug: bool,
    ) -> Option<ExprId> {
        let lhs_whnf = kernel.whnf(goal.lhs);
        let (head, args) = app_spine(kernel, lhs_whnf);
        if args.is_empty() || args.len() > Self::MAX_ABSORB_ARGS {
            return None;
        }
        let anon = kernel.anon();
        let mut local_ctx = LocalContext::new();
        for (&fv, &ty) in &self.fvar_types {
            local_ctx.push(LocalDecl {
                fvar: fv,
                name: anon,
                ty,
                info: BinderInfo::Default,
            });
        }
        for i in 0..args.len() {
            let Ok(arg_ty) = kernel.infer_in(args[i], &mut local_ctx) else {
                continue;
            };
            if !kernel.def_eq(arg_ty, goal.carrier) {
                continue;
            }
            // Position `i` itself must already be def_eq to `goal.rhs`, or
            // this whole path is pointless -- skip straight past the
            // (budget-consuming) nested proof attempt in that case.
            if kernel.def_eq(args[i], goal.rhs) {
                continue;
            }
            let placeholder_fv = self.fresh_fvar();
            let placeholder = kernel.fvar(placeholder_fv);
            let mut kb = MAX_KABSTRACT_NODES;
            let (replaced, found) =
                kabstract_occurrences(kernel, lhs_whnf, args[i], placeholder, &mut kb);
            if !found {
                continue;
            }
            let Some(arg_eq_target) = self.prove_universal_identity(
                kernel,
                goal.level,
                goal.carrier,
                args[i],
                goal.rhs,
                true,
                debug,
            ) else {
                continue;
            };
            if debug {
                eprintln!(
                    "  [absorb] position {i}: {} = {} proved",
                    kernel.render_lean(args[i]),
                    kernel.render_lean(goal.rhs)
                );
            }
            let abstracted = kernel.abstract_fvars(replaced, &[placeholder_fv]);
            let g = kernel.lam(anon, arg_ty, abstracted, BinderInfo::Default);
            let step1 = self.build_congr_arg(
                kernel,
                g,
                goal.level,
                goal.carrier,
                goal.level,
                goal.carrier,
                args[i],
                goal.rhs,
                arg_eq_target,
            );
            let mid = kernel.app(g, goal.rhs);

            // Build `head(..., goal.rhs at i, ..., untouched elsewhere)`
            // literally, THEN re-`whnf` it before looking for other
            // argument positions to generalize — never the other way
            // around. Fixing position `i` at a LITERAL value can unlock
            // further beta/iota reduction this producer could not see
            // before (a course-of-values `brecOn` step function applied to
            // the now-concrete `goal.rhs` reduces into its own body, which
            // is where an operator like multiplication's SECOND operand
            // first appears as a genuine, separable argument rather than
            // being buried inside the unevaluated continuation) — acting on
            // the ORIGINAL `args` positions from `lhs_whnf` alone would
            // keep treating that still-fused operand as opaque, unable to
            // recognize `0 * x = 0` as a plain fact about `HMul.hMul`, ever
            // reduced to `0 * descFactorial …`, one fixed shape at a time.
            let mut lhs_after_literal = head;
            for (j, arg) in args.iter().enumerate() {
                lhs_after_literal =
                    kernel.app(lhs_after_literal, if j == i { goal.rhs } else { *arg });
            }
            let lhs_after_whnf = kernel.whnf(lhs_after_literal);
            if debug {
                let literal_s = kernel.render_lean(lhs_after_literal);
                let whnf_s = kernel.render_lean(lhs_after_whnf);
                eprintln!(
                    "  [absorb-remainder] literal={literal_s} whnf={whnf_s} changed={}",
                    literal_s != whnf_s
                );
            }
            let (lhs_after, reinstantiate_as) = self.generalize_opaque_operands(
                kernel,
                goal.carrier,
                goal.rhs,
                lhs_after_whnf,
                &mut local_ctx,
            );
            if debug {
                eprintln!(
                    "  [absorb-remainder] rebuilt={} other_positions={}",
                    kernel.render_lean(lhs_after),
                    reinstantiate_as.len()
                );
            }
            let remainder = if reinstantiate_as.is_empty() {
                if kernel.def_eq(lhs_after, goal.rhs) {
                    Some(build_eq_refl(
                        kernel,
                        self.eqp_refl,
                        goal.level,
                        goal.carrier,
                        goal.rhs,
                    ))
                } else {
                    self.prove_universal_identity(
                        kernel,
                        goal.level,
                        goal.carrier,
                        lhs_after,
                        goal.rhs,
                        true,
                        debug,
                    )
                }
            } else {
                self.prove_universal_identity_with(
                    kernel,
                    goal.level,
                    goal.carrier,
                    lhs_after,
                    goal.rhs,
                    &reinstantiate_as,
                    true,
                    debug,
                )
            };
            let Some(remainder_proof) = remainder else {
                if debug {
                    eprintln!("  [absorb] position {i}: remainder FAILED");
                }
                continue;
            };
            let result = self.build_eq_trans(
                kernel,
                goal.level,
                goal.carrier,
                lhs_whnf,
                mid,
                goal.rhs,
                step1,
                remainder_proof,
            );
            // Independently confirm the inferred type before returning —
            // same discipline as `try_absurd_from_hypothesis` and
            // `try_case_split_from_hypothesis`: a malformed candidate
            // declines here, never reaches the caller's `add_declaration`.
            let target = build_eq(
                kernel,
                self.eqp_eq,
                goal.level,
                goal.carrier,
                goal.lhs,
                goal.rhs,
            );
            match kernel.infer_in(result, &mut local_ctx) {
                Ok(inferred) if kernel.def_eq(inferred, target) => {
                    if debug {
                        eprintln!("  [absorb] position {i}: SUCCESS");
                    }
                    return Some(result);
                }
                Ok(inferred) => {
                    if debug {
                        eprintln!(
                            "  [absorb] position {i}: inferred {} not defeq target {}",
                            kernel.render_lean(inferred),
                            kernel.render_lean(target)
                        );
                    }
                }
                Err(e) => {
                    if debug {
                        eprintln!("  [absorb] position {i}: infer(result) failed: {e:?}");
                    }
                }
            }
        }
        None
    }

    /// Abstract every occurrence of `needle` inside `haystack` into a fresh
    /// binder, giving a candidate wrap `f`; if any occurrence was found and
    /// `f(other_side)` is definitionally equal to `expected`, build and
    /// return the `congrArg`-shaped proof. Returns `None` (never a hard
    /// error) when no occurrence exists or the resulting wrap does not close
    /// the gap — the caller tries the symmetric direction next.
    #[allow(clippy::too_many_arguments)]
    fn try_congr_rewrite(
        &mut self,
        kernel: &mut Kernel,
        haystack: ExprId,
        needle: ExprId,
        other_side: ExprId,
        expected: ExprId,
        other_is_hyp_lhs: bool,
        hyp_proof: ExprId,
        hyp_goal: EqGoal,
        goal: EqGoal,
        debug: bool,
    ) -> Option<ExprId> {
        let placeholder_fv = self.fresh_fvar();
        let placeholder = kernel.fvar(placeholder_fv);
        let mut budget = MAX_KABSTRACT_NODES;
        let (replaced, found) =
            kabstract_occurrences(kernel, haystack, needle, placeholder, &mut budget);
        if !found {
            if debug {
                eprintln!(
                    "  [kabstract] no occurrence of {} in {}",
                    kernel.render_lean(needle),
                    kernel.render_lean(haystack)
                );
            }
            return None;
        }
        let anon = kernel.anon();
        let abstracted = kernel.abstract_fvars(replaced, &[placeholder_fv]);
        let f = kernel.lam(anon, hyp_goal.carrier, abstracted, BinderInfo::Default);
        let candidate = kernel.app(f, other_side);
        let ok = kernel.def_eq(candidate, expected);
        if debug {
            eprintln!(
                "  [kabstract] found occurrence; candidate={} expected={} defeq={ok}",
                kernel.render_lean(candidate),
                kernel.render_lean(expected)
            );
        }
        if ok {
            return Some(self.build_congr(kernel, f, hyp_proof, hyp_goal, goal));
        }
        // The single congruence rewrite alone does not close the gap: the
        // wrap `f` was found, but `f(other_side)` is not definitionally the
        // side of the goal it needs to be. This is exactly the "step-case
        // bridge is not a single congruence" shape — e.g. `f = fun x => (1 +
        // n) * x` versus the goal's own `fun x => n.succ * x`, differing only
        // by the arithmetic identity `1 + n = n.succ`. Try to prove THAT
        // residual gap as a standalone, universally-quantified auxiliary
        // lemma and splice it onto the congruence proof with `Eq.trans`.
        //
        // `whole_term_match` records whether `f` is the identity (`haystack`
        // was, as a WHOLE, defeq `needle`) — contributing no actual
        // structural context, so `candidate` here is just `other_side`
        // again, related to `expected` by nothing `def_eq` hasn't already
        // ruled out. `try_residual_lemma` still tries its narrowed-diff and
        // split-congruence routes in this case (both DECLINE cleanly, never
        // wrongly succeed, when the two sides genuinely share no structure —
        // see their own docs), but skips its un-narrowed whole-pair
        // fallback: that fallback is what re-poses an unrelated pair as
        // "prove `f(n) = f(succ n))`" and recurses one `succ` deeper at
        // every nested attempt — measured, for
        // `F:ml430-nat-descfactorial-of-lt-fbcf5d26`'s own step case (whose
        // induction hypothesis's RHS is `0`, matching this goal's RHS
        // trivially at the top), burning the entire residual budget on that
        // one dead end before [`Search::try_absorbing_argument`] — the
        // genuinely provable chain — ever got a turn.
        let whole_term_match = kernel.def_eq(haystack, needle);
        let aux = self.try_residual_lemma(
            kernel,
            hyp_goal.level,
            hyp_goal.carrier,
            candidate,
            expected,
            whole_term_match,
            debug,
        )?;
        // `aux : Eq(candidate, expected)`. `build_congr` always returns a
        // proof of `Eq(f(hyp_goal.lhs), f(hyp_goal.rhs))`; `candidate` is
        // `f(hyp_goal.lhs)` when `other_side` was `hyp_goal.lhs` (the RHS
        // branch) and `f(hyp_goal.rhs)` otherwise (the LHS branch), so the
        // two branches need `aux` spliced on opposite sides of `Eq.trans`.
        let congr_proof = self.build_congr(kernel, f, hyp_proof, hyp_goal, goal);
        let a_side = kernel.app(f, hyp_goal.lhs);
        let b_side = kernel.app(f, hyp_goal.rhs);
        Some(if other_is_hyp_lhs {
            // candidate == a_side; aux : Eq(a_side, expected).
            let aux_symm = self.build_eq_symm(
                kernel,
                hyp_goal.level,
                hyp_goal.carrier,
                a_side,
                expected,
                aux,
            );
            self.build_eq_trans(
                kernel,
                hyp_goal.level,
                hyp_goal.carrier,
                expected,
                a_side,
                b_side,
                aux_symm,
                congr_proof,
            )
        } else {
            // candidate == b_side; aux : Eq(b_side, expected).
            self.build_eq_trans(
                kernel,
                hyp_goal.level,
                hyp_goal.carrier,
                a_side,
                b_side,
                expected,
                congr_proof,
                aux,
            )
        })
    }

    /// Generalize the residual gap `Eq(candidate, expected)` back into a
    /// standalone `∀ …, Eq(candidate, expected)` goal over every free
    /// variable this search has minted so far that occurs in either side
    /// (with a KNOWN type, from [`Search::fvar_types`] — a variable whose
    /// type was never recorded makes generalizing it unsound to attempt, so
    /// its presence declines this path rather than guessing), and try to
    /// prove that auxiliary lemma with a nested, budget-sharing call to
    /// [`Search::attempt`]. On success, the returned proof is the lemma
    /// re-applied to the ORIGINAL free variable values, i.e. exactly a proof
    /// of `Eq(candidate, expected)` in the CURRENT scope.
    ///
    /// Bounded by [`MAX_RESIDUAL_LEMMAS`] (decremented on every attempt,
    /// success or failure) so this cannot turn one decline into unbounded
    /// extra search, and the nested `attempt` call shares — rather than
    /// adds to — the outer derivation's [`MAX_BINDERS`]/[`MAX_INDUCTIONS`]
    /// budget, restored afterward regardless of outcome since the lemma is a
    /// self-contained side quest, not a consumer of the primary derivation's
    /// remaining search budget.
    #[allow(clippy::too_many_arguments)]
    fn try_residual_lemma(
        &mut self,
        kernel: &mut Kernel,
        level: LevelId,
        carrier: ExprId,
        candidate: ExprId,
        expected: ExprId,
        skip_whole_pair_fallback: bool,
        debug: bool,
    ) -> Option<ExprId> {
        // First, narrow the gap to its actual point of difference, so the
        // lemma this asks for is as small as it can be — `1 + n = n.succ`,
        // say, rather than the whole multiplication surrounding it. Without
        // this, generalizing the ENTIRE (candidate, expected) pair when they
        // share a large common context just re-poses a goal nearly as hard
        // as the original one it is meant to help close, and a nested
        // `attempt` on it can recurse into needing the very same residual
        // again — burning the shared budget without making progress.
        // Both sides need to be in a COMPARABLE reduced form before a
        // structural spine-diff means anything: `candidate` here is a raw,
        // unreduced `App(f, other_side)` beta-redex (`f` a lambda), which has
        // nothing in common structurally with `expected`'s own head shape
        // until both are whnf-forced through to the same underlying
        // operator application.
        let candidate_whnf = kernel.whnf(candidate);
        let expected_whnf = kernel.whnf(expected);
        let mut diff_budget = MAX_DIFF_NODES;
        if let Some((diff_a, diff_b)) =
            find_diff(kernel, candidate_whnf, expected_whnf, &mut diff_budget)
            && !(kernel.def_eq(diff_a, candidate_whnf) && kernel.def_eq(diff_b, expected_whnf))
        {
            let placeholder_fv = self.fresh_fvar();
            let placeholder = kernel.fvar(placeholder_fv);
            let mut kb = MAX_KABSTRACT_NODES;
            let (replaced, found) =
                kabstract_occurrences(kernel, candidate_whnf, diff_a, placeholder, &mut kb);
            if found {
                let anon = kernel.anon();
                let abstracted = kernel.abstract_fvars(replaced, &[placeholder_fv]);
                let g = kernel.lam(anon, carrier, abstracted, BinderInfo::Default);
                let g_diff_b = kernel.app(g, diff_b);
                if kernel.def_eq(g_diff_b, expected_whnf) {
                    if debug {
                        eprintln!(
                            "  [residual] narrowed diff: {} vs {}",
                            kernel.render_lean(diff_a),
                            kernel.render_lean(diff_b)
                        );
                    }
                    if let Some(aux_diff) = self.prove_universal_identity(
                        kernel, level, carrier, diff_a, diff_b, false, debug,
                    ) {
                        return Some(self.build_congr_arg(
                            kernel, g, level, carrier, level, carrier, diff_a, diff_b, aux_diff,
                        ));
                    }
                }
            }
        }
        // Next, try splitting a DIAGONAL mismatch — the same head applied to
        // the same arguments on both sides collapsed onto one occurrence
        // site — into an independently-generalized, strictly more general
        // statement (see `try_split_congruence`'s own doc). Tried before the
        // whole-pair fallback below since it is more targeted and, when it
        // applies at all, is what actually closes shapes like `Nat.sub_self`
        // that the whole-pair fallback re-poses as the same diagonal.
        if let Some(proof) =
            self.try_split_congruence(kernel, level, carrier, candidate, expected, debug)
        {
            return Some(proof);
        }
        // Fall back to generalizing the whole (candidate, expected) pair —
        // still correct, just less likely to be provable in one shot. Never
        // for a degenerate whole-term match (`skip_whole_pair_fallback`) —
        // see the caller's own doc for why that specific combination is an
        // unproductive, self-similar dead end rather than a merely-harder
        // instance of this same fallback.
        if skip_whole_pair_fallback {
            if debug {
                eprintln!(
                    "  [residual] skipping whole-pair fallback for a degenerate whole-term match"
                );
            }
            return None;
        }
        self.prove_universal_identity(kernel, level, carrier, candidate, expected, false, debug)
    }

    /// Prove `Eq carrier a b` by generalizing every free variable (with a
    /// KNOWN type, from [`Search::fvar_types`]) occurring in either side back
    /// into a standalone `∀ …, Eq(a, b)` goal, and discharging it with a
    /// nested, budget-sharing call to [`Search::attempt`]. On success,
    /// returns that proof re-applied to the ORIGINAL free-variable values —
    /// i.e. a proof of `Eq carrier a b` in the CURRENT scope.
    ///
    /// Bounded by [`MAX_RESIDUAL_LEMMAS`] (decremented on every attempt,
    /// success or failure). The nested `attempt` call shares — rather than
    /// adds to — the outer derivation's [`MAX_BINDERS`]/[`MAX_INDUCTIONS`]
    /// budget, whose counters are restored afterward regardless of outcome:
    /// the lemma is a self-contained side quest, not a consumer of the
    /// primary derivation's remaining search budget.
    #[allow(clippy::too_many_arguments)]
    fn prove_universal_identity(
        &mut self,
        kernel: &mut Kernel,
        level: LevelId,
        carrier: ExprId,
        a: ExprId,
        b: ExprId,
        boost: bool,
        debug: bool,
    ) -> Option<ExprId> {
        self.prove_universal_identity_with(
            kernel,
            level,
            carrier,
            a,
            b,
            &std::collections::BTreeMap::new(),
            boost,
            debug,
        )
    }

    /// [`Search::prove_universal_identity`], generalized so the caller can
    /// control what each generalized variable is RE-INSTANTIATED to once the
    /// universal statement is proved, rather than always instantiating a
    /// variable back at itself.
    ///
    /// Every variable [`collect_fvars`] finds in `a`/`b` is still abstracted
    /// into its own leading `Pi` (unchanged from the base method) — this
    /// argument only changes what value closes each `Pi` back up afterward:
    /// a variable present in `reinstantiate_as` is applied at its MAPPED
    /// value; any other is applied at itself, exactly as before. This is
    /// what lets [`Search::try_split_congruence`] mint FRESH variables for a
    /// diagonal instance's two occurrence sites, prove a strictly more
    /// general two-variable statement about them, and then re-specialize
    /// both sites back to the single original value the diagonal actually
    /// needs — a fresh variable's "value in the current scope" is not
    /// itself, so the default self-instantiation would be a no-op that
    /// proves nothing about the original goal.
    ///
    /// `boost`: whether this nested attempt gets the [`MIN_RESIDUAL_…`]
    /// floors. **Deliberately not applied everywhere.** The floors make an
    /// otherwise-declined nested attempt try its own induction anyway — sound
    /// either way, but exactly what lets an UNPRODUCTIVE, self-similar chain
    /// keep recursing (measured: without restricting this, closing
    /// `F:ml430-nat-descfactorial-of-lt-fbcf5d26` degenerated into
    /// repeatedly "proving" `descFactorial n (n+1) = descFactorial (n+1)
    /// (n+2)`-shaped false statements one `succ` deeper each time, burning
    /// the entire [`MAX_RESIDUAL_LEMMAS`] budget before the genuinely
    /// provable chain ever got a turn). Pass `true` only from
    /// [`Search::try_absorbing_argument`] (an argument position PROVABLY
    /// reaches the target) and [`Search::try_split_congruence`] (a STRICTLY
    /// MORE GENERAL statement than a diagonal already stuck on the same
    /// fact) — the two mechanisms this floor exists for. Every other call
    /// site, INCLUDING case-split's own predecessor obligation (measured:
    /// boosting it too reproduces the same budget-exhausting explosion,
    /// because most of its OWN invocations are against an irrelevant
    /// ancestor hypothesis, not the one that actually matters, and the floor
    /// cannot tell which), passes `false` — unchanged from this producer's
    /// behavior before either new mechanism existed.
    #[allow(clippy::too_many_arguments)]
    fn prove_universal_identity_with(
        &mut self,
        kernel: &mut Kernel,
        level: LevelId,
        carrier: ExprId,
        a: ExprId,
        b: ExprId,
        reinstantiate_as: &std::collections::BTreeMap<u64, ExprId>,
        boost: bool,
        debug: bool,
    ) -> Option<ExprId> {
        if self.residual_budget == 0 {
            return None;
        }
        self.residual_budget -= 1;

        let mut occurring = std::collections::BTreeSet::new();
        let mut budget = MAX_FVAR_COLLECT_NODES;
        collect_fvars(kernel, a, &mut occurring, &mut budget);
        collect_fvars(kernel, b, &mut occurring, &mut budget);
        if occurring.is_empty() {
            return None;
        }
        let ordered: Vec<u64> = occurring.into_iter().collect();
        let mut types = Vec::with_capacity(ordered.len());
        for v in &ordered {
            types.push(*self.fvar_types.get(v)?);
        }

        let base = build_eq(kernel, self.eqp_eq, level, carrier, a, b);
        let anon = kernel.anon();
        let mut residual_goal = base;
        for (v, ty) in ordered.iter().zip(types.iter()) {
            let abstracted = kernel.abstract_fvars(residual_goal, &[*v]);
            residual_goal = kernel.pi(anon, *ty, abstracted, BinderInfo::Default);
        }
        if debug {
            eprintln!("  [residual] goal={}", kernel.render_lean(residual_goal));
        }

        // The MIN_RESIDUAL_* floors below give this nested attempt a
        // guaranteed minimum induction/binder capability no matter how
        // exhausted the outer derivation's shared budget already is — sound
        // either way, but that guarantee is exactly what lets an
        // unproductive chain of these nested attempts keep making just
        // enough apparent progress to recurse again. MAX_RESIDUAL_CHAIN_DEPTH
        // bounds how deep that chain may nest, independent of
        // `residual_budget`'s bound on the total COUNT of attempts — see its
        // own doc for why both are needed.
        if self.residual_depth >= MAX_RESIDUAL_CHAIN_DEPTH {
            if debug {
                eprintln!("  [residual] chain depth exceeded: maximum {MAX_RESIDUAL_CHAIN_DEPTH}");
            }
            return None;
        }
        self.residual_depth += 1;
        let snapshot = (
            self.binders_left,
            self.inductions_left,
            self.binders_used,
            self.inductions_used,
        );
        if boost {
            self.binders_left = self.binders_left.max(MIN_RESIDUAL_BINDERS);
            self.inductions_left = self.inductions_left.max(MIN_RESIDUAL_INDUCTIONS);
        }
        let eqp = EqPrimitives {
            eq: self.eqp_eq,
            eq_refl: self.eqp_refl,
            eq_rec: self.eqp_rec,
        };
        let result = self.attempt(kernel, residual_goal, &eqp, None);
        (
            self.binders_left,
            self.inductions_left,
            self.binders_used,
            self.inductions_used,
        ) = snapshot;
        self.residual_depth -= 1;
        let residual_proof = match result {
            Ok(proof) => proof,
            Err(reason) => {
                if debug {
                    eprintln!("  [residual] FAILED: {reason}");
                }
                return None;
            }
        };

        // Instantiate outermost-first: each successive `Pi` above was wrapped
        // AROUND the previous body, so the LAST variable generalized is the
        // OUTERMOST binder — apply in the reverse of that order.
        let mut aux = residual_proof;
        for v in ordered.iter().rev() {
            let value = reinstantiate_as
                .get(v)
                .copied()
                .unwrap_or_else(|| kernel.fvar(*v));
            aux = kernel.app(aux, value);
        }
        if debug {
            eprintln!("  [residual] proved aux={}", kernel.render_lean(aux));
        }
        Some(aux)
    }

    /// Maximum number of top-level argument positions
    /// [`Search::try_split_congruence`] will compare between `candidate` and
    /// `expected`. Ordinary arithmetic operators (`+`, `*`, `-`, …) are
    /// binary once their typeclass/instance arguments are stripped by
    /// `app_spine`'s own head discovery, so this is a generous, still-finite
    /// ceiling rather than a tight-fitting one; exhausting it declines this
    /// path rather than building an unbounded search.
    const MAX_SPLIT_ARGS: usize = 8;

    /// The hypothesis-independent counterpart to the single-diff narrowing
    /// in [`Search::try_residual_lemma`]: closes a residual gap
    /// `Eq(candidate, expected)` where `candidate` and `expected` share the
    /// SAME head applied to the SAME number of arguments, but differ at
    /// *more than one* argument position — the shape
    /// [`find_diff`] cannot narrow, since it only descends when every
    /// argument but the last already matches.
    ///
    /// The canonical case this exists for: `candidate = f(v, v)`,
    /// `expected = f(g(v), g(v))` for the SAME free variable `v` occurring
    /// at both argument positions (e.g. `v - v` vs `succ v - succ v`, once
    /// `v` is the predecessor a case split or induction just introduced).
    /// [`Search::prove_universal_identity`] can only ever generalize `v`
    /// back to ONE variable, since it collapses every occurrence of the same
    /// free-variable id into a single `Pi` — so the auxiliary goal it poses
    /// is the same DIAGONAL statement the caller was already stuck on,
    /// self-similar under induction and never simpler. The general,
    /// strictly stronger statement obtained by generalizing the two
    /// occurrence SITES independently (`∀ x y, f(x, y) = f(g(x), g(y))`,
    /// e.g. `Nat.succ_sub_succ`'s symmetric form) is what is actually
    /// provable by ordinary induction on one of the two — and it is
    /// STRICTLY MORE GENERAL, so proving it is always a sound way to
    /// discharge the specific diagonal instance: re-specializing both fresh
    /// variables back to the one original value the diagonal needs
    /// ([`Search::prove_universal_identity_with`]'s `reinstantiate_as`) is a
    /// plain instantiation of an already-checked universal fact, not a new
    /// assumption.
    ///
    /// For every differing argument position, `expected`'s side must embed
    /// `candidate`'s side via [`kabstract_occurrences`] (i.e. there is a wrap
    /// `g_i` with `g_i(candidate_arg_i)` defeq `expected_arg_i`) — a real
    /// requirement, not a convenience: it is what lets the fresh variable at
    /// that position be re-specialized on BOTH sides consistently once the
    /// general statement is proved. A position where no such embedding
    /// exists makes this whole path decline (`None`), never build a
    /// mismatched candidate.
    #[allow(
        clippy::too_many_arguments,
        clippy::too_many_lines,
        clippy::items_after_statements
    )]
    fn try_split_congruence(
        &mut self,
        kernel: &mut Kernel,
        level: LevelId,
        carrier: ExprId,
        candidate: ExprId,
        expected: ExprId,
        debug: bool,
    ) -> Option<ExprId> {
        let candidate_whnf = beta_whnf(kernel, candidate);
        let expected_whnf = beta_whnf(kernel, expected);
        let (head_a, args_a) = app_spine(kernel, candidate_whnf);
        let (head_b, args_b) = app_spine(kernel, expected_whnf);
        if debug {
            eprintln!(
                "  [split] entry: candidate={} expected={} head_a={} head_b={} args_a={} args_b={}",
                kernel.render_lean(candidate_whnf),
                kernel.render_lean(expected_whnf),
                kernel.render_lean(head_a),
                kernel.render_lean(head_b),
                args_a.len(),
                args_b.len()
            );
        }
        if args_a.len() != args_b.len()
            || args_a.is_empty()
            || args_a.len() > Self::MAX_SPLIT_ARGS
            || !kernel.def_eq(head_a, head_b)
        {
            if debug {
                eprintln!("  [split] declined: arity/head mismatch");
            }
            return None;
        }

        let mut diff_indices = Vec::new();
        for i in 0..args_a.len() {
            if !kernel.def_eq(args_a[i], args_b[i]) {
                diff_indices.push(i);
            }
        }
        // Fewer than two differing positions is exactly what
        // `find_diff`/the single-diff narrowing in `try_residual_lemma`
        // already covers — decline here so this path only ever does work
        // the simpler one cannot.
        if diff_indices.len() < 2 {
            if debug {
                eprintln!(
                    "  [split] declined: only {} differing position(s)",
                    diff_indices.len()
                );
            }
            return None;
        }

        let mut local_ctx = LocalContext::new();
        let anon = kernel.anon();
        for (&fv, &ty) in &self.fvar_types {
            local_ctx.push(LocalDecl {
                fvar: fv,
                name: anon,
                ty,
                info: BinderInfo::Default,
            });
        }

        // For every differing position, find the wrap `g_i` embedding
        // `args_a[i]` inside `args_b[i]`, and the type of `args_a[i]` (needed
        // to bind the fresh generalization variable). Any failure here
        // declines the whole path — a partial split would generalize some
        // positions and silently keep others fixed at values that may not
        // even occur in `expected`, never a sound thing to return.
        struct Slot {
            fresh: u64,
            wrap: ExprId,
            original: ExprId,
        }
        let mut slots: Vec<Option<Slot>> = (0..args_a.len()).map(|_| None).collect();
        for &i in &diff_indices {
            let placeholder_fv = self.fresh_fvar();
            let placeholder = kernel.fvar(placeholder_fv);
            let mut kb = MAX_KABSTRACT_NODES;
            let (replaced, found) =
                kabstract_occurrences(kernel, args_b[i], args_a[i], placeholder, &mut kb);
            if !found {
                if debug {
                    eprintln!(
                        "  [split] position {i}: {} does not occur in {}",
                        kernel.render_lean(args_a[i]),
                        kernel.render_lean(args_b[i])
                    );
                }
                return None;
            }
            let Ok(arg_ty) = kernel.infer_in(args_a[i], &mut local_ctx) else {
                if debug {
                    eprintln!("  [split] infer(args_a[{i}]) failed");
                }
                return None;
            };
            let abstracted = kernel.abstract_fvars(replaced, &[placeholder_fv]);
            let wrap = kernel.lam(anon, arg_ty, abstracted, BinderInfo::Default);
            let fresh = self.fresh_fvar_typed(arg_ty);
            slots[i] = Some(Slot {
                fresh,
                wrap,
                original: args_a[i],
            });
        }

        // Reconstruct both sides with every differing position replaced by
        // its own fresh variable — `candidate_split` uses the fresh
        // variable directly, `expected_split` uses it through that
        // position's own wrap, so instantiating every fresh variable back
        // at its ORIGINAL value reproduces `candidate`/`expected` up to
        // defeq (checked structurally by the caller of this function via
        // the surrounding congruence machinery, and independently by the
        // final `Kernel::add_declaration`/`infer_in` re-check every
        // candidate this producer emits already goes through).
        let mut candidate_split = head_a;
        let mut expected_split = head_b;
        let mut reinstantiate_as = std::collections::BTreeMap::new();
        for (i, arg) in args_a.iter().enumerate() {
            if let Some(slot) = &slots[i] {
                let fv = kernel.fvar(slot.fresh);
                candidate_split = kernel.app(candidate_split, fv);
                let wrapped = kernel.app(slot.wrap, fv);
                expected_split = kernel.app(expected_split, wrapped);
                reinstantiate_as.insert(slot.fresh, slot.original);
            } else {
                candidate_split = kernel.app(candidate_split, *arg);
                expected_split = kernel.app(expected_split, *arg);
            }
        }

        if debug {
            eprintln!(
                "  [split] {} differing positions; split goal candidate={} expected={}",
                diff_indices.len(),
                kernel.render_lean(candidate_split),
                kernel.render_lean(expected_split)
            );
        }

        self.prove_universal_identity_with(
            kernel,
            level,
            carrier,
            candidate_split,
            expected_split,
            &reinstantiate_as,
            true,
            debug,
        )
    }

    /// `Eq.trans (hab : Eq carrier a b) (hbc : Eq carrier b c) : Eq carrier a
    /// c`, built directly from `Eq.rec` — no hand-written `Eq.trans` theorem
    /// exists in an isolated statement-import kernel either.
    #[allow(clippy::too_many_arguments, clippy::many_single_char_names)]
    fn build_eq_trans(
        &mut self,
        kernel: &mut Kernel,
        level: LevelId,
        carrier: ExprId,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        hab: ExprId,
        hbc: ExprId,
    ) -> ExprId {
        let anon = kernel.anon();
        let x_fv = self.fresh_fvar();
        let x = kernel.fvar(x_fv);
        let concl = build_eq(kernel, self.eqp_eq, level, carrier, a, x);
        let hyp_ty = build_eq(kernel, self.eqp_eq, level, carrier, b, x);
        let anon_hyp = kernel.anon();
        let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
        let motive = lam_fv(kernel, anon, x_fv, carrier, inner, BinderInfo::Default);
        let z = kernel.level_zero();
        let rec = kernel.const_(self.eqp_rec, vec![z, level]);
        let with_carrier = kernel.app(rec, carrier);
        let with_a = kernel.app(with_carrier, b);
        let with_motive = kernel.app(with_a, motive);
        let with_minor = kernel.app(with_motive, hab);
        let with_c = kernel.app(with_minor, c);
        kernel.app(with_c, hbc)
    }

    /// `Eq.symm (h : Eq carrier a b) : Eq carrier b a`, built directly from
    /// `Eq.rec`, for the same reason [`Search::build_eq_trans`] is.
    #[allow(clippy::many_single_char_names)]
    fn build_eq_symm(
        &mut self,
        kernel: &mut Kernel,
        level: LevelId,
        carrier: ExprId,
        a: ExprId,
        b: ExprId,
        h: ExprId,
    ) -> ExprId {
        let anon = kernel.anon();
        let x_fv = self.fresh_fvar();
        let x = kernel.fvar(x_fv);
        let concl = build_eq(kernel, self.eqp_eq, level, carrier, x, a);
        let hyp_ty = build_eq(kernel, self.eqp_eq, level, carrier, a, x);
        let anon_hyp = kernel.anon();
        let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
        let motive = lam_fv(kernel, anon, x_fv, carrier, inner, BinderInfo::Default);
        let refl_a = build_eq_refl(kernel, self.eqp_refl, level, carrier, a);
        let z = kernel.level_zero();
        let rec = kernel.const_(self.eqp_rec, vec![z, level]);
        let with_carrier = kernel.app(rec, carrier);
        let with_a = kernel.app(with_carrier, a);
        let with_motive = kernel.app(with_a, motive);
        let with_minor = kernel.app(with_motive, refl_a);
        let with_b = kernel.app(with_minor, b);
        kernel.app(with_b, h)
    }

    /// `congrArg f hyp : Eq goal.carrier (f hyp.lhs) (f hyp.rhs)`, built
    /// directly from the kernel's generated `Eq.rec` (never a hand-written
    /// `congrArg` theorem — none exists in an isolated statement-import
    /// kernel), so its type is checked against `goal` only when the caller
    /// declares the surrounding theorem.
    fn build_congr(
        &mut self,
        kernel: &mut Kernel,
        f: ExprId,
        hyp_proof: ExprId,
        hyp_goal: EqGoal,
        goal: EqGoal,
    ) -> ExprId {
        self.build_congr_arg(
            kernel,
            f,
            hyp_goal.level,
            hyp_goal.carrier,
            goal.level,
            goal.carrier,
            hyp_goal.lhs,
            hyp_goal.rhs,
            hyp_proof,
        )
    }

    /// `congrArg f hab : Eq out_carrier (f a) (f b)`, given `f : in_carrier ->
    /// out_carrier` and `hab : Eq in_carrier a b` — built directly from the
    /// kernel's generated `Eq.rec`, generalized out of [`Search::build_congr`]
    /// so the residual-lemma path ([`Search::try_residual_lemma`]) can build
    /// a SECOND congruence step (wrapping a narrowed auxiliary identity back
    /// up to the shape the primary rewrite needed) with the same primitive.
    #[allow(clippy::too_many_arguments, clippy::many_single_char_names)]
    fn build_congr_arg(
        &mut self,
        kernel: &mut Kernel,
        f: ExprId,
        in_level: LevelId,
        in_carrier: ExprId,
        out_level: LevelId,
        out_carrier: ExprId,
        a: ExprId,
        b: ExprId,
        hab: ExprId,
    ) -> ExprId {
        let anon = kernel.anon();
        let fa = kernel.app(f, a);
        // motive := fun (x : in_carrier) (_ : Eq in_level in_carrier a x) =>
        //             Eq out_level out_carrier fa (f x)
        let x_fv = self.fresh_fvar();
        let x = kernel.fvar(x_fv);
        let fx = kernel.app(f, x);
        let concl = build_eq(kernel, self.eqp_eq, out_level, out_carrier, fa, fx);
        let hyp_ty = build_eq(kernel, self.eqp_eq, in_level, in_carrier, a, x);
        let anon_hyp = kernel.anon();
        let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
        let motive = lam_fv(kernel, anon, x_fv, in_carrier, inner, BinderInfo::Default);
        let refl_case = build_eq_refl(kernel, self.eqp_refl, out_level, out_carrier, fa);
        let z = kernel.level_zero();
        let rec = kernel.const_(self.eqp_rec, vec![z, in_level]);
        let with_carrier = kernel.app(rec, in_carrier);
        let with_a = kernel.app(with_carrier, a);
        let with_motive = kernel.app(with_a, motive);
        let with_minor = kernel.app(with_motive, refl_case);
        let with_b = kernel.app(with_minor, b);
        kernel.app(with_b, hab)
    }

    /// Structural induction on a zero/succ-shaped binder: build
    /// `T.rec {motive} case_zero case_succ` and apply it directly to the
    /// binder's own bound value, without leaving this binder's `Pi`.
    fn try_induction(
        &mut self,
        kernel: &mut Kernel,
        shape: &NatShape,
        binder: Binder,
        eqp: &EqPrimitives,
        hypothesis: Option<Hypothesis>,
    ) -> Result<ExprId, DeclineReason> {
        let Binder {
            name: binder_name,
            ty: binder_ty,
            info: binder_info,
            body,
        } = binder;
        let anon = kernel.anon();
        let zero_e = kernel.const_(shape.zero_ctor, vec![]);
        let succ_e = kernel.const_(shape.succ_ctor, vec![]);

        // The induction target's own free variable, used only to compute
        // subgoals; the final motive/case terms are re-closed via
        // `abstract_fvars` before this function returns.
        let x_fv = self.fresh_fvar_typed(binder_ty);
        let x = kernel.fvar(x_fv);
        let prop_at_x = kernel.instantiate(body, &[x]);
        let motive = lam_fv(kernel, anon, x_fv, binder_ty, prop_at_x, binder_info);

        // Base case: prove the goal at `zero`. Recursing through `attempt`
        // (rather than assuming `body` is already a bare `Eq`) lets this
        // close goals where further binders — plain hypotheses, or another
        // zero/succ-shaped variable — follow the induction variable.
        let base_goal_expr = kernel.instantiate(body, &[zero_e]);
        if std::env::var("BIS_DEBUG").is_ok() {
            eprintln!(
                "try_induction: binder={} base_goal={}",
                kernel.display_name(binder_name),
                kernel.render_lean(base_goal_expr)
            );
        }
        let case_zero = self
            .attempt(kernel, base_goal_expr, eqp, hypothesis)
            .inspect_err(|e| {
                if std::env::var("BIS_DEBUG").is_ok() {
                    eprintln!("  base case FAILED: {e}");
                }
            })?;

        // Step case: fresh predecessor + induction hypothesis, prove the goal
        // at `succ pred`. The hypothesis carries `body` instantiated at
        // `pred` verbatim — still possibly `Pi`-headed — and is peeled in
        // lockstep with the goal by `instantiate_hypothesis` as `attempt`
        // generalizes any further binders below.
        let pred_fv = self.fresh_fvar_typed(binder_ty);
        let pred = kernel.fvar(pred_fv);
        let pred_goal_expr = kernel.instantiate(body, &[pred]);
        // Typed (unlike this same variable's role in `try_absurd_from_hypothesis`'s
        // OWN internal `ih_fv`, immediately closed by a `lam_fv` a few lines
        // below its own use and never independently `infer_in`-verified
        // first): `Search::close_order_terminal`'s new routes
        // (`Search::ascend_le`, `Search::verify_order_proof`) DO independently
        // `infer_in` a candidate that may still directly embed this raw `ih`
        // fvar, from a `LocalContext` built from `Search::fvar_types` — an
        // unregistered `ih_fv` made that check fail with "unbound free
        // variable" even when the underlying proof term was correct, turning
        // a genuine admit into a decline. The existing `Eq`-side congruence
        // route never needed this (its own final check is the OUTER,
        // fully-closed `Kernel::add_declaration`, after every fvar including
        // this one has already been abstracted back into a real binder), so
        // registering it here changes nothing about that path — an unrelated
        // extra `fvar_types` entry that nothing else looks up.
        let ih_fv = self.fresh_fvar_typed(pred_goal_expr);
        let ih = kernel.fvar(ih_fv);
        let succ_pred = kernel.app(succ_e, pred);
        let step_goal_expr = kernel.instantiate(body, &[succ_pred]);
        let step_ih = Hypothesis {
            proof: ih,
            stmt: pred_goal_expr,
        };
        if std::env::var("BIS_DEBUG").is_ok() {
            eprintln!(
                "try_induction: binder={} step_goal={} ih={}",
                kernel.display_name(binder_name),
                kernel.render_lean(step_goal_expr),
                kernel.render_lean(pred_goal_expr)
            );
        }
        let step_proof = self
            .attempt(kernel, step_goal_expr, eqp, Some(step_ih))
            .inspect_err(|e| {
                if std::env::var("BIS_DEBUG").is_ok() {
                    eprintln!("  step case FAILED: {e}");
                }
            })?;
        let step_body = lam_fv(
            kernel,
            anon,
            ih_fv,
            pred_goal_expr,
            step_proof,
            BinderInfo::Default,
        );
        let case_succ = lam_fv(
            kernel,
            anon,
            pred_fv,
            binder_ty,
            step_body,
            BinderInfo::Default,
        );

        let z = kernel.level_zero();
        let rec = kernel.const_(shape.rec_name, vec![z]);
        let with_motive = kernel.app(rec, motive);
        let with_zero = kernel.app(with_motive, case_zero);
        let with_succ = kernel.app(with_zero, case_succ);

        // Apply this partial recursor application to the CURRENT binder's own
        // value, then wrap in exactly the caller's `Pi(binder_name, ...)`
        // shape (`with_succ`/`motive`/`case_zero`/`case_succ` all sit at the
        // same scope depth as `body` itself, so closing them into the current
        // binder is the ordinary fvar/`abstract_fvars` pattern, never manual
        // de Bruijn arithmetic).
        Ok(lam_fv_apply_major(
            kernel,
            binder_name,
            x_fv,
            binder_ty,
            binder_info,
            with_succ,
        ))
    }

    /// Verify that `proof`'s INFERRED type is exactly `order.family
    /// order.param order.idx` before returning it — the same discipline
    /// [`Search::try_absurd_from_hypothesis`] and
    /// [`Search::try_case_split_from_hypothesis`] already apply to their
    /// own constructions: a malformed candidate declines here, never
    /// reaches the caller's `Kernel::add_declaration`.
    fn verify_order_proof(
        &self,
        kernel: &mut Kernel,
        proof: ExprId,
        order: &OrderGoal,
    ) -> Option<ExprId> {
        let anon = kernel.anon();
        let mut local_ctx = LocalContext::new();
        for (&fv, &ty) in &self.fvar_types {
            local_ctx.push(LocalDecl {
                fvar: fv,
                name: anon,
                ty,
                info: BinderInfo::Default,
            });
        }
        let fam_c = kernel.const_(order.family, order.levels.clone());
        let with_param = kernel.app(fam_c, order.param);
        let target = kernel.app(with_param, order.idx);
        let inferred = kernel.infer_in(proof, &mut local_ctx).ok()?;
        kernel.def_eq(inferred, target).then_some(proof)
    }

    /// Chain `family`'s own "step" constructor forward from a known proof
    /// `proof : family(order.param, current_idx)`, one `succ` at a time,
    /// until `current_idx` becomes definitionally equal to `order.idx` or
    /// [`MAX_LE_ASCENT_STEPS`] is exhausted.
    ///
    /// This is FORCED, never a search: at each step there is exactly one
    /// way to grow the proof (apply `step_ctor` once more), so failing to
    /// match after the budget is a genuine decline, not a missed
    /// alternative. Covers both a literal base-case gap (`0 < 1`, zero
    /// steps past `refl`... one step, see below) and a hypothesis whose own
    /// index already equals the goal's up to a small constant offset —
    /// never a genuinely unbounded or non-literal gap, which correctly
    /// falls through to [`Search::try_order_absorbing_argument`] instead.
    fn ascend_le(
        &mut self,
        kernel: &mut Kernel,
        order: &OrderGoal,
        mut current_idx: ExprId,
        mut proof: ExprId,
    ) -> Option<ExprId> {
        for _ in 0..=MAX_LE_ASCENT_STEPS {
            if std::env::var("BIS_DEBUG").is_ok() {
                eprintln!(
                    "  [ascend] current_idx={} target={}",
                    kernel.render_lean(current_idx),
                    kernel.render_lean(order.idx)
                );
            }
            if kernel.def_eq(current_idx, order.idx) {
                let verified = self.verify_order_proof(kernel, proof, order);
                if std::env::var("BIS_DEBUG").is_ok() {
                    eprintln!("  [ascend] MATCH, verified={}", verified.is_some());
                }
                return verified;
            }
            let step_c = kernel.const_(order.shape.step_ctor, order.levels.clone());
            let with_param = kernel.app(step_c, order.param);
            let with_idx = kernel.app(with_param, current_idx);
            proof = kernel.app(with_idx, proof);
            let succ_c = kernel.const_(order.shape.idx_shape.succ_ctor, vec![]);
            current_idx = kernel.app(succ_c, current_idx);
        }
        if kernel.def_eq(current_idx, order.idx) {
            return self.verify_order_proof(kernel, proof, order);
        }
        None
    }

    /// Close a terminal [`OrderGoal`] — `Eq`'s sibling terminal shape.
    /// Tries, in order: (1) [`Search::try_absurd_elimination`], reused
    /// UNCHANGED and passed the order goal's own raw application directly
    /// as `target` (it never inspected `target`'s shape to begin with —
    /// only ever a retained hypothesis's); (2) [`Search::ascend_le`] from
    /// `refl(param)`, covering direct reflexivity and any small literal
    /// gap; (3) [`Search::ascend_le`] from a live induction hypothesis of
    /// the SAME family at the SAME param, covering a step whose index moved
    /// by a small literal amount.
    ///
    /// Deliberately STOPS here rather than also generalizing `idx` and
    /// posing a fresh residual the way the `Eq` side's own
    /// `try_absorbing_argument` does: an order-side analogue was built and
    /// measured 2026-08-22 to restate the WHOLE ambient goal one level
    /// removed rather than a genuinely smaller side fact, and `attempt`'s
    /// own greedy (wrong-variable-first) induction choice drove it into a
    /// self-similar chain that exhausted the shared `MAX_RESIDUAL_LEMMAS`
    /// budget on a goal as simple as `∀ a b, a ≤ b + a` before ever
    /// backtracking to the choice that closes it — a real capacity cost to
    /// every OTHER caller of the same shared budget, for zero admits on
    /// this producer's actual twelve targets. Removed rather than shipped
    /// half-tuned.
    fn close_order_terminal(
        &mut self,
        kernel: &mut Kernel,
        order: &OrderGoal,
        hypothesis: Option<Hypothesis>,
        debug: bool,
    ) -> Result<ExprId, DeclineReason> {
        if debug {
            eprintln!(
                "close_order_terminal: family={} param={} idx={}",
                kernel.display_name(order.family),
                kernel.render_lean(order.param),
                kernel.render_lean(order.idx)
            );
        }
        let fam_c = kernel.const_(order.family, order.levels.clone());
        let with_param = kernel.app(fam_c, order.param);
        let raw_target = kernel.app(with_param, order.idx);
        if self.eq_available
            && let Some(proof) = self.try_absurd_elimination(kernel, raw_target)
        {
            return Ok(proof);
        }

        let refl_proof = build_le_refl(kernel, order);
        if let Some(proof) = self.ascend_le(kernel, order, order.param, refl_proof) {
            return Ok(proof);
        }

        if let Some(hyp) = hypothesis
            && let Some(hyp_order) = parse_order_goal(self, kernel, hyp.stmt)
            && hyp_order.family == order.family
            && kernel.def_eq(hyp_order.param, order.param)
            && let Some(proof) = self.ascend_le(kernel, order, hyp_order.idx, hyp.proof)
        {
            return Ok(proof);
        }

        Err(DeclineReason::TerminalNotDefEqNoRewrite)
    }

    fn attempt(
        &mut self,
        kernel: &mut Kernel,
        goal: ExprId,
        eqp: &EqPrimitives,
        hypothesis: Option<Hypothesis>,
    ) -> Result<ExprId, DeclineReason> {
        if let ExprNode::Pi(name, ty, body, info) = kernel.expr_node(goal) {
            let (name, ty, body, info) = (*name, *ty, *body, *info);
            if self.binders_left == 0 {
                return Err(DeclineReason::BinderBudgetExceeded);
            }
            self.binders_left -= 1;
            self.binders_used += 1;

            if self.inductions_left > 0 {
                let ty_whnf = kernel.whnf(ty);
                let family = match kernel.expr_node(ty_whnf) {
                    ExprNode::Const(n, _) => Some(*n),
                    _ => None,
                };
                if let Some(family) = family
                    && let Some(shape) = detect_nat_shape(kernel, family)
                {
                    self.inductions_left -= 1;
                    self.inductions_used += 1;
                    let binder = Binder {
                        name,
                        ty,
                        info,
                        body,
                    };
                    if let Ok(proof) = self.try_induction(kernel, &shape, binder, eqp, hypothesis) {
                        return Ok(proof);
                    }
                    self.inductions_left += 1;
                    self.inductions_used -= 1;
                }
            }

            // Plain generalization: introduce a fresh opaque variable and
            // keep going. A live hypothesis is peeled in lockstep — it was
            // built over the SAME remaining binder structure as `body`, so
            // one more generalization here means one more application there
            // (or the hypothesis quietly stops being usable, which is a lost
            // rewrite opportunity, never a hard failure).
            //
            // Also retained in `local_hyps` for the absurd-elimination
            // fallback ([`Search::try_absurd_elimination`]) — `ty` may be an
            // ordinary Prop-valued hypothesis (e.g. `n < k`), not just an
            // opaque generalized value, and there is no cheaper place to
            // notice that than here, where it is already in scope. Popped
            // back off after the recursive call regardless of outcome, so it
            // never leaks into a sibling branch.
            let fv = self.fresh_fvar_typed(ty);
            let x = kernel.fvar(fv);
            let sub_goal = kernel.instantiate(body, &[x]);
            let sub_hypothesis =
                hypothesis.and_then(|hyp| instantiate_hypothesis(kernel, hyp, x, ty));
            let local_hyps_mark = self.local_hyps.len();
            self.local_hyps.push((fv, ty));
            // If a hypothesis was live but could not be carried forward, and
            // that is specifically because its OWN leading `Pi` domain is
            // not the same type as this binder's (rather than it not being
            // `Pi`-headed at all), retain it unapplied in `stuck_hyps` — see
            // that field's doc for why (`Search::try_case_split_elimination`
            // is the only consumer).
            let stuck_hyps_mark = self.stuck_hyps.len();
            if sub_hypothesis.is_none()
                && let Some(hyp) = hypothesis
                && let ExprNode::Pi(_, domain_ty, _, _) = kernel.expr_node(hyp.stmt)
            {
                let domain_ty = *domain_ty;
                if !kernel.def_eq(domain_ty, ty) {
                    self.stuck_hyps.push(hyp);
                }
            }
            let sub_proof = self.attempt(kernel, sub_goal, eqp, sub_hypothesis);
            self.local_hyps.truncate(local_hyps_mark);
            self.stuck_hyps.truncate(stuck_hyps_mark);
            let sub_proof = sub_proof?;
            return Ok(lam_fv(kernel, name, fv, ty, sub_proof, info));
        }
        if self.eq_available
            && let Ok(parsed) = parse_eq_goal(kernel, eqp.eq, goal)
        {
            return self.close_terminal(kernel, parsed, hypothesis);
        }
        // Not an exact `Eq` application — try the sibling terminal shape
        // ([`OrderGoal`]) before declining. `parse_order_goal` WHNF-reduces
        // `goal` itself (unlike `parse_eq_goal`, which never unfolds
        // anything), so a `<`/`≤` surface goal still typeclass-wrapped at
        // this point is found here, not above.
        if let Some(order) = parse_order_goal(self, kernel, goal) {
            return self.close_order_terminal(
                kernel,
                &order,
                hypothesis,
                std::env::var("BIS_DEBUG").is_ok(),
            );
        }
        Err(DeclineReason::NotEqualityGoal)
    }
}

/// Attempt `Eq.refl`, and where that is stuck, a bounded structural induction
/// over a zero/succ-shaped binder plus one congruence rewrite driven by the
/// induction hypothesis. Never dispatches on the target's name or fact id;
/// every structural fact it uses (the equality primitives, the inductive
/// shape, the recursor) is discovered from `kernel`'s own declarations.
///
/// # Errors
///
/// Returns a typed [`DeclineReason`] when the bounded search does not close
/// the goal. A decline is an ordinary outcome, not a failure: this producer is
/// untrusted search, and exhausting a budget or meeting an unsupported shape
/// is exactly what it is supposed to report.
pub fn propose_bounded_induction(
    kernel: &mut Kernel,
    goal: ExprId,
) -> Result<Candidate, DeclineReason> {
    // A purely order-headed statement's minimal import closure (e.g. `n ≤
    // n.factorial`, which never mentions propositional equality anywhere in
    // its own vocabulary) legitimately never imports `Eq` at all — that is
    // NOT the same failure as `Eq` being ambiguous or malformed, so it must
    // not hard-decline here the way `discover_eq_primitives` still does for
    // those. When `Eq` is genuinely absent, `eq_available` is `false` and
    // every consumer of the `eqp_*` fields for anything beyond a
    // pass-through struct is gated on it (see `Search::eq_available`'s own
    // doc) — when `Eq` IS present, this is `discover_eq_primitives(kernel)?`
    // exactly as before, so nothing about an `Eq`-headed derivation changes.
    let (eqp, eq_available) = if declaration_absent(kernel, "Eq") {
        let anon = kernel.anon();
        (
            EqPrimitives {
                eq: anon,
                eq_refl: anon,
                eq_rec: anon,
            },
            false,
        )
    } else {
        (discover_eq_primitives(kernel)?, true)
    };
    let mut search = Search {
        eqp_eq: eqp.eq,
        eqp_refl: eqp.eq_refl,
        eqp_rec: eqp.eq_rec,
        eq_available,
        next_fvar: FVAR_BASE,
        binders_left: MAX_BINDERS,
        inductions_left: MAX_INDUCTIONS,
        binders_used: 0,
        inductions_used: 0,
        fvar_types: std::collections::BTreeMap::new(),
        residual_budget: MAX_RESIDUAL_LEMMAS,
        residual_depth: 0,
        local_hyps: Vec::new(),
        stuck_hyps: Vec::new(),
    };
    let proof = search.attempt(kernel, goal, &eqp, None)?;
    Ok(Candidate {
        proof,
        binders_used: search.binders_used,
        inductions_used: search.inductions_used,
    })
}

/// Self-contained tests for the [`OrderGoal`] terminal-closing capability
/// (`close_order_terminal` and everything it calls), built against THIS
/// project's own [`axeyum_lean_kernel::build_nat_prelude`] rather than an
/// external Mathlib export stream — no typeclass/`OfNat` indirection to
/// wade through, and portable to any host (no `/nas3` dependency), unlike
/// the census sweep this capability was actually developed against. Every
/// admitted candidate here is put through the SAME discipline
/// `nat_order_substitution`'s own tests apply: independently re-inferred,
/// re-`add_declaration`d under a fresh name, and confirmed both axiom-free
/// and citing no other theorem. Every declined candidate is confirmed to
/// decline, never merely "not asserted" — `Result::unwrap_err` panics if it
/// doesn't.
#[cfg(test)]
mod order_terminal_tests {
    use super::*;
    use axeyum_lean_kernel::{Kernel, NatPrelude, build_nat_prelude};

    fn prelude_kernel() -> (Kernel, NatPrelude) {
        let mut kernel = Kernel::new();
        let prelude = build_nat_prelude(&mut kernel).expect("nat prelude must build");
        (kernel, prelude)
    }

    /// Build `Le(a, b)` (`Nat.le a b`, the same 2-constructor inductive
    /// [`LeShape`] detects in a real Mathlib export) directly from the
    /// prelude's own `le` family name — no typeclass indirection at all,
    /// since this is the project's OWN internal representation rather than
    /// Lean surface syntax.
    fn le(kernel: &mut Kernel, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
        let c = kernel.const_(p.le, vec![]);
        let with_a = kernel.app(c, a);
        kernel.app(with_a, b)
    }

    /// Independently confirm an ADMITTED candidate the same way the real
    /// checker binary does: re-infer, re-`def_eq` against `goal`, admit
    /// under a fresh name, and require BOTH an empty axiom footprint and
    /// zero theorem dependencies (axiom-free alone does not rule out citing
    /// another already-axiom-free theorem — see `nat_order_substitution`'s
    /// own tests for why both checks are needed).
    fn assert_clean_admission(
        kernel: &mut Kernel,
        goal: ExprId,
        candidate: &Candidate,
        label: &str,
    ) {
        let inferred = kernel
            .infer(candidate.proof)
            .unwrap_or_else(|e| panic!("{label}: candidate failed to infer: {e:?}"));
        assert!(
            kernel.def_eq(inferred, goal),
            "{label}: candidate's type is not def-eq to the goal"
        );
        let fresh_name = {
            let root = kernel.anon();
            kernel.name_str(root, format!("TestOrderTerminal_{label}"))
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name: fresh_name,
                uparams: vec![],
                ty: goal,
                value: candidate.proof,
            })
            .unwrap_or_else(|e| panic!("{label}: admission failed: {e:?}"));
        assert_eq!(
            kernel.axiom_footprint(fresh_name).len(),
            0,
            "{label}: nonempty axiom footprint"
        );
        assert_eq!(
            kernel.theorem_dependencies(fresh_name).len(),
            0,
            "{label}: cites another theorem"
        );
    }

    /// `∀ n, 0 ≤ n` — the base capability this widening adds: a terminal
    /// goal headed by [`LeShape`] rather than `Eq`, closed by ordinary
    /// induction whose base case is direct reflexivity
    /// ([`Search::ascend_le`] from `refl(zero)`, zero steps) and whose step
    /// case lifts the induction hypothesis by exactly one `step_ctor`
    /// application ([`Search::ascend_le`] from the hypothesis, one step) —
    /// never touching [`Search::try_order_absorbing_argument`] at all.
    #[test]
    fn zero_le_all_admits_by_direct_induction() {
        let (mut kernel, p) = prelude_kernel();
        let nat = kernel.const_(p.nat, vec![]);
        let zero = kernel.const_(p.zero, vec![]);
        let n_fv = 1u64;
        let n = kernel.fvar(n_fv);
        let body = le(&mut kernel, &p, zero, n);
        let anon = kernel.anon();
        let abstracted = kernel.abstract_fvars(body, &[n_fv]);
        let goal = kernel.pi(anon, nat, abstracted, BinderInfo::Default);

        let candidate =
            propose_bounded_induction(&mut kernel, goal).expect("0 <= n must be provable");
        assert_clean_admission(&mut kernel, goal, &candidate, "zero_le_all");
    }

    /// `∀ n, 1 ≤ n` — FALSE at `n = 0` — the adversarial counterpart of
    /// `zero_le_all_admits_by_direct_induction`, over the EXACT same
    /// mechanism (`Le` at a literal parameter, plain induction on the
    /// index). If [`Search::ascend_le`]'s bound check
    /// (`kernel.def_eq(current_idx, order.idx)`) or its loop bound
    /// ([`MAX_LE_ASCENT_STEPS`]) were ever wrong in the permissive
    /// direction, THIS is the base case that would wrongly admit — `Le(1,
    /// 0)` is reachable from `refl(1)` by ASCENDING, which never overshoots
    /// downward, so the only way this could wrongly close is a genuine
    /// defeq-check bug, not merely an off-by-one.
    #[test]
    fn one_le_all_declines() {
        let (mut kernel, p) = prelude_kernel();
        let nat = kernel.const_(p.nat, vec![]);
        let zero = kernel.const_(p.zero, vec![]);
        let succ_c = kernel.const_(p.succ, vec![]);
        let one = kernel.app(succ_c, zero);
        let n_fv = 1u64;
        let n = kernel.fvar(n_fv);
        let body = le(&mut kernel, &p, one, n);
        let anon = kernel.anon();
        let abstracted = kernel.abstract_fvars(body, &[n_fv]);
        let goal = kernel.pi(anon, nat, abstracted, BinderInfo::Default);

        propose_bounded_induction(&mut kernel, goal)
            .expect_err("1 <= n is FALSE at n = 0 and must decline");
    }

    /// `∀ n, 0 ≤ n.succ.succ` — exercises [`Search::ascend_le`] over a
    /// MULTI-step gap in the BASE case (`0 ≤ 0.succ.succ` needs TWO
    /// `step_ctor` applications from `refl(zero)`, not the zero/one-step
    /// gaps `zero_le_all_admits_by_direct_induction` and `one_le_all_declines`
    /// already cover) while the step case still only needs the ordinary
    /// one-step hypothesis lift — together these exercise
    /// [`MAX_LE_ASCENT_STEPS`] actually being greater than one.
    #[test]
    fn ascend_two_steps_admits_zero_le_succ_succ_n() {
        let (mut kernel, p) = prelude_kernel();
        let nat = kernel.const_(p.nat, vec![]);
        let zero = kernel.const_(p.zero, vec![]);
        let succ_c1 = kernel.const_(p.succ, vec![]);
        let n_fv = 1u64;
        let n = kernel.fvar(n_fv);
        let succ_n = kernel.app(succ_c1, n);
        let succ_c2 = kernel.const_(p.succ, vec![]);
        let succ_succ_n = kernel.app(succ_c2, succ_n);
        let body = le(&mut kernel, &p, zero, succ_succ_n);
        let anon = kernel.anon();
        let abstracted = kernel.abstract_fvars(body, &[n_fv]);
        let goal = kernel.pi(anon, nat, abstracted, BinderInfo::Default);

        let candidate = propose_bounded_induction(&mut kernel, goal)
            .expect("0 <= n.succ.succ must be provable by a two-step ascent in the base case");
        assert_clean_admission(&mut kernel, goal, &candidate, "ascend_two_steps");
    }

    /// `∀ n, n.succ.succ ≤ 0` — FALSE for every `n` — the adversarial
    /// counterpart of `ascend_two_steps_admits_zero_le_succ_succ_n`, over
    /// the exact same two-`step_ctor` shape but with `param`/`idx` swapped:
    /// [`Search::ascend_le`] only ever grows the index FORWARD by `succ`,
    /// so it can never reach a SMALLER target no matter how many steps it
    /// is given — the direction in which a bound or off-by-one bug in
    /// `ascend_le` would show up as a wrong ADMIT rather than a
    /// merely-incomplete decline.
    #[test]
    fn ascend_two_steps_declines_succ_succ_n_le_zero() {
        let (mut kernel, p) = prelude_kernel();
        let nat = kernel.const_(p.nat, vec![]);
        let zero = kernel.const_(p.zero, vec![]);
        let succ_c1 = kernel.const_(p.succ, vec![]);
        let n_fv = 1u64;
        let n = kernel.fvar(n_fv);
        let succ_n = kernel.app(succ_c1, n);
        let succ_c2 = kernel.const_(p.succ, vec![]);
        let succ_succ_n = kernel.app(succ_c2, succ_n);
        let body = le(&mut kernel, &p, succ_succ_n, zero);
        let anon = kernel.anon();
        let abstracted = kernel.abstract_fvars(body, &[n_fv]);
        let goal = kernel.pi(anon, nat, abstracted, BinderInfo::Default);

        propose_bounded_induction(&mut kernel, goal)
            .expect_err("n.succ.succ <= 0 is FALSE for every n and must decline");
    }

    /// `declaration_absent` itself, confirmed both ways against a kernel
    /// that unambiguously HAS `Eq` (this project's own `build_nat_prelude`
    /// always declares it eagerly via `build_logic_prelude`, so there is no
    /// lighter-weight constructor here that leaves it out — the genuinely
    /// `Eq`-free case is exercised for real by the Mathlib census targets
    /// this capability was developed against, e.g.
    /// `F:ml430-nat-factorial-pos-f1dd2405`'s minimal import closure, whose
    /// base case `close_order_terminal` closes with `Search::eq_available
    /// == false` — not reproduced here since hand-building a `Eq`-free
    /// prelude from scratch would mean re-declaring `Nat`/`Nat.le` from
    /// raw `Declaration::Inductive`/`Declaration::Recursor` values, which
    /// is exactly the fragile duplication `build_nat_prelude` exists to
    /// avoid). This test only pins the narrower, still load-bearing claim:
    /// the helper's zero/nonzero distinction itself is exactly right,
    /// including the "ambiguous" (`> 1`) case `propose_bounded_induction`
    /// deliberately does NOT treat the same as "absent" (see
    /// `declaration_absent`'s own doc).
    #[test]
    fn declaration_absent_is_false_exactly_when_a_name_is_declared() {
        let (kernel, _p) = prelude_kernel();
        assert!(
            !declaration_absent(&kernel, "Eq"),
            "the prelude kernel declares Eq exactly once"
        );
        assert!(
            declaration_absent(&kernel, "ThisNameIsNeverDeclaredAnywhere"),
            "a name nothing declares must read as absent"
        );
    }
}
