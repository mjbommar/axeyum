//! Reconstructs `F:nat-order-lemma-census`'s twenty `Nat` order/pred/sub/ble
//! lemmas directly against a foreign (untrusted-stream) import kernel's own
//! primitives, admitting each one under the **stream's own declared type**
//! with a proof this project's own kernel constructs.
//!
//! This is a different admission shape from [`super::trusted_substitution`]'s
//! `congrArg`/`congr`/`mt`/`Eq.symm`: those are universally valid logical
//! primitives, so that module builds *both* the type and the value itself and
//! never looks at the stream's own claim. These twenty are arithmetic facts
//! about a *specific* stream-supplied `Nat.le`/`Nat.pred`/`Nat.sub`/`Nat.ble`,
//! so the type the adapter admits must be exactly the one the stream asks
//! for (`wire_ty`, still parsed unconditionally so a malformed record is
//! still rejected regardless of name) — only the *proof* is substituted.
//!
//! Soundness does not depend on the stream's `Nat.pred`/`Nat.sub`/`Nat.ble`
//! matching this project's own recursion scheme exactly: [`reconstruct`]
//! never calls [`Kernel::add_declaration`] itself. It builds a candidate
//! value from primitives discovered structurally in the foreign kernel
//! (never assumed), then validates it with [`Kernel::infer`] +
//! [`Kernel::def_eq`] against `wire_ty` *without* mutating the environment.
//! Only a candidate that independently type-checks is returned to the
//! caller, which performs the one real, authoritative admission through the
//! ordinary trusted gate. A candidate that fails this check is reported as
//! [`SubstitutionError::UnexpectedShape`] and the caller falls back to
//! admitting the stream's own (still trusted-refused) theorem exactly as an
//! ordinary import would — never a coerced or partially-checked substitute.
//!
//! Every construction below mirrors, term-for-term, an already
//! kernel-checked proof in
//! `axeyum-lean-kernel/src/nat_prelude/{order,order_extra,ble}.rs` — this
//! module does not invent new mathematics, it re-derives the same proof
//! against foreign names. **Every** helper this module leans on internally —
//! not just the twenty exported names — is re-invoked as a *Rust*
//! construction function at every use site rather than looked up by name in
//! the foreign kernel, exactly as `trusted_substitution::congr_pair` reuses
//! `build_congr_arg` without ever declaring an intermediate `congrArg`. That
//! includes three names real Mathlib/Lean corpora never export at all
//! (`Nat.le_succ_succ`, `Nat.pred_le`-as-helper, `Nat.ble_self_eq_true`-as-
//! helper; measured 0/138 for `le_succ_succ`) **and** five names that ARE
//! real, present Lean-core flat names — `Nat.le_trans`, `Nat.zero_le`,
//! `Nat.not_succ_le_zero`, `Nat.le_of_succ_le_succ`, `Nat.lt_irrefl`
//! (measured 114/138 or better).
//!
//! An earlier version of this module fetched those five by `Const` reference
//! from the untrusted stream's own environment instead of re-deriving them,
//! reasoning that doing so was sound because the fetched declaration is
//! independently kernel-checked and remains separately un-exempted in the
//! row's closure. That reasoning was correct **today** and wrong as a design:
//! it made this module's soundness depend on `trusted_substitution`'s
//! substitution list never growing to include one of those five names — a
//! fact about a different file, invisible here, and exactly the kind of
//! spooky-action-at-a-distance coupling this repository has been bitten by
//! before. `le_trans`, `zero_le`, `not_succ_le_zero`, `le_of_succ_le_succ`,
//! and `lt_irrefl` are now re-derived from primitives (plus, for the last
//! two, from each other and from `le_trans`) exactly like the three
//! never-exported helpers always were — see [`B::le_trans_at`],
//! [`B::zero_le_at`], [`B::not_succ_le_zero_at`],
//! [`B::le_of_succ_le_succ_at`], [`B::lt_irrefl_at`]. No construction in this
//! module cites a stream-supplied `Theorem` by name any more; the
//! `theorem_dependencies` assertions in this module's own tests are the
//! machine-checked form of that claim, not just this comment.
//!
//! **`Nat.le_trans` itself joined [`SUBSTITUTABLE_NAT_ORDER_THEOREMS`] on
//! 2026-08-22** — it was already reconstructed as the internal helper
//! [`B::le_trans_at`] (used by [`B::le_of_succ_le_succ_at`],
//! [`B::pred_le_pred`]'s inline construction, and [`B::sub_le_at`]) but had
//! never been exposed as a substitutable *name* in its own right, even though
//! it was the single largest first-reported blocker in the frozen census (38
//! rows). Its wire type — `∀ a b c, Le a b → Le b c → Le a c` — is exactly
//! [`B::le_trans_at`]'s own signature with the three `Nat` arguments and two
//! hypotheses re-quantified, so admitting it needed no new construction, only
//! a new match arm in [`build`] wrapping [`B::le_trans_at`] in the matching
//! telescope. `required_optional_prims` needs no new entry — `le_trans_at`
//! touches only `Nat.le`/`Nat.le.step`/`Nat.le.rec`, none of the optional
//! `pred`/`sub`/`ble` primitives, so `Nat.le_trans` falls into the existing
//! `_ => (false, false, false)` default arm.
//!
//! **`Nat.lt_irrefl` joined the same day, the same story again.** It was the
//! single largest first-reported blocker in the next census cut (38 rows,
//! measured once `le_trans` no longer shadowed it) and was already
//! reconstructed as the internal helper [`B::lt_irrefl_at`] (used by
//! [`B::not_succ_le_self`]'s own `Nat.not_succ_le_self` construction and by
//! [`build_sub_lt`]'s base cases). Its real Lean-core wire type — `∀ n, Not
//! (Nat.lt n n)`, i.e. `∀ n, Nat.lt n n → False` where `Nat.lt` is the
//! *stream's own* reducible `Definition` unfolding to `fun a b => Nat.le
//! (Nat.succ a) b` — is not literally [`B::lt_irrefl_at`]'s own conclusion
//! type (`Not (Le (succ n) n)`, stated directly over `Le`/`succ` with no
//! `Nat.lt` mention at all), so admission depends on [`Kernel::def_eq`]
//! delta-unfolding the stream's `Nat.lt` during the final validation — the
//! same reliance [`SUBSTITUTABLE_NAT_ORDER_THEOREMS`]'s existing
//! `Nat.lt_succ_self`/`Nat.lt_add_one`/`Nat.lt_succ_of_le`/`Nat.le_of_lt_succ`
//! entries already have (each of those states its conclusion or hypothesis
//! over `Le`/`succ` too and is admitted against a `Nat.lt`-headed wire type
//! the same way), so no new discovery or validation logic was needed. Only a
//! new match arm in [`build`], identical in shape to the existing
//! `"Nat.not_succ_le_self"` arm because both names wrap the exact same
//! [`B::lt_irrefl_at`] value under a fresh outer `∀ n` binder.
//! `required_optional_prims` needs no new entry for the same reason as
//! `le_trans`: `lt_irrefl_at` touches only primitives already covered by the
//! default `_ => (false, false, false)` arm (confirmed by
//! `required_optional_prims_matches_each_names_own_construction`, extended
//! below to include it in `needs_nothing`).

// Proof-term construction is long, straight-line, and mirrors mathematical
// names one-for-one — exactly the same tradeoff `nat_prelude` itself makes,
// with the same lint allowances (see that module's own `#![allow(...)]`).
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::too_many_arguments
)]

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, Kernel, LevelId, NameId};

use crate::trusted_substitution::{SubstitutionError, exact_name};

/// The complete, reviewed set of `Nat` order/pred/sub/ble theorem names this
/// module will attempt to substitute a self-derived proof for, admitted
/// under the stream's own declared type. Adding a name here is a deliberate,
/// reviewed source edit exactly like
/// [`SUBSTITUTABLE_THEOREMS`](super::trusted_substitution::SUBSTITUTABLE_THEOREMS).
///
/// **Fixed 2026-08-22, was a known limitation.** [`discover`] used to require
/// `Nat.pred`/`Nat.sub`/`Nat.ble` to already be declared *unconditionally*,
/// even for a name (e.g. `Nat.zero_le`, `Nat.succ_le_succ`) whose own
/// construction never uses them. A real stream that declares one of these
/// names *before* `Nat.pred` (Lean's own declaration order, not something
/// this module controls) made [`reconstruct`] decline with
/// `RequiredDeclarationUnavailable("Nat.pred")` for that row even though the
/// requested lemma has nothing to do with `pred`. Measured 2026-08-22 on
/// `streams/r000.ndjson`: `Nat.zero_le`, `Nat.succ_le_succ`,
/// `Nat.ble_self_eq_true`, `Nat.ble_succ_eq_true`, `Nat.ble_eq_true_of_le`,
/// `Nat.le_of_ble_eq_true`, and `Nat.not_le_of_not_ble_eq_true` all declined
/// this way in that one file.
///
/// The fix: [`Prims`] now discovers `pred`/`sub`/`ble` *optionally*
/// (`discover` never fails when one of them is absent — it simply records
/// `None`), and [`reconstruct`] checks [`required_optional_prims`] for the
/// *specific requested name* before calling [`build`], declining with the
/// precise `RequiredDeclarationUnavailable` only when the name's own
/// construction actually needs a primitive that turned out to be `None`.
/// This avoids the larger refactor the previous version of this note
/// predicted: [`build`]'s internal helpers (`induct`'s and `induct_le`'s
/// `&dyn Fn(...) -> ExprId` callbacks) never had to become fallible, because
/// by the time any of them run, [`reconstruct`] has already established that
/// every optional primitive the requested name's construction touches is
/// present — the `pred`/`sub`/`ble` accessors on [`B`] unwrap their
/// `Option<NameId>` only under that already-checked precondition.
///
/// **`Nat.lt_of_lt_of_le`/`Nat.div_rec_lemma` joined 2026-08-22**, once every
/// `Int.ModEq`/`Nat.ModEq` statement stream was measured to name
/// `Nat.div_rec_lemma` as a trusted blocker — `Nat.mod`'s well-founded
/// recursion needs it, so anything whose statement mentions `%` drags it in.
/// `Nat.lt_of_lt_of_le : ∀ a b c, Lt a b → Le b c → Lt a c` needs no new
/// construction at all: it is exactly [`B::le_trans_at`] at `(succ a, b, c)`
/// (`Lt a b` unfolds to `Le (succ a) b`), the same `def_eq`-delta-unfolds-
/// `Nat.lt` reliance the existing `lt_`-shaped entries already have, and this
/// project's own `nat_prelude::order`'s `lt_of_lt_of_le` theorem is built the
/// identical way (confirmed by reading it, not assumed). `Nat.div_rec_lemma
/// {x y} (h : 0 < y ∧ y ≤ x) : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le
/// h.1 h.2) h.1` composes three things this module already has —
/// [`build_sub_lt`], the `lt_of_lt_of_le` construction above, and the
/// stream's own `And` projected via [`B::and_left`]/[`B::and_right`]
/// (built from `And.rec`, never citing the stream's own `h.1`/`h.2` value) —
/// see [`build_div_rec_lemma`]. `required_optional_prims` needs a fourth
/// primitive, `And`, discovered *optionally* like `pred`/`sub`/`ble`
/// ([`discover_optional_and`]) since only this one name needs it.
///
/// **`Nat.div_rec_fuel_lemma` joined 2026-08-22, once every real archive
/// `int-modeq-*.ndjson` stream was measured (`statement_adapter_import`) to
/// name it as the first blocker once `Nat.div_rec_lemma` fell.** Despite the
/// "fuel"/well-founded-recursion-suggesting name, the stream's own PROOF
/// VALUE (read directly, not inferred) is a plain three-fact composition —
/// `Nat.lt_of_lt_of_le (Nat.div_rec_lemma x y ⟨hy, hle⟩) (Nat.le_of_lt_succ x
/// fuel hfuel)` — of exactly the two arms directly above it plus
/// [`build_div_rec_lemma`]'s own value, with `0 < y ∧ y ≤ x` rebuilt fresh
/// via the new [`B::and_intro`] (the mirror of the existing
/// [`B::and_left`]/[`B::and_right`] *projections*: this one *builds* a
/// conjunction instead). See [`build_div_rec_fuel_lemma`]. No new elimination
/// machinery, no well-founded recursion — genuinely no construction was
/// needed once the type was read rather than assumed from the name.
/// `required_optional_prims` maps it identically to `Nat.div_rec_lemma`
/// (`pred`, `sub`, `and`; not `ble`), since it composes exactly that value.
///
/// **`Nat.le_of_succ_le_succ` joined the same day, immediately behind
/// it** — measured as the very next first-blocker on all four
/// `int-modeq-*.ndjson` streams once `Nat.div_rec_fuel_lemma` fell. Fourth
/// instance of the by-now-established pattern (`Nat.zero_le`,
/// `Nat.le_trans`, `Nat.lt_irrefl`, `Nat.not_succ_le_zero`): the real
/// archive's own proof value (`Nat.pred_le_pred (succ n) (succ m)`, read
/// directly) is irrelevant, because [`B::le_of_succ_le_succ_at`] already
/// reconstructs `∀ n m, Le (succ n) (succ m) → Le n m` from primitives —
/// used internally since before this module's `Nat.le_of_lt_succ` entry —
/// and had simply never been exposed as a substitutable NAME in its own
/// right. One list entry, one dispatch arm, no new construction.
pub(crate) const SUBSTITUTABLE_NAT_ORDER_THEOREMS: &[&str] = &[
    "Nat.le_trans",
    "Nat.le_refl",
    "Nat.le_succ",
    "Nat.succ_le_succ",
    "Nat.le_of_lt_succ",
    "Nat.lt_succ_self",
    "Nat.lt_succ_of_le",
    "Nat.lt_add_one",
    "Nat.lt_irrefl",
    "Nat.not_succ_le_self",
    "Nat.not_succ_le_zero",
    "Nat.le_succ_of_le",
    "Nat.zero_lt_succ",
    "Nat.zero_le",
    "Nat.pred_le",
    "Nat.pred_le_pred",
    "Nat.sub_le",
    "Nat.sub_lt",
    "Nat.succ_sub_succ_eq_sub",
    "Nat.ble_self_eq_true",
    "Nat.ble_succ_eq_true",
    "Nat.ble_eq_true_of_le",
    "Nat.le_of_ble_eq_true",
    "Nat.not_le_of_not_ble_eq_true",
    "Nat.lt_of_lt_of_le",
    "Nat.div_rec_lemma",
    "Nat.div_rec_fuel_lemma",
    "Nat.le_of_succ_le_succ",
    // Measured 2026-09-05 (ADR-1662) as the fifth-largest first-reported
    // blocker of the statement-import census, 24 of 756 rows. Mathlib v4.30
    // states it with the ORDER TYPECLASSES on the surface
    // (`LT.lt Nat instLTNat n (HAdd.hAdd .. m 1) -> LE.le Nat instLENat n m`)
    // and proves it by `Nat.le_of_succ_le_succ n m` verbatim, so it shares
    // that name's construction exactly; the instances (`instLTNat`,
    // `instLENat`, `instHAdd`, `instAddNat`, `instOfNatNat`) are all
    // Definitions in the same closure, so [`reconstruct`]'s `def_eq` against
    // the stream's own `wire_ty` unfolds them and this needs no separate
    // typeclass handling. ADR-1667.
    "Nat.le_of_lt_add_one",
];

/// The primitive and directly-reusable-theorem names this module's
/// constructions are built from, discovered structurally in the foreign
/// kernel rather than assumed to exist with a particular shape.
///
/// `Clone`/`Copy` (every field is a bare [`NameId`] or `Option<NameId>`, both
/// `Copy`) so tests can take a real, `discover`-produced value and override
/// just the optional fields to exercise [`check_required_optional_prims`]
/// without having to construct a kernel that is genuinely missing a
/// primitive.
#[derive(Clone, Copy)]
struct Prims {
    nat: NameId,
    zero: NameId,
    succ: NameId,
    rec: NameId,
    le: NameId,
    le_refl: NameId,
    le_step: NameId,
    le_rec: NameId,
    /// `Nat.pred`, discovered *optionally* — `None` when it is absent from
    /// the environment at discovery time (whether because the stream never
    /// declares it or because it appears later in stream order). Only the
    /// names [`required_optional_prims`] marks as needing `pred` may call
    /// [`B::pred`]; every other name must reconstruct without it.
    pred: Option<NameId>,
    /// `Nat.sub`, discovered optionally — see [`Self::pred`].
    sub: Option<NameId>,
    /// `Nat.ble`, discovered optionally — see [`Self::pred`].
    ble: Option<NameId>,
    /// `And`/`And.rec`, discovered optionally — see [`Self::pred`]. Only
    /// `Nat.div_rec_lemma`'s hypothesis is a conjunction; every other name
    /// in [`SUBSTITUTABLE_NAT_ORDER_THEOREMS`] needs neither.
    and_: Option<AndPrims>,
    bool_: NameId,
    bool_true: NameId,
    bool_false: NameId,
    bool_rec: NameId,
    false_: NameId,
    false_rec: NameId,
    true_: NameId,
    true_intro: NameId,
    eq: NameId,
    eq_refl: NameId,
    eq_rec: NameId,
}

fn require_inductive(
    kernel: &Kernel,
    name: NameId,
    label: &'static str,
) -> Result<(), SubstitutionError> {
    match kernel.environment().get(name) {
        Some(Declaration::Inductive { .. }) => Ok(()),
        _ => Err(SubstitutionError::UnexpectedShape(label)),
    }
}

fn require_constructor(
    kernel: &Kernel,
    name: NameId,
    label: &'static str,
) -> Result<(), SubstitutionError> {
    match kernel.environment().get(name) {
        Some(Declaration::Constructor { .. }) => Ok(()),
        _ => Err(SubstitutionError::UnexpectedShape(label)),
    }
}

fn require_recursor(
    kernel: &Kernel,
    name: NameId,
    expected_uparams: usize,
    label: &'static str,
) -> Result<(), SubstitutionError> {
    match kernel.environment().get(name) {
        Some(Declaration::Recursor { uparams, .. }) if uparams.len() == expected_uparams => Ok(()),
        _ => Err(SubstitutionError::UnexpectedShape(label)),
    }
}

/// Look up `rendered` and return it only when it exists under that exact
/// display name (unambiguously) **and** is a `Definition` — otherwise `None`,
/// never an error. This is the discovery primitive for `Nat.pred`/`Nat.sub`/
/// `Nat.ble`: those three are needed by only some of
/// [`SUBSTITUTABLE_NAT_ORDER_THEOREMS`]' constructions, so their absence must
/// not fail [`discover`] itself — [`reconstruct`] decides, per requested
/// name, whether a `None` here is actually fatal (see
/// [`required_optional_prims`]).
fn discover_optional_definition(kernel: &Kernel, rendered: &'static str) -> Option<NameId> {
    let name = exact_name(kernel, rendered).ok()?;
    match kernel.environment().get(name) {
        Some(Declaration::Definition { .. }) => Some(name),
        _ => None,
    }
}

/// The `And`/`And.rec` primitives [`B::and_left`]/[`B::and_right`] depend on
/// — discovered *optionally*, mirroring [`discover_optional_definition`]'s
/// own contract for `Nat.pred`/`Nat.sub`/`Nat.ble`: `None` when `And` is
/// absent or not the expected shape, never an error, because only
/// `Nat.div_rec_lemma`'s hypothesis is a conjunction. `And (a b : Prop) :
/// Prop` is a 2-param, 0-index, 1-constructor `Inductive` (its constructor
/// `And.intro` is checked structurally too, exactly like
/// [`discover_or`]'s own `Or.inl`/`Or.inr`); `And.rec` gets a ONE-universe-
/// param recursor (not two, unlike `Eq.rec`) because both of `And.intro`'s
/// own fields are already `Prop`-sorted — the same shape this project's own
/// `axeyum-lean-kernel::prelude::and_left`/`and_right` construction relies
/// on (confirmed there: `And.rec`'s only level argument is the elimination
/// universe, `zero`).
#[derive(Clone, Copy)]
#[allow(clippy::struct_field_names)]
struct AndPrims {
    and_: NameId,
    and_rec: NameId,
    /// `And.intro`, discovered and structurally checked (see
    /// [`discover_optional_and`]) but not stored until
    /// [`Nat.div_rec_fuel_lemma`](build_div_rec_fuel_lemma) needed to build a
    /// fresh conjunction from its own two separately-bound hypotheses rather
    /// than only ever project an ALREADY-CONSTRUCTED one via
    /// [`B::and_left`]/[`B::and_right`].
    and_intro: NameId,
}

fn discover_optional_and(kernel: &Kernel) -> Option<AndPrims> {
    let and_ = exact_name(kernel, "And").ok()?;
    match kernel.environment().get(and_) {
        Some(Declaration::Inductive {
            num_params,
            num_indices,
            ctor_names,
            ..
        }) if *num_params == 2 && *num_indices == 0 && ctor_names.len() == 1 => {}
        _ => return None,
    }
    let and_intro = exact_name(kernel, "And.intro").ok()?;
    if !matches!(
        kernel.environment().get(and_intro),
        Some(Declaration::Constructor { .. })
    ) {
        return None;
    }
    let and_rec = exact_name(kernel, "And.rec").ok()?;
    match kernel.environment().get(and_rec) {
        Some(Declaration::Recursor { uparams, .. }) if uparams.len() == 1 => {}
        _ => return None,
    }
    Some(AndPrims {
        and_,
        and_rec,
        and_intro,
    })
}

/// Which of the optional [`Prims::pred`]/[`Prims::sub`]/[`Prims::ble`]/
/// [`Prims::and_`] primitives a given [`SUBSTITUTABLE_NAT_ORDER_THEOREMS`]
/// name's own construction actually reads, cross-checked against [`build`]
/// by hand for every name in that list. Names not listed here need none of
/// the four. This is the lazy-discovery fix itself: [`reconstruct`] calls
/// this *before* [`build`], so a real stream that has not yet declared
/// `Nat.pred` at the point it declares (say) `Nat.zero_le` no longer blocks
/// `Nat.zero_le`'s reconstruction on a primitive it never touches.
fn required_optional_prims(rendered: &str) -> (bool, bool, bool, bool) {
    // (needs_pred, needs_sub, needs_ble, needs_and)
    match rendered {
        "Nat.pred_le" | "Nat.pred_le_pred" => (true, false, false, false),
        "Nat.sub_le" | "Nat.sub_lt" | "Nat.succ_sub_succ_eq_sub" => (true, true, false, false),
        "Nat.ble_self_eq_true"
        | "Nat.ble_succ_eq_true"
        | "Nat.ble_eq_true_of_le"
        | "Nat.le_of_ble_eq_true"
        | "Nat.not_le_of_not_ble_eq_true" => (false, false, true, false),
        // `Nat.div_rec_lemma` reduces to `Nat.sub_lt` internally (see
        // `build_div_rec_lemma`), so it needs everything `Nat.sub_lt` needs
        // PLUS `And`/`And.rec` to project its own conjunction hypothesis.
        // `Nat.div_rec_fuel_lemma` composes `build_div_rec_lemma` (for its
        // own `x - y < x` piece) with `Nat.lt_of_lt_of_le`/
        // `Nat.le_of_lt_succ`'s existing constructions (neither of which
        // touches any of the four), so it needs exactly what
        // `Nat.div_rec_lemma` needs — nothing more.
        "Nat.div_rec_lemma" | "Nat.div_rec_fuel_lemma" => (true, true, false, true),
        _ => (false, false, false, false),
    }
}

/// The gate itself, factored out of [`reconstruct`] so it can be unit-tested
/// directly against a [`Prims`] value whose optional fields were overridden
/// to `None` — without needing a kernel that is genuinely missing a
/// primitive. Mutation target: deleting any one of the three `if` arms below
/// must make exactly the test that exercises that primitive's absence fail.
fn check_required_optional_prims(prims: &Prims, rendered: &str) -> Result<(), SubstitutionError> {
    let (needs_pred, needs_sub, needs_ble, needs_and) = required_optional_prims(rendered);
    if needs_pred && prims.pred.is_none() {
        return Err(SubstitutionError::RequiredDeclarationUnavailable(
            "Nat.pred",
        ));
    }
    if needs_sub && prims.sub.is_none() {
        return Err(SubstitutionError::RequiredDeclarationUnavailable("Nat.sub"));
    }
    if needs_ble && prims.ble.is_none() {
        return Err(SubstitutionError::RequiredDeclarationUnavailable("Nat.ble"));
    }
    if needs_and && prims.and_.is_none() {
        return Err(SubstitutionError::RequiredDeclarationUnavailable("And"));
    }
    Ok(())
}

fn discover(kernel: &Kernel) -> Result<Prims, SubstitutionError> {
    let nat = exact_name(kernel, "Nat")?;
    require_inductive(kernel, nat, "Nat is not an Inductive")?;
    let zero = exact_name(kernel, "Nat.zero")?;
    require_constructor(kernel, zero, "Nat.zero is not a Constructor")?;
    let succ = exact_name(kernel, "Nat.succ")?;
    require_constructor(kernel, succ, "Nat.succ is not a Constructor")?;
    let rec = exact_name(kernel, "Nat.rec")?;
    require_recursor(kernel, rec, 1, "Nat.rec is not a 1-uparam Recursor")?;

    let le = exact_name(kernel, "Nat.le")?;
    require_inductive(kernel, le, "Nat.le is not an Inductive")?;
    let le_refl = exact_name(kernel, "Nat.le.refl")?;
    require_constructor(kernel, le_refl, "Nat.le.refl is not a Constructor")?;
    let le_step = exact_name(kernel, "Nat.le.step")?;
    require_constructor(kernel, le_step, "Nat.le.step is not a Constructor")?;
    let le_rec = exact_name(kernel, "Nat.le.rec")?;
    require_recursor(kernel, le_rec, 0, "Nat.le.rec is not a 0-uparam Recursor")?;

    let pred = discover_optional_definition(kernel, "Nat.pred");
    let sub = discover_optional_definition(kernel, "Nat.sub");
    let ble = discover_optional_definition(kernel, "Nat.ble");
    let and_ = discover_optional_and(kernel);

    let bool_ = exact_name(kernel, "Bool")?;
    require_inductive(kernel, bool_, "Bool is not an Inductive")?;
    let bool_true = exact_name(kernel, "Bool.true")?;
    require_constructor(kernel, bool_true, "Bool.true is not a Constructor")?;
    let bool_false = exact_name(kernel, "Bool.false")?;
    require_constructor(kernel, bool_false, "Bool.false is not a Constructor")?;
    let bool_rec = exact_name(kernel, "Bool.rec")?;
    require_recursor(kernel, bool_rec, 1, "Bool.rec is not a 1-uparam Recursor")?;

    let false_ = exact_name(kernel, "False")?;
    require_inductive(kernel, false_, "False is not an Inductive")?;
    let false_rec = exact_name(kernel, "False.rec")?;
    require_recursor(kernel, false_rec, 1, "False.rec is not a 1-uparam Recursor")?;
    let true_ = exact_name(kernel, "True")?;
    require_inductive(kernel, true_, "True is not an Inductive")?;
    let true_intro = exact_name(kernel, "True.intro")?;
    require_constructor(kernel, true_intro, "True.intro is not a Constructor")?;

    let eq = exact_name(kernel, "Eq")?;
    require_inductive(kernel, eq, "Eq is not an Inductive")?;
    let eq_refl = exact_name(kernel, "Eq.refl")?;
    require_constructor(kernel, eq_refl, "Eq.refl is not a Constructor")?;
    let eq_rec = exact_name(kernel, "Eq.rec")?;
    require_recursor(kernel, eq_rec, 2, "Eq.rec is not a 2-uparam Recursor")?;

    Ok(Prims {
        nat,
        zero,
        succ,
        rec,
        le,
        le_refl,
        le_step,
        le_rec,
        pred,
        sub,
        ble,
        and_,
        bool_,
        bool_true,
        bool_false,
        bool_rec,
        false_,
        false_rec,
        true_,
        true_intro,
        eq,
        eq_refl,
        eq_rec,
    })
}

// --- term builders (mirroring nat_prelude::ops::NatOps, generalized to
// discovered foreign names instead of a `NatPrelude`) -----------------------

struct B<'a> {
    kernel: &'a mut Kernel,
    p: &'a Prims,
    next_fvar: u64,
}

const FVAR_BASE: u64 = 950_000_000;

impl<'a> B<'a> {
    fn new(kernel: &'a mut Kernel, p: &'a Prims) -> Self {
        Self {
            kernel,
            p,
            next_fvar: FVAR_BASE,
        }
    }

    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    fn anon(&mut self) -> NameId {
        self.kernel.anon()
    }

    fn level_zero(&mut self) -> LevelId {
        self.kernel.level_zero()
    }

    fn level_one(&mut self) -> LevelId {
        let z = self.kernel.level_zero();
        self.kernel.level_succ(z)
    }

    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = head;
        for &a in args {
            e = self.kernel.app(e, a);
        }
        e
    }

    fn const_app(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        let c = self.kernel.const_(name, vec![]);
        self.apply(c, args)
    }

    fn lam_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.kernel.abstract_fvars(body, &[fv]);
        let anon = self.anon();
        self.kernel.lam(anon, ty, b, BinderInfo::Default)
    }

    fn pi_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.kernel.abstract_fvars(body, &[fv]);
        let anon = self.anon();
        self.kernel.pi(anon, ty, b, BinderInfo::Default)
    }

    fn arrow(&mut self, dom: ExprId, cod: ExprId) -> ExprId {
        let anon = self.anon();
        self.kernel.pi(anon, dom, cod, BinderInfo::Default)
    }

    fn nat_ty(&mut self) -> ExprId {
        self.kernel.const_(self.p.nat, vec![])
    }

    fn bool_ty(&mut self) -> ExprId {
        self.kernel.const_(self.p.bool_, vec![])
    }

    fn zero(&mut self) -> ExprId {
        self.kernel.const_(self.p.zero, vec![])
    }

    fn succ(&mut self, x: ExprId) -> ExprId {
        let name = self.p.succ;
        self.const_app(name, &[x])
    }

    fn bool_true(&mut self) -> ExprId {
        self.kernel.const_(self.p.bool_true, vec![])
    }

    fn bool_false(&mut self) -> ExprId {
        self.kernel.const_(self.p.bool_false, vec![])
    }

    /// Panics if `Nat.pred` was not discovered. Safe to call only for a
    /// `rendered` name [`required_optional_prims`] marks as needing `pred` —
    /// [`reconstruct`] checks that before ever calling [`build`].
    fn pred(&mut self, x: ExprId) -> ExprId {
        let name = self
            .p
            .pred
            .expect("required_optional_prims must gate any call reaching B::pred");
        self.const_app(name, &[x])
    }

    /// Panics if `Nat.sub` was not discovered — see [`Self::pred`].
    fn sub(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let name = self
            .p
            .sub
            .expect("required_optional_prims must gate any call reaching B::sub");
        self.const_app(name, &[x, y])
    }

    /// Panics if `Nat.ble` was not discovered — see [`Self::pred`].
    fn ble(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let name = self
            .p
            .ble
            .expect("required_optional_prims must gate any call reaching B::ble");
        self.const_app(name, &[x, y])
    }

    /// `And.left`-equivalent: from `h : And a b`, extract a proof of `a` via
    /// `And.rec` with the constant motive `fun _ => a` and single minor
    /// premise `fun ha _ => ha` — this project's own
    /// `axeyum-lean-kernel::prelude::and_left` construction, reconstructed
    /// against these discovered, foreign names rather than cited by name.
    /// Panics if `And` was not discovered — see [`Self::pred`].
    fn and_left(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let andp_rec = self
            .p
            .and_
            .as_ref()
            .expect("required_optional_prims must gate any call reaching B::and_left")
            .and_rec;
        let and_ab = self.and_app(a, b);
        let pair_fv = self.fresh();
        let motive = self.lam_fv(pair_fv, and_ab, a);
        let minor = {
            let ha_fv = self.fresh();
            let ha = self.kernel.fvar(ha_fv);
            let hb_fv = self.fresh();
            let inner = self.lam_fv(hb_fv, b, ha);
            self.lam_fv(ha_fv, a, inner)
        };
        let zero = self.level_zero();
        let rec = self.kernel.const_(andp_rec, vec![zero]);
        self.apply(rec, &[a, b, motive, minor, h])
    }

    /// `And.right`-equivalent — [`Self::and_left`]'s mirror, motive `fun _
    /// => b`, minor premise `fun _ hb => hb`.
    fn and_right(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let andp_rec = self
            .p
            .and_
            .as_ref()
            .expect("required_optional_prims must gate any call reaching B::and_right")
            .and_rec;
        let and_ab = self.and_app(a, b);
        let pair_fv = self.fresh();
        let motive = self.lam_fv(pair_fv, and_ab, b);
        let minor = {
            let ha_fv = self.fresh();
            let hb_fv = self.fresh();
            let hb = self.kernel.fvar(hb_fv);
            let inner = self.lam_fv(hb_fv, b, hb);
            self.lam_fv(ha_fv, a, inner)
        };
        let zero = self.level_zero();
        let rec = self.kernel.const_(andp_rec, vec![zero]);
        self.apply(rec, &[a, b, motive, minor, h])
    }

    /// `And a b`, from the discovered `And` name — factored out because both
    /// [`Self::and_left`] and [`Self::and_right`] need it.
    fn and_app(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let and_name = self
            .p
            .and_
            .as_ref()
            .expect("required_optional_prims must gate any call reaching B::and_app")
            .and_;
        self.const_app(and_name, &[a, b])
    }

    /// `And.intro ha hb : And a b`, from the discovered `And.intro`
    /// constructor — the mirror of [`Self::and_left`]/[`Self::and_right`]'s
    /// *projection*: this one *builds* a fresh conjunction from its own two
    /// separately-bound hypotheses, which
    /// [`build_div_rec_fuel_lemma`] needs to re-form the `0 < y ∧ y ≤ x`
    /// hypothesis [`build_div_rec_lemma`]'s own value expects, rather than
    /// projecting one out of an already-conjoined `h`. Panics if `And` was
    /// not discovered — see [`Self::pred`].
    fn and_intro(&mut self, a: ExprId, b: ExprId, ha: ExprId, hb: ExprId) -> ExprId {
        let and_intro = self
            .p
            .and_
            .as_ref()
            .expect("required_optional_prims must gate any call reaching B::and_intro")
            .and_intro;
        self.const_app(and_intro, &[a, b, ha, hb])
    }

    fn le(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let name = self.p.le;
        self.const_app(name, &[x, y])
    }

    fn le_refl_ctor(&mut self, x: ExprId) -> ExprId {
        let name = self.p.le_refl;
        self.const_app(name, &[x])
    }

    fn le_step_ctor(&mut self, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
        let name = self.p.le_step;
        self.const_app(name, &[x, y, h])
    }

    fn eq_at(&mut self, level: LevelId, ty: ExprId, x: ExprId, y: ExprId) -> ExprId {
        let name = self.p.eq;
        let eq = self.kernel.const_(name, vec![level]);
        self.apply(eq, &[ty, x, y])
    }

    fn eq_nat(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let one = self.level_one();
        let nat = self.nat_ty();
        self.eq_at(one, nat, x, y)
    }

    fn eq_bool(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let one = self.level_one();
        let bt = self.bool_ty();
        self.eq_at(one, bt, x, y)
    }

    fn refl_at(&mut self, level: LevelId, ty: ExprId, a: ExprId) -> ExprId {
        let name = self.p.eq_refl;
        let refl = self.kernel.const_(name, vec![level]);
        self.apply(refl, &[ty, a])
    }

    fn refl_nat(&mut self, a: ExprId) -> ExprId {
        let one = self.level_one();
        let nat = self.nat_ty();
        self.refl_at(one, nat, a)
    }

    fn refl_bool(&mut self, a: ExprId) -> ExprId {
        let one = self.level_one();
        let bt = self.bool_ty();
        self.refl_at(one, bt, a)
    }

    fn transport_at(
        &mut self,
        level: LevelId,
        ty: ExprId,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let zero = self.level_zero();
        let name = self.p.eq_rec;
        let rec = self.kernel.const_(name, vec![zero, level]);
        self.apply(rec, &[ty, p, motive, refl_case, q, h])
    }

    /// `fun (x : Nat) (_ : Eq Nat a x) => body(x)`.
    fn eq_motive_nat(&mut self, a: ExprId, body: &dyn Fn(&mut Self, ExprId) -> ExprId) -> ExprId {
        let x_fv = self.fresh();
        let x = self.kernel.fvar(x_fv);
        let concl = body(self, x);
        let hyp = self.eq_nat(a, x);
        let anon = self.anon();
        let inner = self.kernel.lam(anon, hyp, concl, BinderInfo::Default);
        let nat = self.nat_ty();
        self.lam_fv(x_fv, nat, inner)
    }

    fn symm_nat(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let motive = self.eq_motive_nat(a, &|d, x| d.eq_nat(x, a));
        let refl_case = self.refl_nat(a);
        let one = self.level_one();
        let nat = self.nat_ty();
        self.transport_at(one, nat, a, motive, refl_case, b, h)
    }

    /// `h : Eq Nat a b  ⊢  Eq Nat (f a) (f b)`.
    fn congr_nat(
        &mut self,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        f: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let fa = f(self, a);
        let motive = self.eq_motive_nat(a, &|d, x| {
            let fx = f(d, x);
            d.eq_nat(fa, fx)
        });
        let refl_case = self.refl_nat(fa);
        let one = self.level_one();
        let nat = self.nat_ty();
        self.transport_at(one, nat, a, motive, refl_case, b, h)
    }

    /// `Nat.rec.{0} (fun x => p x) base (fun j ih => step j ih) target`.
    fn induct(
        &mut self,
        p: &dyn Fn(&mut Self, ExprId) -> ExprId,
        base: &dyn Fn(&mut Self) -> ExprId,
        step: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
        target: ExprId,
    ) -> ExprId {
        let nat = self.nat_ty();
        let motive = {
            let x_fv = self.fresh();
            let x = self.kernel.fvar(x_fv);
            let body = p(self, x);
            self.lam_fv(x_fv, nat, body)
        };
        let base_term = base(self);
        let step_term = {
            let j_fv = self.fresh();
            let j = self.kernel.fvar(j_fv);
            let ih_fv = self.fresh();
            let ih = self.kernel.fvar(ih_fv);
            let hyp_ty = p(self, j);
            let body = step(self, j, ih);
            let inner = self.lam_fv(ih_fv, hyp_ty, body);
            self.lam_fv(j_fv, nat, inner)
        };
        let z = self.level_zero();
        let name = self.p.rec;
        let rec = self.kernel.const_(name, vec![z]);
        self.apply(rec, &[motive, base_term, step_term, target])
    }

    /// `Nat.le.rec` elimination on `h : Le base x` at a fixed `base`, with
    /// motive `fun (x : Nat) (_ : Le base x) => p x`.
    #[allow(clippy::too_many_arguments)]
    fn induct_le(
        &mut self,
        base: ExprId,
        p: &dyn Fn(&mut Self, ExprId) -> ExprId,
        minor_refl: &dyn Fn(&mut Self) -> ExprId,
        minor_step: &dyn Fn(&mut Self, ExprId, u64, ExprId) -> ExprId,
        target: ExprId,
        h: ExprId,
    ) -> ExprId {
        let nat = self.nat_ty();
        let anon = self.anon();
        let motive = {
            let x_fv = self.fresh();
            let x = self.kernel.fvar(x_fv);
            let dom = self.le(base, x);
            let body = p(self, x);
            let inner = self.kernel.lam(anon, dom, body, BinderInfo::Default);
            self.lam_fv(x_fv, nat, inner)
        };
        let refl_term = minor_refl(self);
        let step_term = {
            let x_fv = self.fresh();
            let x = self.kernel.fvar(x_fv);
            let hx_fv = self.fresh();
            let hx_ty = self.le(base, x);
            let ih_fv = self.fresh();
            let ih = self.kernel.fvar(ih_fv);
            // `ih`'s type is `p x` (the motive at `x`), computed before the
            // call below so this never needs a second mutable borrow of
            // `self` while one is already active for `lam_fv`.
            let ih_ty = p(self, x);
            let body = minor_step(self, x, hx_fv, ih);
            let l_ih = self.lam_fv(ih_fv, ih_ty, body);
            let l_hx = self.lam_fv(hx_fv, hx_ty, l_ih);
            self.lam_fv(x_fv, nat, l_hx)
        };
        let name = self.p.le_rec;
        self.const_app(name, &[base, motive, refl_term, step_term, target, h])
    }

    /// `Le (succ n) (succ m)` from `h : Le n m`, via `Nat.le.rec` at base `n`
    /// — this project's own `Nat.le_succ_succ`, re-derived inline at every
    /// use site rather than declared under a name no real corpus exports.
    fn le_succ_succ_term(&mut self, n: ExprId, m: ExprId, h: ExprId) -> ExprId {
        let sn = self.succ(n);
        self.induct_le(
            n,
            &|d, x| {
                let sx = d.succ(x);
                d.le(sn, sx)
            },
            &|d| {
                let sn = d.succ(n);
                d.le_refl_ctor(sn)
            },
            &|d, x, _hx_fv, ih| {
                let sx = d.succ(x);
                let sn = d.succ(n);
                d.le_step_ctor(sn, sx, ih)
            },
            m,
            h,
        )
    }

    /// `Le a c` from `h1 : Le a b`, `h2 : Le b c` — this project's own
    /// `Nat.le_trans`, via `Nat.le.rec` elimination on `h2` at base `b`.
    /// Primitives only (`Nat.le.step` and `Nat.le.rec`), never a citation of
    /// the stream's own `Nat.le_trans`.
    fn le_trans_at(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        self.induct_le(
            b,
            &|d, x| d.le(a, x),
            &|_d| h1,
            &|d, x, _hx_fv, ih| d.le_step_ctor(a, x, ih),
            c,
            h2,
        )
    }

    /// `fun n => Le zero n`'s proof, this project's own `Nat.zero_le`.
    /// Primitives only.
    fn zero_le_value(&mut self) -> ExprId {
        let n_fv = self.fresh();
        let n = self.kernel.fvar(n_fv);
        let body = self.induct(
            &|d, x| {
                let z = d.zero();
                d.le(z, x)
            },
            &|d| {
                let z = d.zero();
                d.le_refl_ctor(z)
            },
            &|d, j, ih| {
                let z = d.zero();
                d.le_step_ctor(z, j, ih)
            },
            n,
        );
        let nat = self.nat_ty();
        self.lam_fv(n_fv, nat, body)
    }

    fn zero_le_at(&mut self, n: ExprId) -> ExprId {
        let f = self.zero_le_value();
        self.apply(f, &[n])
    }

    /// `Not (Le (succ n) zero)`, this project's own `Nat.not_succ_le_zero`
    /// — eliminate a hypothetical derivation into a family that is `False`
    /// only at index zero and `True` at every successor index. Primitives
    /// only (`Nat.rec` into `Prop`, `True`/`False`, `Nat.le.rec`).
    fn not_succ_le_zero_at(&mut self, n: ExprId) -> ExprId {
        let sn = self.succ(n);
        let zero = self.zero();
        let hyp_ty = self.le(sn, zero);
        let false_ty = self.kernel.const_(self.p.false_, vec![]);
        let true_ty = self.kernel.const_(self.p.true_, vec![]);
        let nat = self.nat_ty();
        let prop = self.kernel.sort_zero();
        let anon = self.anon();

        let family = |d: &mut Self, x: ExprId| -> ExprId {
            let motive = d.kernel.lam(anon, nat, prop, BinderInfo::Default);
            let step = {
                let j_fv = d.fresh();
                let ih_fv = d.fresh();
                let with_ih = d.lam_fv(ih_fv, prop, true_ty);
                d.lam_fv(j_fv, nat, with_ih)
            };
            let one = d.level_one();
            let rec = d.kernel.const_(d.p.rec, vec![one]);
            d.apply(rec, &[motive, false_ty, step, x])
        };

        let h_fv = self.fresh();
        let h = self.kernel.fvar(h_fv);
        let motive = {
            let x_fv = self.fresh();
            let x = self.kernel.fvar(x_fv);
            let dom = self.le(sn, x);
            let body = family(self, x);
            let inner = self.kernel.lam(anon, dom, body, BinderInfo::Default);
            self.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = self.kernel.const_(self.p.true_intro, vec![]);
        let minor_step = {
            let x_fv = self.fresh();
            let x = self.kernel.fvar(x_fv);
            let hx_fv = self.fresh();
            let hx_ty = self.le(sn, x);
            let ih_fv = self.fresh();
            let ih_ty = family(self, x);
            let body = self.kernel.const_(self.p.true_intro, vec![]);
            let with_ih = self.lam_fv(ih_fv, ih_ty, body);
            let with_hx = self.lam_fv(hx_fv, hx_ty, with_ih);
            self.lam_fv(x_fv, nat, with_hx)
        };
        let le_rec = self.p.le_rec;
        let body = self.const_app(le_rec, &[sn, motive, minor_refl, minor_step, zero, h]);
        self.lam_fv(h_fv, hyp_ty, body)
    }

    /// `Le n m` from `h : Le (succ n) (succ m)` — this project's own
    /// `Nat.le_of_succ_le_succ`. Eliminates the derivation with the
    /// predecessor-style family `P 0 = False`, `P (succ x) = Le n x`, via
    /// `Nat.le.rec`; the step case discards its own induction hypothesis and
    /// instead uses [`Self::le_trans_at`] with `Le n (succ n)`. Primitives
    /// plus `le_trans_at`, never a citation of the stream's own
    /// `Nat.le_of_succ_le_succ`.
    fn le_of_succ_le_succ_at(&mut self, n: ExprId, m: ExprId, h: ExprId) -> ExprId {
        let sn = self.succ(n);
        let sm = self.succ(m);
        let false_ty = self.kernel.const_(self.p.false_, vec![]);
        let nat = self.nat_ty();
        let anon = self.anon();
        let prop = self.kernel.sort_zero();

        let predecessor_family = |d: &mut Self, x: ExprId| -> ExprId {
            let motive = d.kernel.lam(anon, nat, prop, BinderInfo::Default);
            let step = {
                let j_fv = d.fresh();
                let j = d.kernel.fvar(j_fv);
                let ignored_fv = d.fresh();
                let body = d.le(n, j);
                let inner = d.lam_fv(ignored_fv, prop, body);
                d.lam_fv(j_fv, nat, inner)
            };
            let one = d.level_one();
            let rec = d.kernel.const_(d.p.rec, vec![one]);
            d.apply(rec, &[motive, false_ty, step, x])
        };

        self.induct_le(
            sn,
            &predecessor_family,
            &|d| d.le_refl_ctor(n),
            &|d, x, hx_fv, _ih| {
                // Deliberately `hx` (`Le sn x`, the *current* step's own
                // hypothesis), never the recursive `ih` (`predecessor_family
                // x`, which does not reduce for a symbolic `x` and is not
                // needed): `Le n sn` composed with `Le sn x` by transitivity
                // gives `Le n x` directly, matching what
                // `predecessor_family (succ x)` ι-reduces to. One step of
                // unfolding, not real recursion.
                let hx = d.kernel.fvar(hx_fv);
                let n_refl = d.le_refl_ctor(n);
                let n_le_sn = d.le_step_ctor(n, n, n_refl);
                d.le_trans_at(n, sn, x, n_le_sn, hx)
            },
            sm,
            h,
        )
    }

    /// `Not (Lt n n)` (i.e. `Le (succ n) n → False`), this project's own
    /// `Nat.lt_irrefl`. Induction on `n`: the base case reduces `Lt 0 0` to
    /// [`Self::not_succ_le_zero_at`]; the step case reduces `Lt (succ x)
    /// (succ x)` to `Lt x x` via [`Self::le_of_succ_le_succ_at`] and applies
    /// the outer induction hypothesis. Primitives plus those two, never a
    /// citation of the stream's own `Nat.lt_irrefl`.
    fn lt_irrefl_at(&mut self, n: ExprId) -> ExprId {
        let false_ty = self.kernel.const_(self.p.false_, vec![]);
        self.induct(
            &|d, x| {
                let sx = d.succ(x);
                let strict = d.le(sx, x);
                d.arrow(strict, false_ty)
            },
            &|d| {
                let zero = d.zero();
                let szero = d.succ(zero);
                let strict = d.le(szero, zero);
                let h_fv = d.fresh();
                let h = d.kernel.fvar(h_fv);
                let discharge = d.not_succ_le_zero_at(zero);
                let applied = d.apply(discharge, &[h]);
                d.lam_fv(h_fv, strict, applied)
            },
            &|d, x, ih| {
                let sx = d.succ(x);
                let ssx = d.succ(sx);
                let strict = d.le(ssx, sx);
                let h_fv = d.fresh();
                let h = d.kernel.fvar(h_fv);
                let reduced = d.le_of_succ_le_succ_at(sx, x, h);
                let body = d.apply(ih, &[reduced]);
                d.lam_fv(h_fv, strict, body)
            },
            n,
        )
    }

    /// `Le (pred n) n`, this project's own `Nat.pred_le`.
    fn pred_le_value(&mut self) -> ExprId {
        let n_fv = self.fresh();
        let n = self.kernel.fvar(n_fv);
        let body = self.induct(
            &|d, x| {
                let px = d.pred(x);
                d.le(px, x)
            },
            &|d| {
                let z = d.zero();
                d.le_refl_ctor(z)
            },
            &|d, j, _ih| {
                let refl_j = d.le_refl_ctor(j);
                d.le_step_ctor(j, j, refl_j)
            },
            n,
        );
        let nat = self.nat_ty();
        self.lam_fv(n_fv, nat, body)
    }

    fn pred_le_at(&mut self, x: ExprId) -> ExprId {
        let f = self.pred_le_value();
        self.apply(f, &[x])
    }

    /// `Eq Nat (sub (succ n) (succ m)) (sub n m)`, this project's own
    /// `Nat.succ_sub_succ_eq_sub` (also one of the 20 target theorems, so
    /// this doubles as its own value builder).
    fn succ_sub_succ_eq_sub_body(&mut self, n: ExprId, m: ExprId) -> ExprId {
        self.induct(
            &|d, x| {
                let sn = d.succ(n);
                let sx = d.succ(x);
                let lhs = d.sub(sn, sx);
                let rhs = d.sub(n, x);
                d.eq_nat(lhs, rhs)
            },
            &|d| d.refl_nat(n),
            &|d, j, ih| {
                let sn = d.succ(n);
                let sj = d.succ(j);
                let lhs = d.sub(sn, sj);
                let rhs = d.sub(n, j);
                d.congr_nat(lhs, rhs, ih, &|d, x| d.pred(x))
            },
            m,
        )
    }

    /// `Eq Bool (ble n n) Bool.true`, this project's own `Nat.ble_self_eq_true`.
    fn ble_self_eq_true_at(&mut self, n: ExprId) -> ExprId {
        self.induct(
            &|d, x| {
                let lhs = d.ble(x, x);
                let t = d.bool_true();
                d.eq_bool(lhs, t)
            },
            &|d| {
                let t = d.bool_true();
                d.refl_bool(t)
            },
            &|_d, _n, ih| ih,
            n,
        )
    }

    /// Eliminate an impossible `Eq Bool Bool.false Bool.true` into `target`.
    fn false_true_elim(&mut self, target: ExprId, equality: ExprId) -> ExprId {
        let bool_ty = self.bool_ty();
        let false_value = self.bool_false();
        let true_value = self.bool_true();
        let prop = self.kernel.sort_zero();
        let anon = self.anon();
        let zero = self.level_zero();
        let one = self.level_one();
        let discriminator = {
            let motive = self.kernel.lam(anon, bool_ty, prop, BinderInfo::Default);
            let rec = self.kernel.const_(self.p.bool_rec, vec![one]);
            let false_prop = self.kernel.const_(self.p.false_, vec![]);
            let true_prop = self.kernel.const_(self.p.true_, vec![]);
            self.apply(rec, &[motive, true_prop, false_prop])
        };
        let motive = {
            let value_fv = self.fresh();
            let value = self.kernel.fvar(value_fv);
            let equality_ty = self.eq_bool(false_value, value);
            let body = self.apply(discriminator, &[value]);
            let inner = self
                .kernel
                .lam(anon, equality_ty, body, BinderInfo::Default);
            self.lam_fv(value_fv, bool_ty, inner)
        };
        let true_intro = self.kernel.const_(self.p.true_intro, vec![]);
        let eq_rec = self.kernel.const_(self.p.eq_rec, vec![zero, one]);
        let impossible = self.apply(
            eq_rec,
            &[
                bool_ty,
                false_value,
                motive,
                true_intro,
                true_value,
                equality,
            ],
        );
        let false_rec = self.kernel.const_(self.p.false_rec, vec![zero]);
        let false_ty = self.kernel.const_(self.p.false_, vec![]);
        let false_motive = self.kernel.lam(anon, false_ty, target, BinderInfo::Default);
        self.apply(false_rec, &[false_motive, impossible])
    }

    /// `Eq Bool (ble n (succ m)) Bool.true`, given `h : Eq Bool (ble n m) Bool.true`.
    /// This project's own `Nat.ble_succ_eq_true`, re-derived inline.
    fn ble_succ_eq_true_full(&mut self) -> ExprId {
        // fun n m h => (double induction on n, generalizing m, exactly as
        // ble.rs's `declare_boolean_le` builds it)
        let hyp_concl = |d: &mut Self, x: ExprId, y: ExprId| -> ExprId {
            let t = d.bool_true();
            let sy = d.succ(y);
            let hyp = {
                let lhs = d.ble(x, y);
                d.eq_bool(lhs, t)
            };
            let concl = {
                let lhs = d.ble(x, sy);
                d.eq_bool(lhs, t)
            };
            d.arrow(hyp, concl)
        };
        let nat = self.nat_ty();

        let motive_n = |d: &mut Self, x: ExprId| -> ExprId {
            let y_fv = d.fresh();
            let y = d.kernel.fvar(y_fv);
            let body = hyp_concl(d, x, y);
            let nat = d.nat_ty();
            d.pi_fv(y_fv, nat, body)
        };
        let base_n = |d: &mut Self| -> ExprId {
            let y_fv = d.fresh();
            let y = d.kernel.fvar(y_fv);
            let zero = d.zero();
            let hyp_ty = {
                let lhs = d.ble(zero, y);
                let t = d.bool_true();
                d.eq_bool(lhs, t)
            };
            let h_fv = d.fresh();
            let t = d.bool_true();
            let body = d.refl_bool(t);
            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            let nat = d.nat_ty();
            d.lam_fv(y_fv, nat, with_h)
        };
        let step_n = |d: &mut Self, np: ExprId, ih_n: ExprId| -> ExprId {
            let snp = d.succ(np);
            let motive_m = |d: &mut Self, y: ExprId| -> ExprId { hyp_concl(d, snp, y) };
            let base_m = |d: &mut Self| -> ExprId {
                let h_fv = d.fresh();
                let h = d.kernel.fvar(h_fv);
                let zero = d.zero();
                let hyp_ty = {
                    let lhs = d.ble(snp, zero);
                    let t = d.bool_true();
                    d.eq_bool(lhs, t)
                };
                let szero = d.succ(zero);
                let target = {
                    let lhs = d.ble(snp, szero);
                    let t = d.bool_true();
                    d.eq_bool(lhs, t)
                };
                let body = d.false_true_elim(target, h);
                d.lam_fv(h_fv, hyp_ty, body)
            };
            let step_m = |d: &mut Self, mp: ExprId, _ih_m: ExprId| -> ExprId {
                let h_fv = d.fresh();
                let h = d.kernel.fvar(h_fv);
                let smp = d.succ(mp);
                let hyp_ty = {
                    let lhs = d.ble(snp, smp);
                    let t = d.bool_true();
                    d.eq_bool(lhs, t)
                };
                let body = d.apply(ih_n, &[mp, h]);
                d.lam_fv(h_fv, hyp_ty, body)
            };
            let y_fv = d.fresh();
            let y = d.kernel.fvar(y_fv);
            let body = d.induct(&motive_m, &base_m, &step_m, y);
            let nat = d.nat_ty();
            d.lam_fv(y_fv, nat, body)
        };

        let n_fv = self.fresh();
        let n = self.kernel.fvar(n_fv);
        let all_m = self.induct(&motive_n, &base_n, &step_n, n);
        self.lam_fv(n_fv, nat, all_m)
    }

    fn ble_succ_eq_true_at(&mut self, n: ExprId, m: ExprId, h: ExprId) -> ExprId {
        let f = self.ble_succ_eq_true_full();
        self.apply(f, &[n, m, h])
    }
}

/// Attempt to reconstruct `rendered` (one of
/// [`SUBSTITUTABLE_NAT_ORDER_THEOREMS`]) as a value that independently
/// type-checks against `wire_ty` — the untrusted stream's own declared type
/// for that name, which this function never alters. Returns `Ok(None)` when
/// `rendered` is not one of these twenty names. Returns `Err(_)` when it is
/// one of these names but this kernel lacks the shape the reconstruction
/// depends on, **or** the candidate value fails to independently
/// type-check against `wire_ty` — the caller must treat both exactly like
/// "not substitutable here" and fall back to the stream's own (still
/// trusted-refused) value, never a coerced admission.
pub(crate) fn reconstruct(
    kernel: &mut Kernel,
    rendered: &str,
    wire_ty: ExprId,
) -> Result<Option<ExprId>, SubstitutionError> {
    if !SUBSTITUTABLE_NAT_ORDER_THEOREMS.contains(&rendered) {
        return Ok(None);
    }
    let prims = discover(kernel)?;
    check_required_optional_prims(&prims, rendered)?;
    let mut b = B::new(kernel, &prims);
    let value = build(&mut b, rendered)?;

    // Validate independently, without mutating the environment: infer the
    // candidate's type and check it against the stream's own declared type.
    let inferred = b
        .kernel
        .infer(value)
        .map_err(|_| SubstitutionError::UnexpectedShape("candidate value failed to infer"))?;
    if !b.kernel.def_eq(inferred, wire_ty) {
        return Err(SubstitutionError::UnexpectedShape(
            "candidate value's inferred type is not def-eq to the stream's declared type",
        ));
    }
    Ok(Some(value))
}

fn build(b: &mut B<'_>, rendered: &str) -> Result<ExprId, SubstitutionError> {
    let nat = b.nat_ty();
    let value = match rendered {
        "Nat.le_trans" => {
            let a_fv = b.fresh();
            let a = b.kernel.fvar(a_fv);
            let bn_fv = b.fresh();
            let bn = b.kernel.fvar(bn_fv);
            let c_fv = b.fresh();
            let c = b.kernel.fvar(c_fv);
            let h1_fv = b.fresh();
            let h1 = b.kernel.fvar(h1_fv);
            let h2_fv = b.fresh();
            let h2 = b.kernel.fvar(h2_fv);
            let h1_ty = b.le(a, bn);
            let h2_ty = b.le(bn, c);
            let body = b.le_trans_at(a, bn, c, h1, h2);
            let with_h2 = b.lam_fv(h2_fv, h2_ty, body);
            let with_h1 = b.lam_fv(h1_fv, h1_ty, with_h2);
            let with_c = b.lam_fv(c_fv, nat, with_h1);
            let with_b = b.lam_fv(bn_fv, nat, with_c);
            b.lam_fv(a_fv, nat, with_b)
        }
        "Nat.le_refl" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let body = b.le_refl_ctor(n);
            b.lam_fv(n_fv, nat, body)
        }
        "Nat.le_succ" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let refl_n = b.le_refl_ctor(n);
            let body = b.le_step_ctor(n, n, refl_n);
            b.lam_fv(n_fv, nat, body)
        }
        "Nat.succ_le_succ" | "Nat.lt_succ_of_le" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let m_fv = b.fresh();
            let m = b.kernel.fvar(m_fv);
            let h_fv = b.fresh();
            let h = b.kernel.fvar(h_fv);
            let hyp_ty = b.le(n, m);
            let body = b.le_succ_succ_term(n, m, h);
            let with_h = b.lam_fv(h_fv, hyp_ty, body);
            let with_m = b.lam_fv(m_fv, nat, with_h);
            b.lam_fv(n_fv, nat, with_m)
        }
        "Nat.le_of_lt_succ" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let m_fv = b.fresh();
            let m = b.kernel.fvar(m_fv);
            let h_fv = b.fresh();
            let h = b.kernel.fvar(h_fv);
            let sn = b.succ(n);
            let sm = b.succ(m);
            // hyp_ty is `Lt n (succ m)`, i.e. `Le (succ n) (succ m)` — NOT
            // `Le n (succ m)` (a from-scratch bug this fixture caught before
            // any archive run did).
            let hyp_ty = b.le(sn, sm);
            let body = b.le_of_succ_le_succ_at(n, m, h);
            let with_h = b.lam_fv(h_fv, hyp_ty, body);
            let with_m = b.lam_fv(m_fv, nat, with_h);
            b.lam_fv(n_fv, nat, with_m)
        }
        "Nat.lt_succ_self" | "Nat.lt_add_one" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let sn = b.succ(n);
            let body = b.le_refl_ctor(sn);
            b.lam_fv(n_fv, nat, body)
        }
        "Nat.not_succ_le_self" | "Nat.lt_irrefl" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let body = b.lt_irrefl_at(n);
            b.lam_fv(n_fv, nat, body)
        }
        // Same story as `Nat.lt_irrefl` a round earlier: `not_succ_le_zero_at`
        // was already reconstructed here and used internally (it discharges the
        // base case of `lt_irrefl_at`), and was simply never exposed as a
        // substitutable NAME. Measured 2026-08-22: once `Nat.div_rec_lemma` was
        // bridged, this became the first blocker for all four `Int.ModEq`
        // statement streams.
        "Nat.not_succ_le_zero" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let body = b.not_succ_le_zero_at(n);
            b.lam_fv(n_fv, nat, body)
        }
        "Nat.le_succ_of_le" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let m_fv = b.fresh();
            let m = b.kernel.fvar(m_fv);
            let h_fv = b.fresh();
            let h = b.kernel.fvar(h_fv);
            let hyp_ty = b.le(n, m);
            let body = b.le_step_ctor(n, m, h);
            let with_h = b.lam_fv(h_fv, hyp_ty, body);
            let with_m = b.lam_fv(m_fv, nat, with_h);
            b.lam_fv(n_fv, nat, with_m)
        }
        "Nat.zero_lt_succ" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let zero = b.zero();
            let base = b.zero_le_at(n);
            let body = b.le_succ_succ_term(zero, n, base);
            b.lam_fv(n_fv, nat, body)
        }
        "Nat.pred_le" => b.pred_le_value(),
        "Nat.pred_le_pred" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let m_fv = b.fresh();
            let m = b.kernel.fvar(m_fv);
            let h_fv = b.fresh();
            let h = b.kernel.fvar(h_fv);
            let hyp_ty = b.le(n, m);
            let body = b.induct_le(
                n,
                &|d, x| {
                    let px = d.pred(x);
                    let pn = d.pred(n);
                    d.le(pn, px)
                },
                &|d| {
                    let pn = d.pred(n);
                    d.le_refl_ctor(pn)
                },
                &|d, x, _hx_fv, ih| {
                    let px = d.pred(x);
                    let pn = d.pred(n);
                    let pred_le_x = d.pred_le_at(x);
                    d.le_trans_at(pn, px, x, ih, pred_le_x)
                },
                m,
                h,
            );
            let with_h = b.lam_fv(h_fv, hyp_ty, body);
            let with_m = b.lam_fv(m_fv, nat, with_h);
            b.lam_fv(n_fv, nat, with_m)
        }
        "Nat.sub_le" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let m_fv = b.fresh();
            let m = b.kernel.fvar(m_fv);
            let body = b.sub_le_at(n, m);
            let with_m = b.lam_fv(m_fv, nat, body);
            b.lam_fv(n_fv, nat, with_m)
        }
        "Nat.succ_sub_succ_eq_sub" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let m_fv = b.fresh();
            let m = b.kernel.fvar(m_fv);
            let body = b.succ_sub_succ_eq_sub_body(n, m);
            let with_m = b.lam_fv(m_fv, nat, body);
            b.lam_fv(n_fv, nat, with_m)
        }
        "Nat.sub_lt" => build_sub_lt(b),
        "Nat.zero_le" => b.zero_le_value(),
        "Nat.ble_self_eq_true" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let body = b.ble_self_eq_true_at(n);
            b.lam_fv(n_fv, nat, body)
        }
        "Nat.ble_succ_eq_true" => b.ble_succ_eq_true_full(),
        "Nat.ble_eq_true_of_le" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let m_fv = b.fresh();
            let m = b.kernel.fvar(m_fv);
            let h_fv = b.fresh();
            let h = b.kernel.fvar(h_fv);
            let hyp_ty = b.le(n, m);
            let at_ty = |d: &mut B<'_>, x: ExprId| -> ExprId {
                let lhs = d.ble(n, x);
                let t = d.bool_true();
                d.eq_bool(lhs, t)
            };
            let body = b.induct_le(
                n,
                &|d, x| at_ty(d, x),
                &|d| d.ble_self_eq_true_at(n),
                &|d, x, _hx_fv, ih| d.ble_succ_eq_true_at(n, x, ih),
                m,
                h,
            );
            let with_h = b.lam_fv(h_fv, hyp_ty, body);
            let with_m = b.lam_fv(m_fv, nat, with_h);
            b.lam_fv(n_fv, nat, with_m)
        }
        "Nat.le_of_ble_eq_true" => build_le_of_ble_eq_true(b),
        "Nat.not_le_of_not_ble_eq_true" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let m_fv = b.fresh();
            let m = b.kernel.fvar(m_fv);
            let true_ = b.bool_true();
            let ble_nm = b.ble(n, m);
            let ble_eq_true = b.eq_bool(ble_nm, true_);
            let false_ty = b.kernel.const_(b.p.false_, vec![]);
            let not_ble = b.arrow(ble_eq_true, false_ty);
            let h1_fv = b.fresh();
            let h1 = b.kernel.fvar(h1_fv);
            let le_nm = b.le(n, m);
            let h2_fv = b.fresh();
            let h2 = b.kernel.fvar(h2_fv);
            let derived = b.ble_eq_true_of_le_at(n, m, h2);
            let contradiction = b.apply(h1, &[derived]);
            let inner = b.lam_fv(h2_fv, le_nm, contradiction);
            let with_h1 = b.lam_fv(h1_fv, not_ble, inner);
            let with_m = b.lam_fv(m_fv, nat, with_h1);
            b.lam_fv(n_fv, nat, with_m)
        }
        "Nat.lt_of_lt_of_le" => {
            let a_fv = b.fresh();
            let a = b.kernel.fvar(a_fv);
            let bn_fv = b.fresh();
            let bn = b.kernel.fvar(bn_fv);
            let c_fv = b.fresh();
            let c = b.kernel.fvar(c_fv);
            let h1_fv = b.fresh();
            let h1 = b.kernel.fvar(h1_fv);
            let h2_fv = b.fresh();
            let h2 = b.kernel.fvar(h2_fv);
            let sa = b.succ(a);
            // hyp1_ty is `Lt a bn`, i.e. `Le (succ a) bn` — the same
            // `Nat.lt`-unfolding reliance `Nat.le_of_lt_succ`'s own
            // `hyp_ty` already has.
            let h1_ty = b.le(sa, bn);
            let h2_ty = b.le(bn, c);
            let body = b.le_trans_at(sa, bn, c, h1, h2);
            let with_h2 = b.lam_fv(h2_fv, h2_ty, body);
            let with_h1 = b.lam_fv(h1_fv, h1_ty, with_h2);
            let with_c = b.lam_fv(c_fv, nat, with_h1);
            let with_b = b.lam_fv(bn_fv, nat, with_c);
            b.lam_fv(a_fv, nat, with_b)
        }
        "Nat.div_rec_lemma" => build_div_rec_lemma(b),
        "Nat.div_rec_fuel_lemma" => build_div_rec_fuel_lemma(b),
        // `Nat.le_of_lt_add_one` shares this arm because Lean 4.30 proves it
        // by `Nat.le_of_succ_le_succ n m` and nothing else; the two differ
        // only in how their TYPE is spelled, and the type is the stream's,
        // never ours. See `SUBSTITUTABLE_NAT_ORDER_THEOREMS`.
        "Nat.le_of_succ_le_succ" | "Nat.le_of_lt_add_one" => {
            let n_fv = b.fresh();
            let n = b.kernel.fvar(n_fv);
            let m_fv = b.fresh();
            let m = b.kernel.fvar(m_fv);
            let h_fv = b.fresh();
            let h = b.kernel.fvar(h_fv);
            let sn = b.succ(n);
            let sm = b.succ(m);
            let hyp_ty = b.le(sn, sm);
            let body = b.le_of_succ_le_succ_at(n, m, h);
            let with_h = b.lam_fv(h_fv, hyp_ty, body);
            let with_m = b.lam_fv(m_fv, nat, with_h);
            b.lam_fv(n_fv, nat, with_m)
        }
        _ => {
            return Err(SubstitutionError::UnexpectedShape(
                "unreachable: checked against SUBSTITUTABLE_NAT_ORDER_THEOREMS above",
            ));
        }
    };
    Ok(value)
}

impl B<'_> {
    /// `Eq Bool (ble n m) Bool.true`, from `h : Le n m` — this project's own
    /// `Nat.ble_eq_true_of_le`, re-derived inline.
    fn ble_eq_true_of_le_at(&mut self, n: ExprId, m: ExprId, h: ExprId) -> ExprId {
        let at_ty = |d: &mut Self, x: ExprId| -> ExprId {
            let lhs = d.ble(n, x);
            let t = d.bool_true();
            d.eq_bool(lhs, t)
        };
        self.induct_le(
            n,
            &|d, x| at_ty(d, x),
            &|d| d.ble_self_eq_true_at(n),
            &|d, x, _hx_fv, ih| d.ble_succ_eq_true_at(n, x, ih),
            m,
            h,
        )
    }
}

/// `Le n m`, from `h : Eq Bool (ble n m) Bool.true` — this project's own
/// `Nat.le_of_ble_eq_true`. Induction on `n`, generalizing `m`: the base case
/// is this project's own inline `zero_le_at`; the step case case-splits on
/// `m` (`m = 0` is absurd via `false_true_elim`, `m = succ m'` closes with
/// the inline `le_succ_succ` construction lifted over the outer induction
/// hypothesis).
fn build_le_of_ble_eq_true(b: &mut B<'_>) -> ExprId {
    let nat = b.nat_ty();

    let hyp_concl = |d: &mut B<'_>, x: ExprId, y: ExprId| -> ExprId {
        let lhs = d.ble(x, y);
        let t = d.bool_true();
        let hyp = d.eq_bool(lhs, t);
        let concl = d.le(x, y);
        d.arrow(hyp, concl)
    };

    let motive_n = |d: &mut B<'_>, x: ExprId| -> ExprId {
        let y_fv = d.fresh();
        let y = d.kernel.fvar(y_fv);
        let body = hyp_concl(d, x, y);
        let nat = d.nat_ty();
        d.pi_fv(y_fv, nat, body)
    };

    let base_n = |d: &mut B<'_>| -> ExprId {
        let y_fv = d.fresh();
        let y = d.kernel.fvar(y_fv);
        let zero = d.zero();
        let hyp_ty = {
            let lhs = d.ble(zero, y);
            let t = d.bool_true();
            d.eq_bool(lhs, t)
        };
        let h_fv = d.fresh();
        let body = d.zero_le_at(y);
        let with_h = d.lam_fv(h_fv, hyp_ty, body);
        let nat = d.nat_ty();
        d.lam_fv(y_fv, nat, with_h)
    };

    let step_n = |d: &mut B<'_>, np: ExprId, ih_n: ExprId| -> ExprId {
        let snp = d.succ(np);
        let motive_m = |d: &mut B<'_>, y: ExprId| -> ExprId { hyp_concl(d, snp, y) };

        let base_m = |d: &mut B<'_>| -> ExprId {
            let h_fv = d.fresh();
            let h = d.kernel.fvar(h_fv);
            let zero = d.zero();
            let hyp_ty = {
                let lhs = d.ble(snp, zero);
                let t = d.bool_true();
                d.eq_bool(lhs, t)
            };
            let target = d.le(snp, zero);
            let body = d.false_true_elim(target, h);
            d.lam_fv(h_fv, hyp_ty, body)
        };

        let step_m = |d: &mut B<'_>, mp: ExprId, _ih_m: ExprId| -> ExprId {
            let h_fv = d.fresh();
            let h = d.kernel.fvar(h_fv);
            let smp = d.succ(mp);
            let hyp_ty = {
                let lhs = d.ble(snp, smp);
                let t = d.bool_true();
                d.eq_bool(lhs, t)
            };
            let smaller = d.apply(ih_n, &[mp, h]);
            let body = d.le_succ_succ_term(np, mp, smaller);
            d.lam_fv(h_fv, hyp_ty, body)
        };

        let y_fv = d.fresh();
        let y = d.kernel.fvar(y_fv);
        let body = d.induct(&motive_m, &base_m, &step_m, y);
        let nat = d.nat_ty();
        d.lam_fv(y_fv, nat, body)
    };

    let n_fv = b.fresh();
    let n = b.kernel.fvar(n_fv);
    let m_fv = b.fresh();
    let m = b.kernel.fvar(m_fv);
    let all_m = b.induct(&motive_n, &base_n, &step_n, n);
    let proof = b.apply(all_m, &[m]);
    let with_m = b.lam_fv(m_fv, nat, proof);
    b.lam_fv(n_fv, nat, with_m)
}

fn build_sub_lt(b: &mut B<'_>) -> ExprId {
    let nat = b.nat_ty();
    let n_fv = b.fresh();
    let n = b.kernel.fvar(n_fv);
    let m_fv = b.fresh();
    let m = b.kernel.fvar(m_fv);

    let inner_stmt = |d: &mut B<'_>, x: ExprId, y: ExprId| -> ExprId {
        let zero = d.zero();
        let szero = d.succ(zero);
        let pos_x = d.le(szero, x);
        let pos_y = d.le(szero, y);
        let sub_xy = d.sub(x, y);
        let s_sub_xy = d.succ(sub_xy);
        let concl = d.le(s_sub_xy, x);
        let with_pos_y = d.arrow(pos_y, concl);
        d.arrow(pos_x, with_pos_y)
    };

    let motive_n = |d: &mut B<'_>, x: ExprId| -> ExprId {
        let y_fv = d.fresh();
        let y = d.kernel.fvar(y_fv);
        let body = inner_stmt(d, x, y);
        let nat = d.nat_ty();
        d.pi_fv(y_fv, nat, body)
    };

    let base_n = |d: &mut B<'_>| -> ExprId {
        let y_fv = d.fresh();
        let y = d.kernel.fvar(y_fv);
        let zero = d.zero();
        let szero = d.succ(zero);
        let pos_zero = d.le(szero, zero);
        let h1_fv = d.fresh();
        let h1 = d.kernel.fvar(h1_fv);
        let pos_y = d.le(szero, y);
        let h2_fv = d.fresh();
        let sub_0y = d.sub(zero, y);
        let ssub = d.succ(sub_0y);
        let target = d.le(ssub, zero);
        let discharge = d.not_succ_le_zero_at(zero);
        let impossible = d.apply(discharge, &[h1]);
        let false_ty = d.kernel.const_(d.p.false_, vec![]);
        let anon = d.anon();
        let motive = d.kernel.lam(anon, false_ty, target, BinderInfo::Default);
        let level_zero = d.level_zero();
        let rec = d.kernel.const_(d.p.false_rec, vec![level_zero]);
        let body = d.apply(rec, &[motive, impossible]);
        let with_h2 = d.lam_fv(h2_fv, pos_y, body);
        let with_h1 = d.lam_fv(h1_fv, pos_zero, with_h2);
        let nat = d.nat_ty();
        d.lam_fv(y_fv, nat, with_h1)
    };

    let step_n = |d: &mut B<'_>, np: ExprId, _ih_n: ExprId| -> ExprId {
        let snp = d.succ(np);
        let zero = d.zero();
        let szero = d.succ(zero);
        let pos_snp = d.le(szero, snp);

        let motive_m = |d: &mut B<'_>, y: ExprId| -> ExprId {
            let zero = d.zero();
            let szero = d.succ(zero);
            let pos_y = d.le(szero, y);
            let sub_val = d.sub(snp, y);
            let ssub = d.succ(sub_val);
            let concl = d.le(ssub, snp);
            d.arrow(pos_y, concl)
        };

        let base_m = |d: &mut B<'_>| -> ExprId {
            let h2_fv = d.fresh();
            let h2 = d.kernel.fvar(h2_fv);
            let zero = d.zero();
            let szero = d.succ(zero);
            let pos_zero = d.le(szero, zero);
            let sub_val = d.sub(snp, zero);
            let ssub = d.succ(sub_val);
            let target = d.le(ssub, snp);
            let discharge = d.not_succ_le_zero_at(zero);
            let impossible = d.apply(discharge, &[h2]);
            let false_ty = d.kernel.const_(d.p.false_, vec![]);
            let anon = d.anon();
            let motive = d.kernel.lam(anon, false_ty, target, BinderInfo::Default);
            let level_zero = d.level_zero();
            let rec = d.kernel.const_(d.p.false_rec, vec![level_zero]);
            let body = d.apply(rec, &[motive, impossible]);
            d.lam_fv(h2_fv, pos_zero, body)
        };

        let step_m = |d: &mut B<'_>, mp: ExprId, _ih_m: ExprId| -> ExprId {
            let smp = d.succ(mp);
            let h2_fv = d.fresh();
            let zero = d.zero();
            let szero = d.succ(zero);
            let pos_smp = d.le(szero, smp);
            let rewrite = d.succ_sub_succ_eq_sub_body(np, mp);
            let sub_np_mp = d.sub(np, mp);
            let sub_snp_smp = d.sub(snp, smp);
            let rewrite_rev = d.symm_nat(sub_snp_smp, sub_np_mp, rewrite);
            let bounded = d.sub_le_at(np, mp);
            let lifted = d.le_succ_succ_term(sub_np_mp, np, bounded);
            let transport_motive = d.eq_motive_nat(sub_np_mp, &|d, value| {
                let sv = d.succ(value);
                d.le(sv, snp)
            });
            let one = d.level_one();
            let nat = d.nat_ty();
            let body = d.transport_at(
                one,
                nat,
                sub_np_mp,
                transport_motive,
                lifted,
                sub_snp_smp,
                rewrite_rev,
            );
            d.lam_fv(h2_fv, pos_smp, body)
        };

        let y_fv = d.fresh();
        let y = d.kernel.fvar(y_fv);
        let body_for_y = d.induct(&motive_m, &base_m, &step_m, y);
        let h1_fv = d.fresh();
        let with_h1 = d.lam_fv(h1_fv, pos_snp, body_for_y);
        let nat = d.nat_ty();
        d.lam_fv(y_fv, nat, with_h1)
    };

    let all_m = b.induct(&motive_n, &base_n, &step_n, n);
    let proof = b.apply(all_m, &[m]);
    let with_m = b.lam_fv(m_fv, nat, proof);
    b.lam_fv(n_fv, nat, with_m)
}

/// `Nat.div_rec_lemma {x y : Nat} (h : 0 < y ∧ y ≤ x) : x - y < x :=
/// Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1`. `h.1 : 0 < y` and `h.2 : y ≤
/// x` are projected from the stream's own `And` via [`B::and_left`]/
/// [`B::and_right`] — never citing the stream's own value for `h.1`/`h.2`,
/// exactly like [`or_elim_pair`](super::trusted_substitution)'s projection
/// of its own disjunction. The two composed facts are [`B::le_trans_at`]
/// (for `lt_of_lt_of_le`, identically to the `"Nat.lt_of_lt_of_le"` arm in
/// [`build`]) and [`build_sub_lt`] (for `sub_lt`, instantiated here at
/// `(x, y)` rather than that function's own `(n, m)` naming).
fn build_div_rec_lemma(b: &mut B<'_>) -> ExprId {
    let nat = b.nat_ty();
    let x_fv = b.fresh();
    let x = b.kernel.fvar(x_fv);
    let y_fv = b.fresh();
    let y = b.kernel.fvar(y_fv);
    let h_fv = b.fresh();
    let h = b.kernel.fvar(h_fv);

    let zero = b.zero();
    let szero = b.succ(zero);
    let pos_y = b.le(szero, y); // `0 < y`, i.e. `Lt Zero y`.
    let le_yx = b.le(y, x); // `y <= x`.
    let hyp_ty = b.and_app(pos_y, le_yx);

    let h1 = b.and_left(pos_y, le_yx, h); // h.1 : 0 < y
    let h2 = b.and_right(pos_y, le_yx, h); // h.2 : y <= x

    // Nat.lt_of_lt_of_le h.1 h.2 : Lt Zero x, i.e. `0 < x`.
    let pos_x = b.le_trans_at(szero, y, x, h1, h2);

    // Nat.sub_lt : forall n m, 0 < n -> 0 < m -> n - m < n, instantiated at
    // (n := x, m := y): Nat.sub_lt pos_x h1 : x - y < x.
    let sub_lt_all = build_sub_lt(b);
    let sub_lt_xy = b.apply(sub_lt_all, &[x, y, pos_x, h1]);

    let with_h = b.lam_fv(h_fv, hyp_ty, sub_lt_xy);
    let with_y = b.lam_fv(y_fv, nat, with_h);
    b.lam_fv(x_fv, nat, with_y)
}

/// `Nat.div_rec_fuel_lemma {x y fuel : Nat} (hy : 0 < y) (hle : y ≤ x)
/// (hfuel : x < fuel + 1) : x - y < fuel` — the last named blocker between
/// the `Int.ModEq` family and a producer (docs/autogenesis/243). Despite the
/// "fuel"/well-founded-recursion-suggesting name, the real stream's own
/// proof VALUE (read directly from a genuine export, not inferred from the
/// name) is not itself well-founded recursion at all — it is a three-fact
/// composition:
///
/// ```text
/// Nat.lt_of_lt_of_le (x - y) x fuel
///   (Nat.div_rec_lemma x y (And.intro hy hle))   -- x - y < x
///   (Nat.le_of_lt_succ x fuel hfuel)              -- x <= fuel
/// ```
///
/// every piece of which this module already has: [`build_div_rec_lemma`]
/// (its value, applied here rather than re-derived), [`B::le_of_succ_le_succ_at`]
/// (backing the `"Nat.le_of_lt_succ"` arm above, reused identically for
/// `x < fuel + 1 -> x <= fuel` since `fuel + 1` def-eq-unfolds through the
/// stream's own `HAdd.hAdd`/`instHAdd`/`Nat.add`/`OfNat.ofNat 1` to `succ
/// fuel`, giving `hfuel : Le (succ x) (succ fuel)` — exactly that arm's own
/// hypothesis shape), and [`B::le_trans_at`] (backing the
/// `"Nat.lt_of_lt_of_le"` arm, reused identically at `(succ (x - y), x,
/// fuel)`). `0 < y ∧ y ≤ x` is rebuilt fresh from `hy`/`hle` via
/// [`B::and_intro`] — never citing the stream's own conjunction value — and
/// handed to `build_div_rec_lemma`'s value, which independently projects it
/// straight back out via `And.rec`/[`B::and_left`]/[`B::and_right`]; nothing
/// here short-circuits that round trip, so the arm adds no new elimination
/// machinery, only composition.
fn build_div_rec_fuel_lemma(b: &mut B<'_>) -> ExprId {
    let nat = b.nat_ty();
    let x_fv = b.fresh();
    let x = b.kernel.fvar(x_fv);
    let y_fv = b.fresh();
    let y = b.kernel.fvar(y_fv);
    let fuel_fv = b.fresh();
    let fuel = b.kernel.fvar(fuel_fv);
    let hy_fv = b.fresh();
    let hy = b.kernel.fvar(hy_fv);
    let hle_fv = b.fresh();
    let hle = b.kernel.fvar(hle_fv);
    let hfuel_fv = b.fresh();
    let hfuel = b.kernel.fvar(hfuel_fv);

    let zero = b.zero();
    let szero = b.succ(zero);
    let pos_y = b.le(szero, y); // `0 < y`, i.e. `Lt Zero y`.
    let le_yx = b.le(y, x); // `y <= x`.
    let sx = b.succ(x);
    let sfuel = b.succ(fuel);
    // `x < fuel + 1`, stated directly as `Le (succ x) (succ fuel)` — the
    // same `Nat.lt`/`+1`-unfolding reliance `"Nat.le_of_lt_succ"`'s own
    // `hyp_ty` already has.
    let hfuel_ty = b.le(sx, sfuel);

    // Rebuild `0 < y ∧ y ≤ x` fresh from `hy`/`hle`, never the stream's own
    // conjunction value, then hand it to `Nat.div_rec_lemma`'s own value.
    let and_h = b.and_intro(pos_y, le_yx, hy, hle);
    let div_rec_lemma_value = build_div_rec_lemma(b);
    let sub_lt_x = b.apply(div_rec_lemma_value, &[x, y, and_h]); // : x - y < x

    // `Nat.le_of_lt_succ x fuel hfuel : x <= fuel`, identical to the
    // `"Nat.le_of_lt_succ"` arm's own construction.
    let le_x_fuel = b.le_of_succ_le_succ_at(x, fuel, hfuel);

    // `Nat.lt_of_lt_of_le (x - y) x fuel sub_lt_x le_x_fuel : x - y < fuel`,
    // identical to the `"Nat.lt_of_lt_of_le"` arm's own construction.
    let sub_xy = b.sub(x, y);
    let s_sub_xy = b.succ(sub_xy);
    let result = b.le_trans_at(s_sub_xy, x, fuel, sub_lt_x, le_x_fuel);

    let with_hfuel = b.lam_fv(hfuel_fv, hfuel_ty, result);
    let with_hle = b.lam_fv(hle_fv, le_yx, with_hfuel);
    let with_hy = b.lam_fv(hy_fv, pos_y, with_hle);
    let with_fuel = b.lam_fv(fuel_fv, nat, with_hy);
    let with_y = b.lam_fv(y_fv, nat, with_fuel);
    b.lam_fv(x_fv, nat, with_y)
}

impl B<'_> {
    /// `Le (sub n m) n`, this project's own `Nat.sub_le`, re-derived inline
    /// using [`Self::le_trans_at`].
    fn sub_le_at(&mut self, n: ExprId, m: ExprId) -> ExprId {
        self.induct(
            &|d, x| {
                let sub_nx = d.sub(n, x);
                d.le(sub_nx, n)
            },
            &|d| d.le_refl_ctor(n),
            &|d, j, ih| {
                let sub_nj = d.sub(n, j);
                let pred_sub_nj = d.pred(sub_nj);
                let pred_le_step = d.pred_le_at(sub_nj);
                d.le_trans_at(pred_sub_nj, sub_nj, n, pred_le_step, ih)
            },
            m,
        )
    }
}

#[cfg(test)]
mod tests {
    //! Fast (no archive, no filesystem), deterministic regression coverage.
    //! [`axeyum_lean_kernel::build_nat_prelude`] gives a real kernel carrying
    //! this project's own `Nat`/`Nat.le`/`Nat.pred`/`Nat.sub`/`Nat.ble` and
    //! every one of the 20 target theorems, each already independently
    //! kernel-checked under its own construction — exactly the shape
    //! `reconstruct` is meant to rebuild. Using each theorem's own declared
    //! type as `wire_ty` exercises the full discovery + construction +
    //! infer/def-eq validation path end-to-end without depending on a
    //! host-local corpus. The archive-backed `real_stream_tests` below is
    //! what actually confirms this fires on genuine Mathlib exports; this
    //! module is what CI runs on every commit.
    use super::*;
    use axeyum_lean_kernel::{Kernel, NatPrelude, build_nat_prelude};

    fn prelude_kernel() -> (Kernel, NatPrelude) {
        let mut kernel = Kernel::new();
        let prelude = build_nat_prelude(&mut kernel).expect("nat prelude must build");
        (kernel, prelude)
    }

    /// The existing kernel-checked name/type this project's own prelude
    /// already carries for `rendered`, used here only as a stand-in
    /// `wire_ty` — never as the value `reconstruct` is allowed to reuse.
    fn field_name(p: &NatPrelude, rendered: &str) -> NameId {
        match rendered {
            "Nat.le_trans" => p.le_trans,
            "Nat.le_refl" => p.le_refl_thm,
            "Nat.le_succ" => p.le_succ,
            "Nat.succ_le_succ" => p.succ_le_succ,
            "Nat.le_of_lt_succ" => p.le_of_lt_succ,
            "Nat.lt_succ_self" => p.lt_succ_self,
            "Nat.lt_succ_of_le" => p.lt_succ_of_le,
            "Nat.lt_add_one" => p.lt_add_one,
            "Nat.lt_irrefl" => p.lt_irrefl,
            "Nat.not_succ_le_self" => p.not_succ_le_self,
            "Nat.not_succ_le_zero" => p.not_succ_le_zero,
            "Nat.le_succ_of_le" => p.le_succ_of_le,
            "Nat.zero_lt_succ" => p.zero_lt_succ,
            "Nat.zero_le" => p.zero_le,
            "Nat.pred_le" => p.pred_le,
            "Nat.pred_le_pred" => p.pred_le_pred,
            "Nat.sub_le" => p.sub_le,
            "Nat.sub_lt" => p.sub_lt,
            "Nat.succ_sub_succ_eq_sub" => p.succ_sub_succ_eq_sub,
            "Nat.ble_self_eq_true" => p.ble_self_eq_true,
            "Nat.ble_succ_eq_true" => p.ble_succ_eq_true,
            "Nat.ble_eq_true_of_le" => p.ble_eq_true_of_le,
            "Nat.le_of_ble_eq_true" => p.le_of_ble_eq_true,
            "Nat.not_le_of_not_ble_eq_true" => p.not_le_of_not_ble_eq_true,
            "Nat.lt_of_lt_of_le" => p.lt_of_lt_of_le,
            "Nat.le_of_succ_le_succ" => p.le_of_succ_le_succ,
            other => panic!("no NatPrelude field mapped for {other:?}"),
        }
    }

    #[test]
    fn every_listed_name_reconstructs_and_kernel_checks_against_our_own_prelude() {
        let (mut kernel, prelude) = prelude_kernel();
        for &rendered in SUBSTITUTABLE_NAT_ORDER_THEOREMS {
            // `Nat.div_rec_lemma` has no `NatPrelude` field to compare
            // against — this project's own `nat_prelude` never states it,
            // only the arithmetic facts (`sub_lt`, `lt_of_lt_of_le`) it
            // composes. Covered separately by
            // `div_rec_lemma_reconstructs_and_kernel_checks`, against a
            // hand-built `And`-carrying wire type. `Nat.div_rec_fuel_lemma`
            // is the same story, one level up — covered by
            // `div_rec_fuel_lemma_reconstructs_and_kernel_checks`.
            // `Nat.le_of_lt_add_one` is Mathlib's TYPECLASS-SPELLED form
            // (`LT.lt Nat instLTNat n (m + 1)`); this project's own
            // `nat_prelude` never states it, and admitting our value at
            // `Nat.le_of_succ_le_succ`'s bare type here would test nothing
            // about the spelling that actually blocks the census rows.
            // Covered instead by
            // `le_of_lt_add_one_reconstructs_against_the_real_mathlib_type`,
            // against the pinned Lean 4.30 export of the real declaration.
            if rendered == "Nat.div_rec_lemma"
                || rendered == "Nat.div_rec_fuel_lemma"
                || rendered == "Nat.le_of_lt_add_one"
            {
                continue;
            }
            let existing = field_name(&prelude, rendered);
            let wire_ty = kernel.environment().get(existing).expect("declared").ty();
            let value = reconstruct(&mut kernel, rendered, wire_ty)
                .unwrap_or_else(|e| panic!("{rendered}: reconstruction declined: {e}"))
                .unwrap_or_else(|| panic!("{rendered}: not recognised as substitutable"));
            let inferred = kernel
                .infer(value)
                .unwrap_or_else(|e| panic!("{rendered}: candidate failed to infer: {e:?}"));
            assert!(
                kernel.def_eq(inferred, wire_ty),
                "{rendered}: candidate's type is not def-eq to wire_ty"
            );
            // Independently admit under a fresh name and confirm axiom-free —
            // the same discipline `trusted_substitution`'s own tests apply to
            // congrArg/congr/mt.
            let fresh_name = {
                let root = kernel.anon();
                kernel.name_str(root, format!("TestReconstruct_{rendered}"))
            };
            kernel
                .add_declaration(Declaration::Theorem {
                    name: fresh_name,
                    uparams: vec![],
                    ty: wire_ty,
                    value,
                })
                .unwrap_or_else(|e| panic!("{rendered}: admission failed: {e:?}"));
            assert_eq!(
                kernel.axiom_footprint(fresh_name).len(),
                0,
                "{rendered}: nonempty axiom footprint"
            );
            // Axiom-free is not the same claim as "cites no theorem" — a
            // proof can have zero axioms while still depending on another
            // Theorem declaration (exactly the gap a prior version of this
            // module had: it cited the *reference* kernel's own
            // `Nat.le_trans`/`Nat.zero_le`/etc., which are themselves
            // axiom-free, so `axiom_footprint` alone never caught it).
            // `theorem_dependencies` is the machine-checked form of "this
            // proof cites no theorem at all", which is what "built from
            // primitives, never a citation" actually means.
            assert_eq!(
                kernel.theorem_dependencies(fresh_name).len(),
                0,
                "{rendered}: cites another theorem: {:?}",
                kernel
                    .theorem_dependencies(fresh_name)
                    .iter()
                    .map(|&n| kernel.display_name(n).to_string())
                    .collect::<Vec<_>>()
            );
        }
    }

    /// `Nat.div_rec_lemma {x y} (h : 0 < y ∧ y ≤ x) : x - y < x`, admitted
    /// against a HAND-BUILT wire type carrying a genuine conjunction
    /// hypothesis — the shape this project's own `nat_prelude` never states
    /// (it has the arithmetic facts `div_rec_lemma` composes, `sub_lt` and
    /// `lt_of_lt_of_le`, but not the composed lemma itself). `prelude_kernel`
    /// already carries a real `And`/`And.rec` — `build_nat_prelude_uncached`
    /// runs `build_logic_prelude` first, which is where `And` comes from
    /// (`axeyum-lean-kernel::prelude`) — so this test looks that up rather
    /// than hand-building a second one (which would collide,
    /// `DeclarationExists`, exactly as a real archive kernel with a `Nat`
    /// import always carries its own `And` too). The hypothesis's own
    /// conjuncts use `Nat.lt` (not the unfolded `Le (succ _) _` form),
    /// exactly like a real Lean export would render `0 < y`, confirming
    /// `build_div_rec_lemma`'s reliance on delta-unfolding `Nat.lt` (the
    /// same reliance the module's other `lt_`-shaped entries already have).
    #[test]
    #[allow(clippy::too_many_lines)]
    fn div_rec_lemma_reconstructs_and_kernel_checks() {
        let (mut kernel, prelude) = prelude_kernel();
        let anon = kernel.anon();
        let mut next_fvar = FVAR_BASE + 40_000_000;
        let mut fresh = || {
            next_fvar += 1;
            next_fvar
        };

        let and_name = exact_name(&kernel, "And").expect("prelude_kernel carries And");

        // wire_ty := (x y : Nat) -> (h : And (Nat.lt Nat.zero y) (Nat.le y x))
        //   -> Nat.lt (Nat.sub x y) x
        let nat_ty = kernel.const_(prelude.nat, vec![]);
        let x_fv = fresh();
        let x = kernel.fvar(x_fv);
        let y_fv = fresh();
        let y = kernel.fvar(y_fv);
        let h_fv = fresh();

        let zero_c = kernel.const_(prelude.zero, vec![]);
        let lt_zero_y = {
            let c = kernel.const_(prelude.lt, vec![]);
            let w1 = kernel.app(c, zero_c);
            kernel.app(w1, y)
        };
        let le_y_x = {
            let c = kernel.const_(prelude.le, vec![]);
            let w1 = kernel.app(c, y);
            kernel.app(w1, x)
        };
        let hyp_ty = {
            let and_const = kernel.const_(and_name, vec![]);
            let w1 = kernel.app(and_const, lt_zero_y);
            kernel.app(w1, le_y_x)
        };
        let concl = {
            let sub_xy = {
                let c = kernel.const_(prelude.sub, vec![]);
                let w1 = kernel.app(c, x);
                kernel.app(w1, y)
            };
            let c = kernel.const_(prelude.lt, vec![]);
            let w1 = kernel.app(c, sub_xy);
            kernel.app(w1, x)
        };

        let mut wire_ty = concl;
        let abstracted = kernel.abstract_fvars(wire_ty, &[h_fv]);
        wire_ty = kernel.pi(anon, hyp_ty, abstracted, BinderInfo::Default);
        let abstracted = kernel.abstract_fvars(wire_ty, &[y_fv]);
        wire_ty = kernel.pi(anon, nat_ty, abstracted, BinderInfo::Default);
        let abstracted = kernel.abstract_fvars(wire_ty, &[x_fv]);
        wire_ty = kernel.pi(anon, nat_ty, abstracted, BinderInfo::Default);

        let value = reconstruct(&mut kernel, "Nat.div_rec_lemma", wire_ty)
            .unwrap_or_else(|e| panic!("Nat.div_rec_lemma: reconstruction declined: {e}"))
            .unwrap_or_else(|| panic!("Nat.div_rec_lemma: not recognised as substitutable"));
        let inferred = kernel
            .infer(value)
            .unwrap_or_else(|e| panic!("Nat.div_rec_lemma: candidate failed to infer: {e:?}"));
        assert!(
            kernel.def_eq(inferred, wire_ty),
            "Nat.div_rec_lemma: candidate's type is not def-eq to wire_ty"
        );

        let fresh_name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDivRecLemma")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name: fresh_name,
                uparams: vec![],
                ty: wire_ty,
                value,
            })
            .unwrap_or_else(|e| panic!("Nat.div_rec_lemma: admission failed: {e:?}"));
        assert_eq!(
            kernel.axiom_footprint(fresh_name).len(),
            0,
            "Nat.div_rec_lemma: nonempty axiom footprint"
        );
        assert_eq!(
            kernel.theorem_dependencies(fresh_name).len(),
            0,
            "Nat.div_rec_lemma: cites another theorem: {:?}",
            kernel
                .theorem_dependencies(fresh_name)
                .iter()
                .map(|&n| kernel.display_name(n).to_string())
                .collect::<Vec<_>>()
        );
    }

    /// `Nat.div_rec_fuel_lemma {x y fuel} (hy : 0 < y) (hle : y ≤ x)
    /// (hfuel : x < Nat.succ fuel) : x - y < fuel` — read directly off the
    /// real `mathlib-v4.30.0-modeq-family-v1` archive streams
    /// (`statement_adapter_import ... Nat.div_rec_fuel_lemma`, all four
    /// identical), hand-built here the same way
    /// `div_rec_lemma_reconstructs_and_kernel_checks` builds its own: this
    /// project's own `nat_prelude` never states this composed lemma, only
    /// the arithmetic facts it composes. Unlike `Nat.div_rec_lemma`'s own
    /// wire type, `hy`/`hle` here are two SEPARATE curried hypotheses, never
    /// a conjunction — confirmed by reading the archive's own printed type,
    /// not assumed from the name. `hfuel` is stated via `Nat.lt`/`Nat.succ`
    /// (not the unfolded `Le` form [`build_div_rec_fuel_lemma`] itself
    /// builds), forcing the same `Nat.lt`-delta-unfolding reliance the real
    /// archive's `fuel + 1` (`HAdd.hAdd`/`OfNat.ofNat 1`) shape has, exactly
    /// like this module's other `lt_`-shaped entries already rely on.
    #[test]
    #[allow(clippy::too_many_lines)]
    fn div_rec_fuel_lemma_reconstructs_and_kernel_checks() {
        let (mut kernel, prelude) = prelude_kernel();
        let anon = kernel.anon();
        let mut next_fvar = FVAR_BASE + 41_000_000;
        let mut fresh = || {
            next_fvar += 1;
            next_fvar
        };

        // wire_ty := (x y fuel : Nat) -> (hy : Nat.lt Nat.zero y) ->
        //   (hle : Nat.le y x) -> (hfuel : Nat.lt x (Nat.succ fuel)) ->
        //   Nat.lt (Nat.sub x y) fuel
        let nat_ty = kernel.const_(prelude.nat, vec![]);
        let x_fv = fresh();
        let x = kernel.fvar(x_fv);
        let y_fv = fresh();
        let y = kernel.fvar(y_fv);
        let fuel_fv = fresh();
        let fuel = kernel.fvar(fuel_fv);
        let hy_fv = fresh();
        let hle_fv = fresh();
        let hfuel_fv = fresh();

        let zero_c = kernel.const_(prelude.zero, vec![]);
        let lt_zero_y = {
            let c = kernel.const_(prelude.lt, vec![]);
            let w1 = kernel.app(c, zero_c);
            kernel.app(w1, y)
        };
        let le_y_x = {
            let c = kernel.const_(prelude.le, vec![]);
            let w1 = kernel.app(c, y);
            kernel.app(w1, x)
        };
        let succ_fuel = {
            let c = kernel.const_(prelude.succ, vec![]);
            kernel.app(c, fuel)
        };
        let lt_x_succ_fuel = {
            let c = kernel.const_(prelude.lt, vec![]);
            let w1 = kernel.app(c, x);
            kernel.app(w1, succ_fuel)
        };
        let concl = {
            let sub_xy = {
                let c = kernel.const_(prelude.sub, vec![]);
                let w1 = kernel.app(c, x);
                kernel.app(w1, y)
            };
            let c = kernel.const_(prelude.lt, vec![]);
            let w1 = kernel.app(c, sub_xy);
            kernel.app(w1, fuel)
        };

        let mut wire_ty = concl;
        let abstracted = kernel.abstract_fvars(wire_ty, &[hfuel_fv]);
        wire_ty = kernel.pi(anon, lt_x_succ_fuel, abstracted, BinderInfo::Default);
        let abstracted = kernel.abstract_fvars(wire_ty, &[hle_fv]);
        wire_ty = kernel.pi(anon, le_y_x, abstracted, BinderInfo::Default);
        let abstracted = kernel.abstract_fvars(wire_ty, &[hy_fv]);
        wire_ty = kernel.pi(anon, lt_zero_y, abstracted, BinderInfo::Default);
        let abstracted = kernel.abstract_fvars(wire_ty, &[fuel_fv]);
        wire_ty = kernel.pi(anon, nat_ty, abstracted, BinderInfo::Default);
        let abstracted = kernel.abstract_fvars(wire_ty, &[y_fv]);
        wire_ty = kernel.pi(anon, nat_ty, abstracted, BinderInfo::Default);
        let abstracted = kernel.abstract_fvars(wire_ty, &[x_fv]);
        wire_ty = kernel.pi(anon, nat_ty, abstracted, BinderInfo::Default);

        let value = reconstruct(&mut kernel, "Nat.div_rec_fuel_lemma", wire_ty)
            .unwrap_or_else(|e| panic!("Nat.div_rec_fuel_lemma: reconstruction declined: {e}"))
            .unwrap_or_else(|| panic!("Nat.div_rec_fuel_lemma: not recognised as substitutable"));
        let inferred = kernel
            .infer(value)
            .unwrap_or_else(|e| panic!("Nat.div_rec_fuel_lemma: candidate failed to infer: {e:?}"));
        assert!(
            kernel.def_eq(inferred, wire_ty),
            "Nat.div_rec_fuel_lemma: candidate's type is not def-eq to wire_ty"
        );

        let fresh_name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDivRecFuelLemma")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name: fresh_name,
                uparams: vec![],
                ty: wire_ty,
                value,
            })
            .unwrap_or_else(|e| panic!("Nat.div_rec_fuel_lemma: admission failed: {e:?}"));
        assert_eq!(
            kernel.axiom_footprint(fresh_name).len(),
            0,
            "Nat.div_rec_fuel_lemma: nonempty axiom footprint"
        );
        assert_eq!(
            kernel.theorem_dependencies(fresh_name).len(),
            0,
            "Nat.div_rec_fuel_lemma: cites another theorem: {:?}",
            kernel
                .theorem_dependencies(fresh_name)
                .iter()
                .map(|&n| kernel.display_name(n).to_string())
                .collect::<Vec<_>>()
        );
    }

    // The "`And` absent" case for `Nat.div_rec_lemma` cannot be exercised
    // through the public `reconstruct` entry point against `prelude_kernel`
    // — it always carries a real `And` (from `build_logic_prelude`, which
    // `build_nat_prelude_uncached` always runs first), exactly like a real
    // archive kernel with any `Nat` import always does. It is covered
    // directly at the gate instead, in
    // `names_needing_an_absent_optional_prim_are_refused_gracefully`
    // (`and_missing`), which injects a `Prims` with `and_: None` — the same
    // technique already used there for `pred`/`sub`/`ble`.

    #[test]
    fn unrecognised_name_declines_with_ok_none() {
        let (mut kernel, _prelude) = prelude_kernel();
        let wire_ty = kernel.sort_zero();
        assert!(matches!(
            reconstruct(&mut kernel, "Nat.frobnicate", wire_ty),
            Ok(None)
        ));
    }

    /// The independent validation guard: a candidate whose type does not
    /// match `wire_ty` must be REFUSED, never coerced. Mutation target: the
    /// `if !kernel.def_eq(...)` check inside [`reconstruct`].
    #[test]
    fn mismatched_wire_ty_is_refused_not_coerced() {
        let (mut kernel, prelude) = prelude_kernel();
        // `Nat.le_succ`'s own type (`∀ n, Le n (succ n)`) is a real Pi type
        // but the WRONG one for `Nat.le_refl` (`∀ n, Le n n`) — same
        // quantifier shape, different conclusion, so a coercion bug would
        // admit it silently rather than crash.
        let wrong_wire_ty = kernel
            .environment()
            .get(prelude.le_succ)
            .expect("declared")
            .ty();
        assert!(matches!(
            reconstruct(&mut kernel, "Nat.le_refl", wrong_wire_ty),
            Err(SubstitutionError::UnexpectedShape(_))
        ));
    }

    #[test]
    fn missing_primitive_declines_with_required_declaration_unavailable() {
        // A kernel with no `Nat` at all cannot discover any primitive this
        // module depends on.
        let mut kernel = Kernel::new();
        let wire_ty = kernel.sort_zero();
        assert!(matches!(
            reconstruct(&mut kernel, "Nat.le_refl", wire_ty),
            Err(SubstitutionError::RequiredDeclarationUnavailable(_))
        ));
    }

    /// Exhaustive classification test for [`required_optional_prims`] — the
    /// exact per-name mapping the lazy-discovery fix depends on. Cross-checked
    /// by hand against every match arm in [`build`]/[`build_sub_lt`]/
    /// [`build_le_of_ble_eq_true`] for which of `Nat.pred`/`Nat.sub`/`Nat.ble`
    /// they call. `Nat.zero_le` mapping to `(false, false, false)` is the
    /// specific claim the regression is about: it is on
    /// [`SUBSTITUTABLE_NAT_ORDER_THEOREMS`] and its own construction
    /// ([`B::zero_le_value`]) never touches `pred`/`sub`/`ble`, so its
    /// reconstruction must not depend on any of the three being discoverable.
    #[test]
    fn required_optional_prims_matches_each_names_own_construction() {
        let needs_nothing = [
            "Nat.le_trans",
            "Nat.le_refl",
            "Nat.le_succ",
            "Nat.succ_le_succ",
            "Nat.le_of_lt_succ",
            "Nat.lt_succ_self",
            "Nat.lt_succ_of_le",
            "Nat.lt_add_one",
            "Nat.lt_irrefl",
            "Nat.not_succ_le_self",
            "Nat.not_succ_le_zero",
            "Nat.le_succ_of_le",
            "Nat.zero_lt_succ",
            "Nat.zero_le",
            "Nat.lt_of_lt_of_le",
            "Nat.le_of_succ_le_succ",
            "Nat.le_of_lt_add_one",
        ];
        for name in needs_nothing {
            assert_eq!(
                required_optional_prims(name),
                (false, false, false, false),
                "{name}: expected to need none of pred/sub/ble/and"
            );
        }

        for name in ["Nat.pred_le", "Nat.pred_le_pred"] {
            assert_eq!(
                required_optional_prims(name),
                (true, false, false, false),
                "{name}: expected pred only"
            );
        }

        for name in ["Nat.sub_le", "Nat.sub_lt", "Nat.succ_sub_succ_eq_sub"] {
            assert_eq!(
                required_optional_prims(name),
                (true, true, false, false),
                "{name}: expected pred and sub"
            );
        }

        for name in [
            "Nat.ble_self_eq_true",
            "Nat.ble_succ_eq_true",
            "Nat.ble_eq_true_of_le",
            "Nat.le_of_ble_eq_true",
            "Nat.not_le_of_not_ble_eq_true",
        ] {
            assert_eq!(
                required_optional_prims(name),
                (false, false, true, false),
                "{name}: expected ble only"
            );
        }

        assert_eq!(
            required_optional_prims("Nat.div_rec_lemma"),
            (true, true, false, true),
            "Nat.div_rec_lemma: expected pred, sub, and and"
        );
        assert_eq!(
            required_optional_prims("Nat.div_rec_fuel_lemma"),
            (true, true, false, true),
            "Nat.div_rec_fuel_lemma: expected pred, sub, and and (same as Nat.div_rec_lemma)"
        );

        // Every name in the substitution list is covered by exactly one of
        // the five groups above — this closes the loop against the list
        // drifting out of sync with the classification.
        for &name in SUBSTITUTABLE_NAT_ORDER_THEOREMS {
            let (pred, sub, ble, and_) = required_optional_prims(name);
            assert!(
                !sub || pred,
                "{name}: every name needing sub also needs pred in this module's constructions"
            );
            assert!(
                !and_ || (pred && sub),
                "{name}: every name needing and also needs pred and sub (it composes sub_lt)"
            );
            let _ = ble;
        }
    }

    /// The lazy-discovery fix itself, exercised end-to-end through the real
    /// production code path ([`build`]) rather than a re-implementation:
    /// take a genuine [`Prims`] from a fully-populated kernel (so `pred`,
    /// `sub`, and `ble` really do exist), then force them all to `None` —
    /// simulating a stream where none of the three has been declared yet —
    /// and confirm every name [`required_optional_prims`] says needs none of
    /// them still reconstructs and kernel-checks. Before the fix, `discover`
    /// itself would have failed outright the moment `Nat.pred` was missing,
    /// for every one of these names, regardless of whether they use it.
    #[test]
    fn names_needing_no_optional_prim_reconstruct_even_when_all_three_are_absent() {
        let (mut kernel, prelude) = prelude_kernel();
        let full_prims = discover(&kernel).expect("full prelude carries every primitive");
        let starved_prims = Prims {
            pred: None,
            sub: None,
            ble: None,
            ..full_prims
        };

        for &rendered in SUBSTITUTABLE_NAT_ORDER_THEOREMS {
            let (needs_pred, needs_sub, needs_ble, needs_and) = required_optional_prims(rendered);
            if needs_pred || needs_sub || needs_ble || needs_and {
                continue;
            }
            let mut b = B::new(&mut kernel, &starved_prims);
            let value = build(&mut b, rendered).unwrap_or_else(|e| {
                panic!("{rendered}: expected to reconstruct without pred/sub/ble, got {e}")
            });
            let existing = field_name(&prelude, rendered);
            let wire_ty = kernel.environment().get(existing).expect("declared").ty();
            let inferred = kernel
                .infer(value)
                .unwrap_or_else(|e| panic!("{rendered}: candidate failed to infer: {e:?}"));
            assert!(
                kernel.def_eq(inferred, wire_ty),
                "{rendered}: candidate's type is not def-eq to wire_ty"
            );
        }
    }

    /// The other half of the fix: a name that DOES need one of the optional
    /// primitives must still be refused — via the graceful
    /// `RequiredDeclarationUnavailable`, never a panic — when that primitive
    /// is genuinely absent. This is [`check_required_optional_prims`] tested
    /// directly, which is also the mutation target: comment out any one of
    /// its three `if` arms and the corresponding case below fails (its
    /// `Ok(())` is no longer refused).
    #[test]
    fn names_needing_an_absent_optional_prim_are_refused_gracefully() {
        let (kernel, _prelude) = prelude_kernel();
        let full_prims = discover(&kernel).expect("full prelude carries every primitive");

        let pred_missing = Prims {
            pred: None,
            ..full_prims
        };
        assert!(matches!(
            check_required_optional_prims(&pred_missing, "Nat.pred_le"),
            Err(SubstitutionError::RequiredDeclarationUnavailable(
                "Nat.pred"
            ))
        ));
        // sub_le needs BOTH pred and sub; with only sub missing it must still
        // be refused, naming the primitive that is actually absent.
        let sub_missing = Prims {
            sub: None,
            ..full_prims
        };
        assert!(matches!(
            check_required_optional_prims(&sub_missing, "Nat.sub_le"),
            Err(SubstitutionError::RequiredDeclarationUnavailable("Nat.sub"))
        ));
        let ble_missing = Prims {
            ble: None,
            ..full_prims
        };
        assert!(matches!(
            check_required_optional_prims(&ble_missing, "Nat.ble_self_eq_true"),
            Err(SubstitutionError::RequiredDeclarationUnavailable("Nat.ble"))
        ));
        // `Nat.div_rec_lemma` needs `pred`/`sub` too (it composes `sub_lt`),
        // so give it those and withhold only `and_` to isolate the fourth
        // guard.
        let and_missing = Prims {
            and_: None,
            ..full_prims
        };
        assert!(matches!(
            check_required_optional_prims(&and_missing, "Nat.div_rec_lemma"),
            Err(SubstitutionError::RequiredDeclarationUnavailable("And"))
        ));

        // The unaffected case: a name that needs nothing must never be
        // refused, no matter which optional primitives are missing.
        let all_missing = Prims {
            pred: None,
            sub: None,
            ble: None,
            and_: None,
            ..full_prims
        };
        assert!(check_required_optional_prims(&all_missing, "Nat.zero_le").is_ok());
    }
}

/// `Nat.le_of_lt_add_one` at the type Mathlib v4.30 actually exports, against
/// the pinned `lean4export` stream of the real declaration and its whole
/// closure (ADR-1667). Committed rather than read from a host-local archive
/// precisely because the SPELLING is the thing under test: the census rows
/// this unblocks are refused for a type written with the order typeclasses
/// (`LT.lt Nat instLTNat n (HAdd.hAdd .. m 1)`), not the bare `Nat.le`
/// shape this project's own prelude uses.
#[cfg(test)]
mod real_mathlib_type_tests {
    use super::*;
    use crate::{ImportLimits, import_ndjson};
    use std::io::Cursor;

    const LE_OF_LT_ADD_ONE_FIXTURE: &str =
        include_str!("../../../docs/plan/fixtures/lean4export-v4.30-nat-le-of-lt-add-one.ndjson");

    fn fixture_kernel() -> Kernel {
        let completed = import_ndjson(
            Cursor::new(LE_OF_LT_ADD_ONE_FIXTURE.as_bytes()),
            ImportLimits::default(),
        )
        .expect("pinned Mathlib fixture must import");
        completed.into_parts().0
    }

    fn wire_ty_of(kernel: &Kernel, rendered: &str) -> ExprId {
        kernel
            .environment()
            .iter()
            .find(|(name, decl)| {
                matches!(decl, Declaration::Theorem { .. })
                    && kernel.display_name(**name).to_string() == rendered
            })
            .map(|(_, decl)| decl.ty())
            .unwrap_or_else(|| panic!("{rendered} is not a Theorem in the fixture"))
    }

    /// POSITIVE control.
    #[test]
    fn le_of_lt_add_one_reconstructs_against_the_real_mathlib_type() {
        let mut kernel = fixture_kernel();
        let wire_ty = wire_ty_of(&kernel, "Nat.le_of_lt_add_one");
        let value = reconstruct(&mut kernel, "Nat.le_of_lt_add_one", wire_ty)
            .expect("reconstruction must not decline")
            .expect("Nat.le_of_lt_add_one must be recognised as substitutable");
        let inferred = kernel.infer(value).expect("candidate must infer");
        assert!(
            kernel.def_eq(inferred, wire_ty),
            "candidate's type is not def-eq to Mathlib's own declared type"
        );
        let fresh_name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestRealLeOfLtAddOne")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name: fresh_name,
                uparams: vec![],
                ty: wire_ty,
                value,
            })
            .expect("reconstructed Nat.le_of_lt_add_one must kernel-check");
        assert_eq!(kernel.axiom_footprint(fresh_name).len(), 0);
        assert_eq!(
            kernel.theorem_dependencies(fresh_name).len(),
            0,
            "the reconstruction must cite no theorem: {:?}",
            kernel
                .theorem_dependencies(fresh_name)
                .iter()
                .map(|&n| kernel.display_name(n).to_string())
                .collect::<Vec<_>>()
        );
    }

    /// NEGATIVE control at the KERNEL, with this module's own `def_eq` guard
    /// bypassed: the reconstructed value is admitted directly at
    /// `Nat.le_succ`'s type (`forall n, n <= n + 1`, a real theorem in the
    /// same fixture and a real Pi over `Nat`), which it does not prove. Only
    /// the kernel can refuse this — nothing in `reconstruct` runs.
    #[test]
    fn the_value_at_another_fixture_theorems_type_is_refused_by_the_kernel() {
        let mut kernel = fixture_kernel();
        let wire_ty = wire_ty_of(&kernel, "Nat.le_of_lt_add_one");
        let value = reconstruct(&mut kernel, "Nat.le_of_lt_add_one", wire_ty)
            .expect("reconstruction must not decline")
            .expect("must be substitutable");
        let wrong_ty = wire_ty_of(&kernel, "Nat.le_succ");
        let fresh_name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestRealLeOfLtAddOneWrongType")
        };
        let outcome = kernel.add_declaration(Declaration::Theorem {
            name: fresh_name,
            uparams: vec![],
            ty: wrong_ty,
            value,
        });
        assert!(
            outcome.is_err(),
            "the kernel must refuse the value at Nat.le_succ's type, got {outcome:?}"
        );
    }

    /// NEGATIVE control at this module's own validation guard: offering a
    /// mismatched `wire_ty` must make [`reconstruct`] DECLINE rather than
    /// coerce. Mutation target: the `def_eq` check inside `reconstruct`.
    #[test]
    fn a_mismatched_wire_ty_makes_reconstruct_decline() {
        let mut kernel = fixture_kernel();
        let wrong_ty = wire_ty_of(&kernel, "Nat.le_succ");
        assert!(matches!(
            reconstruct(&mut kernel, "Nat.le_of_lt_add_one", wrong_ty),
            Err(SubstitutionError::UnexpectedShape(_))
        ));
    }
}

#[cfg(test)]
mod real_stream_tests {
    //! Not run by default (reads the frozen census archive, host-local under
    //! `/nas3`, not part of this repository). Run explicitly with
    //! `cargo test -p axeyum-lean-import --lib nat_order_substitution::real_stream_tests -- --ignored --nocapture`,
    //! optionally overriding the directory with
    //! `AXEYUM_NAT_ORDER_PROBE_DIR`. This is the mechanism the census
    //! re-run's per-name success/failure table was produced with.
    use super::*;
    use crate::{ImportLimits, import_ndjson};
    use axeyum_lean_kernel::Kernel;
    use std::collections::BTreeMap;
    use std::fs::File;
    use std::io::BufReader;

    const DEFAULT_DIR: &str = "/nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams";

    fn wire_ty_of(kernel: &Kernel, rendered: &str) -> Option<ExprId> {
        kernel
            .environment()
            .iter()
            .find(|(name, decl)| {
                matches!(decl, Declaration::Theorem { .. })
                    && kernel.display_name(**name).to_string() == rendered
            })
            .map(|(_, decl)| decl.ty())
    }

    #[test]
    #[ignore = "reads the frozen census archive under /nas3, not part of this repository"]
    fn probe_real_archive() {
        let dir =
            std::env::var("AXEYUM_NAT_ORDER_PROBE_DIR").unwrap_or_else(|_| DEFAULT_DIR.into());
        let mut entries: Vec<_> = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("read_dir {dir}: {e}"))
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|ext| ext == "ndjson"))
            .collect();
        entries.sort();
        assert!(!entries.is_empty(), "no .ndjson files found under {dir}");

        let mut present: BTreeMap<&str, u32> = BTreeMap::new();
        let mut ok: BTreeMap<&str, u32> = BTreeMap::new();
        let mut failed: BTreeMap<&str, Vec<String>> = BTreeMap::new();

        for path in &entries {
            let file = File::open(path).unwrap_or_else(|e| panic!("open {path:?}: {e}"));
            let reader = BufReader::new(file);
            let Ok(completed) = import_ndjson(reader, ImportLimits::default()) else {
                continue;
            };
            let (mut kernel, _report) = completed.into_parts();
            for &rendered in SUBSTITUTABLE_NAT_ORDER_THEOREMS {
                let Some(wire_ty) = wire_ty_of(&kernel, rendered) else {
                    continue;
                };
                *present.entry(rendered).or_default() += 1;
                match reconstruct(&mut kernel, rendered, wire_ty) {
                    Ok(Some(value)) => {
                        // Independently re-verify: infer + def_eq against
                        // `wire_ty` (the exact discipline `reconstruct`
                        // itself already applied), THEN actually admit under
                        // a synthetic name and require an empty axiom
                        // footprint against THIS REAL STREAM's own
                        // environment — not just this project's own prelude
                        // (see the fast `tests` module for that check).
                        let inferred = kernel
                            .infer(value)
                            .unwrap_or_else(|e| panic!("{path:?} {rendered}: {e:?}"));
                        assert!(
                            kernel.def_eq(inferred, wire_ty),
                            "{path:?} {rendered}: re-inferred type not def-eq to wire_ty"
                        );
                        let probe_name = {
                            let root = kernel.anon();
                            kernel.name_str(root, format!("ProbeReconstruct_{rendered}"))
                        };
                        kernel
                            .add_declaration(Declaration::Theorem {
                                name: probe_name,
                                uparams: vec![],
                                ty: wire_ty,
                                value,
                            })
                            .unwrap_or_else(|e| {
                                panic!("{path:?} {rendered}: admission failed: {e:?}")
                            });
                        let footprint = kernel.axiom_footprint(probe_name);
                        assert!(
                            footprint.is_empty(),
                            "{path:?} {rendered}: nonempty axiom footprint {footprint:?}"
                        );
                        // Axiom-free is not "cites no theorem" (a theorem
                        // dependency can itself be axiom-free) — require the
                        // stronger, machine-checked claim against THIS REAL
                        // STREAM's own environment: no admitted Theorem
                        // (this stream's `Nat.le_trans` included) appears
                        // anywhere in the dependency closure.
                        let theorem_deps = kernel.theorem_dependencies(probe_name);
                        assert!(
                            theorem_deps.is_empty(),
                            "{path:?} {rendered}: cites another theorem: {:?}",
                            theorem_deps
                                .iter()
                                .map(|&n| kernel.display_name(n).to_string())
                                .collect::<Vec<_>>()
                        );
                        *ok.entry(rendered).or_default() += 1;
                    }
                    Ok(None) => unreachable!("rendered is in SUBSTITUTABLE_NAT_ORDER_THEOREMS"),
                    Err(e) => {
                        failed
                            .entry(rendered)
                            .or_default()
                            .push(format!("{path:?}: {e}"));
                    }
                }
            }
        }

        println!("files: {}", entries.len());
        for &rendered in SUBSTITUTABLE_NAT_ORDER_THEOREMS {
            let p = present.get(rendered).copied().unwrap_or(0);
            let o = ok.get(rendered).copied().unwrap_or(0);
            println!("{rendered}: present={p} ok={o}");
            if let Some(errs) = failed.get(rendered) {
                for e in errs.iter().take(2) {
                    println!("    decline: {e}");
                }
            }
        }
    }
}
