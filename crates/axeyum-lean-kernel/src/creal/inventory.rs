//! Per-module `CReal` declaration inventory, sharded so that a lane adding a
//! declaration to one `creal/` module edits exactly one file under
//! `creal/inventory/` — never the shared array this replaces.
//!
//! # Why this exists
//!
//! `creal_tests.rs` used to carry a single pinned
//! `let expected: [(&str, crate::NameId, &str); 432] = [ ... ];` covering
//! every `CReal` declaration. Every lane adding *any* declaration anywhere in
//! `creal/` had to edit that one array, so every pair of concurrent `creal`
//! lanes collided on it — the pin conflicted or was merge-damaged eight-plus
//! times in one day (`CLAUDE.md`'s multi-agent hygiene section has the
//! incident list, including the zero-conflict trap where two correct
//! increments merged cleanly into a stale count).
//!
//! The fix: one shard per `creal/` source module (plus `base` for the base
//! algebra declared directly in `creal.rs`, rather than through a
//! `creal/*.rs` submodule), each owned by whoever is already editing that
//! module. Adding a declaration to an EXISTING module means editing that
//! module's shard file ONLY. Adding a brand-new `creal/` module means two
//! one-line, order-insensitive additions here (a `mod` line and an
//! `all.extend(...)` line) — see the module list below, which is why it is
//! kept alphabetical: two lanes adding different new modules touch different
//! lines and merge without conflict. (Named `base`, not `core`, to avoid
//! shadowing the `core` crate inside this module's own namespace.)
//!
//! # Coverage, not counting
//!
//! No shard carries a pinned length. The count that used to guard against a
//! forgotten registration is superseded by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`, which
//! derives coverage from `kernel.environment()` directly — in both
//! directions, plus a check that no declaration is claimed by more than one
//! shard (impossible with a single array, newly possible now that there are
//! many).

mod alternating;
mod archimedean;
mod archimedean_squeeze;
mod base;
mod cancellation;
mod completeness;
mod congruence;
mod convergence;
mod cos_sign;
mod cotransitivity;
mod crossing;
mod density;
mod deriv_unique;
mod derivative;
mod evt_row1;
mod exp_fn;
mod exponential;
mod extreme_value;
mod fermat;
mod field;
mod geometric;
mod integral;
mod inverse;
mod inverse_fn;
mod ivt;
mod ivt_boundary;
mod lattice;
mod lub_boundary;
mod monotone;
mod mul_self_zero;
mod mvt;
mod order_extra;
mod pi;
mod polynomial;
mod power;
mod product;
mod ratio_test;
mod rolle;
mod series;
mod speedup;
mod sqrt;
mod sup_laws;
mod supremum;
mod trig;
mod trig_fn;
mod uniform_continuity;
mod uniform_convergence;

/// The union of every shard, in shard-registration order (irrelevant to the
/// coverage/duplicate checks in `creal_tests.rs`, which treat this as a set).
pub(crate) fn all_entries(
    p: crate::CRealPrelude,
) -> Vec<(&'static str, crate::NameId, &'static str)> {
    let mut all = Vec::new();
    all.extend(alternating::entries(p));
    all.extend(archimedean::entries(p));
    all.extend(archimedean_squeeze::entries(p));
    all.extend(base::entries(p));
    all.extend(cancellation::entries(p));
    all.extend(completeness::entries(p));
    all.extend(congruence::entries(p));
    all.extend(convergence::entries(p));
    all.extend(cos_sign::entries(p));
    all.extend(cotransitivity::entries(p));
    all.extend(crossing::entries(p));
    all.extend(density::entries(p));
    all.extend(deriv_unique::entries(p));
    all.extend(derivative::entries(p));
    all.extend(evt_row1::entries(p));
    all.extend(exp_fn::entries(p));
    all.extend(exponential::entries(p));
    all.extend(extreme_value::entries(p));
    all.extend(fermat::entries(p));
    all.extend(field::entries(p));
    all.extend(geometric::entries(p));
    all.extend(integral::entries(p));
    all.extend(inverse::entries(p));
    all.extend(inverse_fn::entries(p));
    all.extend(ivt::entries(p));
    all.extend(ivt_boundary::entries(p));
    all.extend(lattice::entries(p));
    all.extend(lub_boundary::entries(p));
    all.extend(monotone::entries(p));
    all.extend(mul_self_zero::entries(p));
    all.extend(mvt::entries(p));
    all.extend(order_extra::entries(p));
    all.extend(pi::entries(p));
    all.extend(polynomial::entries(p));
    all.extend(power::entries(p));
    all.extend(product::entries(p));
    all.extend(ratio_test::entries(p));
    all.extend(rolle::entries(p));
    all.extend(series::entries(p));
    all.extend(speedup::entries(p));
    all.extend(sqrt::entries(p));
    all.extend(sup_laws::entries(p));
    all.extend(supremum::entries(p));
    all.extend(trig::entries(p));
    all.extend(trig_fn::entries(p));
    all.extend(uniform_continuity::entries(p));
    all.extend(uniform_convergence::entries(p));
    all
}
