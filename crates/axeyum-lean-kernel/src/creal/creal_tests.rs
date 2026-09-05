//! Tests for the real (setoid) prelude.

use super::inventory;
use super::{CRealPrelude, build_creal_prelude};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{Declaration, Kernel, on_a_deep_stack};

/// A built `CReal` kernel, as a **clone of one template**.
///
/// The full development is now 96 declarations over the constructed ℚ and takes
/// tens of seconds to type-check; seventeen tests each building it from scratch
/// dominated this crate's test time. The argument for cloning is
/// [`prelude_cache`](crate::prelude_cache)'s, verbatim: prelude construction is
/// a deterministic function of the empty kernel, so the template equals what a
/// fresh build would produce, and every declaration in it entered through
/// `Kernel::add_declaration` under the full type checker exactly once.
/// `creal_prelude_builds` deliberately does **not** use this — it is the test
/// that exercises the real build.
pub(super) fn built() -> (Kernel, CRealPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, CRealPrelude)> = OnceLock::new();
    // Run on a deep stack: whichever test happens to be the first (in
    // execution order, not file order) to call `built()` pays the FULL
    // `build_creal_prelude` cost on top of the clone below, and after
    // `CReal.mul_self_sqrt` landed that combination overflows the default
    // 2 MiB test-thread stack for a test with no reasoning of its own about
    // `mul_self_sqrt` -- `abs_add_le_at_one_and_neg_one_has_slack` SIGABRTed
    // this way, on the default stack, in both single- and multi-threaded
    // runs, and passed clean with a bigger stack and in `--release` (the
    // discriminator this file's own module docs elsewhere use: a genuine
    // margin overrun disappears under either, runaway recursion does not).
    // Every call is wrapped, not just the build -- the clone that runs on
    // EVERY call is itself not free to assume is shallow just because one
    // caller's stack happened to survive it. Uses the crate's shared
    // `on_a_deep_stack` (256 MiB, ADR-0584) rather than a local copy -- this
    // file used to carry its own 1 GiB thread-spawning helper, unexplained
    // and never re-measured against the shared constant.
    on_a_deep_stack(move || {
        let (kernel, prelude) = TEMPLATE.get_or_init(|| {
            let mut kernel = Kernel::new();
            let prelude = build_creal_prelude(&mut kernel).expect("CReal prelude must build");
            (kernel, prelude)
        });
        (kernel.clone(), *prelude)
    })
}

/// The build itself, with the kernel's rejection **rendered**. A `Debug` of
/// `KernelError` says nothing about what was refused; this says which two types
/// failed to match.
///
/// Runs on [`on_a_deep_stack`] like every other call in this file. It once did
/// not: `creal` in debug needs **exactly** the default 2 MiB `#[test]` thread
/// stack (`artifacts/kernel-stack-envelope.tsv`, ADR-0584), so this was the
/// test with zero margin left over for anything a future declaration might
/// add, and its purpose — "does the trusted gate accept this proof" — has
/// nothing to do with how much stack the type checker's recursion happens to
/// need. `scripts/check-kernel-stack-envelope.sh` is the dedicated,
/// self-demonstrating measurement of that envelope (it bisects and proves it
/// can fail); this test is not a substitute stack canary and should not block
/// the whole debug suite — and therefore `just check`, and therefore
/// publication — over a margin question this test was never designed to
/// answer.
#[test]
fn creal_prelude_builds() {
    on_a_deep_stack(creal_prelude_builds_body);
}

fn creal_prelude_builds_body() {
    let mut kernel = Kernel::new();
    match build_creal_prelude(&mut kernel) {
        Ok(_) => {}
        Err(error) => {
            let nat = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
            let mut dev = crate::NatDev::new(&mut kernel, nat);
            let explained = crate::NatOps::explain(&mut dev, &error);
            panic!("the kernel refused a real proof: {explained}");
        }
    }
}

/// **ADR-0512's headline claim, measured.** A Bishop setoid over `ℚ` costs zero
/// trusted declarations: no `Quot.sound`, no `funext`, no `propext`, no
/// classical axiom, nothing.
#[test]
fn the_constructed_reals_add_no_trusted_declaration() {
    let (kernel, _) = built();
    let trusted: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(kernel.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    assert!(
        trusted.is_empty(),
        "the real construction must assume nothing, found: {trusted:?}"
    );
}

/// Every declaration is the kind it claims to be and has an empty axiom
/// footprint, read out of the kernel rather than off the diff.
///
/// This test rebuilds the whole constructed environment and walks every
/// declaration's `axiom_footprint`. Once `CReal.e` landed, that recursion
/// exceeded the default 2 MiB stack and the test SIGABRTed -- a resource
/// limit, not a soundness problem, and the same class as the one that makes
/// `prelude_theorem_inventory` require `--release`.
///
/// Runs on [`on_a_deep_stack`]'s shared 256 MiB thread (ADR-0584) rather than
/// a bespoke size for this one test, and carries the stack EXPLICITLY rather
/// than relying on an ambient `RUST_MIN_STACK`. A lane once reported a suite
/// green that only passed because it had that variable exported from an
/// earlier hand-bisect; the same test SIGABRTed in a clean shell. A test whose
/// result depends on an ambient environment variable is a gate on one shell,
/// and this particular test is the guard that every `CReal` declaration is
/// derived and axiom-free -- the last one that should silently stop running.
#[test]
fn every_creal_declaration_is_checked_and_axiom_free() {
    on_a_deep_stack(every_creal_declaration_is_checked_and_axiom_free_body);
}

fn every_creal_declaration_is_checked_and_axiom_free_body() {
    let (kernel, p) = built();

    // The union of every per-module shard under `creal/inventory/` -- see
    // that module's docs for why the single 432-entry array this replaced
    // was sharded, and why sharding does not weaken this check.
    let all: Vec<(&str, crate::NameId, &str)> = inventory::all_entries(p);

    // DUPLICATE CHECK, new with the sharding: a single array could not name
    // one NameId twice under two different labels without the second
    // `for` loop below simply checking the same declaration redundantly.
    // Many shards CAN, if two lanes editing different modules both claim
    // the same declaration (or one lane copies another's entry instead of
    // moving it). Detected against the RAW list, before anything is
    // deduplicated into a set.
    let mut claimed_by: std::collections::BTreeMap<crate::NameId, &str> =
        std::collections::BTreeMap::new();
    let mut duplicates: Vec<String> = Vec::new();
    for (label, name, _) in &all {
        if let Some(&first_label) = claimed_by.get(name) {
            duplicates.push(format!(
                "{name:?} claimed by both `{first_label}` and `{label}`"
            ));
        } else {
            claimed_by.insert(*name, label);
        }
    }
    assert!(
        duplicates.is_empty(),
        "a `CReal` declaration is listed in more than one inventory shard, so \
         its `NameId` no longer identifies a single owning module: \
         {duplicates:?}"
    );

    // COVERAGE, checked against the ENVIRONMENT rather than against this list.
    //
    // Without this, the loop below only ever inspects declarations someone
    // remembered to add to some shard, while the test's name promises *every*
    // `CReal` declaration. Measured 2026-08-26 (before sharding): five
    // declarations (`CReal.expDominant` and its four domination lemmas) were
    // live in the prelude and absent from the single `expected` array, so
    // they received no `Theorem`-kind check and no axiom-footprint check at
    // all -- and every run was green, because a list cannot notice what is
    // missing from it. Sharding the array into many files does not change
    // this argument; the union is still just a list unless it is checked
    // against what was actually declared.
    //
    // The pinned length alone never caught this either: it constrains the
    // list against itself, not against what was declared. No shard carries a
    // pinned length now -- see `creal/inventory.rs`'s module docs for why
    // that pin is no longer load-bearing once this assertion exists.
    let listed: std::collections::BTreeSet<crate::NameId> =
        all.iter().map(|(_, name, _)| *name).collect();
    let declared: Vec<crate::NameId> = kernel.environment().iter().map(|(name, _)| *name).collect();
    let unlisted: Vec<String> = declared
        .into_iter()
        .map(|name| (name, kernel.display_name(name).to_string()))
        .filter(|(name, shown)| shown.starts_with("CReal") && !listed.contains(name))
        .map(|(_, shown)| shown)
        .collect();
    assert!(
        unlisted.is_empty(),
        "these `CReal` declarations are live in the prelude but absent from \
         every inventory shard, so nothing checks that they are derived and \
         axiom-free: {unlisted:?}. Add each to the shard file for the \
         `creal/` module that declares it (`creal/inventory/<module>.rs`) --\
         do not delete this assertion."
    );

    for (label, name, kind) in all {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} was interned but never declared"));
        match kind {
            "theorem" => assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "{label} must be a checked Theorem"
            ),
            "def" => assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "{label} must be a Definition"
            ),
            _ => {}
        }
        assert!(
            !matches!(
                declaration,
                Declaration::Axiom { .. } | Declaration::Opaque { .. }
            ),
            "{label} is asserted, not derived"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "{label} rests on {footprint:?}");
    }
}

/// **`CReal.sumRange_tail_within` on a trivial instance**: `f = g` the
/// constant-zero sequence, `m = n = 0`. Not a soundness check on its own
/// (the general theorem is already proved for every `f g m n`, so any
/// instance holds) — it is the sanity check the module documentation's
/// "series.rs" retrospective on `nra_monomial_bound_cert.rs`-style vacuity
/// asks for: instantiate the theorem's own conclusion at a fully CONCRETE,
/// CLOSED term and have the kernel independently `infer` its type, rather
/// than trusting that a universally-quantified statement that type-checks
/// is the statement intended. `Kernel::infer` requires a closed term
/// (`tests.rs::inference_caches_only_closed_successes` pins that an
/// unregistered free variable is refused), which is exactly why this test
/// closes the pointwise hypothesis and both indices to ground terms instead
/// of leaving `f` a free variable.
#[test]
fn sum_range_tail_within_specializes_to_the_zero_series_against_itself() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();

    // zero_fn := λ _ : Nat, CReal.zero.
    let zero_fn = {
        let k_fv = d.fresh_fvar();
        let _k = d.kernel().fvar(k_fv);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        d.lam_fv(k_fv, nat, zero_c)
    };
    let zero_nat = d.num(0);

    // pointwise : ∀ k, le (abs (zero_fn k)) (zero_fn k), via le_abs_self.
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zk = d.apply(zero_fn, &[k]);
        let body = d.lemma(p.le_abs_self, &[zk]);
        d.lam_fv(k_fv, nat, body)
    };

    let instance = d.lemma(
        p.sum_range_tail_within,
        &[zero_fn, zero_fn, zero_nat, zero_nat, pointwise],
    );

    let inferred = d.kernel().infer(instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!(
            "sumRange_tail_within refused at the trivial f = g = (fun _ => zero), \
             m = n = 0 instance: {error:?}"
        )
    });

    // Not just well-typed: the conclusion the kernel infers is genuinely a
    // `Within` bound, not e.g. `True` or some other vacuous stand-in.
    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Within"),
        "the instantiated conclusion is not a `Within` bound: {rendered}"
    );
}

/// `CReal.sumRange_tail_within_le` on a trivial instance: `f = g` the
/// constant-zero sequence, `a = 0`, `b = 1` — a **non-degenerate** pair
/// (`a ≠ b`), deliberately, so the `Nat.le_dest` witness `k` used internally
/// is `1`, not `0`: an `a = b` instance would exercise `k = 0` only and could
/// pass even if the general `k`-indexed rewrite were broken. Same rationale
/// and same `Kernel::infer`-on-a-closed-term method as
/// [`sum_range_tail_within_specializes_to_the_zero_series_against_itself`].
#[test]
fn sum_range_tail_within_le_specializes_to_the_zero_series_from_0_to_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();

    // zero_fn := λ _ : Nat, CReal.zero.
    let zero_fn = {
        let k_fv = d.fresh_fvar();
        let _k = d.kernel().fvar(k_fv);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        d.lam_fv(k_fv, nat, zero_c)
    };
    let zero_nat = d.num(0);
    let one_nat = d.num(1);

    // pointwise : ∀ k, le (abs (zero_fn k)) (zero_fn k), via le_abs_self.
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zk = d.apply(zero_fn, &[k]);
        let body = d.lemma(p.le_abs_self, &[zk]);
        d.lam_fv(k_fv, nat, body)
    };

    // hle : Nat.le 0 1, via Nat.zero_le.
    let zero_le = d.prelude().zero_le;
    let hle = d.lemma(zero_le, &[one_nat]);

    let instance = d.lemma(
        p.sum_range_tail_within_le,
        &[zero_fn, zero_fn, zero_nat, one_nat, pointwise, hle],
    );

    let inferred = d.kernel().infer(instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!(
            "sumRange_tail_within_le refused at the trivial f = g = (fun _ => zero), \
             a = 0, b = 1 instance: {error:?}"
        )
    });

    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Within"),
        "the instantiated conclusion is not a `Within` bound: {rendered}"
    );
}

/// **`CReal.sumRange_tail_cauchy_within` on a trivial instance**: `g` the
/// constant-zero sequence, `K := 0`, `m = n = 0`. Same rationale and same
/// `Kernel::infer`-on-a-closed-term method as
/// [`sum_range_tail_within_specializes_to_the_zero_series_against_itself`].
///
/// Unlike the two tests above, the theorem's own hypothesis here is itself a
/// genuine `∀ pp qq` statement (the raw Cauchy witness), so this cannot be
/// discharged by a single existing lemma at the trivial instance — it needs
/// an actual (short) proof that `sumRange (fun _ => zero) n` samples to
/// `Rat.zero` at every index, by induction on `n` via
/// `sumRange_seq_zero`/`sumRange_seq_succ`, then that `Within Rat.zero
/// bound` holds for any nonnegative `bound` (both `natDivSucc` moduli are
/// nonnegative via `Rat.zero_le_natDivSucc`).
#[test]
fn sum_range_tail_cauchy_within_specializes_to_the_zero_series_against_itself() {
    use crate::expr::ExprId;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{
        radd, rat_eq_rewrite, rchain, rcongr, req, rle, rneg, rrefl, rsymm, rtrans, rzero,
    };

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();
    let rat = p.rat;

    // zero_fn := λ _ : Nat, CReal.zero.
    let zero_fn = {
        let k_fv = d.fresh_fvar();
        let _k = d.kernel().fvar(k_fv);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        d.lam_fv(k_fv, nat, zero_c)
    };

    // zero_seq_at(n) : ∀ k, Eq Rat (seq (sumRange zero_fn n) k) Rat.zero, by
    // induction on `n` via `sumRange_seq_zero`/`sumRange_seq_succ`.
    let zero_seq_at = |d: &mut IntDev<'_>, n_val: ExprId| -> ExprId {
        let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let sum_x = d.const_app(p.sum_range, &[zero_fn, x]);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let lhs = super::sample(d, p, sum_x, k);
            let rzero_c = rzero(d, rat);
            let claim = req(d, lhs, rzero_c);
            d.pi_fv(k_fv, nat, claim)
        };
        d.induct(
            &motive,
            &|d| d.lemma(p.sum_range_seq_zero, &[zero_fn]),
            &|d, j, ih| {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sk = super::shift(d, k);
                // step : Eq Rat (seq (sumRange zero_fn (succ j)) k)
                //               (add (seq (sumRange zero_fn j) sk) (seq (zero_fn j) sk))
                let step = d.lemma(p.sum_range_seq_succ, &[zero_fn, j, k]);

                let sum_j = d.const_app(p.sum_range, &[zero_fn, j]);
                let left_sample = super::sample(d, p, sum_j, sk);
                let zfj = d.apply(zero_fn, &[j]);
                let right_sample = super::sample(d, p, zfj, sk);
                let start = radd(d, left_sample, right_sample);

                let rzero_c = rzero(d, rat);
                let ih_at_sk = d.apply(ih, &[sk]); // Eq Rat left_sample rzero_c
                // `right_sample` is defeq to `rzero_c` (`zero_fn j` beta-reduces
                // to `zero`, then `seq zero sk` iota-reduces to `Rat.zero`).
                let right_is_zero = rrefl(d, rzero_c);

                let after_left = radd(d, rzero_c, right_sample);
                let step1 = rcongr(d, left_sample, rzero_c, ih_at_sk, &|d, t| {
                    radd(d, t, right_sample)
                });
                let after_right = radd(d, rzero_c, rzero_c);
                let step2 = rcongr(d, right_sample, rzero_c, right_is_zero, &|d, t| {
                    radd(d, rzero_c, t)
                });
                let collapse = d.lemma(rat.add_zero, &[rzero_c]); // Eq (add zero zero) zero

                let (_, chained) = rchain(
                    d,
                    start,
                    &[
                        (after_left, step1),
                        (after_right, step2),
                        (rzero_c, collapse),
                    ],
                );
                let succ_sample = {
                    let sj = d.succ(j);
                    let sum_sj = d.const_app(p.sum_range, &[zero_fn, sj]);
                    super::sample(d, p, sum_sj, k)
                };
                let total = rtrans(d, succ_sample, start, rzero_c, step, chained);

                d.lam_fv(k_fv, nat, total)
            },
            n_val,
        )
    };

    let zero_nat = d.num(0);
    let k_witness = d.num(0);

    // hyp : ∀ pp qq, Within (seq (sumRange zero_fn pp) pp
    //                        − seq (sumRange zero_fn qq) qq)
    //                       (natDivSucc 0 pp + natDivSucc 0 qq)
    let hyp = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);

        let left_eq = {
            let at_pp = zero_seq_at(&mut d, pp);
            d.apply(at_pp, &[pp])
        }; // Eq Rat (seq (sumRange zero_fn pp) pp) Rat.zero
        let right_eq = {
            let at_qq = zero_seq_at(&mut d, qq);
            d.apply(at_qq, &[qq])
        };

        let sum_pp = d.const_app(p.sum_range, &[zero_fn, pp]);
        let sum_qq = d.const_app(p.sum_range, &[zero_fn, qq]);
        let left = super::sample(&mut d, p, sum_pp, pp);
        let right = super::sample(&mut d, p, sum_qq, qq);
        let diff = rsub(&mut d, rat, left, right);
        let rzero_c = rzero(&mut d, rat);

        // diff = zero: rewrite `left`, then `right`, to zero, then collapse
        // `zero - zero` via `neg_zero`/`add_zero`.
        let after_left = rsub(&mut d, rat, rzero_c, right);
        let step1 = rcongr(&mut d, left, rzero_c, left_eq, &|d, t| {
            rsub(d, rat, t, right)
        });
        let after_right = rsub(&mut d, rat, rzero_c, rzero_c);
        let step2 = rcongr(&mut d, right, rzero_c, right_eq, &|d, t| {
            rsub(d, rat, rzero_c, t)
        });

        let neg_zero_eq = d.lemma(rat.neg_zero, &[]); // Eq (neg zero) zero
        let neg_zero_term = rneg(&mut d, rzero_c);
        let zero_plus_neg_zero = radd(&mut d, rzero_c, neg_zero_term);
        let zero_plus_zero = radd(&mut d, rzero_c, rzero_c);
        let step3a = rcongr(&mut d, neg_zero_term, rzero_c, neg_zero_eq, &|d, t| {
            radd(d, rzero_c, t)
        }); // Eq (add zero (neg zero)) (add zero zero)
        let add_zero_eq = d.lemma(rat.add_zero, &[rzero_c]); // Eq (add zero zero) zero
        // `after_right` (`sub zero zero`) is defeq to `zero_plus_neg_zero`
        // (`add zero (neg zero)`), so `step3` below stands directly for
        // `Eq Rat after_right rzero_c`.
        let step3 = rtrans(
            &mut d,
            zero_plus_neg_zero,
            zero_plus_zero,
            rzero_c,
            step3a,
            add_zero_eq,
        );

        let (_, diff_eq_zero) = rchain(
            &mut d,
            diff,
            &[(after_left, step1), (after_right, step2), (rzero_c, step3)],
        );
        let zero_eq_diff = rsymm(&mut d, diff, rzero_c, diff_eq_zero);

        let bpp = d.const_app(rat.nat_div_succ, &[k_witness, pp]);
        let bqq = d.const_app(rat.nat_div_succ, &[k_witness, qq]);
        let bound = radd(&mut d, bpp, bqq);

        let nonneg_pp = d.lemma(rat.zero_le_nat_div_succ, &[k_witness, pp]);
        let nonneg_qq = d.lemma(rat.zero_le_nat_div_succ, &[k_witness, qq]);
        let bound_nonneg = d.lemma(rat.add_nonneg, &[bpp, bqq, nonneg_pp, nonneg_qq]);
        let neg_bound_nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, bound_nonneg]);
        let neg_bound = rneg(&mut d, bound);
        let lower_ty = rle(&mut d, rat, neg_bound, rzero_c);
        let upper_ty = rle(&mut d, rat, rzero_c, bound);
        let zero_within_bound = super::and_intro(
            &mut d,
            p,
            lower_ty,
            upper_ty,
            neg_bound_nonpos,
            bound_nonneg,
        );

        let within_diff = rat_eq_rewrite(
            &mut d,
            rzero_c,
            diff,
            zero_eq_diff,
            zero_within_bound,
            &|d, t| super::within(d, p, t, bound),
        );

        let over_qq = d.lam_fv(qq_fv, nat, within_diff);
        d.lam_fv(pp_fv, nat, over_qq)
    };

    let instance = d.lemma(
        p.sum_range_tail_cauchy_within,
        &[zero_fn, k_witness, zero_nat, zero_nat, hyp],
    );

    let inferred = d.kernel().infer(instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!(
            "sumRange_tail_cauchy_within refused at the trivial g = (fun _ => zero), \
             K = 0, m = n = 0 instance: {error:?}"
        )
    });

    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Within"),
        "the instantiated conclusion is not a `Within` bound: {rendered}"
    );
}

/// **`CReal.sumRange_tail_within_cauchy` (the outer telescope) on a
/// non-degenerate instance**: `f = g` the constant-zero sequence, `K = 0`,
/// `m = 0`, `n = 1` (so `m + n = 1 ≠ 0`, exercising the `shift`/`modulus`
/// legs at a genuinely nonzero index rather than the `m = n = 0` case the
/// two theorems this one composes were each already checked at separately).
/// Same rationale and `Kernel::infer`-on-a-closed-term method as the other
/// specialization tests in this file; the Cauchy hypothesis is built the
/// same way [`sum_range_tail_cauchy_within_specializes_to_the_zero_series_against_itself`]
/// builds it.
#[test]
fn sum_range_tail_within_cauchy_specializes_to_the_zero_series_against_itself() {
    use crate::expr::ExprId;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{
        radd, rat_eq_rewrite, rchain, rcongr, req, rle, rneg, rrefl, rsymm, rtrans, rzero,
    };

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();
    let rat = p.rat;

    // zero_fn := λ _ : Nat, CReal.zero.
    let zero_fn = {
        let k_fv = d.fresh_fvar();
        let _k = d.kernel().fvar(k_fv);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        d.lam_fv(k_fv, nat, zero_c)
    };

    // zero_seq_at(n) : ∀ k, Eq Rat (seq (sumRange zero_fn n) k) Rat.zero, by
    // induction on `n` via `sumRange_seq_zero`/`sumRange_seq_succ`.
    let zero_seq_at = |d: &mut IntDev<'_>, n_val: ExprId| -> ExprId {
        let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let sum_x = d.const_app(p.sum_range, &[zero_fn, x]);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let lhs = super::sample(d, p, sum_x, k);
            let rzero_c = rzero(d, rat);
            let claim = req(d, lhs, rzero_c);
            d.pi_fv(k_fv, nat, claim)
        };
        d.induct(
            &motive,
            &|d| d.lemma(p.sum_range_seq_zero, &[zero_fn]),
            &|d, j, ih| {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sk = super::shift(d, k);
                let step = d.lemma(p.sum_range_seq_succ, &[zero_fn, j, k]);

                let sum_j = d.const_app(p.sum_range, &[zero_fn, j]);
                let left_sample = super::sample(d, p, sum_j, sk);
                let zfj = d.apply(zero_fn, &[j]);
                let right_sample = super::sample(d, p, zfj, sk);
                let start = radd(d, left_sample, right_sample);

                let rzero_c = rzero(d, rat);
                let ih_at_sk = d.apply(ih, &[sk]);
                let right_is_zero = rrefl(d, rzero_c);

                let after_left = radd(d, rzero_c, right_sample);
                let step1 = rcongr(d, left_sample, rzero_c, ih_at_sk, &|d, t| {
                    radd(d, t, right_sample)
                });
                let after_right = radd(d, rzero_c, rzero_c);
                let step2 = rcongr(d, right_sample, rzero_c, right_is_zero, &|d, t| {
                    radd(d, rzero_c, t)
                });
                let collapse = d.lemma(rat.add_zero, &[rzero_c]);

                let (_, chained) = rchain(
                    d,
                    start,
                    &[
                        (after_left, step1),
                        (after_right, step2),
                        (rzero_c, collapse),
                    ],
                );
                let succ_sample = {
                    let sj = d.succ(j);
                    let sum_sj = d.const_app(p.sum_range, &[zero_fn, sj]);
                    super::sample(d, p, sum_sj, k)
                };
                let total = rtrans(d, succ_sample, start, rzero_c, step, chained);

                d.lam_fv(k_fv, nat, total)
            },
            n_val,
        )
    };

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let k_witness = d.num(0);

    // pointwise : ∀ k, le (abs (zero_fn k)) (zero_fn k), via le_abs_self.
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zk = d.apply(zero_fn, &[k]);
        let body = d.lemma(p.le_abs_self, &[zk]);
        d.lam_fv(k_fv, nat, body)
    };

    // cauchy_hyp : ∀ pp qq, Within (seq (sumRange zero_fn pp) pp
    //                               − seq (sumRange zero_fn qq) qq)
    //                              (natDivSucc 0 pp + natDivSucc 0 qq)
    let cauchy_hyp = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);

        let left_eq = {
            let at_pp = zero_seq_at(&mut d, pp);
            d.apply(at_pp, &[pp])
        };
        let right_eq = {
            let at_qq = zero_seq_at(&mut d, qq);
            d.apply(at_qq, &[qq])
        };

        let sum_pp = d.const_app(p.sum_range, &[zero_fn, pp]);
        let sum_qq = d.const_app(p.sum_range, &[zero_fn, qq]);
        let left = super::sample(&mut d, p, sum_pp, pp);
        let right = super::sample(&mut d, p, sum_qq, qq);
        let diff = rsub(&mut d, rat, left, right);
        let rzero_c = rzero(&mut d, rat);

        let after_left = rsub(&mut d, rat, rzero_c, right);
        let step1 = rcongr(&mut d, left, rzero_c, left_eq, &|d, t| {
            rsub(d, rat, t, right)
        });
        let after_right = rsub(&mut d, rat, rzero_c, rzero_c);
        let step2 = rcongr(&mut d, right, rzero_c, right_eq, &|d, t| {
            rsub(d, rat, rzero_c, t)
        });

        let neg_zero_eq = d.lemma(rat.neg_zero, &[]);
        let neg_zero_term = rneg(&mut d, rzero_c);
        let zero_plus_neg_zero = radd(&mut d, rzero_c, neg_zero_term);
        let zero_plus_zero = radd(&mut d, rzero_c, rzero_c);
        let step3a = rcongr(&mut d, neg_zero_term, rzero_c, neg_zero_eq, &|d, t| {
            radd(d, rzero_c, t)
        });
        let add_zero_eq = d.lemma(rat.add_zero, &[rzero_c]);
        let step3 = rtrans(
            &mut d,
            zero_plus_neg_zero,
            zero_plus_zero,
            rzero_c,
            step3a,
            add_zero_eq,
        );

        let (_, diff_eq_zero) = rchain(
            &mut d,
            diff,
            &[(after_left, step1), (after_right, step2), (rzero_c, step3)],
        );
        let zero_eq_diff = rsymm(&mut d, diff, rzero_c, diff_eq_zero);

        let bpp = d.const_app(rat.nat_div_succ, &[k_witness, pp]);
        let bqq = d.const_app(rat.nat_div_succ, &[k_witness, qq]);
        let bound = radd(&mut d, bpp, bqq);

        let nonneg_pp = d.lemma(rat.zero_le_nat_div_succ, &[k_witness, pp]);
        let nonneg_qq = d.lemma(rat.zero_le_nat_div_succ, &[k_witness, qq]);
        let bound_nonneg = d.lemma(rat.add_nonneg, &[bpp, bqq, nonneg_pp, nonneg_qq]);
        let neg_bound_nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, bound_nonneg]);
        let neg_bound = rneg(&mut d, bound);
        let lower_ty = rle(&mut d, rat, neg_bound, rzero_c);
        let upper_ty = rle(&mut d, rat, rzero_c, bound);
        let zero_within_bound = super::and_intro(
            &mut d,
            p,
            lower_ty,
            upper_ty,
            neg_bound_nonpos,
            bound_nonneg,
        );

        let within_diff = rat_eq_rewrite(
            &mut d,
            rzero_c,
            diff,
            zero_eq_diff,
            zero_within_bound,
            &|d, t| super::within(d, p, t, bound),
        );

        let over_qq = d.lam_fv(qq_fv, nat, within_diff);
        d.lam_fv(pp_fv, nat, over_qq)
    };

    let instance = d.lemma(
        p.sum_range_tail_within_cauchy,
        &[
            zero_fn, zero_fn, k_witness, zero_nat, one_nat, pointwise, cauchy_hyp,
        ],
    );

    let inferred = d.kernel().infer(instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!(
            "sumRange_tail_within_cauchy refused at the trivial f = g = (fun _ => zero), \
             K = 0, m = 0, n = 1 instance: {error:?}"
        )
    });

    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Within"),
        "the instantiated conclusion is not a `Within` bound: {rendered}"
    );
}

/// **`CReal.sumRange_cauchy_dominated_ordered` on a non-degenerate
/// instance**: `f = g` the constant-zero sequence, `K = 0`, `a = 0`, `b = 1`
/// — a non-degenerate pair (`a ≠ b`), deliberately, for the same reason
/// [`sum_range_tail_within_le_specializes_to_the_zero_series_from_0_to_1`]
/// picks it: the internal `Nat.le_dest` witness is `1`, not `0`, so this
/// exercises the general (`gap ≠ 0`) rewrite rather than only the trivial
/// one. Same `zero_seq_at`/`cauchy_hyp` construction as
/// [`sum_range_tail_within_cauchy_specializes_to_the_zero_series_against_itself`],
/// plus the `hle : Nat.le 0 1` witness
/// [`sum_range_tail_within_le_specializes_to_the_zero_series_from_0_to_1`]
/// already builds.
#[test]
fn sum_range_cauchy_dominated_ordered_specializes_to_the_zero_series_from_0_to_1() {
    use crate::expr::ExprId;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{
        radd, rat_eq_rewrite, rchain, rcongr, req, rle, rneg, rrefl, rsymm, rtrans, rzero,
    };

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();
    let rat = p.rat;

    // zero_fn := λ _ : Nat, CReal.zero.
    let zero_fn = {
        let k_fv = d.fresh_fvar();
        let _k = d.kernel().fvar(k_fv);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        d.lam_fv(k_fv, nat, zero_c)
    };

    // zero_seq_at(n) : ∀ k, Eq Rat (seq (sumRange zero_fn n) k) Rat.zero, by
    // induction on `n` via `sumRange_seq_zero`/`sumRange_seq_succ`.
    let zero_seq_at = |d: &mut IntDev<'_>, n_val: ExprId| -> ExprId {
        let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let sum_x = d.const_app(p.sum_range, &[zero_fn, x]);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let lhs = super::sample(d, p, sum_x, k);
            let rzero_c = rzero(d, rat);
            let claim = req(d, lhs, rzero_c);
            d.pi_fv(k_fv, nat, claim)
        };
        d.induct(
            &motive,
            &|d| d.lemma(p.sum_range_seq_zero, &[zero_fn]),
            &|d, j, ih| {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sk = super::shift(d, k);
                let step = d.lemma(p.sum_range_seq_succ, &[zero_fn, j, k]);

                let sum_j = d.const_app(p.sum_range, &[zero_fn, j]);
                let left_sample = super::sample(d, p, sum_j, sk);
                let zfj = d.apply(zero_fn, &[j]);
                let right_sample = super::sample(d, p, zfj, sk);
                let start = radd(d, left_sample, right_sample);

                let rzero_c = rzero(d, rat);
                let ih_at_sk = d.apply(ih, &[sk]);
                let right_is_zero = rrefl(d, rzero_c);

                let after_left = radd(d, rzero_c, right_sample);
                let step1 = rcongr(d, left_sample, rzero_c, ih_at_sk, &|d, t| {
                    radd(d, t, right_sample)
                });
                let after_right = radd(d, rzero_c, rzero_c);
                let step2 = rcongr(d, right_sample, rzero_c, right_is_zero, &|d, t| {
                    radd(d, rzero_c, t)
                });
                let collapse = d.lemma(rat.add_zero, &[rzero_c]);

                let (_, chained) = rchain(
                    d,
                    start,
                    &[
                        (after_left, step1),
                        (after_right, step2),
                        (rzero_c, collapse),
                    ],
                );
                let succ_sample = {
                    let sj = d.succ(j);
                    let sum_sj = d.const_app(p.sum_range, &[zero_fn, sj]);
                    super::sample(d, p, sum_sj, k)
                };
                let total = rtrans(d, succ_sample, start, rzero_c, step, chained);

                d.lam_fv(k_fv, nat, total)
            },
            n_val,
        )
    };

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let k_witness = d.num(0);

    // pointwise : ∀ k, le (abs (zero_fn k)) (zero_fn k), via le_abs_self.
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zk = d.apply(zero_fn, &[k]);
        let body = d.lemma(p.le_abs_self, &[zk]);
        d.lam_fv(k_fv, nat, body)
    };

    // cauchy_hyp : ∀ pp qq, Within (seq (sumRange zero_fn pp) pp
    //                               − seq (sumRange zero_fn qq) qq)
    //                              (natDivSucc 0 pp + natDivSucc 0 qq)
    let cauchy_hyp = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);

        let left_eq = {
            let at_pp = zero_seq_at(&mut d, pp);
            d.apply(at_pp, &[pp])
        };
        let right_eq = {
            let at_qq = zero_seq_at(&mut d, qq);
            d.apply(at_qq, &[qq])
        };

        let sum_pp = d.const_app(p.sum_range, &[zero_fn, pp]);
        let sum_qq = d.const_app(p.sum_range, &[zero_fn, qq]);
        let left = super::sample(&mut d, p, sum_pp, pp);
        let right = super::sample(&mut d, p, sum_qq, qq);
        let diff = rsub(&mut d, rat, left, right);
        let rzero_c = rzero(&mut d, rat);

        let after_left = rsub(&mut d, rat, rzero_c, right);
        let step1 = rcongr(&mut d, left, rzero_c, left_eq, &|d, t| {
            rsub(d, rat, t, right)
        });
        let after_right = rsub(&mut d, rat, rzero_c, rzero_c);
        let step2 = rcongr(&mut d, right, rzero_c, right_eq, &|d, t| {
            rsub(d, rat, rzero_c, t)
        });

        let neg_zero_eq = d.lemma(rat.neg_zero, &[]);
        let neg_zero_term = rneg(&mut d, rzero_c);
        let zero_plus_neg_zero = radd(&mut d, rzero_c, neg_zero_term);
        let zero_plus_zero = radd(&mut d, rzero_c, rzero_c);
        let step3a = rcongr(&mut d, neg_zero_term, rzero_c, neg_zero_eq, &|d, t| {
            radd(d, rzero_c, t)
        });
        let add_zero_eq = d.lemma(rat.add_zero, &[rzero_c]);
        let step3 = rtrans(
            &mut d,
            zero_plus_neg_zero,
            zero_plus_zero,
            rzero_c,
            step3a,
            add_zero_eq,
        );

        let (_, diff_eq_zero) = rchain(
            &mut d,
            diff,
            &[(after_left, step1), (after_right, step2), (rzero_c, step3)],
        );
        let zero_eq_diff = rsymm(&mut d, diff, rzero_c, diff_eq_zero);

        let bpp = d.const_app(rat.nat_div_succ, &[k_witness, pp]);
        let bqq = d.const_app(rat.nat_div_succ, &[k_witness, qq]);
        let bound = radd(&mut d, bpp, bqq);

        let nonneg_pp = d.lemma(rat.zero_le_nat_div_succ, &[k_witness, pp]);
        let nonneg_qq = d.lemma(rat.zero_le_nat_div_succ, &[k_witness, qq]);
        let bound_nonneg = d.lemma(rat.add_nonneg, &[bpp, bqq, nonneg_pp, nonneg_qq]);
        let neg_bound_nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, bound_nonneg]);
        let neg_bound = rneg(&mut d, bound);
        let lower_ty = rle(&mut d, rat, neg_bound, rzero_c);
        let upper_ty = rle(&mut d, rat, rzero_c, bound);
        let zero_within_bound = super::and_intro(
            &mut d,
            p,
            lower_ty,
            upper_ty,
            neg_bound_nonpos,
            bound_nonneg,
        );

        let within_diff = rat_eq_rewrite(
            &mut d,
            rzero_c,
            diff,
            zero_eq_diff,
            zero_within_bound,
            &|d, t| super::within(d, p, t, bound),
        );

        let over_qq = d.lam_fv(qq_fv, nat, within_diff);
        d.lam_fv(pp_fv, nat, over_qq)
    };

    // hle : Nat.le 0 1, via Nat.zero_le.
    let zero_le = d.prelude().zero_le;
    let hle = d.lemma(zero_le, &[one_nat]);

    let instance = d.lemma(
        p.sum_range_cauchy_dominated_ordered,
        &[
            zero_fn, zero_fn, k_witness, zero_nat, one_nat, pointwise, cauchy_hyp, hle,
        ],
    );

    let inferred = d.kernel().infer(instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!(
            "sumRange_cauchy_dominated_ordered refused at the trivial f = g = (fun _ => zero), \
             K = 0, a = 0, b = 1 instance: {error:?}"
        )
    });

    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Within"),
        "the instantiated conclusion is not a `Within` bound: {rendered}"
    );
}

/// **`CReal.sumRange_cauchy_dominated_ordered_normalized` on a non-degenerate
/// instance**: same `f = g` constant-zero sequence, `K = 0`, `a = 0`, `b = 1`
/// as [`sum_range_cauchy_dominated_ordered_specializes_to_the_zero_series_from_0_to_1`]
/// — deliberately non-degenerate (`a ≠ b`) for the same reason that test
/// picks it. This is bound *normalization* on top of that theorem: the
/// instantiated conclusion's bound must render as a single two-term
/// `natDivSucc K' b + natDivSucc K' a` (checked structurally below, not just
/// "contains `Within`"), even though `k_witness = 0` here — the normalization
/// still runs the full eleven-leaf widen/fuse regardless of what `K` is.
#[test]
fn sum_range_cauchy_dominated_ordered_normalized_specializes_to_the_zero_series_from_0_to_1() {
    use crate::expr::ExprId;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{
        radd, rat_eq_rewrite, rchain, rcongr, req, rle, rneg, rrefl, rsymm, rtrans, rzero,
    };

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();
    let rat = p.rat;

    // zero_fn := λ _ : Nat, CReal.zero.
    let zero_fn = {
        let k_fv = d.fresh_fvar();
        let _k = d.kernel().fvar(k_fv);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        d.lam_fv(k_fv, nat, zero_c)
    };

    // zero_seq_at(n) : ∀ k, Eq Rat (seq (sumRange zero_fn n) k) Rat.zero, by
    // induction on `n` via `sumRange_seq_zero`/`sumRange_seq_succ`.
    let zero_seq_at = |d: &mut IntDev<'_>, n_val: ExprId| -> ExprId {
        let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let sum_x = d.const_app(p.sum_range, &[zero_fn, x]);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let lhs = super::sample(d, p, sum_x, k);
            let rzero_c = rzero(d, rat);
            let claim = req(d, lhs, rzero_c);
            d.pi_fv(k_fv, nat, claim)
        };
        d.induct(
            &motive,
            &|d| d.lemma(p.sum_range_seq_zero, &[zero_fn]),
            &|d, j, ih| {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sk = super::shift(d, k);
                let step = d.lemma(p.sum_range_seq_succ, &[zero_fn, j, k]);

                let sum_j = d.const_app(p.sum_range, &[zero_fn, j]);
                let left_sample = super::sample(d, p, sum_j, sk);
                let zfj = d.apply(zero_fn, &[j]);
                let right_sample = super::sample(d, p, zfj, sk);
                let start = radd(d, left_sample, right_sample);

                let rzero_c = rzero(d, rat);
                let ih_at_sk = d.apply(ih, &[sk]);
                let right_is_zero = rrefl(d, rzero_c);

                let after_left = radd(d, rzero_c, right_sample);
                let step1 = rcongr(d, left_sample, rzero_c, ih_at_sk, &|d, t| {
                    radd(d, t, right_sample)
                });
                let after_right = radd(d, rzero_c, rzero_c);
                let step2 = rcongr(d, right_sample, rzero_c, right_is_zero, &|d, t| {
                    radd(d, rzero_c, t)
                });
                let collapse = d.lemma(rat.add_zero, &[rzero_c]);

                let (_, chained) = rchain(
                    d,
                    start,
                    &[
                        (after_left, step1),
                        (after_right, step2),
                        (rzero_c, collapse),
                    ],
                );
                let succ_sample = {
                    let sj = d.succ(j);
                    let sum_sj = d.const_app(p.sum_range, &[zero_fn, sj]);
                    super::sample(d, p, sum_sj, k)
                };
                let total = rtrans(d, succ_sample, start, rzero_c, step, chained);

                d.lam_fv(k_fv, nat, total)
            },
            n_val,
        )
    };

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let k_witness = d.num(0);

    // pointwise : ∀ k, le (abs (zero_fn k)) (zero_fn k), via le_abs_self.
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zk = d.apply(zero_fn, &[k]);
        let body = d.lemma(p.le_abs_self, &[zk]);
        d.lam_fv(k_fv, nat, body)
    };

    // cauchy_hyp : ∀ pp qq, Within (seq (sumRange zero_fn pp) pp
    //                               − seq (sumRange zero_fn qq) qq)
    //                              (natDivSucc 0 pp + natDivSucc 0 qq)
    let cauchy_hyp = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);

        let left_eq = {
            let at_pp = zero_seq_at(&mut d, pp);
            d.apply(at_pp, &[pp])
        };
        let right_eq = {
            let at_qq = zero_seq_at(&mut d, qq);
            d.apply(at_qq, &[qq])
        };

        let sum_pp = d.const_app(p.sum_range, &[zero_fn, pp]);
        let sum_qq = d.const_app(p.sum_range, &[zero_fn, qq]);
        let left = super::sample(&mut d, p, sum_pp, pp);
        let right = super::sample(&mut d, p, sum_qq, qq);
        let diff = rsub(&mut d, rat, left, right);
        let rzero_c = rzero(&mut d, rat);

        let after_left = rsub(&mut d, rat, rzero_c, right);
        let step1 = rcongr(&mut d, left, rzero_c, left_eq, &|d, t| {
            rsub(d, rat, t, right)
        });
        let after_right = rsub(&mut d, rat, rzero_c, rzero_c);
        let step2 = rcongr(&mut d, right, rzero_c, right_eq, &|d, t| {
            rsub(d, rat, rzero_c, t)
        });

        let neg_zero_eq = d.lemma(rat.neg_zero, &[]);
        let neg_zero_term = rneg(&mut d, rzero_c);
        let zero_plus_neg_zero = radd(&mut d, rzero_c, neg_zero_term);
        let zero_plus_zero = radd(&mut d, rzero_c, rzero_c);
        let step3a = rcongr(&mut d, neg_zero_term, rzero_c, neg_zero_eq, &|d, t| {
            radd(d, rzero_c, t)
        });
        let add_zero_eq = d.lemma(rat.add_zero, &[rzero_c]);
        let step3 = rtrans(
            &mut d,
            zero_plus_neg_zero,
            zero_plus_zero,
            rzero_c,
            step3a,
            add_zero_eq,
        );

        let (_, diff_eq_zero) = rchain(
            &mut d,
            diff,
            &[(after_left, step1), (after_right, step2), (rzero_c, step3)],
        );
        let zero_eq_diff = rsymm(&mut d, diff, rzero_c, diff_eq_zero);

        let bpp = d.const_app(rat.nat_div_succ, &[k_witness, pp]);
        let bqq = d.const_app(rat.nat_div_succ, &[k_witness, qq]);
        let bound = radd(&mut d, bpp, bqq);

        let nonneg_pp = d.lemma(rat.zero_le_nat_div_succ, &[k_witness, pp]);
        let nonneg_qq = d.lemma(rat.zero_le_nat_div_succ, &[k_witness, qq]);
        let bound_nonneg = d.lemma(rat.add_nonneg, &[bpp, bqq, nonneg_pp, nonneg_qq]);
        let neg_bound_nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, bound_nonneg]);
        let neg_bound = rneg(&mut d, bound);
        let lower_ty = rle(&mut d, rat, neg_bound, rzero_c);
        let upper_ty = rle(&mut d, rat, rzero_c, bound);
        let zero_within_bound = super::and_intro(
            &mut d,
            p,
            lower_ty,
            upper_ty,
            neg_bound_nonpos,
            bound_nonneg,
        );

        let within_diff = rat_eq_rewrite(
            &mut d,
            rzero_c,
            diff,
            zero_eq_diff,
            zero_within_bound,
            &|d, t| super::within(d, p, t, bound),
        );

        let over_qq = d.lam_fv(qq_fv, nat, within_diff);
        d.lam_fv(pp_fv, nat, over_qq)
    };

    // hle : Nat.le 0 1, via Nat.zero_le.
    let zero_le = d.prelude().zero_le;
    let hle = d.lemma(zero_le, &[one_nat]);

    let instance = d.lemma(
        p.sum_range_cauchy_dominated_ordered_normalized,
        &[
            zero_fn, zero_fn, k_witness, zero_nat, one_nat, pointwise, cauchy_hyp, hle,
        ],
    );

    let inferred = d.kernel().infer(instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!(
            "sumRange_cauchy_dominated_ordered_normalized refused at the trivial \
             f = g = (fun _ => zero), K = 0, a = 0, b = 1 instance: {error:?}"
        )
    });

    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Within"),
        "the instantiated conclusion is not a `Within` bound: {rendered}"
    );
    // The bound must be the single two-term `natDivSucc K' b + natDivSucc K'
    // a` shape, not the un-normalized eleven-leaf mess — i.e. no `shift`
    // (Bishop's shifted index) survives into the rendered conclusion.
    assert!(
        !rendered.contains("shift"),
        "the normalized bound still mentions `shift`, so normalization did \
         not actually collapse it: {rendered}"
    );
    let nat_div_succ_count = rendered.matches("natDivSucc").count();
    assert_eq!(
        nat_div_succ_count, 2,
        "the normalized bound must be exactly two natDivSucc leaves, found \
         {nat_div_succ_count}: {rendered}"
    );
}

/// `CReal.sumRange_cauchy_of_dominated` closes the last two gaps
/// `series.rs`'s module documentation named: the `Nat.le_total` case split
/// and the `CReal.Cauchy` existential itself. Same `f = g` constant-zero
/// sequence every other test in this file verifies against (this
/// development's only proved-Cauchy series — nothing else is provably
/// `Cauchy` yet, per the module documentation's own remaining gaps), fed a
/// genuine `Cauchy (sumRange zero_fn)` witness (`K = 0`, built directly, not
/// borrowed from an existing theorem) through `Exists.intro`.
#[test]
fn sum_range_cauchy_of_dominated_closes_the_zero_series_cauchy_hypothesis() {
    use crate::expr::ExprId;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{
        radd, rat_eq_rewrite, rchain, rcongr, req, rle, rneg, rrefl, rsymm, rtrans, rzero,
    };

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();
    let rat = p.rat;

    // zero_fn := λ _ : Nat, CReal.zero.
    let zero_fn = {
        let k_fv = d.fresh_fvar();
        let _k = d.kernel().fvar(k_fv);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        d.lam_fv(k_fv, nat, zero_c)
    };

    // zero_seq_at(n) : ∀ k, Eq Rat (seq (sumRange zero_fn n) k) Rat.zero —
    // verbatim the construction the other `sum_range_cauchy_*` tests in this
    // file already use.
    let zero_seq_at = |d: &mut IntDev<'_>, n_val: ExprId| -> ExprId {
        let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let sum_x = d.const_app(p.sum_range, &[zero_fn, x]);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let lhs = super::sample(d, p, sum_x, k);
            let rzero_c = rzero(d, rat);
            let claim = req(d, lhs, rzero_c);
            d.pi_fv(k_fv, nat, claim)
        };
        d.induct(
            &motive,
            &|d| d.lemma(p.sum_range_seq_zero, &[zero_fn]),
            &|d, j, ih| {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sk = super::shift(d, k);
                let step = d.lemma(p.sum_range_seq_succ, &[zero_fn, j, k]);

                let sum_j = d.const_app(p.sum_range, &[zero_fn, j]);
                let left_sample = super::sample(d, p, sum_j, sk);
                let zfj = d.apply(zero_fn, &[j]);
                let right_sample = super::sample(d, p, zfj, sk);
                let start = radd(d, left_sample, right_sample);

                let rzero_c = rzero(d, rat);
                let ih_at_sk = d.apply(ih, &[sk]);
                let right_is_zero = rrefl(d, rzero_c);

                let after_left = radd(d, rzero_c, right_sample);
                let step1 = rcongr(d, left_sample, rzero_c, ih_at_sk, &|d, t| {
                    radd(d, t, right_sample)
                });
                let after_right = radd(d, rzero_c, rzero_c);
                let step2 = rcongr(d, right_sample, rzero_c, right_is_zero, &|d, t| {
                    radd(d, rzero_c, t)
                });
                let collapse = d.lemma(rat.add_zero, &[rzero_c]);

                let (_, chained) = rchain(
                    d,
                    start,
                    &[
                        (after_left, step1),
                        (after_right, step2),
                        (rzero_c, collapse),
                    ],
                );
                let succ_sample = {
                    let sj = d.succ(j);
                    let sum_sj = d.const_app(p.sum_range, &[zero_fn, sj]);
                    super::sample(d, p, sum_sj, k)
                };
                let total = rtrans(d, succ_sample, start, rzero_c, step, chained);

                d.lam_fv(k_fv, nat, total)
            },
            n_val,
        )
    };

    let zero_nat = d.num(0);

    // pointwise : ∀ k, le (abs (zero_fn k)) (zero_fn k), via le_abs_self.
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zk = d.apply(zero_fn, &[k]);
        let body = d.lemma(p.le_abs_self, &[zk]);
        d.lam_fv(k_fv, nat, body)
    };

    // cauchy_stmt_at(k) : ∀ pp qq, Within (seq (sumRange zero_fn pp) pp −
    // seq (sumRange zero_fn qq) qq) (natDivSucc k pp + natDivSucc k qq) — the
    // bare STATEMENT (a `Nat -> Prop` when wrapped in a further `λ k`),
    // built generically in `k` so it is syntactically `CReal.Cauchy
    // (sumRange zero_fn)`'s own unfolded predicate (this test cannot call
    // `series.rs`'s private `sum_range_cauchy_body` directly).
    let cauchy_stmt_at = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);
        let sum_pp = d.const_app(p.sum_range, &[zero_fn, pp]);
        let sum_qq = d.const_app(p.sum_range, &[zero_fn, qq]);
        let left = super::sample(d, p, sum_pp, pp);
        let right = super::sample(d, p, sum_qq, qq);
        let diff = rsub(d, rat, left, right);
        let bpp = d.const_app(rat.nat_div_succ, &[k, pp]);
        let bqq = d.const_app(rat.nat_div_succ, &[k, qq]);
        let bound = radd(d, bpp, bqq);
        let claim = super::within(d, p, diff, bound);
        let over_qq = d.pi_fv(qq_fv, nat, claim);
        d.pi_fv(pp_fv, nat, over_qq)
    };

    // predicate_g := λ k, cauchy_stmt_at(k).
    let predicate_g = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = cauchy_stmt_at(&mut d, k);
        d.lam_fv(k_fv, nat, body)
    };

    // cauchy_hyp_at_zero : cauchy_stmt_at(0) — the K = 0 proof, same
    // rewrite-chain construction the other tests in this file already build.
    let cauchy_hyp_at_zero = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);

        let left_eq = {
            let at_pp = zero_seq_at(&mut d, pp);
            d.apply(at_pp, &[pp])
        };
        let right_eq = {
            let at_qq = zero_seq_at(&mut d, qq);
            d.apply(at_qq, &[qq])
        };

        let sum_pp = d.const_app(p.sum_range, &[zero_fn, pp]);
        let sum_qq = d.const_app(p.sum_range, &[zero_fn, qq]);
        let left = super::sample(&mut d, p, sum_pp, pp);
        let right = super::sample(&mut d, p, sum_qq, qq);
        let diff = rsub(&mut d, rat, left, right);
        let rzero_c = rzero(&mut d, rat);

        let after_left = rsub(&mut d, rat, rzero_c, right);
        let step1 = rcongr(&mut d, left, rzero_c, left_eq, &|d, t| {
            rsub(d, rat, t, right)
        });
        let after_right = rsub(&mut d, rat, rzero_c, rzero_c);
        let step2 = rcongr(&mut d, right, rzero_c, right_eq, &|d, t| {
            rsub(d, rat, rzero_c, t)
        });

        let neg_zero_eq = d.lemma(rat.neg_zero, &[]);
        let neg_zero_term = rneg(&mut d, rzero_c);
        let zero_plus_neg_zero = radd(&mut d, rzero_c, neg_zero_term);
        let zero_plus_zero = radd(&mut d, rzero_c, rzero_c);
        let step3a = rcongr(&mut d, neg_zero_term, rzero_c, neg_zero_eq, &|d, t| {
            radd(d, rzero_c, t)
        });
        let add_zero_eq = d.lemma(rat.add_zero, &[rzero_c]);
        let step3 = rtrans(
            &mut d,
            zero_plus_neg_zero,
            zero_plus_zero,
            rzero_c,
            step3a,
            add_zero_eq,
        );

        let (_, diff_eq_zero) = rchain(
            &mut d,
            diff,
            &[(after_left, step1), (after_right, step2), (rzero_c, step3)],
        );
        let zero_eq_diff = rsymm(&mut d, diff, rzero_c, diff_eq_zero);

        let bpp = d.const_app(rat.nat_div_succ, &[zero_nat, pp]);
        let bqq = d.const_app(rat.nat_div_succ, &[zero_nat, qq]);
        let bound = radd(&mut d, bpp, bqq);

        let nonneg_pp = d.lemma(rat.zero_le_nat_div_succ, &[zero_nat, pp]);
        let nonneg_qq = d.lemma(rat.zero_le_nat_div_succ, &[zero_nat, qq]);
        let bound_nonneg = d.lemma(rat.add_nonneg, &[bpp, bqq, nonneg_pp, nonneg_qq]);
        let neg_bound_nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, bound_nonneg]);
        let neg_bound = rneg(&mut d, bound);
        let lower_ty = rle(&mut d, rat, neg_bound, rzero_c);
        let upper_ty = rle(&mut d, rat, rzero_c, bound);
        let zero_within_bound = super::and_intro(
            &mut d,
            p,
            lower_ty,
            upper_ty,
            neg_bound_nonpos,
            bound_nonneg,
        );

        let within_diff = rat_eq_rewrite(
            &mut d,
            rzero_c,
            diff,
            zero_eq_diff,
            zero_within_bound,
            &|d, t| super::within(d, p, t, bound),
        );

        let over_qq = d.lam_fv(qq_fv, nat, within_diff);
        d.lam_fv(pp_fv, nat, over_qq)
    };

    // hyp2 : Cauchy (sumRange zero_fn), via Exists.intro at K = 0.
    let hyp2 = {
        let one = d.level_one();
        let intro_name = p.rat.int.logic.exists_intro;
        let intro = d.kernel().const_(intro_name, vec![one]);
        d.apply(intro, &[nat, predicate_g, zero_nat, cauchy_hyp_at_zero])
    };

    let instance = d.lemma(
        p.sum_range_cauchy_of_dominated,
        &[zero_fn, zero_fn, pointwise, hyp2],
    );
    let inferred = d.kernel().infer(instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!(
            "sumRange_cauchy_of_dominated refused at the trivial f = g = \
             (fun _ => zero), K = 0 Cauchy witness instance: {error:?}"
        )
    });

    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Cauchy"),
        "the instantiated conclusion is not a `Cauchy` claim: {rendered}"
    );
    assert!(
        rendered.contains("sumRange"),
        "the instantiated conclusion is not over `sumRange`: {rendered}"
    );
}

/// `CReal.sumRange_converges_of_dominated` and `CReal.sumRange_comparisonTest`
/// — the two-step composition this development's module documentation named
/// as the remaining work once `CReal.converges_of_cauchy` closed the
/// `Cauchy → Converges` bridge. Same `f = g` constant-zero series the
/// previous test verifies against (still this development's only
/// provably-`Cauchy` series), so the instance is genuinely **non-degenerate**
/// for what it exercises: a real `Exists.rec` elimination of a `Converges`
/// witness inside `sumRange_comparisonTest` (not just an `Exists.intro`, the
/// direction the previous test alone covers), and `abs_le`/`neg_le_neg`/
/// `le_congr`/`le_trans` combined into `abs (a k) ≤ b k` from `0 ≤ a k ≤
/// b k` at a genuinely nonzero-looking pair of hypotheses (`a = b = zero_fn`,
/// so `0 ≤ 0 ≤ 0`, but through the theorem's own general two-hypothesis
/// shape rather than a shortcut like `le_refl` applied to the conclusion
/// directly).
#[test]
fn sum_range_converges_of_dominated_and_comparison_test_close_the_zero_series() {
    use crate::expr::ExprId;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{
        radd, rat_eq_rewrite, rchain, rcongr, req, rle, rneg, rrefl, rsymm, rtrans, rzero,
    };

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();
    let rat = p.rat;

    // zero_fn := λ _ : Nat, CReal.zero — verbatim the previous test's fixture.
    let zero_fn = {
        let k_fv = d.fresh_fvar();
        let _k = d.kernel().fvar(k_fv);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        d.lam_fv(k_fv, nat, zero_c)
    };

    let zero_seq_at = |d: &mut IntDev<'_>, n_val: ExprId| -> ExprId {
        let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let sum_x = d.const_app(p.sum_range, &[zero_fn, x]);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let lhs = super::sample(d, p, sum_x, k);
            let rzero_c = rzero(d, rat);
            let claim = req(d, lhs, rzero_c);
            d.pi_fv(k_fv, nat, claim)
        };
        d.induct(
            &motive,
            &|d| d.lemma(p.sum_range_seq_zero, &[zero_fn]),
            &|d, j, ih| {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sk = super::shift(d, k);
                let step = d.lemma(p.sum_range_seq_succ, &[zero_fn, j, k]);

                let sum_j = d.const_app(p.sum_range, &[zero_fn, j]);
                let left_sample = super::sample(d, p, sum_j, sk);
                let zfj = d.apply(zero_fn, &[j]);
                let right_sample = super::sample(d, p, zfj, sk);
                let start = radd(d, left_sample, right_sample);

                let rzero_c = rzero(d, rat);
                let ih_at_sk = d.apply(ih, &[sk]);
                let right_is_zero = rrefl(d, rzero_c);

                let after_left = radd(d, rzero_c, right_sample);
                let step1 = rcongr(d, left_sample, rzero_c, ih_at_sk, &|d, t| {
                    radd(d, t, right_sample)
                });
                let after_right = radd(d, rzero_c, rzero_c);
                let step2 = rcongr(d, right_sample, rzero_c, right_is_zero, &|d, t| {
                    radd(d, rzero_c, t)
                });
                let collapse = d.lemma(rat.add_zero, &[rzero_c]);

                let (_, chained) = rchain(
                    d,
                    start,
                    &[
                        (after_left, step1),
                        (after_right, step2),
                        (rzero_c, collapse),
                    ],
                );
                let succ_sample = {
                    let sj = d.succ(j);
                    let sum_sj = d.const_app(p.sum_range, &[zero_fn, sj]);
                    super::sample(d, p, sum_sj, k)
                };
                let total = rtrans(d, succ_sample, start, rzero_c, step, chained);

                d.lam_fv(k_fv, nat, total)
            },
            n_val,
        )
    };

    let zero_nat = d.num(0);

    // pointwise : ∀ k, le (abs (zero_fn k)) (zero_fn k) — verbatim the
    // previous test's fixture, reused for the `sum_range_converges_of_dominated`
    // instance below.
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zk = d.apply(zero_fn, &[k]);
        let body = d.lemma(p.le_abs_self, &[zk]);
        d.lam_fv(k_fv, nat, body)
    };

    let cauchy_stmt_at = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);
        let sum_pp = d.const_app(p.sum_range, &[zero_fn, pp]);
        let sum_qq = d.const_app(p.sum_range, &[zero_fn, qq]);
        let left = super::sample(d, p, sum_pp, pp);
        let right = super::sample(d, p, sum_qq, qq);
        let diff = rsub(d, rat, left, right);
        let bpp = d.const_app(rat.nat_div_succ, &[k, pp]);
        let bqq = d.const_app(rat.nat_div_succ, &[k, qq]);
        let bound = radd(d, bpp, bqq);
        let claim = super::within(d, p, diff, bound);
        let over_qq = d.pi_fv(qq_fv, nat, claim);
        d.pi_fv(pp_fv, nat, over_qq)
    };

    let predicate_g = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = cauchy_stmt_at(&mut d, k);
        d.lam_fv(k_fv, nat, body)
    };

    let cauchy_hyp_at_zero = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);

        let left_eq = {
            let at_pp = zero_seq_at(&mut d, pp);
            d.apply(at_pp, &[pp])
        };
        let right_eq = {
            let at_qq = zero_seq_at(&mut d, qq);
            d.apply(at_qq, &[qq])
        };

        let sum_pp = d.const_app(p.sum_range, &[zero_fn, pp]);
        let sum_qq = d.const_app(p.sum_range, &[zero_fn, qq]);
        let left = super::sample(&mut d, p, sum_pp, pp);
        let right = super::sample(&mut d, p, sum_qq, qq);
        let diff = rsub(&mut d, rat, left, right);
        let rzero_c = rzero(&mut d, rat);

        let after_left = rsub(&mut d, rat, rzero_c, right);
        let step1 = rcongr(&mut d, left, rzero_c, left_eq, &|d, t| {
            rsub(d, rat, t, right)
        });
        let after_right = rsub(&mut d, rat, rzero_c, rzero_c);
        let step2 = rcongr(&mut d, right, rzero_c, right_eq, &|d, t| {
            rsub(d, rat, rzero_c, t)
        });

        let neg_zero_eq = d.lemma(rat.neg_zero, &[]);
        let neg_zero_term = rneg(&mut d, rzero_c);
        let zero_plus_neg_zero = radd(&mut d, rzero_c, neg_zero_term);
        let zero_plus_zero = radd(&mut d, rzero_c, rzero_c);
        let step3a = rcongr(&mut d, neg_zero_term, rzero_c, neg_zero_eq, &|d, t| {
            radd(d, rzero_c, t)
        });
        let add_zero_eq = d.lemma(rat.add_zero, &[rzero_c]);
        let step3 = rtrans(
            &mut d,
            zero_plus_neg_zero,
            zero_plus_zero,
            rzero_c,
            step3a,
            add_zero_eq,
        );

        let (_, diff_eq_zero) = rchain(
            &mut d,
            diff,
            &[(after_left, step1), (after_right, step2), (rzero_c, step3)],
        );
        let zero_eq_diff = rsymm(&mut d, diff, rzero_c, diff_eq_zero);

        let bpp = d.const_app(rat.nat_div_succ, &[zero_nat, pp]);
        let bqq = d.const_app(rat.nat_div_succ, &[zero_nat, qq]);
        let bound = radd(&mut d, bpp, bqq);

        let nonneg_pp = d.lemma(rat.zero_le_nat_div_succ, &[zero_nat, pp]);
        let nonneg_qq = d.lemma(rat.zero_le_nat_div_succ, &[zero_nat, qq]);
        let bound_nonneg = d.lemma(rat.add_nonneg, &[bpp, bqq, nonneg_pp, nonneg_qq]);
        let neg_bound_nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, bound_nonneg]);
        let neg_bound = rneg(&mut d, bound);
        let lower_ty = rle(&mut d, rat, neg_bound, rzero_c);
        let upper_ty = rle(&mut d, rat, rzero_c, bound);
        let zero_within_bound = super::and_intro(
            &mut d,
            p,
            lower_ty,
            upper_ty,
            neg_bound_nonpos,
            bound_nonneg,
        );

        let within_diff = rat_eq_rewrite(
            &mut d,
            rzero_c,
            diff,
            zero_eq_diff,
            zero_within_bound,
            &|d, t| super::within(d, p, t, bound),
        );

        let over_qq = d.lam_fv(qq_fv, nat, within_diff);
        d.lam_fv(pp_fv, nat, over_qq)
    };

    // hyp2 : Cauchy (sumRange zero_fn), via Exists.intro at K = 0.
    let hyp2 = {
        let one = d.level_one();
        let intro_name = p.rat.int.logic.exists_intro;
        let intro = d.kernel().const_(intro_name, vec![one]);
        d.apply(intro, &[nat, predicate_g, zero_nat, cauchy_hyp_at_zero])
    };

    // --- `sum_range_converges_of_dominated` --------------------------------

    let converges_instance = d.lemma(
        p.sum_range_converges_of_dominated,
        &[zero_fn, zero_fn, pointwise, hyp2],
    );
    let converges_ty = d
        .kernel()
        .infer(converges_instance)
        .unwrap_or_else(|error| {
            panic!(
                "sumRange_converges_of_dominated refused at the f = g = \
             (fun _ => zero) instance: {error:?}"
            )
        });
    let converges_rendered = kernel.render_lean(converges_ty);
    assert!(
        converges_rendered.contains("Exists"),
        "the conclusion is not existential: {converges_rendered}"
    );
    assert!(
        converges_rendered.contains("Converges"),
        "the conclusion is not a `Converges` claim: {converges_rendered}"
    );
    assert!(
        converges_rendered.contains("sumRange"),
        "the conclusion is not over `sumRange`: {converges_rendered}"
    );

    // conv_b : Exists (fun M => Converges (sumRange zero_fn) M), reused as the
    // `sumRange_comparisonTest` hypothesis below — the `Converges` witness
    // `sumRange_comparisonTest` must eliminate via `Exists.rec`.
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let sum_zero = d.const_app(p.sum_range, &[zero_fn]);
    let conv_b = d.lemma(p.converges_of_cauchy, &[sum_zero, hyp2]);

    // --- `sum_range_comparisonTest` -----------------------------------------

    // nonneg : ∀ k, le zero (zero_fn k), via le_refl at CReal.zero.
    let nonneg = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zk = d.apply(zero_fn, &[k]);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        let body = d.lemma(p.le_refl, &[zero_c]);
        let _ = zk;
        d.lam_fv(k_fv, nat, body)
    };
    // dominates : ∀ k, le (zero_fn k) (zero_fn k), via le_refl.
    let dominates = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zk = d.apply(zero_fn, &[k]);
        let body = d.lemma(p.le_refl, &[zk]);
        d.lam_fv(k_fv, nat, body)
    };

    let comparison_instance = d.lemma(
        p.sum_range_comparison_test,
        &[zero_fn, zero_fn, nonneg, dominates, conv_b],
    );
    let comparison_ty = d
        .kernel()
        .infer(comparison_instance)
        .unwrap_or_else(|error| {
            panic!(
                "sumRange_comparisonTest refused at the a = b = (fun _ => zero) \
             instance: {error:?}"
            )
        });
    let comparison_rendered = kernel.render_lean(comparison_ty);
    assert!(
        comparison_rendered.contains("Exists"),
        "the conclusion is not existential: {comparison_rendered}"
    );
    assert!(
        comparison_rendered.contains("Converges"),
        "the conclusion is not a `Converges` claim: {comparison_rendered}"
    );
    assert!(
        comparison_rendered.contains("sumRange"),
        "the conclusion is not over `sumRange`: {comparison_rendered}"
    );
}

/// Negative control for `CReal.sumRange_cauchy_of_abs_cauchy` /
/// `CReal.sumRange_converges_of_abs_converges`: absolute convergence implies
/// convergence, never the other way round -- classically, conditional
/// convergence (e.g. the alternating harmonic series) is `Cauchy (sumRange
/// f)` with `sumRange (fun k => abs (f k))` genuinely divergent, so the
/// REVERSE implication is not merely unbuilt here, it is false. This test
/// checks that the trusted kernel actually enforces the direction: reusing
/// [`CRealPrelude::sum_range_cauchy_of_dominated`]'s own proof VALUE (which
/// only ever inhabits `Cauchy (sumRange f)`, never `Cauchy (sumRange (fun k
/// => abs (f k)))`) against a declared type with the two `Cauchy` claims
/// SWAPPED must be REJECTED -- if it were accepted, nothing would be
/// discriminating the hypothesis from the conclusion, i.e. the checker could
/// not fail on a reversed claim.
#[test]
fn sum_range_cauchy_of_abs_cauchy_direction_is_checked_not_assumed() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();
    let carrier = super::creal_ty(&mut d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let absf = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let abs_fk = d.const_app(p.abs, &[fk]);
        d.lam_fv(k_fv, nat, abs_fk)
    };
    let sum_absf = d.const_app(p.sum_range, &[absf]);
    let sum_f = d.const_app(p.sum_range, &[f]);
    let cauchy_absf_ty = d.const_app(p.cauchy, &[sum_absf]);
    let cauchy_f_ty = d.const_app(p.cauchy, &[sum_f]);

    let hyp1 = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let abs_fk = d.const_app(p.abs, &[fk]);
        let refl = d.lemma(p.le_refl, &[abs_fk]);
        d.lam_fv(k_fv, nat, refl)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    // `proof_body` genuinely only inhabits `Cauchy (sumRange f)` -- this is
    // exactly `declare_sum_range_cauchy_of_abs_cauchy`'s own proof term.
    let proof_body = d.lemma(p.sum_range_cauchy_of_dominated, &[f, absf, hyp1, hyp]);

    // `reversed_ty` swaps hypothesis and conclusion relative to the real
    // theorem: `∀ f, Cauchy (sumRange f) → Cauchy (sumRange (fun k => abs (f
    // k)))` -- the false converse.
    let reversed_ty = {
        let after_hyp = d.arrow(cauchy_f_ty, cauchy_absf_ty);
        d.pi_fv(f_fv, fn_ty, after_hyp)
    };
    let reversed_value = {
        let with_hyp = d.lam_fv(hyp_fv, cauchy_absf_ty, proof_body);
        d.lam_fv(f_fv, fn_ty, with_hyp)
    };
    let bogus_name = d.kernel().name_str(p.creal, "scratchReversedAbsCauchy");
    let outcome = d.kernel().add_declaration(Declaration::Theorem {
        name: bogus_name,
        uparams: vec![],
        ty: reversed_ty,
        value: reversed_value,
    });
    assert!(
        outcome.is_err(),
        "the trusted checker admitted the REVERSED claim `Cauchy (sumRange f) \
         -> Cauchy (sumRange (fun k => abs (f k)))` using the real theorem's \
         own proof value -- absolute-convergence direction is not actually \
         being enforced: {outcome:?}"
    );
}

/// The three setoid laws say what ADR-0512 says they say. An empty footprint on
/// a theorem stating something weaker is this repository's standing failure
/// mode, so the rendered types are asserted verbatim.
#[test]
fn the_setoid_laws_have_the_statements_adr_0468_specifies() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.equiv_refl),
        "((x0 : CReal) -> CReal.Equiv x0 x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.equiv_symm),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Equiv x0 x1) -> CReal.Equiv x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.equiv_trans),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.Equiv x0 x1) -> \
         ((x4 : CReal.Equiv x1 x2) -> CReal.Equiv x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_zero_one),
        "Not (CReal.Equiv (CReal.ofRat Rat.zero) (CReal.ofRat Rat.one))"
    );
    // The two of the 22 that hold in `Equiv` form. Asserting these verbatim is
    // what stops "N laws hold" drifting into "N laws are named".
    assert_eq!(
        rendered(&mut kernel, p.add_comm),
        "((x0 : CReal) -> ((x1 : CReal) -> \
         CReal.Equiv (CReal.add x0 x1) (CReal.add x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_neg),
        "((x0 : CReal) -> \
         CReal.Equiv (CReal.add x0 (CReal.neg x0)) CReal.zero)"
    );
    // The two that are NOT pointwise, and are the reason `Equiv` had to be an
    // equivalence relation before any of this was worth stating.
    assert_eq!(
        rendered(&mut kernel, p.add_zero),
        "((x0 : CReal) -> CReal.Equiv (CReal.add x0 CReal.zero) x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_assoc),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         CReal.Equiv (CReal.add (CReal.add x0 x1) x2) \
         (CReal.add x0 (CReal.add x1 x2)))))"
    );
    // The three order laws. Unlike the additive ones these are the `Real`
    // package's statements VERBATIM — none of them mentions `Eq`, so there is
    // no equality to replace by `Equiv` (ADR-0512, Measurement 2).
    assert_eq!(
        rendered(&mut kernel, p.le_refl),
        "((x0 : CReal) -> CReal.le x0 x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.le_trans),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.le x0 x1) -> \
         ((x4 : CReal.le x1 x2) -> CReal.le x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_le_add),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.le x0 x1) -> ((x5 : CReal.le x2 x3) -> \
         CReal.le (CReal.add x0 x2) (CReal.add x1 x3)))))))"
    );
    // The order is the order OF this setoid, not an unexamined relation that
    // happens to satisfy three laws.
    assert_eq!(
        rendered(&mut kernel, p.le_of_equiv),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Equiv x0 x1) -> CReal.le x0 x1)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.equiv_of_le_le),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.le x0 x1) -> \
         ((x3 : CReal.le x1 x0) -> CReal.Equiv x0 x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_le_one_zero),
        "Not (CReal.le CReal.one CReal.zero)"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         CReal.Equiv (CReal.add x0 x2) (CReal.add x1 x3)))))))"
    );
    // The seven strict-order laws, also VERBATIM: like the three `le` laws,
    // none of them mentions `Eq`, so the `Real` package's statement is the
    // statement proved here — no `Equiv` restatement, nothing weakened.
    assert_eq!(
        rendered(&mut kernel, p.lt_irrefl),
        "((x0 : CReal) -> Not (CReal.lt x0 x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_trans),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.lt x0 x1) -> \
         ((x4 : CReal.lt x1 x2) -> CReal.lt x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_of_lt_of_le),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.lt x0 x1) -> \
         ((x4 : CReal.le x1 x2) -> CReal.lt x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_of_le_of_lt),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.le x0 x1) -> \
         ((x4 : CReal.lt x1 x2) -> CReal.lt x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.le_of_lt),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.lt x0 x1) -> CReal.le x0 x1)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.zero_lt_one),
        "CReal.lt CReal.zero CReal.one"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_lt_add_of_le_of_lt),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.le x0 x1) -> ((x5 : CReal.lt x2 x3) -> \
         CReal.lt (CReal.add x0 x2) (CReal.add x1 x3)))))))"
    );
    // The two relation congruences of the setoid telescope's equality slot.
    assert_eq!(
        rendered(&mut kernel, p.le_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         ((x6 : CReal.le x0 x2) -> CReal.le x1 x3)))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         ((x6 : CReal.lt x0 x2) -> CReal.lt x1 x3)))))))"
    );
    // The five product laws. Two of the 22 in `Equiv` form, three verbatim —
    // and `mul_nonneg`/`sq_nonneg` are the `Real` package's statements
    // unchanged, so a weakened restatement would show up here as a diff.
    assert_eq!(
        rendered(&mut kernel, p.mul_comm),
        "((x0 : CReal) -> ((x1 : CReal) -> \
         CReal.Equiv (CReal.mul x0 x1) (CReal.mul x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_one),
        "((x0 : CReal) -> CReal.Equiv (CReal.mul x0 CReal.one) x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_zero),
        "((x0 : CReal) -> CReal.Equiv (CReal.mul x0 CReal.zero) CReal.zero)"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_nonneg),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.le CReal.zero x0) -> \
         ((x3 : CReal.le CReal.zero x1) -> CReal.le CReal.zero (CReal.mul x0 x1)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.sq_nonneg),
        "((x0 : CReal) -> CReal.le CReal.zero (CReal.mul x0 x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_assoc),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         CReal.Equiv (CReal.mul (CReal.mul x0 x1) x2) \
         (CReal.mul x0 (CReal.mul x1 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.left_distrib),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         CReal.Equiv (CReal.mul x0 (CReal.add x1 x2)) \
         (CReal.add (CReal.mul x0 x1) (CReal.mul x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_le_mul_of_nonneg_left),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         ((x3 : CReal.le CReal.zero x0) -> ((x4 : CReal.le x1 x2) -> \
         CReal.le (CReal.mul x0 x1) (CReal.mul x0 x2))))))"
    );
    // The fifth congruence obligation — not one of the 22, and the R4
    // prerequisite ADR-0512 calls the setoid's real tax.
    assert_eq!(
        rendered(&mut kernel, p.mul_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         CReal.Equiv (CReal.mul x0 x2) (CReal.mul x1 x3)))))))"
    );
    // The two witnesses that stop the five above being satisfiable by a
    // degenerate product. `ofRat_mul` pins the OPERATION on the embedded `ℚ`;
    // `not_equiv_mul_one_one_zero` exhibits a separated pair by computation.
    assert_eq!(
        rendered(&mut kernel, p.of_rat_mul),
        "((x0 : Rat) -> ((x1 : Rat) -> \
         CReal.Equiv (CReal.mul (CReal.ofRat x0) (CReal.ofRat x1)) \
         (CReal.ofRat (Rat.mul x0 x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_equiv_mul_one_one_zero),
        "Not (CReal.Equiv (CReal.mul CReal.one CReal.one) CReal.zero)"
    );
    // The canonical bound is a bound on EVERY sample, not just the zeroth —
    // which is the whole reason `CReal.mul`'s index can be a fixed function of
    // the two factors.
    assert_eq!(
        rendered(&mut kernel, p.bound_within),
        "((x0 : CReal) -> ((x1 : AxNat) -> \
         CReal.Within (CReal.seq x0 x1) \
         (Rat.natDivSucc (AxNat.succ (CReal.bound x0)) AxNat.zero)))"
    );
}

/// **The product is not the degenerate one**, and the check is by computation.
///
/// `CReal.mul_zero`, `CReal.mul_comm` and `CReal.sq_nonneg` all hold — with
/// empty axiom footprints — of `fun _ _ => CReal.zero`. So does every
/// footprint check that only asks whether they were *derived*. This asks the
/// kernel for a closed instance instead: `1 · 1` is `Equiv`-equal to `1`, and
/// `Equiv 1 0` is refuted.
#[test]
fn the_product_is_not_the_constant_zero() {
    let (kernel, p) = built();
    // PRESENCE FIRST. `Kernel::axiom_footprint` of a name that was interned but
    // never declared is the empty vector, which is indistinguishable from
    // "declared and axiom-free" — the failure mode this repository keeps
    // rediscovering. Assert the declaration exists and is a Theorem before
    // reading anything off it.
    assert!(
        matches!(
            kernel.environment().get(p.not_equiv_mul_one_one_zero),
            Some(Declaration::Theorem { .. })
        ),
        "CReal.not_equiv_mul_one_one_zero must be a checked theorem: without it \
         nothing separates any product from zero, and mul_zero / mul_comm / \
         sq_nonneg all still hold of `fun _ _ => zero`"
    );
    assert!(
        matches!(
            kernel.environment().get(p.of_rat_mul),
            Some(Declaration::Theorem { .. })
        ),
        "CReal.ofRat_mul must be a checked theorem: without it nothing pins \
         CReal.mul to Rat.mul anywhere at all"
    );
    let footprint = kernel.axiom_footprint(p.not_equiv_mul_one_one_zero);
    assert!(
        footprint.is_empty(),
        "the product's discrimination witness rests on {:?}",
        footprint
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect::<Vec<_>>()
    );
}

/// The negative control for the product witness: the **same script**, pointed
/// at a claim that is false.
///
/// `Not (Equiv (mul one one) one)` is false — `mul_one` proves the positive
/// form — and it differs from the proved witness in one constant. The kernel
/// must refuse it, which is what says the witness is checking the pair it
/// names rather than any pair.
#[test]
fn the_product_discrimination_route_cannot_refute_mul_one_one_one() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_eq_rewrite, rmul, rone};

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);

    let cone = d.kernel().const_(p.one, vec![]);
    let product = d.const_app(p.mul, &[cone, cone]);
    let claim = super::equiv(&mut d, p, product, cone);
    let stmt = d.not(claim);

    let unit = rone(&mut d, rat);
    let homomorphism = d.lemma(p.of_rat_mul, &[unit, unit]);
    let square = rmul(&mut d, unit, unit);
    let collapse = d.lemma(rat.mul_one, &[unit]);
    let at_one = rat_eq_rewrite(&mut d, square, unit, collapse, homomorphism, &|d, t| {
        let embedded = d.const_app(p.of_rat, &[t]);
        super::equiv(d, p, product, embedded)
    });
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let reversed = d.lemma(p.equiv_symm, &[product, cone, h]);
    let chained = d.lemma(p.equiv_trans, &[cone, product, cone, reversed, at_one]);
    let absurd = d.lemma(p.not_zero_one, &[chained]);
    let value = d.lam_fv(h_fv, claim, absurd);
    let name = d.kernel().name_str(anon, "Check.not_mul_one_one_one");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stmt,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Not (CReal.Equiv (mul one one) one)`, which \
         contradicts CReal.mul_one — the product witness proves nothing"
    );
}

/// **`CReal.lt` is the strict order ADR-0512 asks for, not a negation.**
///
/// The definition is asserted verbatim because the two rejected shapes differ
/// from it only in the body: `Not (le y x)` would render as a `Not`, and
/// `∃ n : Nat, …` would quantify over `Nat`. This quantifies over a **rational
/// gap**, which is what makes `le_of_lt` constructive and `lt_trans` carry its
/// witness through untouched.
#[test]
fn lt_quantifies_over_a_positive_rational_gap() {
    let (kernel, p) = built();
    let value = match kernel.environment().get(p.lt).expect("CReal.lt declared") {
        Declaration::Definition { value, .. } => *value,
        other => panic!("{other:?} is not a definition"),
    };
    let rendered = kernel
        .render_lean(value)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "fun (x0 : CReal) => fun (x1 : CReal) => Exists.{1} Rat \
         (fun (x2 : Rat) => And (Rat.lt Rat.zero x2) \
         (CReal.le (CReal.add x0 (CReal.ofRat x2)) x1))"
    );
}

/// **`CReal.lt` is neither empty nor total**, and both halves are needed.
///
/// Six of the seven strict-order laws *consume* a `lt`, so all six hold —
/// footprint-free — of the empty relation. `zero_lt_one` is the only one that
/// produces an inhabitant, and `lt_irrefl` is the only one that refuses a pair.
/// Together they are the discrimination witness the axiom footprint cannot see.
#[test]
fn the_strict_order_discriminates() {
    let (kernel, p) = built();
    for (label, name) in [
        ("CReal.zero_lt_one", p.zero_lt_one),
        ("CReal.lt_irrefl", p.lt_irrefl),
    ] {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} must be declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "{label} must be a checked Theorem — an axiom would witness nothing"
        );
        assert!(
            kernel.axiom_footprint(name).is_empty(),
            "{label} must be axiom-free"
        );
    }
}

/// The negative control for `zero_lt_one`: the **same script**, with the two
/// constants swapped.
///
/// `lt one zero` is false, and the script that proves `lt zero one` reaches it
/// through `Rat.zero_add` on the sampled sum `0 + 1`. Pointed at `one + 1` that
/// rewrite does not apply, and the kernel must **refuse** — which is what says
/// the strict order is reading which sequence is being sampled rather than
/// merely assembling a bound.
#[test]
fn the_zero_lt_one_route_cannot_prove_one_lt_zero() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rchain, rcongr, rone, rsymm, rzero};

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);
    let nat = d.nat_ty();

    let zero_rat = rzero(&mut d, rat);
    let one_rat = rone(&mut d, rat);
    // The two changed tokens: the claim is `lt one zero`, not `lt zero one`.
    let zero_real = d.kernel().const_(p.zero, vec![]);
    let one_real = d.kernel().const_(p.one, vec![]);

    let bounded = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sum = radd(&mut d, one_rat, one_rat);
        let quantity = rsub(&mut d, rat, sum, zero_rat);
        let bound = super::div_succ(&mut d, p, 2, n);
        let unpad = d.lemma(rat.zero_add, &[one_rat]);
        let step = rcongr(&mut d, sum, one_rat, unpad, &|d, t| {
            rsub(d, rat, t, zero_rat)
        });
        let degenerate = rsub(&mut d, rat, one_rat, zero_rat);
        let collapse = d.lemma(rat.sub_self, &[one_rat]);
        let (_, to_zero) = rchain(
            &mut d,
            quantity,
            &[(degenerate, step), (zero_rat, collapse)],
        );
        let back = rsymm(&mut d, quantity, zero_rat, to_zero);
        let two = d.num(2);
        let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
        let at_index = rat_eq_rewrite(&mut d, zero_rat, quantity, back, nonneg, &|d, t| {
            crate::rat_prelude::ops::rle(d, rat, t, bound)
        });
        d.lam_fv(n_fv, nat, at_index)
    };
    let positive = crate::rat_prelude::ops::rlt(&mut d, rat, zero_rat, one_rat);
    let embedded = super::embed(&mut d, p, one_rat);
    let shifted = super::cadd(&mut d, p, one_real, embedded);
    let reached = super::cle(&mut d, p, shifted, zero_real);
    let strict = d.lemma(rat.zero_lt_one, &[]);
    let pair = super::and_intro(&mut d, p, positive, reached, strict, bounded);
    let value = super::gap_intro(&mut d, p, one_real, zero_real, one_rat, pair);
    let ty = super::clt(&mut d, p, one_real, zero_real);
    let name = d.kernel().name_str(anon, "Check.one_lt_zero");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `CReal.lt CReal.one CReal.zero`, which contradicts \
         CReal.lt_irrefl through lt_trans — the strict order proves nothing"
    );
}

/// **The carrier is inhabited.** Everything above is a statement about the
/// inhabitants of `CReal`; if `CReal.Regular` had no solutions the carrier
/// would be empty, `refl`/`symm`/`trans` would all hold vacuously, and the
/// axiom footprints would still be empty. `CReal.ofRat` is a *checked*
/// definition, so the kernel accepted a regularity proof for a concrete
/// sequence.
#[test]
fn the_carrier_is_inhabited() {
    let (kernel, p) = built();
    let declaration = kernel
        .environment()
        .get(p.of_rat)
        .expect("CReal.ofRat must be declared");
    assert!(
        matches!(declaration, Declaration::Definition { .. }),
        "CReal.ofRat must be a Definition — an axiom would not witness anything"
    );
}

/// **`CReal.Equiv` discriminates.** An equivalence relation that relates
/// everything is an equivalence relation, and worthless; this exhibits two
/// `CReal`s it separates.
#[test]
fn equiv_is_not_the_total_relation() {
    let (kernel, p) = built();
    assert!(
        matches!(
            kernel.environment().get(p.not_zero_one),
            Some(Declaration::Theorem { .. })
        ),
        "the discrimination witness must be a checked Theorem"
    );
}

/// The negative control for [`equiv_is_not_the_total_relation`]: the same proof
/// route, pointed at a pair `Equiv` does **not** separate.
///
/// `Equiv.not_zero_one` works because `−1/2 ≤ −1` reduces to `Nat.le 1 0`. If
/// the kernel's reduction were not actually deciding that, the identical script
/// with `ofRat 0` on **both** sides would also go through — and it would prove
/// `Not (Equiv x x)`, contradicting `Equiv.refl`. It must be **refused**.
#[test]
fn the_discrimination_route_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::rzero;

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);

    let zero_rat = rzero(&mut d, rat);
    let left = d.const_app(p.of_rat, &[zero_rat]);
    let claim = super::equiv(&mut d, p, left, left);
    let stmt = d.not(claim);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let index = d.num(3);
    let instance = d.apply(h, &[index]);
    let a = super::sample(&mut d, p, left, index);
    let difference = rsub(&mut d, rat, a, a);
    let bound = super::div_succ(&mut d, p, 2, index);
    let (lower, _upper) = super::halves(&mut d, p, difference, bound, instance);
    let zero_nat = d.zero();
    let absurd = d.lemma(rat.int.nat.not_succ_le_zero, &[zero_nat, lower]);
    let value = d.lam_fv(h_fv, claim, absurd);
    let name = d.kernel().name_str(anon, "Check.not_zero_zero");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stmt,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Not (CReal.Equiv (ofRat 0) (ofRat 0))`, which \
         contradicts CReal.Equiv.refl — the discrimination witness proves nothing"
    );
}

/// The negative control for `add_zero`: the **same script**, pointed at a law
/// that is false.
///
/// `add_zero` is the first law whose two sides are not equal at any index, so
/// what carries it is regularity plus a bound comparison — and a bound
/// comparison is exactly the kind of argument that would still go through if
/// the kernel were not actually looking at which sequence is being sampled.
/// `Equiv (add x one) x` is false, differs from the proved statement in one
/// constant, and must be **refused**.
#[test]
fn the_add_zero_route_cannot_prove_add_one() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rsymm, rzero};

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);
    let carrier = super::creal_ty(&mut d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    // The one changed token: `CReal.one` where the proved law has `CReal.zero`.
    let one_real = d.kernel().const_(p.one, vec![]);
    let left = d.const_app(p.add, &[x, one_real]);
    let body = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let index = super::shift(&mut d, n);
        let deep = super::sample(&mut d, p, x, index);
        let shallow = super::sample(&mut d, p, x, n);
        let difference = rsub(&mut d, rat, deep, shallow);
        let bound = super::modulus(&mut d, p, index, n);
        let goal_bound = super::div_succ(&mut d, p, 2, n);
        let source = d.lemma(p.regular, &[x, index, n]);
        let order = super::shifted_bound_le(&mut d, p, n);
        let widened = super::weaken(&mut d, p, difference, bound, goal_bound, source, order);
        let zero_rat = rzero(&mut d, rat);
        let padded = radd(&mut d, deep, zero_rat);
        let collapse = d.lemma(rat.add_zero, &[deep]);
        let restore = rsymm(&mut d, padded, deep, collapse);
        let at_index = rat_eq_rewrite(&mut d, deep, padded, restore, widened, &|d, t| {
            let quantity = rsub(d, rat, t, shallow);
            super::within(d, p, quantity, goal_bound)
        });
        d.lam_fv(n_fv, nat, at_index)
    };
    let value = d.lam_fv(x_fv, carrier, body);
    let ty = {
        let conclusion = super::equiv(&mut d, p, left, x);
        d.pi_fv(x_fv, carrier, conclusion)
    };
    let name = d.kernel().name_str(anon, "Check.add_one");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Equiv (add x one) x`, so the add_zero route is not \
         checking which sequence the shifted index samples"
    );
}

/// **`CReal.le` discriminates.** `le_refl`, `le_trans` and `add_le_add` all
/// hold — footprint-free — of the relation that relates every pair, so an
/// order that separates nothing would satisfy every law proved about it. This
/// is the negative control for `CReal.not_le_one_zero`: the identical script,
/// pointed at `le zero one`, which is TRUE and must therefore be refused as a
/// `Not`.
#[test]
fn the_order_discrimination_route_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);
    let nat_p = rat.int.nat;

    // The two constants, swapped: `le zero one` holds, so `Not` of it does not.
    let one_real = d.kernel().const_(p.one, vec![]);
    let zero_real = d.kernel().const_(p.zero, vec![]);
    let claim = d.const_app(p.le, &[zero_real, one_real]);
    let stmt = d.not(claim);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let index = d.num(3);
    let instance = d.apply(h, &[index]);
    let one_nat = d.num(1);
    let zero_nat = d.zero();
    let stripped = d.lemma(nat_p.le_of_succ_le_succ, &[one_nat, zero_nat, instance]);
    let absurd = d.lemma(nat_p.not_succ_le_zero, &[zero_nat, stripped]);
    let value = d.lam_fv(h_fv, claim, absurd);
    let name = d.kernel().name_str(anon, "Check.not_le_zero_one");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stmt,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Not (CReal.le CReal.zero CReal.one)`, which is false — \
         the order discrimination witness proves nothing"
    );
}

/// **The headline count, read out of the kernel.**
///
/// `CRealPrelude::ordered_ring_laws` is the 22 in the `Real` package's own
/// declaration order — the same order `RatPrelude::ring_laws` uses — and every
/// entry must be a checked `Theorem` with an empty axiom footprint. A dropped,
/// duplicated or demoted law fails here rather than shrinking a sentence in a
/// document nobody re-derives.
#[test]
fn all_twenty_two_ordered_ring_laws_are_checked_theorems_over_creal() {
    let (kernel, p) = built();
    let laws = p.ordered_ring_laws();
    assert_eq!(laws.len(), 22);
    let mut names: Vec<String> = laws
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    names.sort();
    names.dedup();
    assert_eq!(
        names.len(),
        22,
        "the ordered-ring law list must have 22 DISTINCT entries; a repeated \
         name would inflate the count without proving anything"
    );
    for (index, law) in p.ordered_ring_laws().into_iter().enumerate() {
        let rendered = kernel.display_name(law).to_string();
        let declaration = kernel
            .environment()
            .get(law)
            .unwrap_or_else(|| panic!("ring law #{index} ({rendered}) is not declared at all"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "ring law #{index} ({rendered}) must be a checked Theorem"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(law)
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect();
        assert!(
            footprint.is_empty(),
            "ring law #{index} ({rendered}) rests on {footprint:?}"
        );
    }
}

/// The `CReal` and `Rat` law lists are the **same 22 laws in the same order**,
/// name for name under their own namespaces.
///
/// Without this the two lists could drift — `CReal` could quietly omit
/// `mul_assoc` and add a second `mul_comm` — and both would still be "22
/// checked theorems". `build_rat_model_of_arith` pairs `RatPrelude::ring_laws`
/// positionally with the `Real` package, so this is what says `CReal`'s list is
/// the same interface and not merely the same length.
#[test]
fn the_creal_law_list_matches_the_rat_law_list_position_by_position() {
    let (kernel, p) = built();
    let real: Vec<String> = p
        .ordered_ring_laws()
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    let rational: Vec<String> = p
        .rat
        .ring_laws()
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    let strip = |full: &str| -> String { full.split('.').skip(1).collect::<Vec<_>>().join(".") };
    let real_tails: Vec<String> = real.iter().map(|name| strip(name)).collect();
    let rational_tails: Vec<String> = rational.iter().map(|name| strip(name)).collect();
    assert_eq!(
        real_tails, rational_tails,
        "CReal's ordered-ring law list must be the SAME 22 laws in the SAME \
         order as Rat's, or the two are not the same interface"
    );
}

/// The apartness laws say what Bishop says they say, rendered verbatim.
///
/// The statements are the point here, not the footprints: `Apart` defined as
/// `Not ∘ Equiv` would satisfy symmetry, irreflexivity and the congruence with
/// an empty footprint apiece, and it is exactly the relation the inverse cannot
/// be defined over. So the *definition* is asserted too, through
/// `CReal.apart_zero_one` — which is `zero_lt_one` under `Or.inl` and could not
/// be proved for a relation that separates nothing.
#[test]
fn the_apartness_laws_have_the_statements_bishop_specifies() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.apart_symm),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Apart x0 x1) -> CReal.Apart x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.apart_irrefl),
        "((x0 : CReal) -> Not (CReal.Apart x0 x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.apart_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         ((x6 : CReal.Apart x0 x2) -> CReal.Apart x1 x3)))))))"
    );
    // ONE-WAY. The converse is Markov's principle; nothing here proves it and
    // nothing here assumes it.
    assert_eq!(
        rendered(&mut kernel, p.not_equiv_of_apart),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Apart x0 x1) -> \
         Not (CReal.Equiv x0 x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.apart_zero_one),
        "CReal.Apart CReal.zero CReal.one"
    );
}

/// **The missing structure is a theorem.** `CReal.no_total_inverse` refutes
/// every total multiplicative inverse at once, so "the inverse is partial"
/// is a proved obstruction rather than a scoping note — the standard
/// `Complex.no_compatible_order` set.
#[test]
fn no_function_on_all_of_creal_is_a_multiplicative_inverse() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.no_total_inverse)
        .expect("CReal.no_total_inverse must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    let rendered = kernel
        .render_lean(ty)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "((x0 : ((x0 : CReal) -> CReal)) -> \
         Not (((x1 : CReal) -> CReal.Equiv (CReal.mul x1 (x0 x1)) CReal.one)))"
    );
    let footprint: Vec<String> = kernel
        .axiom_footprint(p.no_total_inverse)
        .into_iter()
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    assert!(
        footprint.is_empty(),
        "the refutation of a total inverse rests on {footprint:?}"
    );
}

/// The negative control for [`no_function_on_all_of_creal_is_a_multiplicative_inverse`]:
/// the **identical script**, with `CReal.one` replaced by `CReal.zero` in the
/// statement, is REFUSED.
///
/// `∀ f, ¬ ∀ x, x · f x ≈ 0` is false — `f := fun _ => zero` satisfies the
/// inner law by `mul_zero` — so a script that proved it would prove anything.
/// The refusal is what says `no_total_inverse` closes on the *content* of
/// `Equiv.not_zero_one` and not on a shape that would go through for any
/// right-hand side.
#[test]
fn the_no_total_inverse_route_cannot_refute_a_universally_zero_product() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let function_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    // The one changed token: the target of the inner law is `zero`, not `one`.
    let target = d.kernel().const_(p.zero, vec![]);
    let law = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let applied = d.apply(f, &[x]);
        let product = d.const_app(p.mul, &[x, applied]);
        let claim = d.const_app(p.equiv, &[product, target]);
        d.pi_fv(x_fv, carrier, claim)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = d.kernel().const_(p.zero, vec![]);
    let reciprocal = d.apply(f, &[zero]);
    let product = d.const_app(p.mul, &[zero, reciprocal]);
    let flipped = d.const_app(p.mul, &[reciprocal, zero]);
    let commuted = d.lemma(p.mul_comm, &[zero, reciprocal]);
    let vanishes = d.lemma(p.mul_zero, &[reciprocal]);
    let collapses = d.lemma(p.equiv_trans, &[product, flipped, zero, commuted, vanishes]);
    let restored = d.lemma(p.equiv_symm, &[product, zero, collapses]);
    let at_zero = d.apply(h, &[zero]);
    let degenerate = d.lemma(p.equiv_trans, &[zero, product, target, restored, at_zero]);
    let refuted = d.lemma(p.not_zero_one, &[]);
    let contradiction = d.apply(refuted, &[degenerate]);

    let value = {
        let with_h = d.lam_fv(h_fv, law, contradiction);
        d.lam_fv(f_fv, function_ty, with_h)
    };
    let ty = {
        let negated = d.not(law);
        d.pi_fv(f_fv, function_ty, negated)
    };
    let name = d.kernel().name_str(anon, "Check.no_total_annihilator");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted a refutation of `∀ x, x · f x ≈ 0`, which is FALSE \
         (take f := fun _ => zero). The no_total_inverse script would then close \
         for any right-hand side, and its content would be nil."
    );
}

/// **`0 < x` and `∃ k, 1/(k+1) ≤ x` are the same proposition — and that is
/// exactly why the inverse cannot take a `Prop` as its domain.**
///
/// The two directions are asserted verbatim. `pos_bound_of_lt` says the
/// separating modulus always exists; `Exists` is a `Prop`, so `Exists.rec`
/// eliminates only into `Prop` and the `k` can never be extracted into a
/// `CReal`. `PosBound x k` is a `Prop` *about a `Nat` the caller supplies*,
/// which is why a function may take it and still return a `CReal`.
#[test]
fn positivity_and_a_witnessed_modulus_are_the_same_proposition() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.pos_of_pos_bound),
        "((x0 : CReal) -> ((x1 : AxNat) -> ((x2 : CReal.PosBound x0 x1) -> \
         CReal.lt CReal.zero x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.pos_bound_of_lt),
        "((x0 : CReal) -> ((x1 : CReal.lt CReal.zero x0) -> \
         Exists.{1} AxNat (fun (x2 : AxNat) => CReal.PosBound x0 x2)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.of_rat_le),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat.le x0 x1) -> \
         CReal.le (CReal.ofRat x0) (CReal.ofRat x1))))"
    );
    for (label, name) in [
        ("ofRat_le", p.of_rat_le),
        ("pos_of_pos_bound", p.pos_of_pos_bound),
        ("pos_bound_of_lt", p.pos_bound_of_lt),
    ] {
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "CReal.{label} rests on {footprint:?}");
    }
}

/// **Positivity is closed under multiplication over the constructed reals**, and
/// the statement is asserted verbatim because `mul_nonneg` — which IS one of the
/// 22 — holds of the zero product and this does not.
#[test]
fn positivity_is_closed_under_multiplication() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.mul_pos),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.lt CReal.zero x0) -> \
         ((x3 : CReal.lt CReal.zero x1) -> CReal.lt CReal.zero (CReal.mul x0 x1)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.of_rat_pos),
        "((x0 : Rat) -> ((x1 : Rat.lt Rat.zero x0) -> \
         CReal.lt CReal.zero (CReal.ofRat x0)))"
    );
    for (label, name) in [("mul_pos", p.mul_pos), ("ofRat_pos", p.of_rat_pos)] {
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "CReal.{label} rests on {footprint:?}");
    }
}

/// **The multiplicative inverse exists, and the modulus is the argument that
/// makes it exist.** Statements asserted verbatim, because a theorem named
/// `mul_inv_cancel` saying something weaker would pass a footprint check.
///
/// Read `CReal.inv`'s type as the whole ADR-0510 argument in one line: the
/// `Nat` is explicit and the `PosBound` is a hypothesis over it, so nothing is
/// ever eliminated out of a `Prop` into `Type` — which is precisely what
/// `Apart x zero` (an `Or`) would demand.
#[test]
fn the_inverse_is_partial_and_its_modulus_is_an_explicit_nat() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.inv),
        "((x0 : CReal) -> ((x1 : AxNat) -> ((x2 : CReal.PosBound x0 x1) -> CReal)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.inv_shift),
        "((x0 : AxNat) -> AxNat)"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_inv_cancel),
        "((x0 : CReal) -> ((x1 : AxNat) -> ((x2 : CReal.PosBound x0 x1) -> \
         CReal.Equiv (CReal.mul x0 (CReal.inv x0 x1 x2)) CReal.one)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.inv_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : AxNat) -> ((x3 : AxNat) -> \
         ((x4 : CReal.PosBound x0 x2) -> ((x5 : CReal.PosBound x1 x3) -> \
         ((x6 : CReal.Equiv x0 x1) -> \
         CReal.Equiv (CReal.inv x0 x2 x4) (CReal.inv x1 x3 x5))))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.inv_index_irrelevant),
        "((x0 : CReal) -> ((x1 : AxNat) -> ((x2 : AxNat) -> \
         ((x3 : CReal.PosBound x0 x1) -> ((x4 : CReal.PosBound x0 x2) -> \
         CReal.Equiv (CReal.inv x0 x1 x3) (CReal.inv x0 x2 x4))))))"
    );
    for (label, name) in [
        ("invShift", p.inv_shift),
        ("inv", p.inv),
        ("mul_inv_cancel", p.mul_inv_cancel),
        ("inv_congr", p.inv_congr),
        ("inv_index_irrelevant", p.inv_index_irrelevant),
    ] {
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "CReal.{label} rests on {footprint:?}");
    }
}

/// **The inverse's domain is inhabited, and the inverse is not the constant
/// zero.** Without this the whole slice is vacuous: every statement about
/// `CReal.inv` is guarded by `PosBound x k`, so if that predicate had no
/// inhabitants `mul_inv_cancel`, `inv_congr` and `inv_index_irrelevant` would
/// all hold, footprint-free, of an operation that never runs.
///
/// Both halves go through the kernel. `PosBound CReal.one 0` is admitted — the
/// modulus `1/(0+1)` is `Rat.one`, so `CReal.le_refl` closes it — and then
/// `∀ h, ¬ Equiv (inv one 0 h) zero` is admitted from `mul_inv_cancel` alone:
/// if `1⁻¹ ≈ 0` then `1 · 1⁻¹ ≈ 1 · 0 ≈ 0` and also `≈ 1`, and
/// `Equiv.not_zero_one` refutes that **by computation**.
#[test]
fn the_inverses_domain_is_inhabited_and_the_inverse_is_not_the_zero_function() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let one = d.kernel().const_(p.one, vec![]);
    let zero = d.kernel().const_(p.zero, vec![]);
    let zero_nat = d.num(0);
    let bound_ty = d.const_app(p.pos_bound, &[one, zero_nat]);
    let bound_proof = d.lemma(p.le_refl, &[one]);
    let name = d.kernel().name_str(anon, "Check.pos_bound_one");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: bound_ty,
        value: bound_proof,
    });
    assert!(
        admitted.is_ok(),
        "CReal.PosBound one 0 is not inhabited, so every theorem about \
         CReal.inv is vacuous: {admitted:?}"
    );

    // `∀ (h : PosBound one 0), ¬ Equiv (inv one 0 h) zero`.
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let reciprocal = d.const_app(p.inv, &[one, zero_nat, h]);
    let claim = d.const_app(p.equiv, &[reciprocal, zero]);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);

    let cancel = d.lemma(p.mul_inv_cancel, &[one, zero_nat, h]);
    let product = d.const_app(p.mul, &[one, reciprocal]);
    let degenerate = d.const_app(p.mul, &[one, zero]);
    let reflexive = d.lemma(p.equiv_refl, &[one]);
    let stepped = d.lemma(p.mul_congr, &[one, one, reciprocal, zero, reflexive, he]);
    let vanish = d.lemma(p.mul_zero, &[one]);
    let collapsed = d.lemma(p.equiv_trans, &[product, degenerate, zero, stepped, vanish]);
    let flipped = d.lemma(p.equiv_symm, &[product, zero, collapsed]);
    let absurd = d.lemma(p.equiv_trans, &[zero, product, one, flipped, cancel]);
    let refuted = d.lemma(p.not_zero_one, &[]);
    let contradiction = d.apply(refuted, &[absurd]);

    let value = {
        let with_he = d.lam_fv(he_fv, claim, contradiction);
        d.lam_fv(h_fv, bound_ty, with_he)
    };
    let ty = {
        let negated = d.not(claim);
        d.pi_fv(h_fv, bound_ty, negated)
    };
    let name = d.kernel().name_str(anon, "Check.inv_one_is_not_zero");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "the kernel refused `1⁻¹ is not zero`, which follows from \
         mul_inv_cancel and Equiv.not_zero_one alone: {admitted:?}"
    );
}

/// The negative controls for the inverse: **the same proof terms, pointed at
/// statements one token away, are REFUSED.**
///
/// `∀ x k h, x · x⁻¹ ≈ 0` is false wherever `PosBound` is inhabited — it would
/// give `0 ≈ 1` through `Check.inv_one_is_not_zero`'s argument — and
/// `∀ x k h, x⁻¹ ≈ x` is false at `x = 1 + 1`. If either mutation were
/// accepted, the verbatim statement tests above would be pinning a shape rather
/// than a fact.
#[test]
fn the_inverse_route_cannot_prove_the_one_token_mutations() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let nat = d.nat_ty();
    let zero = d.kernel().const_(p.zero, vec![]);

    // `x · x⁻¹ ≈ 0`, not `≈ 1`.
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let bound_ty = d.const_app(p.pos_bound, &[x, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let reciprocal = d.const_app(p.inv, &[x, k, h]);
    let product = d.const_app(p.mul, &[x, reciprocal]);
    let claim = d.const_app(p.equiv, &[product, zero]);
    let ty = {
        let inner = d.pi_fv(h_fv, bound_ty, claim);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(x_fv, carrier, with_k)
    };
    let value = {
        let instance = d.lemma(p.mul_inv_cancel, &[x, k, h]);
        let with_h = d.lam_fv(h_fv, bound_ty, instance);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(x_fv, carrier, with_k)
    };
    let name = d.kernel().name_str(anon, "Check.inv_annihilates");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `x · x⁻¹ ≈ 0`, which with an inhabited PosBound \
         gives 0 ≈ 1 and refutes Equiv.not_zero_one"
    );

    // `x⁻¹ ≈ x`, from the modulus-irrelevance term.
    let claim = d.const_app(p.equiv, &[reciprocal, x]);
    let ty = {
        let inner = d.pi_fv(h_fv, bound_ty, claim);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(x_fv, carrier, with_k)
    };
    let value = {
        let instance = d.lemma(p.inv_index_irrelevant, &[x, k, k, h, h]);
        let with_h = d.lam_fv(h_fv, bound_ty, instance);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(x_fv, carrier, with_k)
    };
    let name = d.kernel().name_str(anon, "Check.inv_is_the_identity");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `x⁻¹ ≈ x`, which is FALSE at x = 1 + 1"
    );
}

/// **The cancellation lemmas' statements, pinned verbatim.** `inv_nonneg`'s
/// conclusion mentions its own `PosBound` witness (unlike every prior
/// hypothesis in this file, which only ever *gates* a statement) — so this is
/// also the regression test for that binder being genuinely dependent
/// (`pi_fv`, not `d.arrow`): an anonymous-binder Pi whose body still names
/// the un-bound witness is an `UnboundFVar` the kernel refuses at
/// `add_declaration` time, invisible to `cargo check`. It fired once while
/// authoring this pair.
#[test]
fn the_cancellation_lemmas_have_the_statements_this_slice_specifies() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.inv_nonneg),
        "((x0 : CReal) -> ((x1 : AxNat) -> ((x2 : CReal.PosBound x0 x1) -> \
         CReal.le CReal.zero (CReal.inv x0 x1 x2))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.le_of_mul_le_mul_left),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : AxNat) -> \
         ((x4 : CReal.PosBound x0 x3) -> ((x5 : CReal.le (CReal.mul x0 x1) \
         (CReal.mul x0 x2)) -> CReal.le x1 x2))))))"
    );
    for (label, name) in [
        ("inv_nonneg", p.inv_nonneg),
        ("le_of_mul_le_mul_left", p.le_of_mul_le_mul_left),
    ] {
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "CReal.{label} rests on {footprint:?}");
    }
}

/// **A concrete, asymmetric instantiation of `le_of_mul_le_mul_left`.**
/// `c := 1`, `x := 1`, `y := 1 + 1`, so `mul c x ≤ mul c y` is the TRUE
/// direction `1 ≤ 1+1`. A symmetric instance (`x = y`) cannot catch an
/// argument-order defect in the theorem's own `ty`/`value` construction —
/// `le x y` and `le y x` coincide there — this one can: the assertion below
/// pins the CONCLUSION's rendered type exactly, so a `x`/`y` transposition
/// inside `declare_le_of_mul_le_mul_left` would print `CReal.le (CReal.add
/// CReal.one CReal.one) CReal.one` instead, and the test would fail.
#[test]
fn le_of_mul_le_mul_left_concrete_asymmetric_instance() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let rat = p.rat;

    let one = d.kernel().const_(p.one, vec![]);
    let two = d.const_app(p.add, &[one, one]);
    let zero_nat = d.num(0);

    // `PosBound one 0`: `le (ofRat (natDivSucc 1 0)) one`, and `natDivSucc 1
    // 0` computes to `Rat.one` — `ofRat (natDivSucc 1 0)` IS `CReal.one` by
    // defeq, so `le_refl one` closes it (same witness the domain-inhabited
    // test above uses).
    let h = d.lemma(p.le_refl, &[one]);

    // `le one two`, from `le_add_of_nonneg one Rat.one (0 ≤ 1)`: its
    // conclusion `le one (add one (ofRat Rat.one))` IS `le one two`
    // syntactically, since `one := ofRat Rat.one` already.
    let rat_zero = crate::rat_prelude::ops::rzero(&mut d, rat);
    let rat_one = crate::rat_prelude::ops::rone(&mut d, rat);
    let rat_zero_lt_one = d.lemma(rat.zero_lt_one, &[]);
    let rat_zero_le_one = d.lemma(rat.le_of_lt, &[rat_zero, rat_one, rat_zero_lt_one]);
    let one_le_two = d.lemma(p.le_add_of_nonneg, &[one, rat_one, rat_zero_le_one]);

    // `le zero one`, for `mul_le_mul_of_nonneg_left`'s nonneg-left hypothesis.
    let zero = d.kernel().const_(p.zero, vec![]);
    let zero_lt_one = d.lemma(p.zero_lt_one, &[]);
    let zero_le_one = d.lemma(p.le_of_lt, &[zero, one, zero_lt_one]);

    // `le (mul one one) (mul one two)`.
    let hyp = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[one, one, two, zero_le_one, one_le_two],
    );

    let concl = d.lemma(p.le_of_mul_le_mul_left, &[one, one, two, zero_nat, h, hyp]);

    let name = d.kernel().name_str(anon, "Check.cancellation_one_two");
    let ty = d.const_app(p.le, &[one, two]);
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: concl,
    });
    assert!(
        admitted.is_ok(),
        "le_of_mul_le_mul_left at c=x=1, y=1+1 did not produce `le one two`: {admitted:?}"
    );

    let rendered = d
        .kernel()
        .render_lean(ty)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "CReal.le CReal.one (CReal.add CReal.one CReal.one)"
    );

    // The TRANSPOSED conclusion, `le two one` (FALSE: 2 ≤ 1), for the SAME
    // proof term: refused, because `concl`'s actual type is `le one two`.
    let transposed_ty = d.const_app(p.le, &[two, one]);
    let name = d.kernel().name_str(anon, "Check.cancellation_transposed");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: transposed_ty,
        value: concl,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `le two one` (2 ≤ 1) from the same proof term \
         that establishes `le one two` — le_of_mul_le_mul_left's x/y must be \
         transposed"
    );
}

/// The lattice laws say what ADR-0519 says they say — **rendered types,
/// verbatim**. An empty axiom footprint on a theorem named `max_le` that says
/// something weaker would pass every other check in this file.
#[test]
fn the_lattice_laws_have_the_statements_adr_0490_specifies() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    // The three operations are total functions on ℝ — `max` and `min` binary,
    // `abs` unary. No side condition, so nothing here can be vacuous by an
    // uninhabited guard; what it CAN be is degenerate, which the two
    // discriminations below rule out.
    assert_eq!(
        rendered(&mut kernel, p.max),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal))"
    );
    assert_eq!(
        rendered(&mut kernel, p.min),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal))"
    );
    assert_eq!(rendered(&mut kernel, p.abs), "((x0 : CReal) -> CReal)");

    assert_eq!(
        rendered(&mut kernel, p.le_max_left),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal.le x0 (CReal.max x0 x1)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.le_max_right),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal.le x1 (CReal.max x0 x1)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.max_le),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.le x0 x2) -> \
         ((x4 : CReal.le x1 x2) -> CReal.le (CReal.max x0 x1) x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.min_le_left),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal.le (CReal.min x0 x1) x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.min_le_right),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal.le (CReal.min x0 x1) x1))"
    );
    assert_eq!(
        rendered(&mut kernel, p.le_min),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.le x2 x0) -> \
         ((x4 : CReal.le x2 x1) -> CReal.le x2 (CReal.min x0 x1))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.max_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         CReal.Equiv (CReal.max x0 x2) (CReal.max x1 x3)))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.min_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         CReal.Equiv (CReal.min x0 x2) (CReal.min x1 x3)))))))"
    );
    // `abs` is stated through `CReal.abs`, not through the `max x (neg x)` it
    // unfolds to — otherwise these would be `max` laws wearing another name.
    assert_eq!(
        rendered(&mut kernel, p.le_abs_self),
        "((x0 : CReal) -> CReal.le x0 (CReal.abs x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.neg_le_abs),
        "((x0 : CReal) -> CReal.le (CReal.neg x0) (CReal.abs x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.abs_le),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.le x0 x1) -> \
         ((x3 : CReal.le (CReal.neg x0) x1) -> CReal.le (CReal.abs x0) x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.abs_nonneg),
        "((x0 : CReal) -> CReal.le CReal.zero (CReal.abs x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.abs_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Equiv x0 x1) -> \
         CReal.Equiv (CReal.abs x0) (CReal.abs x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_le_zero_neg_one),
        "Not (CReal.le CReal.zero (CReal.neg CReal.one))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_equiv_abs_neg_one),
        "Not (CReal.Equiv (CReal.abs (CReal.neg CReal.one)) (CReal.neg CReal.one))"
    );
}

/// **The lattice is not degenerate, and `abs` is not the identity.**
///
/// Nothing in this module carries a side condition, so no statement here is
/// vacuous for want of an inhabited guard — the failure mode is the other one:
/// a degenerate operation satisfying every law. `max x y := x` satisfies
/// `le_max_left` by reflexivity; `abs x := x` satisfies `le_abs_self`,
/// `neg_le_abs` and `abs_le`. Both are ruled out **through the kernel**, from
/// the laws alone:
///
/// - `Equiv (max x x) x` — the join is idempotent, by antisymmetry;
/// - `Equiv (max zero one) one` **and** `¬ Equiv (max zero one) zero` — so
///   `max` is not the left projection;
/// - `¬ Equiv (abs (neg one)) (neg one)`, already a kernel theorem, is
///   **consumed** here rather than merely named.
#[test]
fn the_lattice_is_not_degenerate_and_abs_is_not_the_identity() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    // `∀ x, Equiv (max x x) x`, by antisymmetry — needs BOTH directions, so a
    // `max` that ignored one argument would still pass but a `max` that
    // returned a constant would not.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let combined = d.const_app(p.max, &[x, x]);
        let up = d.lemma(p.le_max_left, &[x, x]);
        let reflexive = d.lemma(p.le_refl, &[x]);
        let down = d.lemma(p.max_le, &[x, x, x, reflexive, reflexive]);
        let body = d.lemma(p.equiv_of_le_le, &[combined, x, down, up]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let claim = d.const_app(p.equiv, &[combined, x]);
            d.pi_fv(x_fv, carrier, claim)
        };
        let name = d.kernel().name_str(anon, "Check.max_idempotent");
        let admitted = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            admitted.is_ok(),
            "the kernel refused `max x x ≈ x`, which is antisymmetry over \
             le_max_left and max_le: {admitted:?}"
        );
    }

    // `¬ Equiv (max zero one) zero` — `max` is not the left projection. If it
    // were, `one ≤ max zero one ≈ zero` would refute not_le_one_zero.
    {
        let combined = d.const_app(p.max, &[zero, one]);
        let hypothesis = d.const_app(p.equiv, &[combined, zero]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dominated = d.lemma(p.le_max_right, &[zero, one]);
        let collapsed = d.lemma(p.le_of_equiv, &[combined, zero, h]);
        let absurd = d.lemma(p.le_trans, &[one, combined, zero, dominated, collapsed]);
        let refuted = d.lemma(p.not_le_one_zero, &[]);
        let contradiction = d.apply(refuted, &[absurd]);
        let value = d.lam_fv(h_fv, hypothesis, contradiction);
        let ty = d.not(hypothesis);
        let name = d
            .kernel()
            .name_str(anon, "Check.max_is_not_the_left_projection");
        let admitted = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            admitted.is_ok(),
            "the kernel refused `max 0 1 ≉ 0`, so every lattice law here would \
             hold of the left projection: {admitted:?}"
        );
    }

    // `¬ Equiv (min zero one) one` — and `min` is not the right projection.
    {
        let combined = d.const_app(p.min, &[zero, one]);
        let hypothesis = d.const_app(p.equiv, &[combined, one]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dominated = d.lemma(p.min_le_left, &[zero, one]);
        let reversed = d.lemma(p.equiv_symm, &[combined, one, h]);
        let lifted = d.lemma(p.le_of_equiv, &[one, combined, reversed]);
        let absurd = d.lemma(p.le_trans, &[one, combined, zero, lifted, dominated]);
        let refuted = d.lemma(p.not_le_one_zero, &[]);
        let contradiction = d.apply(refuted, &[absurd]);
        let value = d.lam_fv(h_fv, hypothesis, contradiction);
        let ty = d.not(hypothesis);
        let name = d
            .kernel()
            .name_str(anon, "Check.min_is_not_the_right_projection");
        let admitted = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            admitted.is_ok(),
            "the kernel refused `min 0 1 ≉ 1`: {admitted:?}"
        );
    }

    // `abs` is not the identity: `not_equiv_abs_neg_one` is CONSUMED, so a
    // deleted or weakened version of it fails here and not only in the
    // inventory.
    {
        let negative = d.const_app(p.neg, &[one]);
        let magnitude = d.const_app(p.abs, &[negative]);
        let claim = d.const_app(p.equiv, &[magnitude, negative]);
        let refuted = d.lemma(p.not_equiv_abs_neg_one, &[]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let contradiction = d.apply(refuted, &[h]);
        let false_ty = d.false_ty();
        let value = d.lam_fv(h_fv, claim, contradiction);
        let ty = d.arrow(claim, false_ty);
        let name = d.kernel().name_str(anon, "Check.abs_is_not_the_identity");
        let admitted = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            admitted.is_ok(),
            "the kernel refused `|−1| ≉ −1`, so `abs x := x` would satisfy \
             everything else proved about abs: {admitted:?}"
        );
    }
}

/// A concrete instantiation of [`CRealPrelude::mul_self_abs`] at `x := neg
/// one` -- a NEGATIVE value, the case classical trichotomy needs and this
/// development's `Rat.le_or_lt` case split (at the RATIONAL level, one
/// below `CReal`) supplies instead. Checked against the independently
/// reconstructed statement `mul (abs (neg one)) (abs (neg one)) ~
/// mul (neg one) (neg one)`.
#[test]
fn mul_self_abs_concrete_instantiation_at_neg_one() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_one = d.const_app(p.neg, &[one]);

    let proof = d.lemma(p.mul_self_abs, &[neg_one]);

    let abs_neg_one = d.const_app(p.abs, &[neg_one]);
    let lhs = d.const_app(p.mul, &[abs_neg_one, abs_neg_one]);
    let rhs = d.const_app(p.mul, &[neg_one, neg_one]);
    let ty = d.const_app(p.equiv, &[lhs, rhs]);

    let name = d.kernel().name_str(anon, "Check.mul_self_abs_at_neg_one");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: proof,
    });
    assert!(
        admitted.is_ok(),
        "mul_self_abs at (neg one) must give EXACTLY Equiv (mul (abs (neg \
         one)) (abs (neg one))) (mul (neg one) (neg one)): {admitted:?}"
    );
}

/// Negative control for
/// [`mul_self_abs_concrete_instantiation_at_neg_one`]: the SAME proof term
/// must be REFUSED against `mul (abs (neg one)) (abs (neg one)) ~ neg one`
/// -- a statement missing the self-multiplication on the right, which a
/// vacuous or degenerate `mul_self_abs` could not be distinguished from by
/// shape alone.
#[test]
fn mul_self_abs_argument_is_load_bearing() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_one = d.const_app(p.neg, &[one]);
    let proof = d.lemma(p.mul_self_abs, &[neg_one]);

    let abs_neg_one = d.const_app(p.abs, &[neg_one]);
    let lhs = d.const_app(p.mul, &[abs_neg_one, abs_neg_one]);
    let wrong_ty = d.const_app(p.equiv, &[lhs, neg_one]);

    let name = d.kernel().name_str(anon, "Check.mul_self_abs_wrong_target");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: wrong_ty,
        value: proof,
    });
    assert!(
        admitted.is_err(),
        "mul_self_abs's proof at (neg one) must NOT type-check against `mul \
         (abs (neg one)) (abs (neg one)) ~ neg one`: {admitted:?}"
    );
}

/// The negative controls for the lattice: **the same proof terms, pointed at
/// statements one token away, are REFUSED.**
///
/// Without these, the verbatim-statement test above pins a shape rather than a
/// fact — a kernel whose conversion checker accepted anything would make every
/// assertion in this file pass.
#[test]
fn the_lattice_route_cannot_prove_the_one_token_mutations() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let zero = d.kernel().const_(p.zero, vec![]);

    // `max x y ≤ x`, from `le_max_left` — the direction reversed. FALSE at
    // x = 0, y = 1.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let combined = d.const_app(p.max, &[x, y]);
        let claim = d.const_app(p.le, &[combined, x]);
        let value = {
            let instance = d.lemma(p.le_max_left, &[x, y]);
            let with_y = d.lam_fv(y_fv, carrier, instance);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let with_y = d.pi_fv(y_fv, carrier, claim);
            d.pi_fv(x_fv, carrier, with_y)
        };
        let name = d.kernel().name_str(anon, "Check.max_is_below_its_argument");
        let refused = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            refused.is_err(),
            "the kernel accepted `max x y ≤ x`, which is FALSE at x = 0, y = 1"
        );
    }

    // `|x| ≤ 0`, from `abs_nonneg` — the order reversed. FALSE at x = 1.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let magnitude = d.const_app(p.abs, &[x]);
        let claim = d.const_app(p.le, &[magnitude, zero]);
        let value = {
            let instance = d.lemma(p.abs_nonneg, &[x]);
            d.lam_fv(x_fv, carrier, instance)
        };
        let ty = d.pi_fv(x_fv, carrier, claim);
        let name = d.kernel().name_str(anon, "Check.abs_is_nonpositive");
        let refused = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            refused.is_err(),
            "the kernel accepted `|x| ≤ 0`, which is FALSE at x = 1"
        );
    }

    // `¬ (|1| ≈ 1)` — `not_equiv_abs_neg_one`'s own script with `neg one`
    // replaced by `one`. The statement is FALSE (`|1| ≈ 1` holds), so the
    // discrimination above must NOT generalize.
    {
        let magnitude = d.const_app(p.abs, &[one]);
        let hypothesis = d.const_app(p.equiv, &[magnitude, one]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let nonneg = d.lemma(p.abs_nonneg, &[one]);
        let reflexive = d.lemma(p.equiv_refl, &[zero]);
        let absurd = d.lemma(
            p.le_congr,
            &[zero, zero, magnitude, one, reflexive, h, nonneg],
        );
        let refuted = d.lemma(p.not_le_zero_neg_one, &[]);
        let contradiction = d.apply(refuted, &[absurd]);
        let value = d.lam_fv(h_fv, hypothesis, contradiction);
        let ty = d.not(hypothesis);
        let name = d.kernel().name_str(anon, "Check.abs_one_is_not_one");
        let refused = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            refused.is_err(),
            "the kernel accepted `|1| ≉ 1`, which is FALSE — so the abs \
             discrimination would be proving nothing about the sign"
        );
    }
}

/// **The derivative says what it claims, character for character** — the
/// carrier's `spec` and the one nonlinear witness.
///
/// An empty axiom footprint cannot carry either claim. A `spec` whose bound
/// were `1/(e+1)` alone, WITHOUT the `·|y−x|` factor, is a different and much
/// weaker notion (it would not force differentiability at all, only a crude
/// closeness), and it is equally axiom-free. A `hasDerivative_sq` concluding
/// `fun x => x` instead of `fun x => x + x` is simply the wrong derivative and
/// is likewise axiom-free. What separates them is the STATEMENT.
///
/// Three things to read in the pinned `spec`, all load-bearing:
///
/// * **The modulus is a FIELD of the carrier**, appearing in the hypothesis as
///   `HasDerivativeOn.modulus x0 x1 x2 x3 x4 x5`. This is uniform
///   differentiability on `[a,b]`, not a pointwise limit. That is forced, not
///   stylistic: Markov's principle is unavailable here, `Apart` is an `Or`, and
///   `Or`'s recursor does not eliminate into `Type`, so nothing can branch on a
///   real comparison to compute a modulus.
/// * **Four `CReal.le` premises confine BOTH points to `[a,b]`.** Dropping the
///   ones about `y` would make the conclusion a statement about a half-open
///   region and the witnesses would not survive.
/// * **The error bound is `(1/(e+1)) · |y−x|`, a PRODUCT.** This is why the
///   carrier could not reuse `UniformlyContinuousOn`'s rational-constant
///   closeness bound unchanged.
#[test]
fn the_derivative_is_stated_exactly() {
    on_a_deep_stack(the_derivative_is_stated_exactly_body);
}

fn the_derivative_is_stated_exactly_body() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_creal_prelude(&mut k).expect("CReal prelude must build");

    let rendered = |k: &Kernel, name: crate::NameId| -> String {
        match k
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{} must be declared", k.display_name(name)))
        {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => {
                k.render_lean(*ty)
            }
            other => panic!("{other:?} is not a theorem or definition"),
        }
    };

    let spec = rendered(&k, p.hd_spec);
    assert!(
        spec.contains(
            "CReal.mul (CReal.ofRat (Rat.natDivSucc (AxNat.succ AxNat.zero) x5)) \
                       (CReal.abs (CReal.add x7 (CReal.neg x6)))"
        ),
        "the error bound must be (1/(e+1))*|y-x|; without the |y-x| factor this \
         is a crude closeness condition, not differentiability: {spec}"
    );
    assert_eq!(
        spec, HAS_DERIVATIVE_ON_SPEC_TYPE,
        "CReal.HasDerivativeOn.spec"
    );

    let sq = rendered(&k, p.has_derivative_sq);
    assert!(
        sq.contains("CReal.add x2 x2"),
        "the derivative of r*r is x+x, not x: {sq}"
    );
    assert_eq!(sq, HAS_DERIVATIVE_SQ_TYPE, "CReal.hasDerivative_sq");
}

/// The pinned type of `CReal.HasDerivativeOn.spec`.
const HAS_DERIVATIVE_ON_SPEC_TYPE: &str = "((x0 : ((x0 : CReal) -> CReal)) -> ((x1 : ((x1 : CReal) -> CReal)) -> ((x2 : CReal) -> ((x3 : CReal) -> ((x4 : CReal.HasDerivativeOn x0 x1 x2 x3) -> ((x5 : AxNat) -> ((x6 : CReal) -> ((x7 : CReal) -> ((x8 : CReal.le x2 x6) -> ((x9 : CReal.le x6 x3) -> ((x10 : CReal.le x2 x7) -> ((x11 : CReal.le x7 x3) -> ((x12 : CReal.le (CReal.abs (CReal.add x7 (CReal.neg x6))) (CReal.ofRat (Rat.natDivSucc (AxNat.succ AxNat.zero) (CReal.HasDerivativeOn.modulus x0 x1 x2 x3 x4 x5)))) -> CReal.le (CReal.abs (CReal.add (CReal.add (x0 x7) (CReal.neg (x0 x6))) (CReal.neg (CReal.mul (x1 x6) (CReal.add x7 (CReal.neg x6)))))) (CReal.mul (CReal.ofRat (Rat.natDivSucc (AxNat.succ AxNat.zero) x5)) (CReal.abs (CReal.add x7 (CReal.neg x6)))))))))))))))))";

/// The pinned type of `CReal.hasDerivative_sq`.
const HAS_DERIVATIVE_SQ_TYPE: &str = "((x0 : CReal) -> ((x1 : CReal) -> CReal.HasDerivativeOn (fun (x2 : CReal) => CReal.mul x2 x2) (fun (x2 : CReal) => CReal.add x2 x2) x0 x1))";

/// **Mandatory computation test** for `CReal.riemannSum` (see the task
/// briefing this module was built against): a single-subinterval Riemann
/// sum of the constant function `1` on `[0, 1]` must COMPUTE to `1`, not
/// merely type-check.
///
/// `riemannSum (fun _ => one) zero one 0` has `m = 0`, so `n = Nat.succ 0 =
/// 1` (one subinterval), `Δ = (one − zero) · Rat.natDivSucc 1 0 = 1 · 1`,
/// and its single term samples at the left endpoint `i = 0`: `f(zero)·Δ =
/// one · one`. `CReal.seq` of that at an arbitrary index must reduce, by
/// unfolding alone (β/δ/ι — no lemma, no `Equiv`), to the same rational
/// `CReal.seq one` reduces to at the same index. This is checked by
/// declaring `Eq Rat (seq (riemannSum …) 2) (seq one 2)` with the proof
/// `Eq.refl` at the LEFT side and letting `Kernel::add_declaration` verify
/// the two sides are actually definitionally equal: if the sample point or
/// the `Δ` arithmetic had the wrong shape (e.g. `Δ` and the index
/// transposed — the exact failure mode the task briefing warns a
/// type-correct definition can still have), this reduction would not close
/// and `add_declaration` would return `Err`, not silently accept a vacuous
/// or ill-typed term.
#[test]
fn riemann_sum_of_the_constant_one_on_0_1_computes_to_one() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rrefl};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = super::creal_ty(&mut d, p);

    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = d.kernel().const_(p.zero, vec![]);

    // const_one := fun _ : CReal => one.
    let const_one = {
        let x_fv = d.fresh_fvar();
        let _x = d.kernel().fvar(x_fv);
        d.lam_fv(x_fv, carrier, one_c)
    };

    let zero_m = d.num(0); // m := 0, so n = Nat.succ 0 = 1.
    let rsum_term = d.const_app(p.riemann_sum, &[const_one, zero_c, one_c, zero_m]);

    let index = d.num(2);
    let lhs = d.const_app(p.seq, &[rsum_term, index]);
    let rhs = d.const_app(p.seq, &[one_c, index]);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, lhs);

    let anon = kernel.anon();
    let name = kernel.name_str(
        anon,
        "__riemann_sum_of_the_constant_one_on_0_1_computes_to_one",
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: stmt,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "riemannSum (fun _ => one) zero one 0 did NOT compute to one at \
                 sample index 2 (not merely type-check): {error:?}"
            )
        });
}

/// **Mandatory computation test**, extending
/// [`riemann_sum_of_the_constant_one_on_0_1_computes_to_one`] to a
/// NON-UNIT interval and a NON-ONE constant: a single-subinterval Riemann
/// sum of the constant `2` on `[0, 3]` must COMPUTE to `6`, catching the
/// exact bug class a definition can pass type-checking with but still have
/// (`Δ` and the constant transposed, or a stray `Δ`-count arithmetic slip)
/// that the all-`one`s `c = 1, [0, 1]` instance is too degenerate to expose
/// — `1 · 1` reads the same whichever factor is which.
///
/// `c`, `[a, b]` and the target `6` are all built from `CReal.one`/`add`
/// alone (never `CReal.ofNat`, which is its own delta-step-plus-`Rat`-
/// normalization construction — irrelevant to what this test is checking),
/// so the only new arithmetic this test exercises beyond the existing one
/// is the constant/width multiplication, not a second embedding route.
#[test]
fn riemann_sum_of_the_constant_two_on_0_3_computes_to_six() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rrefl};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = super::creal_ty(&mut d, p);

    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let two_c = d.const_app(p.add, &[one_c, one_c]); // 1 + 1 = 2
    let three_c = d.const_app(p.add, &[two_c, one_c]); // 2 + 1 = 3
    let six_c = d.const_app(p.add, &[three_c, three_c]); // 3 + 3 = 6

    // const_two := fun _ : CReal => two_c.
    let const_two = {
        let x_fv = d.fresh_fvar();
        let _x = d.kernel().fvar(x_fv);
        d.lam_fv(x_fv, carrier, two_c)
    };

    let zero_m = d.num(0); // m := 0, so n = Nat.succ 0 = 1.
    let rsum_term = d.const_app(p.riemann_sum, &[const_two, zero_c, three_c, zero_m]);

    let index = d.num(2);
    let lhs = d.const_app(p.seq, &[rsum_term, index]);
    let rhs = d.const_app(p.seq, &[six_c, index]);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, lhs);

    let anon = kernel.anon();
    let name = kernel.name_str(
        anon,
        "__riemann_sum_of_the_constant_two_on_0_3_computes_to_six",
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: stmt,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "riemannSum (fun _ => 2) 0 3 0 did NOT compute to 6 at sample \
                 index 2 (not merely type-check): {error:?}"
            )
        });
}

/// **Mandatory concrete instantiation for `CReal.riemannSum_split_exact`,
/// with `F := id` rather than a constant** -- a constant `F` cannot
/// discriminate a wrong split point at all (`riemannSum (fun _ => k) a b m`
/// equals `k*(b-a)` for EVERY `m`, so `2c + 2(3-c)` is `6` for every `c`
/// whatsoever, aligned or not). `a := 0`, `b := 3`, `m_ac := 1`, `m_cb := 3`
/// (so `n_ac = 2`, `n_cb = 4`, `n_ab = 6` -- the task's own hand-verified
/// aligned case: `q := 1/3`, `k := 2`), `hcong := fun x y h => h` (`id`
/// trivially respects `Equiv`). Asserts the kernel accepts the theorem
/// applied at these exact arguments against the INDEPENDENTLY built expected
/// type (never merely inferred), confirming the `Nat.succ`/`Nat.add`
/// literal arithmetic (`m_ab = 5`, `n_ac = 2`) reduces as this module's
/// own hand computation says it must, and that `hcong` threads correctly
/// for a genuinely non-constant `F`.
#[test]
fn riemann_sum_split_exact_at_id_zero_three_one_three() {
    crate::on_a_deep_stack(riemann_sum_split_exact_at_id_zero_three_one_three_body);
}

fn riemann_sum_split_exact_at_id_zero_three_one_three_body() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = super::creal_ty(&mut d, p);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let two_c = d.const_app(p.add, &[one_c, one_c]);
    let three_c = d.const_app(p.add, &[two_c, one_c]);

    let id_fn = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        d.lam_fv(x_fv, carrier, x)
    };

    let m_ac = d.num(1);
    let m_cb = d.num(3);

    // hcong : forall x y, Equiv x y -> Equiv (id x) (id y) := fun x y h => h
    // (`id x`/`id y` beta-reduce to `x`/`y`, so `h` itself already has the
    // needed type).
    let hcong = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hxy_ty = super::equiv(&mut d, p, x, y);
        let body = d.lam_fv(h_fv, hxy_ty, h);
        let over_y = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, over_y)
    };

    let proof = d.lemma(
        p.riemann_sum_split_exact,
        &[id_fn, zero_c, three_c, m_ac, m_cb, hcong],
    );

    // Independently built expected type: m_ab := add (succ m_ac) m_cb,
    // delta_ab := width_of(0,3) * embed(natDivSucc 1 m_ab), c := 0 + (ofNat
    // (succ m_ac)) * delta_ab -- the SAME recipe `integral.rs`'s
    // `width_of`/`delta_of`/`sample_point` use internally, rebuilt here
    // (those helpers are private to `integral.rs`, not visible from this
    // sibling module) so interning lines this up with what the theorem's own
    // proof term actually produces.
    let n_ac = d.succ(m_ac);
    let m_ab = {
        let nat_add = d.prelude().add;
        d.const_app(nat_add, &[n_ac, m_cb])
    };
    let width_ab = {
        let neg_a = d.const_app(p.neg, &[zero_c]);
        d.const_app(p.add, &[three_c, neg_a])
    };
    let one_nat = d.num(1);
    let frac_ab_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, m_ab]);
    let frac_ab = super::embed(&mut d, p, frac_ab_rat);
    let delta_ab = d.const_app(p.mul, &[width_ab, frac_ab]);
    let on_ac = d.const_app(p.of_nat, &[n_ac]);
    let w1 = d.const_app(p.mul, &[on_ac, delta_ab]);
    let c = d.const_app(p.add, &[zero_c, w1]);

    let riemann_ab = d.const_app(p.riemann_sum, &[id_fn, zero_c, three_c, m_ab]);
    let riemann_ac = d.const_app(p.riemann_sum, &[id_fn, zero_c, c, m_ac]);
    let riemann_cb = d.const_app(p.riemann_sum, &[id_fn, c, three_c, m_cb]);
    let rhs = d.const_app(p.add, &[riemann_ac, riemann_cb]);
    let expected_ty = super::equiv(&mut d, p, riemann_ab, rhs);

    // A negative control asserting the SAME proof term against a
    // deliberately-swapped-mesh-count statement was tried here and removed:
    // it drove the kernel's typechecker into unbounded work (observed >2:35
    // wall-clock at 99.9% CPU with RSS still climbing past 2.6 GB before
    // being killed, not a stack overflow) -- the same "symbolic test can be
    // pathological" shape this codebase's own gotchas document. The POSITIVE
    // check below (kernel accepts the real proof against the independently
    // rebuilt expected statement) is the real verification; deleting the
    // negative control rather than debugging its cost, per the documented
    // convention.
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "__riemann_sum_split_exact_at_id_zero_three_one_three");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "riemannSum_split_exact at F := id, a := 0, b := 3, \
                 m_ac := 1, m_cb := 3 did NOT type-check against the \
                 independently rebuilt expected statement: {error:?}"
            )
        });
}

/// **Mandatory concrete instantiation for
/// `CReal.riemannSum_split_exact_of_uc`** -- the SAME identity as
/// `riemannSum_split_exact`, discharged from a `UniformlyContinuousOn`
/// witness (`CReal.uniformly_continuous_id`) instead of a global `hcong`.
/// `F := id` (again, not a constant: a constant cannot discriminate a wrong
/// split point), `a := 0`, `b := ofNat 3`, `m_ac := 1`, `m_cb := 3` (so
/// `n_ac = 2`, `n_cb = 4`, `m_ab = 5`, matching this file's own
/// `riemann_sum_split_exact_at_id_zero_three_one_three` test's hand
/// computation, `b` built via `ofNat 3` here rather than an add-chain since
/// `hab` needs an actual `le zero (ofNat 3)` proof this route already knows
/// how to build). Asserts the kernel accepts the theorem applied at these
/// exact arguments against the INDEPENDENTLY built expected type.
#[test]
fn riemann_sum_split_exact_of_uc_at_id_zero_three_one_three() {
    crate::on_a_deep_stack(riemann_sum_split_exact_of_uc_at_id_zero_three_one_three_body);
}

fn riemann_sum_split_exact_of_uc_at_id_zero_three_one_three_body() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = super::creal_ty(&mut d, p);

    let zero_nat = d.num(0);
    let three_nat = d.num(3);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let b = d.const_app(p.of_nat, &[three_nat]);

    let id_fn = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        d.lam_fv(x_fv, carrier, x)
    };

    let m_ac = d.num(1);
    let m_cb = d.num(3);

    let u = d.lemma(p.uniformly_continuous_id, &[zero_c, b]);

    // hab : CReal.le zero (ofNat 3) -- same route as this file's own
    // `riemann_sum_reblock_close`-family tests (`Rat.zero_le_natDivSucc`
    // lifted across `CReal.ofRat_le`).
    let hab = {
        let rat_3 = d.const_app(p.rat.nat_div_succ, &[three_nat, zero_nat]);
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[three_nat, zero_nat]);
        d.lemma(p.of_rat_le, &[rzero, rat_3, rle])
    };

    let proof = d.lemma(
        p.riemann_sum_split_exact_of_uc,
        &[id_fn, zero_c, b, m_ac, m_cb, u, hab],
    );

    // Independently built expected type -- the same recipe
    // `riemann_sum_split_exact_at_id_zero_three_one_three`'s own expected
    // type uses, with `b := ofNat 3` in place of that test's add-chain
    // `three_c` (interning makes `ofNat 3` here line up with what the
    // theorem's own proof term produces for THIS `b`).
    let n_ac = d.succ(m_ac);
    let m_ab = {
        let nat_add = d.prelude().add;
        d.const_app(nat_add, &[n_ac, m_cb])
    };
    let width_ab = {
        let neg_a = d.const_app(p.neg, &[zero_c]);
        d.const_app(p.add, &[b, neg_a])
    };
    let one_nat = d.num(1);
    let frac_ab_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, m_ab]);
    let frac_ab = super::embed(&mut d, p, frac_ab_rat);
    let delta_ab = d.const_app(p.mul, &[width_ab, frac_ab]);
    let on_ac = d.const_app(p.of_nat, &[n_ac]);
    let w1 = d.const_app(p.mul, &[on_ac, delta_ab]);
    let c = d.const_app(p.add, &[zero_c, w1]);

    let riemann_ab = d.const_app(p.riemann_sum, &[id_fn, zero_c, b, m_ab]);
    let riemann_ac = d.const_app(p.riemann_sum, &[id_fn, zero_c, c, m_ac]);
    let riemann_cb = d.const_app(p.riemann_sum, &[id_fn, c, b, m_cb]);
    let rhs = d.const_app(p.add, &[riemann_ac, riemann_cb]);
    let expected_ty = super::equiv(&mut d, p, riemann_ab, rhs);

    let anon = kernel.anon();
    let name = kernel.name_str(
        anon,
        "__riemann_sum_split_exact_of_uc_at_id_zero_three_one_three",
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "riemannSum_split_exact_of_uc at F := id, a := 0, \
                 b := ofNat 3, m_ac := 1, m_cb := 3 did NOT type-check \
                 against the independently rebuilt expected statement: \
                 {error:?}"
            )
        });
}

/// **Mandatory concrete instantiation for
/// `CReal.riemannSum_split_scale_invariant`, with a negative (swapped-count)
/// control.** `a := 0`, `b := 3`, `m_ac0 := 0`, `m_cb0 := 1` (so `n_ac0 :=
/// 1`, `n_cb0 := 2`, `m_ab0 := 2`, `delta_ab0 := 3 * (1/3) = 1`, `c_0 := 0 +
/// 1*1 = 1`), `k := 1` (so, via `succ_mul_succ`, `m_ac_k := 1`, `m_cb_k :=
/// 3`, `n_ac_k := 2`, `m_ab_k := 5`, `delta_ab_k := 3 * (1/6) = 0.5`, `c_k :=
/// 0 + 2*0.5 = 1`) — the SAME numeric case as this module's own hand
/// computation for `riemannSum_split_exact`'s aligned family (`q := 1/3, k :=
/// 2`), read one level up: two DIFFERENT mesh counts computing the SAME
/// split point. Positive: the kernel accepts the theorem applied at these
/// exact arguments against the INDEPENDENTLY rebuilt expected type `Equiv
/// c_k c_0`. Negative: the SAME proof term is asserted against a
/// deliberately WRONG conclusion built with `n_cb0` (`= 2`) in place of
/// `n_ac0` inside `c_0`'s own formula — genuinely a different concrete value
/// (`2` vs `1`), not a vacuous or symbolic swap, so no risk of the
/// unbounded-typechecker cost this file's own `riemannSum_split_exact` test
/// documents and avoids.
#[test]
fn riemann_sum_split_scale_invariant_at_zero_three_zero_one_one() {
    crate::on_a_deep_stack(riemann_sum_split_scale_invariant_at_zero_three_zero_one_one_body);
}

fn riemann_sum_split_scale_invariant_at_zero_three_zero_one_one_body() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let two_c = d.const_app(p.add, &[one_c, one_c]);
    let three_c = d.const_app(p.add, &[two_c, one_c]);

    let m_ac0 = d.num(0);
    let m_cb0 = d.num(1);
    let k = d.num(1);

    let proof = d.lemma(
        p.riemann_sum_split_scale_invariant,
        &[zero_c, three_c, m_ac0, m_cb0, k],
    );

    // Independently rebuilt expected type, using the SAME public-API recipe
    // (`p.add`/`p.neg`/`p.mul`/`p.of_nat`/`p.rat.nat_div_succ`/
    // `super::embed`) `riemannSum_split_exact`'s own concrete test above
    // uses -- `width_of`/`delta_of` are private to `integral.rs`, not
    // visible from this sibling module.
    let width_ab = {
        let neg_a = d.const_app(p.neg, &[zero_c]);
        d.const_app(p.add, &[three_c, neg_a])
    };
    let one_nat = d.num(1);

    // c_0 at (m_ac0 := 0, m_cb0 := 1): n_ac0 := 1, m_ab0 := 2.
    let n_ac0 = d.num(1);
    let n_cb0 = d.num(2);
    let m_ab0 = d.num(2);
    let frac_ab0 = d.const_app(p.rat.nat_div_succ, &[one_nat, m_ab0]);
    let embed_ab0 = super::embed(&mut d, p, frac_ab0);
    let delta_ab0 = d.const_app(p.mul, &[width_ab, embed_ab0]);
    let on_ac0 = d.const_app(p.of_nat, &[n_ac0]);
    let w0 = d.const_app(p.mul, &[on_ac0, delta_ab0]);
    let c_0 = d.const_app(p.add, &[zero_c, w0]);

    // c_k at (m_ac_k := 1, m_cb_k := 3), i.e. `succ_mul_succ(0,1).0 = 1`,
    // `succ_mul_succ(1,1).0 = 3`: n_ac_k := 2, m_ab_k := add(2,3) = 5.
    let n_ac_k = d.num(2);
    let m_ab_k = d.num(5);
    let frac_ab_k = d.const_app(p.rat.nat_div_succ, &[one_nat, m_ab_k]);
    let embed_ab_k = super::embed(&mut d, p, frac_ab_k);
    let delta_ab_k = d.const_app(p.mul, &[width_ab, embed_ab_k]);
    let on_ac_k = d.const_app(p.of_nat, &[n_ac_k]);
    let w_k = d.const_app(p.mul, &[on_ac_k, delta_ab_k]);
    let c_k = d.const_app(p.add, &[zero_c, w_k]);

    let expected_ty = super::equiv(&mut d, p, c_k, c_0);

    // Negative control built BEFORE any `add_declaration` call below, since
    // `d` holds `kernel` mutably borrowed for as long as it is in scope --
    // asserted against a FALSE conclusion that uses `n_cb0` (= 2) instead of
    // `n_ac0` (= 1) inside `c_0`'s own formula -- genuinely a different
    // concrete value (`w0_wrong = 2*1 = 2` vs the true `w0 = 1*1 = 1`),
    // all-concrete (no symbolic swap), so this is exactly the discriminating
    // instance the positive check below cannot rule out on its own.
    let on_cb0 = d.const_app(p.of_nat, &[n_cb0]);
    let w0_wrong = d.const_app(p.mul, &[on_cb0, delta_ab0]);
    let c_0_wrong = d.const_app(p.add, &[zero_c, w0_wrong]);
    let false_ty = super::equiv(&mut d, p, c_k, c_0_wrong);

    let anon = d.kernel().anon();
    let name_ok = d.kernel().name_str(
        anon,
        "__riemann_sum_split_scale_invariant_at_zero_three_zero_one_one_ok",
    );
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name: name_ok,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "riemannSum_split_scale_invariant at a := 0, b := 3, \
                 m_ac0 := 0, m_cb0 := 1, k := 1 did NOT type-check against \
                 the independently rebuilt expected statement `Equiv c_k \
                 c_0`: {error:?}"
            )
        });

    let name_bad = d.kernel().name_str(
        anon,
        "__riemann_sum_split_scale_invariant_at_zero_three_zero_one_one_bad",
    );
    let result_bad = d.kernel().add_declaration(Declaration::Theorem {
        name: name_bad,
        uparams: vec![],
        ty: false_ty,
        value: proof,
    });
    assert!(
        result_bad.is_err(),
        "the SAME proof term must be REFUSED against the FALSE conclusion \
         built with n_cb0 in place of n_ac0 (genuinely different concrete \
         values, 2 vs 1)"
    );
}

/// **Mandatory computation test for `CReal.ofNat_le`.** Instantiates it at
/// explicit small naturals `i := 1`, `j := 3` against a CONCRETE
/// `Nat.le 1 3` witness built from `Nat.le_intro 1 3 2 (rfl : 1+2=3)` — not a
/// symbolic hypothesis — and checks the kernel accepts
/// `CReal.ofNat_le 1 3 h : CReal.le (ofNat 1) (ofNat 3)` at that exact type.
/// A `Δ`/index transposition (e.g. `ofNat_le` accidentally proving
/// `le (ofNat j) (ofNat i)`, or using `k` where `i`/`j` belong) would still
/// type-check as SOME `CReal.le` statement but not this one, which is why the
/// declared `ty` below is asserted rather than merely inferred.
#[test]
fn of_nat_le_at_one_and_three_proves_le_one_three() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let one_nat = d.num(1);
    let three_nat = d.num(3);
    let two_nat = d.num(2);

    // h : Nat.le 1 3, from `Nat.le_intro 1 3 2 (rfl : add 1 2 = 3)`.
    // `le_intro`'s hypothesis type is `Eq Nat (add 1 2) 3`; `Eq.refl Nat 3`
    // checks against it by defeq (`add 1 2` reduces to `3`).
    let eq_proof = d.refl(three_nat);
    let nat_le_intro = d.prelude().le_intro;
    let hle = d.const_app(nat_le_intro, &[one_nat, three_nat, two_nat, eq_proof]);

    let value = d.const_app(p.of_nat_le, &[one_nat, three_nat, hle]);

    let of_nat_1 = d.const_app(p.of_nat, &[one_nat]);
    let of_nat_3 = d.const_app(p.of_nat, &[three_nat]);
    let ty = super::cle(&mut d, p, of_nat_1, of_nat_3);

    let anon = kernel.anon();
    let name = kernel.name_str(anon, "__of_nat_le_at_one_and_three_proves_le_one_three");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.ofNat_le 1 3 h did NOT check against \
                 CReal.le (ofNat 1) (ofNat 3) (not merely SOME le statement): {error:?}"
            )
        });
}

/// **Mandatory computation test for `CReal.ofNat_add`.** Instantiates it at
/// explicit small naturals `a := 2`, `b := 3` and checks the kernel accepts
/// `CReal.ofNat_add 2 3 : Equiv (ofNat 5) (add (ofNat 2) (ofNat 3))` at that
/// EXACT type, with `5` a literal (not the unevaluated `Nat.add 2 3`) — the
/// asserted `ty` below is built from `d.num(5)` directly, so this also pins
/// that `Nat.add 2 3` reduces to the literal `5` by defeq. A transposition
/// (e.g. proving `Equiv (ofNat 5) (add (ofNat 3) (ofNat 2))`, or `ofNat 6`
/// instead of `5`) would still type-check as SOME `Equiv` statement but not
/// this one.
#[test]
fn of_nat_add_at_two_and_three_proves_equiv_ofnat_five_add() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let two_nat = d.num(2);
    let three_nat = d.num(3);
    let five_nat = d.num(5);

    let value = d.const_app(p.of_nat_add, &[two_nat, three_nat]);

    let of_nat_5 = d.const_app(p.of_nat, &[five_nat]);
    let of_nat_2 = d.const_app(p.of_nat, &[two_nat]);
    let of_nat_3 = d.const_app(p.of_nat, &[three_nat]);
    let sum_real = super::cadd(&mut d, p, of_nat_2, of_nat_3);
    let ty = super::equiv(&mut d, p, of_nat_5, sum_real);

    let anon = kernel.anon();
    let name = kernel.name_str(
        anon,
        "__of_nat_add_at_two_and_three_proves_equiv_ofnat_five_add",
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.ofNat_add 2 3 did NOT check against \
                 Equiv (ofNat 5) (add (ofNat 2) (ofNat 3)) (not merely SOME \
                 Equiv statement): {error:?}"
            )
        });
}

/// **Mandatory computation test for `CReal.ofNat_mul`.** Instantiates it at
/// explicit small naturals `a := 2`, `b := 3` and checks the kernel accepts
/// `CReal.ofNat_mul 2 3 : Equiv (ofNat 6) (mul (ofNat 2) (ofNat 3))` at that
/// EXACT type, `6` a literal — same rationale as the `ofNat_add` test above,
/// with `Nat.mul 2 3` reducing to `6` by defeq.
#[test]
fn of_nat_mul_at_two_and_three_proves_equiv_ofnat_six_mul() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let two_nat = d.num(2);
    let three_nat = d.num(3);
    let six_nat = d.num(6);

    let value = d.const_app(p.of_nat_mul, &[two_nat, three_nat]);

    let of_nat_6 = d.const_app(p.of_nat, &[six_nat]);
    let of_nat_2 = d.const_app(p.of_nat, &[two_nat]);
    let of_nat_3 = d.const_app(p.of_nat, &[three_nat]);
    let prod_real = d.const_app(p.mul, &[of_nat_2, of_nat_3]);
    let ty = super::equiv(&mut d, p, of_nat_6, prod_real);

    let anon = kernel.anon();
    let name = kernel.name_str(
        anon,
        "__of_nat_mul_at_two_and_three_proves_equiv_ofnat_six_mul",
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.ofNat_mul 2 3 did NOT check against \
                 Equiv (ofNat 6) (mul (ofNat 2) (ofNat 3)) (not merely SOME \
                 Equiv statement): {error:?}"
            )
        });
}

/// **Mandatory computation test for `CReal.riemannSum_sample_in_bounds`.**
/// Instantiates it at `a := CReal.zero`, `b := CReal.ofNat 3`, `m := 2`
/// (so `n = succ m = 3`), `i := 1` — the sample point at index `1` of a
/// 3-subinterval partition of `[0, 3]`, i.e. `Δ = 3 · 1/3 = 1` and the sample
/// point is `0 + 1·Δ`, genuinely INSIDE `(0, 3)` rather than at an endpoint —
/// against CONCRETE witnesses (`0 ≤ 3` from `Rat.zero_le_natDivSucc`, `1 < 3`
/// from `Nat.le_intro 2 3 1 (rfl : 2+1=3)`), and checks the kernel accepts
/// the application at the EXACT expected `And (le a sp) (le sp b)` type,
/// built independently here from `CReal.add`/`CReal.neg`/`CReal.mul`/
/// `CReal.ofNat`/`CReal.ofRat` rather than by calling back into
/// `integral.rs`'s private term builders. A `Δ`/index transposition (e.g.
/// swapping which factor is `ofNat i` and which is the width) would still
/// type-check as SOME `And` of two `le`s but not this one.
#[test]
fn riemann_sample_in_bounds_at_zero_three_two_one_lands_strictly_inside() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three_nat = d.num(3);

    let a = d.kernel().const_(p.zero, vec![]);
    let b = d.const_app(p.of_nat, &[three_nat]);
    let m = two_nat;
    let i = one_nat;

    // hab : CReal.le zero (ofNat 3), directly from `Rat.zero_le_natDivSucc`
    // lifted across `CReal.ofRat_le` (`CReal.zero` and `CReal.ofNat 3` are
    // each one delta-step from an `ofRat` of a `Rat.natDivSucc`).
    let hab = {
        let rat_3 = d.const_app(p.rat.nat_div_succ, &[three_nat, zero_nat]);
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[three_nat, zero_nat]);
        d.lemma(p.of_rat_le, &[rzero, rat_3, rle])
    };

    // hlt : Nat.lt 1 3 (defeq Nat.le 2 3), from `Nat.le_intro 2 3 1
    // (rfl : add 2 1 = 3)`.
    let hlt = {
        let eq_proof = d.refl(three_nat);
        let nat_le_intro = d.prelude().le_intro;
        d.const_app(nat_le_intro, &[two_nat, three_nat, one_nat, eq_proof])
    };

    let value = d.const_app(p.riemann_sample_in_bounds, &[a, b, m, i, hab, hlt]);

    // The expected sample point, built independently: `sp := add a (mul
    // (ofNat i) delta)`, `delta := mul (add b (neg a)) (ofRat (natDivSucc 1
    // m))` -- exactly `integral.rs::sample_point`/`delta_of`'s own shape.
    let ty = {
        let rat_frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
        let frac_real = d.const_app(p.of_rat, &[rat_frac]);
        let neg_a = d.const_app(p.neg, &[a]);
        let width = d.const_app(p.add, &[b, neg_a]);
        let delta = d.const_app(p.mul, &[width, frac_real]);
        let of_nat_i = d.const_app(p.of_nat, &[i]);
        let shift = d.const_app(p.mul, &[of_nat_i, delta]);
        let sp = d.const_app(p.add, &[a, shift]);

        let a_le_sp = super::cle(&mut d, p, a, sp);
        let sp_le_b = super::cle(&mut d, p, sp, b);
        d.const_app(p.rat.int.logic.and, &[a_le_sp, sp_le_b])
    };

    let anon = kernel.anon();
    let name = kernel.name_str(
        anon,
        "__riemann_sample_in_bounds_at_zero_three_two_one_lands_strictly_inside",
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.riemannSum_sample_in_bounds 0 3 2 1 hab hlt did NOT check \
                 against And (le 0 sp) (le sp 3) at the expected sample point \
                 (not merely SOME And of le statements): {error:?}"
            )
        });
}

/// **Mandatory computation test for `CReal.fineSample_in_bounds`.**
/// Instantiates it at `a := CReal.zero`, `b := CReal.ofNat 1`, `m := n :=
/// 1` (so BOTH the coarse partition and each block's fine partition split
/// into `succ 1 = 2` pieces), `i := m := 1`, `j := n := 1` — the LAST fine
/// sample point of the LAST coarse block, the hardest boundary case: `Δ_m =
/// 1 · 1/2 = 1/2`, `base = 0 + 1·Δ_m = 1/2`, `Δ_fine = Δ_m · 1/2 = 1/4`,
/// `x = base + 1·Δ_fine = 3/4` — strictly inside `[0, 1]`, one `Δ_fine`
/// short of `b`, which an off-by-one in either the coarse or fine index
/// arithmetic would push past. `hi : Nat.le 1 1` and `hj : Nat.lt 1 2` are
/// both `Nat.le.refl` (the latter via `Lt n (succ n)`'s own `Nat.le (succ
/// n) (succ n)` unfolding). Checks the kernel accepts the application at
/// the EXACT expected `And (le a x) (le x b)` type, built independently
/// here from `CReal.add`/`CReal.neg`/`CReal.mul`/`CReal.ofNat`/`CReal.ofRat`
/// rather than by calling back into `integral.rs`'s private term builders.
#[test]
fn fine_sample_in_bounds_at_zero_one_m1_n1_last_block_last_sample() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    let a = d.kernel().const_(p.zero, vec![]);
    let b = d.const_app(p.of_nat, &[one_nat]);
    let m = one_nat;
    let n = one_nat;
    let i = one_nat;
    let j = one_nat;

    // hab : CReal.le zero (ofNat 1), the same route the
    // `riemannSum_sample_in_bounds` computation test above uses.
    let hab = {
        let rat_1 = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, zero_nat]);
        d.lemma(p.of_rat_le, &[rzero, rat_1, rle])
    };

    let np = d.prelude();
    // hi : Nat.le 1 1, i.e. `Nat.le.refl 1`.
    let hi = d.const_app(np.le_refl, &[one_nat]);
    // hj : Nat.lt 1 2, defeq `Nat.le 2 2`, i.e. `Nat.le.refl 2`.
    let hj = d.const_app(np.le_refl, &[two_nat]);

    let value = d.const_app(p.fine_sample_in_bounds, &[a, b, m, n, i, j, hab, hi, hj]);

    // The expected fine sample point, built independently: `x := add base
    // (mul (ofNat j) delta_fine)`, `base := add a (mul (ofNat i) delta_m)`,
    // `delta_m := mul (add b (neg a)) (ofRat (natDivSucc 1 m))`,
    // `delta_fine := mul delta_m (ofRat (natDivSucc 1 n))` -- exactly
    // `integral.rs`'s own `sample_point`/`delta_nonneg_of`/
    // `fine_term_and_bounds` shapes.
    let ty = {
        let neg_a = d.const_app(p.neg, &[a]);
        let width = d.const_app(p.add, &[b, neg_a]);
        let rat_frac_m = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
        let frac_m = d.const_app(p.of_rat, &[rat_frac_m]);
        let delta_m = d.const_app(p.mul, &[width, frac_m]);
        let of_nat_i = d.const_app(p.of_nat, &[i]);
        let i_delta_m = d.const_app(p.mul, &[of_nat_i, delta_m]);
        let base = d.const_app(p.add, &[a, i_delta_m]);

        let rat_frac_n = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
        let frac_n = d.const_app(p.of_rat, &[rat_frac_n]);
        let delta_fine = d.const_app(p.mul, &[delta_m, frac_n]);
        let of_nat_j = d.const_app(p.of_nat, &[j]);
        let term = d.const_app(p.mul, &[of_nat_j, delta_fine]);
        let x = d.const_app(p.add, &[base, term]);

        let a_le_x = super::cle(&mut d, p, a, x);
        let x_le_b = super::cle(&mut d, p, x, b);
        d.const_app(p.rat.int.logic.and, &[a_le_x, x_le_b])
    };

    let anon = kernel.anon();
    let name = kernel.name_str(
        anon,
        "__fine_sample_in_bounds_at_zero_one_m1_n1_last_block_last_sample",
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.fineSample_in_bounds 0 1 1 1 1 1 hab hi hj did NOT \
                 check against And (le 0 x) (le x 1) at the expected fine \
                 sample point (not merely SOME And of le statements): \
                 {error:?}"
            )
        });
}

/// **Transposition guard for `CReal.fineSample_in_bounds`.** Identical to
/// [`fine_sample_in_bounds_at_zero_one_m1_n1_last_block_last_sample`] but at
/// `m := 1`, `n := 2` (`m != n`, per this session's own briefing: `m = n`
/// cannot detect a coarse/fine mesh or index transposition), `i := m := 1`,
/// `j := n := 2` — again the last fine sample of the last coarse block:
/// `Δ_m = 1/2`, `base = 1/2`, `Δ_fine = Δ_m · 1/3 = 1/6`, `x = 1/2 + 2·1/6 =
/// 5/6`, strictly inside `[0, 1]`.
#[test]
fn fine_sample_in_bounds_at_zero_one_m1_n2_last_block_last_sample() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three_nat = d.num(3);

    let a = d.kernel().const_(p.zero, vec![]);
    let b = d.const_app(p.of_nat, &[one_nat]);
    let m = one_nat;
    let n = two_nat;
    let i = one_nat;
    let j = two_nat;

    let hab = {
        let rat_1 = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, zero_nat]);
        d.lemma(p.of_rat_le, &[rzero, rat_1, rle])
    };

    let np = d.prelude();
    // hi : Nat.le 1 1.
    let hi = d.const_app(np.le_refl, &[one_nat]);
    // hj : Nat.lt 2 3, defeq `Nat.le 3 3`.
    let hj = d.const_app(np.le_refl, &[three_nat]);

    let value = d.const_app(p.fine_sample_in_bounds, &[a, b, m, n, i, j, hab, hi, hj]);

    let ty = {
        let neg_a = d.const_app(p.neg, &[a]);
        let width = d.const_app(p.add, &[b, neg_a]);
        let rat_frac_m = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
        let frac_m = d.const_app(p.of_rat, &[rat_frac_m]);
        let delta_m = d.const_app(p.mul, &[width, frac_m]);
        let of_nat_i = d.const_app(p.of_nat, &[i]);
        let i_delta_m = d.const_app(p.mul, &[of_nat_i, delta_m]);
        let base = d.const_app(p.add, &[a, i_delta_m]);

        let rat_frac_n = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
        let frac_n = d.const_app(p.of_rat, &[rat_frac_n]);
        let delta_fine = d.const_app(p.mul, &[delta_m, frac_n]);
        let of_nat_j = d.const_app(p.of_nat, &[j]);
        let term = d.const_app(p.mul, &[of_nat_j, delta_fine]);
        let x = d.const_app(p.add, &[base, term]);

        let a_le_x = super::cle(&mut d, p, a, x);
        let x_le_b = super::cle(&mut d, p, x, b);
        d.const_app(p.rat.int.logic.and, &[a_le_x, x_le_b])
    };

    let anon = kernel.anon();
    let name = kernel.name_str(
        anon,
        "__fine_sample_in_bounds_at_zero_one_m1_n2_last_block_last_sample",
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.fineSample_in_bounds 0 1 1 2 1 2 hab hi hj did NOT \
                 check against And (le 0 x) (le x 1) at the expected fine \
                 sample point (not merely SOME And of le statements): \
                 {error:?}"
            )
        });
}

/// **Computation/argument-order test for `CReal.riemannSum_le_on`.**
/// Instantiates it at `f := g := fun _ => one`, `a := zero`, `b := ofNat 3`,
/// `m := 0` (so `n = 1`, a single subinterval), with `hab : le zero (ofNat
/// 3)` and the RESTRICTED `hfg : ∀ z, le zero z → le z (ofNat 3) → le one
/// one` (built from `le_refl one`, ignoring the two bounds — a global `hfg`
/// would also work here, but this checks the RESTRICTED-arity application
/// itself, catching an `f`/`g` or `hab`/`hfg` argument transposition, which
/// would still type-check as SOME `le` statement but not this one), and
/// checks the kernel accepts it at the EXACT expected
/// `le (riemannSum f a b m) (riemannSum g a b m)` type.
#[test]
fn riemann_sum_le_on_at_the_constant_function_type_checks_at_the_expected_statement() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = super::creal_ty(&mut d, p);

    let zero_nat = d.num(0);
    let three_nat = d.num(3);

    let a = d.kernel().const_(p.zero, vec![]);
    let b = d.const_app(p.of_nat, &[three_nat]);
    let m = zero_nat;
    let one_c = d.kernel().const_(p.one, vec![]);

    // f := g := fun _ : CReal => one.
    let const_one = {
        let x_fv = d.fresh_fvar();
        let _x = d.kernel().fvar(x_fv);
        d.lam_fv(x_fv, carrier, one_c)
    };
    let f = const_one;
    let g = const_one;

    // hab : le zero (ofNat 3).
    let hab = {
        let rat_3 = d.const_app(p.rat.nat_div_succ, &[three_nat, zero_nat]);
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[three_nat, zero_nat]);
        d.lemma(p.of_rat_le, &[rzero, rat_3, rle])
    };

    // hfg : ∀ z, le zero z → le z (ofNat 3) → le one one.
    let hfg = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let lo_fv = d.fresh_fvar();
        let hi_fv = d.fresh_fvar();
        let lo_ty = super::cle(&mut d, p, a, z);
        let hi_ty = super::cle(&mut d, p, z, b);
        let refl_one = d.lemma(p.le_refl, &[one_c]);
        let with_hi = d.lam_fv(hi_fv, hi_ty, refl_one);
        let with_lo = d.lam_fv(lo_fv, lo_ty, with_hi);
        d.lam_fv(z_fv, carrier, with_lo)
    };

    let value = d.const_app(p.riemann_sum_le_on, &[f, g, a, b, m, hab, hfg]);

    let rsum_f = d.const_app(p.riemann_sum, &[f, a, b, m]);
    let rsum_g = d.const_app(p.riemann_sum, &[g, a, b, m]);
    let ty = super::cle(&mut d, p, rsum_f, rsum_g);

    let anon = kernel.anon();
    let name = kernel.name_str(
        anon,
        "__riemann_sum_le_on_at_the_constant_function_type_checks_at_the_expected_statement",
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.riemannSum_le_on (fun _ => one) (fun _ => one) 0 3 0 hab hfg \
                 did NOT check against le (riemannSum f 0 3 0) (riemannSum g 0 3 0) \
                 (not merely SOME le statement): {error:?}"
            )
        });
}

/// **Concrete, argument-order-sensitive instantiation of
/// `CReal.le_of_forall_le_add_small`.** `x := zero`, `y := one`: `le zero
/// one` is a TRUE, ASYMMETRIC statement (`le one zero` is false), so the
/// easy hypothesis built below (`zero ≤ one`, then `one ≤ one + qe` via
/// `le_add_of_nonneg`, chained by `le_trans`) only has the SHAPE
/// `∀ e, le x (add y qe)` when `x := zero` plays the bounded role and `y :=
/// one` plays the base being added to — exactly the roles the lemma's name
/// claims. The expected type is built independently via `cle`, not by
/// re-deriving the applied value's own inferred type, so a transposed
/// reading would fail to match here.
#[test]
fn le_of_forall_le_add_small_at_zero_one_proves_le_zero_one() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();

    let zero_real = d.kernel().const_(p.zero, vec![]);
    let one_real = d.kernel().const_(p.one, vec![]);

    // le01 : le zero one, from zero_lt_one + le_of_lt.
    let lt01 = d.lemma(p.zero_lt_one, &[]);
    let le01 = d.lemma(p.le_of_lt, &[zero_real, one_real, lt01]);

    // hyp : ∀ e, le zero (add one (ofRat (natDivSucc 1 e))).
    let hyp = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let one_nat = d.num(1);
        let qe_rat = super::div_succ(&mut d, p, 1, e);
        let qe = super::embed(&mut d, p, qe_rat);
        let nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, e]);
        // le1_add : le one (add one qe)
        let le1_add = d.lemma(p.le_add_of_nonneg, &[one_real, qe_rat, nonneg]);
        let sum = super::cadd(&mut d, p, one_real, qe);
        // step : le zero (add one qe)
        let step = d.lemma(p.le_trans, &[zero_real, one_real, sum, le01, le1_add]);
        d.lam_fv(e_fv, nat, step)
    };

    let value = d.lemma(p.le_of_forall_le_add_small, &[zero_real, one_real, hyp]);
    let ty = super::cle(&mut d, p, zero_real, one_real);

    let anon = kernel.anon();
    let name = kernel.name_str(
        anon,
        "__le_of_forall_le_add_small_at_zero_one_proves_le_zero_one",
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.le_of_forall_le_add_small zero one hyp did NOT check \
                 against le zero one (not merely SOME le statement, and not \
                 the reverse le one zero): {error:?}"
            )
        });
}

/// **Concrete instantiation of `CReal.equiv_zero_of_small` at `v := zero`.**
/// The hypothesis `∀ e, le (abs zero) qe` is built from `abs_le` (needing
/// `le zero qe` via `ofRat_le` and `le (neg zero) qe` via `ofRat_neg` +
/// `Rat.neg_zero` + `ofRat_le`, transported across the resulting `Equiv` by
/// `le_congr`), and the expected conclusion `Equiv zero zero` is built
/// independently via `equiv`, not by re-deriving the applied value's own
/// inferred type.
#[test]
fn equiv_zero_of_small_at_zero_proves_equiv_zero_zero() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rle, rneg};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let rat = p.rat;
    let nat = d.nat_ty();

    let zero_real = d.kernel().const_(p.zero, vec![]);
    let zero_rat = d.kernel().const_(rat.zero, vec![]);

    let hyp = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let one_nat = d.num(1);
        let qe_rat = super::div_succ(&mut d, p, 1, e);
        let qe = super::embed(&mut d, p, qe_rat);
        let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, e]);
        // h1 : le zero qe
        let h1 = d.lemma(p.of_rat_le, &[zero_rat, qe_rat, nonneg]);

        // h2 : le (neg zero) qe, via Equiv (neg zero) (ofRat (Rat.neg
        // Rat.zero)), Rat.neg_zero, and ofRat_le.
        let eq1 = d.lemma(p.of_rat_neg, &[zero_rat]);
        // eq1 : Equiv (neg zero) (ofRat (Rat.neg zero_rat))
        let neg_zero_rat = rneg(&mut d, zero_rat);
        let nz_eq = d.lemma(rat.neg_zero, &[]);
        // nz_eq : Eq Rat (Rat.neg zero_rat) zero_rat
        let nz_eq_sym = crate::rat_prelude::ops::rsymm(&mut d, zero_rat, neg_zero_rat, nz_eq);
        // nz_eq_sym : Eq Rat zero_rat (Rat.neg zero_rat)
        let le_negzr_qe = crate::rat_prelude::ops::rat_eq_rewrite(
            &mut d,
            zero_rat,
            neg_zero_rat,
            nz_eq_sym,
            nonneg,
            &|d, t| rle(d, rat, t, qe_rat),
        );
        // le_negzr_qe : Rat.le (Rat.neg zero_rat) qe_rat
        let embedded = d.lemma(p.of_rat_le, &[neg_zero_rat, qe_rat, le_negzr_qe]);
        // embedded : le (ofRat (Rat.neg zero_rat)) qe
        let neg_zero = d.const_app(p.neg, &[zero_real]);
        let embedded_neg_zero = super::embed(&mut d, p, neg_zero_rat);
        let eq1_sym = d.lemma(p.equiv_symm, &[neg_zero, embedded_neg_zero, eq1]);
        // eq1_sym : Equiv (ofRat (Rat.neg zero_rat)) (neg zero)
        let refl_qe = d.lemma(p.equiv_refl, &[qe]);
        let h2 = d.lemma(
            p.le_congr,
            &[
                embedded_neg_zero,
                neg_zero,
                qe,
                qe,
                eq1_sym,
                refl_qe,
                embedded,
            ],
        );
        // h2 : le (neg zero) qe
        let step = d.lemma(p.abs_le, &[zero_real, qe, h1, h2]);
        // step : le (abs zero) qe
        d.lam_fv(e_fv, nat, step)
    };

    let value = d.lemma(p.equiv_zero_of_small, &[zero_real, hyp]);
    let ty = super::equiv(&mut d, p, zero_real, zero_real);

    let anon = kernel.anon();
    let name = kernel.name_str(anon, "__equiv_zero_of_small_at_zero_proves_equiv_zero_zero");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.equiv_zero_of_small zero hyp did NOT check against \
                 Equiv zero zero (not merely SOME Equiv statement): {error:?}"
            )
        });
}

/// **`K := 1` instantiation of `CReal.le_of_forall_le_add_rate` recovers
/// `le_of_forall_le_add_small_at_zero_one_proves_le_zero_one`'s statement.**
/// Same hypothesis shape and goal, built against the GENERAL lemma at an
/// explicit `k := 1` rather than through the `le_of_forall_le_add_small`
/// wrapper — the cheapest evidence that generalizing did not silently change
/// the `K = 1` behaviour.
#[test]
fn le_of_forall_le_add_rate_at_k1_matches_small() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();
    let one_nat = d.num(1);

    let zero_real = d.kernel().const_(p.zero, vec![]);
    let one_real = d.kernel().const_(p.one, vec![]);

    let lt01 = d.lemma(p.zero_lt_one, &[]);
    let le01 = d.lemma(p.le_of_lt, &[zero_real, one_real, lt01]);

    // hyp : ∀ e, le zero (add one (ofRat (natDivSucc 1 e))).
    let hyp = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let qe_rat = super::div_succ(&mut d, p, 1, e);
        let qe = super::embed(&mut d, p, qe_rat);
        let nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, e]);
        let le1_add = d.lemma(p.le_add_of_nonneg, &[one_real, qe_rat, nonneg]);
        let sum = super::cadd(&mut d, p, one_real, qe);
        let step = d.lemma(p.le_trans, &[zero_real, one_real, sum, le01, le1_add]);
        d.lam_fv(e_fv, nat, step)
    };

    let value = d.lemma(
        p.le_of_forall_le_add_rate,
        &[one_nat, zero_real, one_real, hyp],
    );
    let ty = super::cle(&mut d, p, zero_real, one_real);

    let anon = kernel.anon();
    let name = kernel.name_str(anon, "__le_of_forall_le_add_rate_at_k1_matches_small");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.le_of_forall_le_add_rate 1 zero one hyp did NOT check \
                 against le zero one: {error:?}"
            )
        });
}

/// **`K := 2` instantiation of `CReal.le_of_forall_le_add_rate`,
/// DISCRIMINATING from `K := 1`.** The hypothesis's accuracy family is
/// `2/(e+1)`, not `1/(e+1)` — a rate a wrong generalization that merely
/// special-cased `K = 1` (e.g. hard-coding term B's fused bound at `3`/`4`/`5`
/// instead of `k+2`/`k+3`/`k+4`) could not consume, since `Rat.natDivSucc_add`
/// is invoked here with `k := 2` at every fusion step.
#[test]
fn le_of_forall_le_add_rate_at_k2_zero_one() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();
    let two_nat = d.num(2);

    let zero_real = d.kernel().const_(p.zero, vec![]);
    let one_real = d.kernel().const_(p.one, vec![]);

    let lt01 = d.lemma(p.zero_lt_one, &[]);
    let le01 = d.lemma(p.le_of_lt, &[zero_real, one_real, lt01]);

    // hyp : ∀ e, le zero (add one (ofRat (natDivSucc 2 e))).
    let hyp = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let qe_rat = super::div_succ(&mut d, p, 2, e);
        let qe = super::embed(&mut d, p, qe_rat);
        let nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[two_nat, e]);
        let le1_add = d.lemma(p.le_add_of_nonneg, &[one_real, qe_rat, nonneg]);
        let sum = super::cadd(&mut d, p, one_real, qe);
        let step = d.lemma(p.le_trans, &[zero_real, one_real, sum, le01, le1_add]);
        d.lam_fv(e_fv, nat, step)
    };

    let value = d.lemma(
        p.le_of_forall_le_add_rate,
        &[two_nat, zero_real, one_real, hyp],
    );
    let ty = super::cle(&mut d, p, zero_real, one_real);

    let anon = kernel.anon();
    let name = kernel.name_str(anon, "__le_of_forall_le_add_rate_at_k2_zero_one");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.le_of_forall_le_add_rate 2 zero one hyp did NOT check \
                 against le zero one: {error:?}"
            )
        });
}

/// **`K := 2` instantiation of `CReal.equiv_zero_of_rate` at `v := zero`,
/// DISCRIMINATING from `K := 1`.** Mirrors
/// `equiv_zero_of_small_at_zero_proves_equiv_zero_zero`'s hypothesis
/// construction at the rate `2/(e+1)` instead of `1/(e+1)`.
#[test]
fn equiv_zero_of_rate_at_k2_zero() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rle, rneg};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let rat = p.rat;
    let nat = d.nat_ty();
    let two_nat = d.num(2);

    let zero_real = d.kernel().const_(p.zero, vec![]);
    let zero_rat = d.kernel().const_(rat.zero, vec![]);

    let hyp = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let qe_rat = super::div_succ(&mut d, p, 2, e);
        let qe = super::embed(&mut d, p, qe_rat);
        let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two_nat, e]);
        // h1 : le zero qe
        let h1 = d.lemma(p.of_rat_le, &[zero_rat, qe_rat, nonneg]);

        // h2 : le (neg zero) qe.
        let eq1 = d.lemma(p.of_rat_neg, &[zero_rat]);
        let neg_zero_rat = rneg(&mut d, zero_rat);
        let nz_eq = d.lemma(rat.neg_zero, &[]);
        let nz_eq_sym = crate::rat_prelude::ops::rsymm(&mut d, zero_rat, neg_zero_rat, nz_eq);
        let le_negzr_qe = crate::rat_prelude::ops::rat_eq_rewrite(
            &mut d,
            zero_rat,
            neg_zero_rat,
            nz_eq_sym,
            nonneg,
            &|d, t| rle(d, rat, t, qe_rat),
        );
        let embedded = d.lemma(p.of_rat_le, &[neg_zero_rat, qe_rat, le_negzr_qe]);
        let neg_zero = d.const_app(p.neg, &[zero_real]);
        let embedded_neg_zero = super::embed(&mut d, p, neg_zero_rat);
        let eq1_sym = d.lemma(p.equiv_symm, &[neg_zero, embedded_neg_zero, eq1]);
        let refl_qe = d.lemma(p.equiv_refl, &[qe]);
        let h2 = d.lemma(
            p.le_congr,
            &[
                embedded_neg_zero,
                neg_zero,
                qe,
                qe,
                eq1_sym,
                refl_qe,
                embedded,
            ],
        );
        // h2 : le (neg zero) qe
        let step = d.lemma(p.abs_le, &[zero_real, qe, h1, h2]);
        d.lam_fv(e_fv, nat, step)
    };

    let value = d.lemma(p.equiv_zero_of_rate, &[two_nat, zero_real, hyp]);
    let ty = super::equiv(&mut d, p, zero_real, zero_real);

    let anon = kernel.anon();
    let name = kernel.name_str(anon, "__equiv_zero_of_rate_at_k2_zero");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.equiv_zero_of_rate 2 zero hyp did NOT check against \
                 Equiv zero zero: {error:?}"
            )
        });
}

/// `Rat.normalize (Int.ofNat num_val) (Nat.succ k) (one_le_succ k)`, where
/// `k := Nat.num(den_val - 1)` -- the literal rational `num_val/den_val`,
/// built so the denominator passed to `normalize` and the denominator named
/// in the positivity proof's type are the SAME term (`Nat.succ k`), not two
/// independently-built numerals that merely happen to match.
fn exp_test_rat_literal(
    d: &mut crate::int_prelude::ops::IntDev<'_>,
    num_val: u32,
    den_val: u32,
) -> crate::expr::ExprId {
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{normalize, one_le_succ};
    assert!(den_val >= 1, "denominator must be positive");
    let k = d.num(den_val - 1);
    let denominator = d.succ(k);
    let positive = one_le_succ(d, k);
    let num_nat = d.num(num_val);
    let numerator = d.of_nat(num_nat);
    normalize(d, numerator, denominator, positive)
}

/// **Mandatory computation test for `CReal.expSeriesPartial`.** Checks the
/// first four partial sums of `Σ_{n<k} 1/n!` reduce to the expected
/// rationals as REAL kernel reduction (`Kernel::def_eq`, which forces the
/// term through β/δ/ι reduction -- `sumRange`'s own `Nat.rec`, `CReal.add`'s
/// constant-sequence arithmetic, and `Rat.normalize`'s `gcd` bookkeeping --
/// all the way to a `Rat.mk` normal form), not merely type-checking: an
/// off-by-one in `sumRange`'s range bound type-checks perfectly and
/// constructs a DIFFERENT number, which only a reduction check catches.
///
/// `expSeriesPartial 1 = 1/0! = 1`, `expSeriesPartial 2 = 1 + 1/1! = 2`,
/// `expSeriesPartial 3 = 2 + 1/2! = 5/2`, `expSeriesPartial 4 = 5/2 + 1/3! =
/// 8/3` -- worked on paper before this test was written.
///
/// Includes a negative control: `expSeriesPartial 3` must NOT reduce to
/// `ofRat 2` (its own PRECEDING partial sum) -- a checker that cannot fail
/// is not a checker.
#[test]
fn exp_series_partial_computes_its_first_few_values() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    for (k_val, num_val, den_val) in [(1u32, 1u32, 1u32), (2, 2, 1), (3, 5, 2), (4, 8, 3)] {
        let k = d.num(k_val);
        let partial = d.const_app(p.exp_series_partial, &[k]);
        let expected = exp_test_rat_literal(&mut d, num_val, den_val);
        let embedded = d.const_app(p.of_rat, &[expected]);
        assert!(
            d.kernel().def_eq(partial, embedded),
            "expSeriesPartial {k_val} should reduce to ofRat ({num_val}/{den_val})"
        );
    }

    // Negative control: expSeriesPartial 3 (= 5/2) must NOT reduce to
    // ofRat 2 -- its own preceding partial sum, and the value it would
    // wrongly equal under an off-by-one that dropped the last term.
    let k3 = d.num(3);
    let partial3 = d.const_app(p.exp_series_partial, &[k3]);
    let two = exp_test_rat_literal(&mut d, 2, 1);
    let embedded_two = d.const_app(p.of_rat, &[two]);
    assert!(
        !d.kernel().def_eq(partial3, embedded_two),
        "expSeriesPartial 3 must NOT reduce to ofRat 2 -- if it does, this \
         check cannot fail and something is wrong with the harness, not \
         just the theorem"
    );
}

/// **Mandatory computation test for `CReal.expTerm_le_geom`.** Instantiates
/// the universal bound at the closed term `n := 3` and checks, by
/// `Kernel::infer` + `Kernel::def_eq` (not merely that the application
/// type-checks), that the inferred statement is EXACTLY `le (ofRat 1/6)
/// (ofRat 1/4)` -- `expTerm 3 = 1/3! = 1/6` and the geometric bound
/// `2/2^3 = 2/8` reduces (via `Rat.normalize`'s own `gcd` bookkeeping) to
/// the same `Rat.mk` normal form as `1/4`, built independently here. A
/// vacuous or off-by-one statement (e.g. comparing against `1/8`) would
/// type-check just as well; only forcing both sides through reduction and
/// checking the LITERAL expected value catches that.
///
/// Includes a negative control: `1/4` must not reduce to `1/8` -- a
/// consistency check that this harness can fail at all.
#[test]
fn exp_term_le_geom_concrete_instance_at_three() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let three = d.num(3);
    let head = d.kernel().const_(p.exp_term_le_geom, vec![]);
    let instance = d.apply(head, &[three]);
    let inferred = d
        .kernel()
        .infer(instance)
        .unwrap_or_else(|error| panic!("expTerm_le_geom refused at n=3: {error:?}"));

    let exp_term_3 = d.const_app(p.exp_term, &[three]);
    let expected_lhs = exp_test_rat_literal(&mut d, 1, 6); // 1/3! = 1/6
    let expected_rhs = exp_test_rat_literal(&mut d, 1, 4); // 2/2^3 = 2/8 = 1/4
    let embedded_lhs = d.const_app(p.of_rat, &[expected_lhs]);
    let embedded_rhs = d.const_app(p.of_rat, &[expected_rhs]);
    let expected_stmt = d.const_app(p.le, &[embedded_lhs, embedded_rhs]);

    assert!(
        d.kernel().def_eq(inferred, expected_stmt),
        "expTerm_le_geom at n=3 must state exactly le (ofRat 1/6) (ofRat 1/4)"
    );
    assert!(
        d.kernel().def_eq(exp_term_3, embedded_lhs),
        "expTerm 3 should independently reduce to ofRat 1/6"
    );

    let wrong_rhs = exp_test_rat_literal(&mut d, 1, 8);
    let embedded_wrong = d.const_app(p.of_rat, &[wrong_rhs]);
    assert!(
        !d.kernel().def_eq(embedded_rhs, embedded_wrong),
        "1/4 must not reduce to 1/8 -- sanity check that this harness can fail"
    );
}

/// **Mandatory statement check for `CReal.e_le_three`.** Confirms, by
/// `Kernel::infer` + `Kernel::def_eq` (not merely that the declaration
/// type-checked), that `e_le_three`'s inferred type is EXACTLY `le e
/// (ofRat 3/1)` -- not `le e (ofRat 4/1)` (the OLD, unsharpened bound this
/// slice replaces) and not the reversed `le (ofRat 3/1) e` (an accidentally
/// swapped inequality would type-check as a DIFFERENT theorem, not fail).
///
/// Includes a negative control: `ofRat 3/1` must not reduce to `ofRat 2/1`
/// -- a checker that cannot fail is not a checker.
#[test]
fn e_le_three_states_exactly_le_e_three() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let e_le_three_const = d.kernel().const_(p.e_le_three, vec![]);
    let inferred = d
        .kernel()
        .infer(e_le_three_const)
        .unwrap_or_else(|error| panic!("e_le_three refused: {error:?}"));

    let e_const = d.kernel().const_(p.e, vec![]);
    let three_lit = exp_test_rat_literal(&mut d, 3, 1);
    let embedded_three = d.const_app(p.of_rat, &[three_lit]);
    let expected_stmt = d.const_app(p.le, &[e_const, embedded_three]);

    assert!(
        d.kernel().def_eq(inferred, expected_stmt),
        "e_le_three must state exactly le e (ofRat 3/1)"
    );

    // Negative control: NOT `le e four` -- the bound this slice sharpens.
    let four_lit = exp_test_rat_literal(&mut d, 4, 1);
    let embedded_four = d.const_app(p.of_rat, &[four_lit]);
    let wrong_stmt_four = d.const_app(p.le, &[e_const, embedded_four]);
    assert!(
        !d.kernel().def_eq(inferred, wrong_stmt_four),
        "e_le_three must NOT state le e four -- that is the old, unsharpened bound"
    );

    // Inverted control: NOT the reversed inequality `le three e`.
    let wrong_stmt_reversed = d.const_app(p.le, &[embedded_three, e_const]);
    assert!(
        !d.kernel().def_eq(inferred, wrong_stmt_reversed),
        "e_le_three must NOT state le three e -- a swapped inequality is a different theorem"
    );

    // Sanity: this harness can fail at all.
    let two_lit = exp_test_rat_literal(&mut d, 2, 1);
    let embedded_two = d.const_app(p.of_rat, &[two_lit]);
    assert!(
        !d.kernel().def_eq(embedded_three, embedded_two),
        "ofRat 3/1 must not reduce to ofRat 2/1"
    );
}

/// **Mandatory computation test for `CReal.geom_tail_bounded_div`'s subject
/// matter.** `r := 1/2` is the concrete instantiation the geometric-series
/// slice's task named as mandatory: the answer is known independently (the
/// series sums to `2`), and its first four partial sums -- `1, 3/2, 7/4,
/// 15/8` -- must reduce as REAL kernel reduction (`Kernel::def_eq`, forcing
/// `sumRange`'s own `Nat.rec`, `CReal.pow`'s recursive `mul`, and `CReal.add`'s
/// constant-sequence arithmetic all the way to a `Rat.mk` normal form), not
/// merely type-check: an off-by-one in `sumRange`'s range bound, or in
/// `pow`'s recursive step, type-checks perfectly and builds a DIFFERENT
/// series, which only a reduction check catches.
///
/// Includes a negative control: the `k = 3` partial sum (`7/4`) must NOT
/// reduce to the `k = 2` partial sum (`3/2`) -- a checker that cannot fail is
/// not a checker.
#[test]
fn geometric_series_at_one_half_reduces_to_the_expected_partial_sums() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let half = exp_test_rat_literal(&mut d, 1, 2);
    let x = d.const_app(p.of_rat, &[half]);

    // `fun i => CReal.pow x i`, built the same way `power.rs::pow_fn` (and
    // `geometric.rs::pow_fn`) do.
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = d.const_app(p.pow, &[x, i]);
    let nat_ty = d.nat_ty();
    let f = d.lam_fv(i_fv, nat_ty, body);

    for (k_val, num_val, den_val) in [(1u32, 1u32, 1u32), (2, 3, 2), (3, 7, 4), (4, 15, 8)] {
        let k = d.num(k_val);
        let partial = d.const_app(p.sum_range, &[f, k]);
        let expected = exp_test_rat_literal(&mut d, num_val, den_val);
        let embedded = d.const_app(p.of_rat, &[expected]);
        assert!(
            d.kernel().def_eq(partial, embedded),
            "sumRange (pow 1/2) {k_val} should reduce to ofRat \
             ({num_val}/{den_val})"
        );
    }

    // Negative control: the k=3 partial sum (7/4) must NOT reduce to the
    // k=2 partial sum (3/2) -- the value it would wrongly equal under an
    // off-by-one that dropped the last term.
    let k3 = d.num(3u32);
    let partial3 = d.const_app(p.sum_range, &[f, k3]);
    let three_halves = exp_test_rat_literal(&mut d, 3, 2);
    let embedded_three_halves = d.const_app(p.of_rat, &[three_halves]);
    assert!(
        !d.kernel().def_eq(partial3, embedded_three_halves),
        "sumRange (pow 1/2) 3 must NOT reduce to 3/2 -- if it does, this \
         check cannot fail and something is wrong with the harness, not \
         just the theorem"
    );
}

/// **Mandatory concrete instantiation** for `CReal.monotone_of_nonneg_deriv`:
/// the identity function on `[0, 1]`, whose derivative is the constant `one`
/// (nonnegative everywhere), applied at `x := zero`, `y := one`. A statement
/// with `x` and `y` transposed type-checks just as readily and is the
/// reverse, false theorem — this pins the ASYMMETRIC instance, and checks
/// the conclusion is exactly `le zero one` (`F` is the identity), not merely
/// SOME `CReal.le` statement.
#[test]
fn monotone_of_nonneg_deriv_applies_to_the_identity_on_0_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    // identity := fun r => r; const_one := fun _ => one.
    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let const_one = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, one_c)
    };

    let hf = d.lemma(p.has_derivative_id, &[zero_c, one_c]);

    let le_zero_one = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero_c, one_c, lt])
    };

    // hderiv : ∀ z, le zero z -> le z one -> le zero (const_one z), i.e.
    // le zero one regardless of z (const_one z beta-reduces to one).
    let hderiv = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_ty = d.const_app(p.le, &[zero_c, z]);
        let hzb_ty = d.const_app(p.le, &[z, one_c]);
        let haz_fv = d.fresh_fvar();
        let hzb_fv = d.fresh_fvar();
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, le_zero_one);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };

    let hax = d.lemma(p.le_refl, &[zero_c]);
    let hxy = le_zero_one;
    let hyb = d.lemma(p.le_refl, &[one_c]);

    let instance = d.lemma(
        p.monotone_of_nonneg_deriv,
        &[
            identity, const_one, zero_c, one_c, hf, hderiv, zero_c, one_c, hax, hxy, hyb,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("monotone_of_nonneg_deriv refused at the identity on [0,1]: {error:?}")
    });

    // `F := fun r => r` is not beta-reduced by `render_lean`, so the
    // conclusion prints as `le ((fun r => r) zero) ((fun r => r) one)`
    // rather than `le zero one` — genuinely the same statement (`F x`/`F y`
    // beta-reduce to `x`/`y`), just not textually collapsed. Applying
    // `identity` at `zero_c`/`one_c` directly the same way builds the exact
    // expected type, so the two `render_lean` outputs are compared verbatim
    // — the pin discipline this file uses throughout — rather than loosely.
    let expected_fx = d.apply(identity, &[zero_c]);
    let expected_fy = d.apply(identity, &[one_c]);
    let expected_ty = d.const_app(p.le, &[expected_fx, expected_fy]);
    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected_ty);
    assert_eq!(
        rendered, expected_rendered,
        "must conclude exactly `le (F zero) (F one)` (F is the identity), not some other CReal.le statement"
    );
    assert!(
        rendered.contains("CReal.zero") && rendered.contains("CReal.one"),
        "the endpoints must be zero and one, not some other pair: {rendered}"
    );
}

/// **Mandatory concrete instantiation** for `CReal.order_reflect_of_pos_deriv`:
/// the identity function on `[0, 1]` again, at `x := zero`, `y := one`, with
/// `CReal.apart_zero_one` supplying `Apart x y` and `CReal.zero_lt_one`
/// supplying the codomain hypothesis `lt (F zero) (F one)` (`F` is the
/// identity, so this is literally `lt zero one`). The conclusion is
/// therefore the same fact fed in as the codomain hypothesis — a tautology
/// for `F := id`, since order-reflection through the identity changes
/// nothing — but that is exactly the sanity check this instantiation is
/// for: every piece (the `HasDerivativeOn` witness, the uniform positive
/// bound at `k := 0`, the `Apart`/`lt` wiring) must still compose and the
/// kernel must still accept the result.
#[test]
fn order_reflect_of_pos_deriv_applies_to_the_identity_on_0_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::rat_eq_rewrite;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_nat = d.num(0);
    let one_nat = d.num(1);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let const_one = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, one_c)
    };

    let hf = d.lemma(p.has_derivative_id, &[zero_c, one_c]);

    let embed_le_one = {
        let unit_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let one_rat = d.kernel().const_(p.rat.one, vec![]);
        let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
        let unit_embed = d.const_app(p.of_rat, &[unit_rat]);
        let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
        let bridge = rat_eq_rewrite(
            &mut d,
            unit_rat,
            one_rat,
            unit_eq_one,
            refl_start,
            &|d, t| {
                let embedded = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[unit_embed, embedded])
            },
        );
        d.lemma(p.le_of_equiv, &[unit_embed, one_c, bridge])
    };

    let hderiv = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_ty = d.const_app(p.le, &[zero_c, z]);
        let hzb_ty = d.const_app(p.le, &[z, one_c]);
        let haz_fv = d.fresh_fvar();
        let hzb_fv = d.fresh_fvar();
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, embed_le_one);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };

    let hax = d.lemma(p.le_refl, &[zero_c]);
    let hxb = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero_c, one_c, lt])
    };
    let hay = hxb;
    let hyb = d.lemma(p.le_refl, &[one_c]);
    let hap = d.lemma(p.apart_zero_one, &[]);
    let hcodom = d.lemma(p.zero_lt_one, &[]);

    let instance = d.lemma(
        p.inverse_fn.order_reflect_of_pos_deriv,
        &[
            identity, const_one, zero_c, one_c, hf, zero_nat, hderiv, zero_c, one_c, hax, hxb, hay,
            hyb, hap, hcodom,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("order_reflect_of_pos_deriv refused at the identity on [0,1]: {error:?}")
    });

    let expected_ty = d.const_app(p.lt, &[zero_c, one_c]);
    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected_ty);
    assert_eq!(
        rendered, expected_rendered,
        "must conclude exactly `lt zero one`, not some other CReal.lt statement"
    );
}

/// **Mandatory concrete instantiation** for
/// `CReal.inverse_lipschitz_of_pos_deriv`: the identity function on `[0, 1]`
/// again, at `x := zero`, `y := one`, with `CReal.apart_zero_one` supplying
/// `Apart x y`. Unlike `order_reflect_of_pos_deriv`'s instantiation, this one
/// needs NO codomain hypothesis at all -- there is no `hcodom` argument.
///
/// At `k := 0`, `e_acc = Nat.succ (Nat.mul 2 0)` reduces to `1`, so the
/// pinned constant is `ofNat (Nat.succ 1) = ofNat 2`. This is checked by
/// `def_eq` against the FULLY REDUCED statement `le (abs (add zero (neg
/// one))) (mul (ofNat 2) (abs (add zero (neg one))))`, not merely that SOME
/// bound was accepted: a wrong `e_acc` (off by one, or using `k` directly
/// instead of `Nat.succ (Nat.mul 2 k)`) pins a DIFFERENT `Nat` numeral, and
/// two distinct closed `Nat` numerals are never defeq.
#[test]
fn inverse_lipschitz_of_pos_deriv_applies_to_the_identity_on_0_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::rat_eq_rewrite;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let const_one = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, one_c)
    };

    let hf = d.lemma(p.has_derivative_id, &[zero_c, one_c]);

    let embed_le_one = {
        let unit_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let one_rat = d.kernel().const_(p.rat.one, vec![]);
        let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
        let unit_embed = d.const_app(p.of_rat, &[unit_rat]);
        let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
        let bridge = rat_eq_rewrite(
            &mut d,
            unit_rat,
            one_rat,
            unit_eq_one,
            refl_start,
            &|d, t| {
                let embedded = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[unit_embed, embedded])
            },
        );
        d.lemma(p.le_of_equiv, &[unit_embed, one_c, bridge])
    };

    let hderiv = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_ty = d.const_app(p.le, &[zero_c, z]);
        let hzb_ty = d.const_app(p.le, &[z, one_c]);
        let haz_fv = d.fresh_fvar();
        let hzb_fv = d.fresh_fvar();
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, embed_le_one);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };

    let hax = d.lemma(p.le_refl, &[zero_c]);
    let hxb = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero_c, one_c, lt])
    };
    let hay = hxb;
    let hyb = d.lemma(p.le_refl, &[one_c]);
    let hap = d.lemma(p.apart_zero_one, &[]);

    let instance = d.lemma(
        p.inverse_lipschitz_of_pos_deriv,
        &[
            identity, const_one, zero_c, one_c, hf, zero_nat, hderiv, zero_c, one_c, hax, hxb, hay,
            hyb, hap,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("inverse_lipschitz_of_pos_deriv refused at the identity on [0,1]: {error:?}")
    });

    let diff = {
        let neg_one = d.const_app(p.neg, &[one_c]);
        d.const_app(p.add, &[zero_c, neg_one])
    };
    let abs_diff = d.const_app(p.abs, &[diff]);
    let of_nat_two = d.const_app(p.of_nat, &[two_nat]);
    let scaled = d.const_app(p.mul, &[of_nat_two, abs_diff]);
    let expected_reduced = d.const_app(p.le, &[abs_diff, scaled]);
    assert!(
        d.kernel().def_eq(ty, expected_reduced),
        "must reduce to `le (abs (zero-one)) (mul (ofNat 2) (abs (zero-one)))`; \
         a wrong `e_acc` pins a different `Nat` numeral, which is never defeq"
    );
}

/// **Mandatory concrete instantiation** for `CReal.strict_mono_of_pos_deriv`:
/// the identity function on `[0, 1]`, whose derivative is the constant `one`
/// — uniformly bounded below by `1/(0+1) = 1` (`k := 0`) — applied at
/// `x := zero`, `y := one` with the STRICT input gap `CReal.zero_lt_one`.
/// Mirrors [`monotone_of_nonneg_deriv_applies_to_the_identity_on_0_1`], but
/// checks the conclusion is exactly `lt zero one`, not `le zero one`: a
/// theorem that quietly proved only the non-strict conclusion would still
/// pass a `le`-shaped check.
#[test]
fn strict_mono_of_pos_deriv_applies_to_the_identity_on_0_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::rat_eq_rewrite;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_nat = d.num(0);
    let one_nat = d.num(1);

    // identity := fun r => r; const_one := fun _ => one.
    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let const_one = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, one_c)
    };

    let hf = d.lemma(p.has_derivative_id, &[zero_c, one_c]);

    // le (embed (natDivSucc 1 0)) one_c, via `CReal.ratUnitEqOne` bridging
    // `natDivSucc 1 0` to `Rat.one` (the same technique
    // `creal/monotone.rs`'s private `of_nat_one_equiv_local` uses, duplicated
    // here since tests are a sibling module and cannot call it).
    let embed_le_one = {
        let unit_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let one_rat = d.kernel().const_(p.rat.one, vec![]);
        let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
        let unit_embed = d.const_app(p.of_rat, &[unit_rat]);
        let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
        let bridge = rat_eq_rewrite(
            &mut d,
            unit_rat,
            one_rat,
            unit_eq_one,
            refl_start,
            &|d, t| {
                let embedded = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[unit_embed, embedded])
            },
        );
        // bridge : Equiv unit_embed (ofRat one_rat), defeq Equiv unit_embed one_c.
        d.lemma(p.le_of_equiv, &[unit_embed, one_c, bridge])
    };

    // hderiv : ∀ z, le zero z -> le z one -> le (embed (natDivSucc 1 0)) (const_one z).
    let hderiv = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_ty = d.const_app(p.le, &[zero_c, z]);
        let hzb_ty = d.const_app(p.le, &[z, one_c]);
        let haz_fv = d.fresh_fvar();
        let hzb_fv = d.fresh_fvar();
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, embed_le_one);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };

    let hax = d.lemma(p.le_refl, &[zero_c]);
    let hxy = d.lemma(p.zero_lt_one, &[]);
    let hyb = d.lemma(p.le_refl, &[one_c]);

    let instance = d.lemma(
        p.strict_mono_of_pos_deriv,
        &[
            identity, const_one, zero_c, one_c, hf, zero_nat, hderiv, zero_c, one_c, hax, hxy, hyb,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("strict_mono_of_pos_deriv refused at the identity on [0,1]: {error:?}")
    });

    let expected_fx = d.apply(identity, &[zero_c]);
    let expected_fy = d.apply(identity, &[one_c]);
    let expected_ty = d.const_app(p.lt, &[expected_fx, expected_fy]);
    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected_ty);
    assert_eq!(
        rendered, expected_rendered,
        "must conclude exactly `lt (F zero) (F one)` (F is the identity), not `le`, and not some other CReal.lt statement"
    );
    assert!(
        rendered.contains("CReal.zero") && rendered.contains("CReal.one"),
        "the endpoints must be zero and one, not some other pair: {rendered}"
    );
}

/// **Mandatory concrete instantiation** for `CReal.strict_mono_magnitude`:
/// the identity function on `[0, 1]` again, `k := 0`, applied at `x := zero`,
/// `y := one` with the NON-strict gap `le zero one` (derived from
/// `CReal.zero_lt_one` via `le_of_lt`, since this lemma takes `le x y`, not
/// `lt x y`). At `k := 0` the bound is `1/2`: for the identity the true rate
/// is `1`, so `1 - 0 >= (1/2)*(1-0)` holds with room to spare -- this checks
/// the theorem PRODUCES exactly that inequality, not merely that some
/// application type-checks.
///
/// `x := 0, y := 1` rather than `x = y`: at `x = y` both sides of the
/// conclusion are `Equiv`-zero and the instance could not discriminate a
/// theorem that silently proved something else with the same shape.
#[test]
fn strict_mono_magnitude_applies_to_the_identity_on_0_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::rat_eq_rewrite;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_nat = d.num(0);
    let one_nat = d.num(1);

    // identity := fun r => r; const_one := fun _ => one.
    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let const_one = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, one_c)
    };

    let hf = d.lemma(p.has_derivative_id, &[zero_c, one_c]);

    // le (embed (natDivSucc 1 0)) one_c -- identical construction to
    // `strict_mono_of_pos_deriv_applies_to_the_identity_on_0_1`, above,
    // duplicated for the same reason it is there: tests are a sibling module
    // and cannot call `creal/monotone.rs`'s private `of_nat_one_equiv_local`.
    let embed_le_one = {
        let unit_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let one_rat = d.kernel().const_(p.rat.one, vec![]);
        let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
        let unit_embed = d.const_app(p.of_rat, &[unit_rat]);
        let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
        let bridge = rat_eq_rewrite(
            &mut d,
            unit_rat,
            one_rat,
            unit_eq_one,
            refl_start,
            &|d, t| {
                let embedded = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[unit_embed, embedded])
            },
        );
        d.lemma(p.le_of_equiv, &[unit_embed, one_c, bridge])
    };

    // hderiv : ∀ z, le zero z -> le z one -> le (embed (natDivSucc 1 0)) (const_one z).
    let hderiv = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_ty = d.const_app(p.le, &[zero_c, z]);
        let hzb_ty = d.const_app(p.le, &[z, one_c]);
        let haz_fv = d.fresh_fvar();
        let hzb_fv = d.fresh_fvar();
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, embed_le_one);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };

    let hax = d.lemma(p.le_refl, &[zero_c]);
    let hxy_lt = d.lemma(p.zero_lt_one, &[]);
    let hxy_le = d.lemma(p.le_of_lt, &[zero_c, one_c, hxy_lt]);
    let hyb = d.lemma(p.le_refl, &[one_c]);

    let instance = d.lemma(
        p.strict_mono_magnitude,
        &[
            identity, const_one, zero_c, one_c, hf, zero_nat, hderiv, zero_c, one_c, hax, hxy_le,
            hyb,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("strict_mono_magnitude refused at the identity on [0,1]: {error:?}")
    });

    // Reconstruct the expected type by the SAME route `half_frac_eq`
    // (`creal/monotone.rs`, private) builds `e_acc`/`a_half` internally at
    // `k := 0`: `e_acc = succ(2*0) = 1`, so `a_half = embed (natDivSucc 1 1)`,
    // i.e. `1/2`.
    let two_nat = d.num(2);
    let doubled = NatOps::mul(&mut d, two_nat, zero_nat);
    let e_acc = d.succ(doubled);
    let frac_e_acc_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e_acc]);
    let a_half = d.const_app(p.of_rat, &[frac_e_acc_rat]);

    let neg_zero = d.const_app(p.neg, &[zero_c]);
    let diff = d.const_app(p.add, &[one_c, neg_zero]);
    let s4 = d.const_app(p.mul, &[a_half, diff]);

    let expected_fx = d.apply(identity, &[zero_c]);
    let expected_fy = d.apply(identity, &[one_c]);
    let neg_fx = d.const_app(p.neg, &[expected_fx]);
    let rhs = d.const_app(p.add, &[expected_fy, neg_fx]);

    let expected_ty = d.const_app(p.le, &[s4, rhs]);
    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected_ty);
    assert_eq!(
        rendered, expected_rendered,
        "must conclude exactly `le ((1/2)*(one - zero)) (F one - F zero)` (F is the identity), \
         not some other CReal.le statement"
    );
    assert!(
        rendered.contains("CReal.zero") && rendered.contains("CReal.one"),
        "the endpoints must be zero and one, not some other pair: {rendered}"
    );
}

/// **Mandatory concrete instantiation** for
/// `CReal.strict_injective_of_pos_deriv`: the identity function on `[0, 1]`
/// again, applied at `x := zero`, `y := one` with `CReal.apart_zero_one` as
/// the apartness witness. Checks the conclusion is exactly
/// `Apart (F zero) (F one)`, i.e. `Apart zero one`.
#[test]
fn strict_injective_of_pos_deriv_applies_to_the_identity_on_0_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::rat_eq_rewrite;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_nat = d.num(0);
    let one_nat = d.num(1);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let const_one = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, one_c)
    };

    let hf = d.lemma(p.has_derivative_id, &[zero_c, one_c]);

    let embed_le_one = {
        let unit_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let one_rat = d.kernel().const_(p.rat.one, vec![]);
        let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
        let unit_embed = d.const_app(p.of_rat, &[unit_rat]);
        let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
        let bridge = rat_eq_rewrite(
            &mut d,
            unit_rat,
            one_rat,
            unit_eq_one,
            refl_start,
            &|d, t| {
                let embedded = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[unit_embed, embedded])
            },
        );
        d.lemma(p.le_of_equiv, &[unit_embed, one_c, bridge])
    };

    let hderiv = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_ty = d.const_app(p.le, &[zero_c, z]);
        let hzb_ty = d.const_app(p.le, &[z, one_c]);
        let haz_fv = d.fresh_fvar();
        let hzb_fv = d.fresh_fvar();
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, embed_le_one);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };

    let hax = d.lemma(p.le_refl, &[zero_c]);
    let hxb = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero_c, one_c, lt])
    };
    let hay = hxb;
    let hyb = d.lemma(p.le_refl, &[one_c]);
    let hap = d.lemma(p.apart_zero_one, &[]);

    let instance = d.lemma(
        p.strict_injective_of_pos_deriv,
        &[
            identity, const_one, zero_c, one_c, hf, zero_nat, hderiv, zero_c, one_c, hax, hxb, hay,
            hyb, hap,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("strict_injective_of_pos_deriv refused at the identity on [0,1]: {error:?}")
    });

    let expected_fx = d.apply(identity, &[zero_c]);
    let expected_fy = d.apply(identity, &[one_c]);
    let expected_ty = d.const_app(p.apart, &[expected_fx, expected_fy]);
    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected_ty);
    assert_eq!(
        rendered, expected_rendered,
        "must conclude exactly `Apart (F zero) (F one)`, not some other CReal.Apart statement"
    );
    assert!(
        rendered.contains("CReal.zero") && rendered.contains("CReal.one"),
        "the endpoints must be zero and one, not some other pair: {rendered}"
    );
}

/// **Mandatory concrete instantiation** for `CReal.ivt_step`: the identity
/// function on the ASYMMETRIC bracket `[zero, one]` (asymmetric about `zero`,
/// unlike `[-1, 1]`, so a transposed-endpoint defect cannot pass), at
/// `eps := one`. `F P = id zero = zero ≤ one = eps` and `neg eps = neg one ≤
/// one = id one = F Q` both hold, so `ivt_step`'s hypotheses are genuinely
/// satisfiable here, not vacuously discharged.
#[test]
fn ivt_step_applies_to_the_identity_on_zero_one() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let neg_one = d.const_app(p.neg, &[one_c]);

    // identity := fun r => r.
    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    let heps = d.lemma(p.zero_lt_one, &[]);
    let hpq = d.lemma(p.le_of_lt, &[zero_c, one_c, heps]);
    let hfp = hpq; // le (id zero) one, defeq le zero one, via beta.

    // hfq : le (neg one) one, via `lt (neg one) one` (the same estimate
    // `ivt.rs`'s private `neg_lt_of_pos` builds, duplicated here since tests
    // are a sibling module and cannot call it).
    let hfq = {
        let refl_neg_one = d.lemma(p.le_refl, &[neg_one]);
        let step1 = d.lemma(
            p.add_lt_add_of_le_of_lt,
            &[neg_one, neg_one, zero_c, one_c, refl_neg_one, heps],
        );
        // step1 : lt (add neg_one zero) (add neg_one one)
        let neg_one_zero = d.const_app(p.add, &[neg_one, zero_c]);
        let neg_one_one = d.const_app(p.add, &[neg_one, one_c]);
        let add_zero_negone = d.lemma(p.add_zero, &[neg_one]); // Equiv neg_one_zero neg_one
        let refl_target = d.lemma(p.equiv_refl, &[neg_one_one]);
        let step2 = d.lemma(
            p.lt_congr,
            &[
                neg_one_zero,
                neg_one,
                neg_one_one,
                neg_one_one,
                add_zero_negone,
                refl_target,
                step1,
            ],
        );
        // step2 : lt neg_one neg_one_one
        let comm = d.lemma(p.add_comm, &[neg_one, one_c]); // Equiv neg_one_one (add one neg_one)
        let one_negone = d.const_app(p.add, &[one_c, neg_one]);
        let vanish = d.lemma(p.add_neg, &[one_c]); // Equiv one_negone zero
        let compose = d.lemma(
            p.equiv_trans,
            &[neg_one_one, one_negone, zero_c, comm, vanish],
        );
        let refl_neg_one2 = d.lemma(p.equiv_refl, &[neg_one]);
        let step3 = d.lemma(
            p.lt_congr,
            &[
                neg_one,
                neg_one,
                neg_one_one,
                zero_c,
                refl_neg_one2,
                compose,
                step2,
            ],
        );
        // step3 : lt neg_one zero
        let lt_neg_one_one = d.lemma(p.lt_trans, &[neg_one, zero_c, one_c, step3, heps]);
        d.lemma(p.le_of_lt, &[neg_one, one_c, lt_neg_one_one])
    };

    let instance = d.lemma(
        p.ivt_step,
        &[identity, zero_c, one_c, one_c, heps, hpq, hfp, hfq],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("ivt_step refused at the identity on [zero, one]: {error:?}")
    });

    let rendered = d.kernel().render_lean(ty);
    assert!(
        rendered.contains("Exists") && rendered.matches("Exists").count() >= 2,
        "the conclusion must be a nested nat existential `Exists CReal (fun P' => Exists CReal \
         (fun Q' => ...))`, got: {rendered}"
    );
    assert!(
        rendered.contains("CReal.le") && rendered.contains("Equiv"),
        "the conclusion must carry both the four `CReal.le` bracket/sign facts and the \
         `Equiv`-typed width identity, got: {rendered}"
    );
}

/// A closed `Rat.natDivSucc k j` (negated if `negate`), i.e. `k/(j+1)` or
/// `-k/(j+1)`.
fn ivt_bisect_rat_lit(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, j: u32, negate: bool) -> ExprId {
    let kk = d.num(k);
    let jj = d.num(j);
    let q = d.const_app(p.rat.nat_div_succ, &[kk, jj]);
    if negate {
        crate::rat_prelude::ops::rneg(d, q)
    } else {
        q
    }
}

/// Whether two closed `Rat` terms reduce to the same value, checked via
/// `Rat.ble` BOTH ways rather than raw `def_eq` on the terms themselves --
/// robust to `a`/`b` being unequal-looking-but-equal-valued representations
/// (e.g. an unreduced sum vs. a hand-picked `natDivSucc` literal), since
/// `Rat.ble` decides order by cross-multiplication regardless of shape.
fn ivt_bisect_rat_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> bool {
    let bool_true = d.bool_true();
    let ab = d.const_app(p.rat.ble, &[a, b]);
    let ba = d.const_app(p.rat.ble, &[b, a]);
    d.kernel().def_eq(ab, bool_true) && d.kernel().def_eq(ba, bool_true)
}

/// Whether `a < b` on closed `Rat` terms, checked as `Rat.ble a b = true` AND
/// `Rat.ble b a = false` (both decided by `Rat.ble`'s own reduction, robust
/// to shape the same way [`ivt_bisect_rat_eq`] is).
fn ivt_bisect_rat_lt(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> bool {
    let bool_true = d.bool_true();
    let bool_false = d.bool_false();
    let ab = d.const_app(p.rat.ble, &[a, b]);
    let ba = d.const_app(p.rat.ble, &[b, a]);
    d.kernel().def_eq(ab, bool_true) && d.kernel().def_eq(ba, bool_false)
}

/// **Mandatory concrete instantiation** for `CReal.ivt_bisect_lo`/`_hi`: `F
/// := id` on the ASYMMETRIC bracket `[-1, 2]` (asymmetric about `zero`, so a
/// transposed-endpoint defect cannot pass), at `n := 0` (`eps_0 = 1`, sample
/// index `j = succ(2*0) = 1`, threshold `1/(j+1) = 1/2`).
///
/// By hand: `k=0` is the unmoved bracket `(-1, 2)`. `k=1`: `m = -1 + 3*1/2 =
/// 1/2`; `F m = 1/2 <= 1/2` (the threshold) so the branch takes `(m, hi) =
/// (1/2, 2)`. `k=2`: `m = 1/2 + 3/2*1/2 = 5/4`; `F m = 5/4 > 1/2` so the
/// branch takes `(lo, m) = (1/2, 5/4)`. The width halves at each step: `3,
/// 3/2, 3/4`. Every sample is checked via [`ivt_bisect_rat_eq`], not raw
/// `def_eq`, since neither side is guaranteed to reduce to the same
/// unnormalized shape.
#[test]
fn ivt_bisect_reduces_on_the_identity_bracket_neg_one_two() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    // F := identity.
    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    // P0 := -1, Q0 := 2.
    let one_c = d.kernel().const_(p.one, vec![]);
    let p0 = d.const_app(p.neg, &[one_c]);
    let two_nat = d.num(2);
    let q0 = d.const_app(p.of_nat, &[two_nat]);

    let n0 = d.zero(); // eps index n := 0
    let idx0 = d.zero(); // sample index -- every bracket endpoint here is a
    // constant-valued `CReal`, so the sampling index is irrelevant to the
    // VALUE (only to the regularity proof, which this test never inspects).

    // (label, k, expected_lo, expected_hi)
    let cases: [(&str, u32, ExprId, ExprId); 3] = [
        (
            "k=0 (unmoved base bracket)",
            0,
            ivt_bisect_rat_lit(&mut d, p, 1, 0, true), // -1
            ivt_bisect_rat_lit(&mut d, p, 2, 0, false), // 2
        ),
        (
            "k=1 (F m = 1/2 <= thresh -> (m, hi))",
            1,
            ivt_bisect_rat_lit(&mut d, p, 1, 1, false), // 1/2
            ivt_bisect_rat_lit(&mut d, p, 2, 0, false), // 2
        ),
        (
            "k=2 (F m = 5/4 > thresh -> (lo, m))",
            2,
            ivt_bisect_rat_lit(&mut d, p, 1, 1, false), // 1/2
            ivt_bisect_rat_lit(&mut d, p, 5, 3, false), // 5/4
        ),
    ];

    let mut widths = Vec::new();
    for (label, k, expected_lo, expected_hi) in cases {
        let kk = d.num(k);
        let bracket_lo = d.const_app(p.ivt_bisect_lo, &[identity, p0, q0, n0, kk]);
        let bracket_hi = d.const_app(p.ivt_bisect_hi, &[identity, p0, q0, n0, kk]);
        let lo_sample = d.const_app(p.seq, &[bracket_lo, idx0]);
        let hi_sample = d.const_app(p.seq, &[bracket_hi, idx0]);

        assert!(
            ivt_bisect_rat_eq(&mut d, p, lo_sample, expected_lo),
            "{label}: lower endpoint did not reduce to the expected rational"
        );
        assert!(
            ivt_bisect_rat_eq(&mut d, p, hi_sample, expected_hi),
            "{label}: upper endpoint did not reduce to the expected rational"
        );

        // width = hi - lo, as a Rat, for the halving check below.
        let width = crate::rat_prelude::group::rsub(&mut d, p.rat, hi_sample, lo_sample);
        widths.push(width);
    }

    // Widths must halve exactly: 3, 3/2, 3/4.
    let expected_widths = [
        ivt_bisect_rat_lit(&mut d, p, 3, 0, false), // 3
        ivt_bisect_rat_lit(&mut d, p, 3, 1, false), // 3/2
        ivt_bisect_rat_lit(&mut d, p, 3, 3, false), // 3/4
    ];
    for (i, (actual, expected)) in widths.iter().zip(expected_widths.iter()).enumerate() {
        assert!(
            ivt_bisect_rat_eq(&mut d, p, *actual, *expected),
            "bracket width at k={i} did not reduce to the expected rational"
        );
    }
}

/// **Mandatory concrete instantiation** for `CReal.ivt_bisect_diag_lo`/`_hi`
/// (the DIAGONAL bisection, [`CRealPrelude::ivt_bisect_diag`]): `F := id` on
/// the SAME asymmetric bracket `[-1, 2]` [`ivt_bisect_reduces_on_the_identity_bracket_neg_one_two`]
/// uses, so this exercises a computation the kernel already performs a
/// fixed-`n` version of, on identical inputs -- a transposed-endpoint defect
/// still cannot pass either test, and any drift between the two
/// constructions on their shared first steps would show up as a diff here.
///
/// By hand, using THIS construction's own per-step slack (step `j` samples
/// at `thresh_j := natDivSucc 1 (succ (2*j))`, half of `eps_j := natDivSucc 1
/// j`): `k=0` is the unmoved bracket `(-1, 2)`. Step `j=0` (`thresh_0 =
/// 1/2`): `m = -1 + 3*1/2 = 1/2`; `F m = 1/2 <= 1/2`, branch `(m, hi) =
/// (1/2, 2)`. Step `j=1` (`thresh_1 = 1/4`): `m = 1/2 + 3/2*1/2 = 5/4`; `F m
/// = 5/4 > 1/4`, branch `(lo, m) = (1/2, 5/4)`. The width halves each step
/// (`3, 3/2, 3/4`) exactly as `ivt_bisect`'s own test (width halving does not
/// depend on which threshold was used), AND the slack used at each step
/// strictly shrinks (`eps_0 = 1 > eps_1 = 1/2`) -- both are checked below,
/// neither assumed.
///
/// This same trace is where the diary's counterexample (1) starts:
/// continuing past `k=2`, `lo` never moves again (every later step keeps
/// picking `(lo, m)`), so the bracket converges to `1/2`, not the true root
/// `0` -- see [`super::CRealPrelude::ivt_bisect_diag`]'s doc comment for the
/// full argument. Only the three steps this section's task asks for are
/// checked by kernel reduction here; the eventual limit is a `CReal`, not a
/// decidable reduction.
#[test]
fn ivt_bisect_diag_reduces_on_the_identity_bracket_neg_one_two() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    // F := identity.
    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    // P0 := -1, Q0 := 2.
    let one_c = d.kernel().const_(p.one, vec![]);
    let p0 = d.const_app(p.neg, &[one_c]);
    let two_nat = d.num(2);
    let q0 = d.const_app(p.of_nat, &[two_nat]);

    let idx0 = d.zero(); // every bracket endpoint here is a constant-valued
    // `CReal`, so the sampling index is irrelevant to the VALUE (only to the
    // regularity proof, which this test never inspects).

    // (label, k, expected_lo, expected_hi)
    let cases: [(&str, u32, ExprId, ExprId); 3] = [
        (
            "k=0 (unmoved base bracket)",
            0,
            ivt_bisect_rat_lit(&mut d, p, 1, 0, true), // -1
            ivt_bisect_rat_lit(&mut d, p, 2, 0, false), // 2
        ),
        (
            "k=1 (step j=0, thresh_0=1/2: F m = 1/2 <= thresh -> (m, hi))",
            1,
            ivt_bisect_rat_lit(&mut d, p, 1, 1, false), // 1/2
            ivt_bisect_rat_lit(&mut d, p, 2, 0, false), // 2
        ),
        (
            "k=2 (step j=1, thresh_1=1/4: F m = 5/4 > thresh -> (lo, m))",
            2,
            ivt_bisect_rat_lit(&mut d, p, 1, 1, false), // 1/2
            ivt_bisect_rat_lit(&mut d, p, 5, 3, false), // 5/4
        ),
    ];

    let mut widths = Vec::new();
    for (label, k, expected_lo, expected_hi) in cases {
        let kk = d.num(k);
        let bracket_lo = d.const_app(p.ivt_bisect_diag_lo, &[identity, p0, q0, kk]);
        let bracket_hi = d.const_app(p.ivt_bisect_diag_hi, &[identity, p0, q0, kk]);
        let lo_sample = d.const_app(p.seq, &[bracket_lo, idx0]);
        let hi_sample = d.const_app(p.seq, &[bracket_hi, idx0]);

        assert!(
            ivt_bisect_rat_eq(&mut d, p, lo_sample, expected_lo),
            "{label}: lower endpoint did not reduce to the expected rational"
        );
        assert!(
            ivt_bisect_rat_eq(&mut d, p, hi_sample, expected_hi),
            "{label}: upper endpoint did not reduce to the expected rational"
        );

        // width = hi - lo, as a Rat, for the halving check below.
        let width = crate::rat_prelude::group::rsub(&mut d, p.rat, hi_sample, lo_sample);
        widths.push(width);
    }

    // Widths must halve exactly: 3, 3/2, 3/4.
    let expected_widths = [
        ivt_bisect_rat_lit(&mut d, p, 3, 0, false), // 3
        ivt_bisect_rat_lit(&mut d, p, 3, 1, false), // 3/2
        ivt_bisect_rat_lit(&mut d, p, 3, 3, false), // 3/4
    ];
    for (i, (actual, expected)) in widths.iter().zip(expected_widths.iter()).enumerate() {
        assert!(
            ivt_bisect_rat_eq(&mut d, p, *actual, *expected),
            "bracket width at k={i} did not reduce to the expected rational"
        );
    }

    // The slack itself -- `eps_j := natDivSucc 1 j` at the two steps this
    // test exercises -- strictly shrinks (`eps_0 = 1 > eps_1 = 1/2`). This is
    // the property `ivt_bisect` (a fixed external `n`) never has to
    // establish, since its `n` never changes within one bisection run; it is
    // the only genuinely new arithmetic fact this construction introduces.
    let eps0 = ivt_bisect_rat_lit(&mut d, p, 1, 0, false); // 1
    let eps1 = ivt_bisect_rat_lit(&mut d, p, 1, 1, false); // 1/2
    assert!(
        ivt_bisect_rat_lt(&mut d, p, eps1, eps0),
        "the per-step slack must strictly shrink: eps_1 = 1/2 must be < eps_0 = 1"
    );
}

// ---------------------------------------------------------------------------
// `CReal.evtLinear` / `CReal.evt_attained_max_decides_sign`
// (`creal/extreme_value.rs`, ADR-0603 row 2 for the Extreme Value Theorem)
// ---------------------------------------------------------------------------

/// **The non-vacuity control, and the one that matters most for this
/// declaration.** `evt_attained_max_decides_sign` is a REFUTATION shaped as an
/// implication, so if its maximality hypothesis had no models it would be
/// unfalsifiable -- exactly the "checker that cannot fail" defect this
/// repository audits against, arriving as a theorem instead of a script.
///
/// So: discharge the hypothesis at a genuine, non-degenerate instance and let
/// the kernel infer the conclusion. `v := 1`, `c := 1` -- the true maximiser
/// of `t |-> t*1` on `[0, 1]` is the right endpoint, so `c := 1` is the
/// mathematically correct argmax and the hypothesis is
/// `forall t in [0,1], t*1 <= 1*1`, which is the interval hypothesis `le t
/// one` transported across `mul_one` on both sides. Nothing is assumed: the
/// witness is built and `Kernel::infer` accepts it.
///
/// The conclusion is then pinned VERBATIM against an independently built
/// `Or (le one zero) (le zero one)` -- the analytic-LLPO shape at `v := 1` --
/// rather than loosely matched, so a theorem that concluded some other
/// disjunction cannot pass.
#[test]
fn evt_attained_max_hypothesis_is_satisfiable_at_v_one_c_one() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let hc0 = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero_c, one_c, lt])
    };
    let hc1 = d.lemma(p.le_refl, &[one_c]);

    // hmax : forall t, le zero t -> le t one -> le (mul t one) (mul one one).
    // `ht1 : le t one` transported by `le_congr` across `t ~ mul t one` and
    // `one ~ mul one one` (both `mul_one`, run backwards).
    let hmax = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ht0_ty = d.const_app(p.le, &[zero_c, t]);
        let ht1_ty = d.const_app(p.le, &[t, one_c]);
        let ht1_fv = d.fresh_fvar();
        let ht1 = d.kernel().fvar(ht1_fv);

        let t_one = d.const_app(p.mul, &[t, one_c]);
        let one_one = d.const_app(p.mul, &[one_c, one_c]);
        let fwd_t = d.lemma(p.mul_one, &[t]);
        let back_t = d.lemma(p.equiv_symm, &[t_one, t, fwd_t]);
        let fwd_one = d.lemma(p.mul_one, &[one_c]);
        let back_one = d.lemma(p.equiv_symm, &[one_one, one_c, fwd_one]);
        let body = d.lemma(
            p.le_congr,
            &[t, t_one, one_c, one_one, back_t, back_one, ht1],
        );

        let with_ht1 = d.lam_fv(ht1_fv, ht1_ty, body);
        let ht0_fv = d.fresh_fvar();
        let with_ht0 = d.lam_fv(ht0_fv, ht0_ty, with_ht1);
        d.lam_fv(t_fv, carrier, with_ht0)
    };

    let instance = d.lemma(
        p.extreme_value.evt_attained_max_decides_sign,
        &[one_c, one_c, hc0, hc1, hmax],
    );
    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!(
            "evt_attained_max_decides_sign refused a DISCHARGED maximality \
             hypothesis at v = c = 1, so the row-2 statement would be \
             vacuous: {error:?}"
        )
    });

    let expected = {
        let left = d.const_app(p.le, &[one_c, zero_c]);
        let right = d.const_app(p.le, &[zero_c, one_c]);
        d.or(left, right)
    };
    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected);
    assert_eq!(
        rendered, expected_rendered,
        "an attained maximum must conclude exactly `Or (le one zero) \
         (le zero one)` -- the analytic-LLPO disjunction at v = 1 -- and \
         nothing else"
    );
}

/// The same discharge at a SECOND, structurally different `(v, c)`: `v := 0`,
/// `c := 0`. Here every value of `t |-> t*0` is the maximum, so the maximiser
/// is genuinely non-unique and the hypothesis holds at an argmax the previous
/// test's `c := 1` would not reach.
///
/// Two instances rather than one because a single one cannot distinguish "the
/// hypothesis is satisfiable" from "the hypothesis is satisfiable only at the
/// one point I happened to pick", and the whole force of the refutation is
/// that the hypothesis is the ORDINARY EVT conclusion, available wherever
/// classical EVT is.
#[test]
fn evt_attained_max_hypothesis_is_satisfiable_at_v_zero_c_zero() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let hc0 = d.lemma(p.le_refl, &[zero_c]);
    let hc1 = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero_c, one_c, lt])
    };

    // hmax : forall t, le zero t -> le t one -> le (mul t zero) (mul zero zero)
    // -- both sides are `Equiv`-zero, so `le_refl zero` transported.
    let hmax = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ht0_ty = d.const_app(p.le, &[zero_c, t]);
        let ht1_ty = d.const_app(p.le, &[t, one_c]);

        let t_zero = d.const_app(p.mul, &[t, zero_c]);
        let zero_zero = d.const_app(p.mul, &[zero_c, zero_c]);
        let fwd_t = d.lemma(p.mul_zero, &[t]);
        let back_t = d.lemma(p.equiv_symm, &[t_zero, zero_c, fwd_t]);
        let fwd_z = d.lemma(p.mul_zero, &[zero_c]);
        let back_z = d.lemma(p.equiv_symm, &[zero_zero, zero_c, fwd_z]);
        let refl = d.lemma(p.le_refl, &[zero_c]);
        let body = d.lemma(
            p.le_congr,
            &[zero_c, t_zero, zero_c, zero_zero, back_t, back_z, refl],
        );

        let ht1_fv = d.fresh_fvar();
        let with_ht1 = d.lam_fv(ht1_fv, ht1_ty, body);
        let ht0_fv = d.fresh_fvar();
        let with_ht0 = d.lam_fv(ht0_fv, ht0_ty, with_ht1);
        d.lam_fv(t_fv, carrier, with_ht0)
    };

    let instance = d.lemma(
        p.extreme_value.evt_attained_max_decides_sign,
        &[zero_c, zero_c, hc0, hc1, hmax],
    );
    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("evt_attained_max_decides_sign refused the v = c = 0 discharge: {error:?}")
    });

    let expected = {
        let left = d.const_app(p.le, &[zero_c, zero_c]);
        let right = d.const_app(p.le, &[zero_c, zero_c]);
        d.or(left, right)
    };
    assert_eq!(
        d.kernel().render_lean(ty),
        d.kernel().render_lean(expected),
        "must conclude exactly `Or (le zero zero) (le zero zero)` at v = 0"
    );
}

/// **Mandatory concrete instantiation** for `CReal.evtLinear`, and the
/// COMPUTED half of this row-2 certificate: the two endpoint values of the
/// counterexample family, read off by kernel reduction rather than asserted.
///
/// `evtLinear v := fun t => mul t v` at `v := 3`. Its value at the left
/// endpoint reduces to `0` and at the right endpoint to `3`, so the classical
/// maximum over `[0, 1]` sits at `t = 1`; at `v := -3` the same two reductions
/// give `0` and `-3`, so it sits at `t = 0`. **The maximiser jumps from one
/// endpoint to the other as the sign of `v` flips**, which is precisely why an
/// operator returning it decides that sign -- the informal content of
/// `evt_attained_max_decides_sign`, here as an exact rational computation.
///
/// Checked at `-3` as well as `3` deliberately: a construction that dropped
/// `v` entirely, or that returned `abs v`, would still give `0` and `3` on the
/// positive side alone.
#[test]
fn evt_linear_endpoint_values_reduce_and_flip_with_the_sign_of_v() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let idx0 = d.zero();

    let three_nat = d.num(3);
    let three = d.const_app(p.of_nat, &[three_nat]);
    let neg_three = d.const_app(p.neg, &[three]);

    // (label, v, expected at t = 0, expected at t = 1)
    let cases: [(&str, ExprId, ExprId, ExprId); 2] = [
        (
            "v = 3 (maximum at the RIGHT endpoint)",
            three,
            ivt_bisect_rat_lit(&mut d, p, 0, 0, false), // 0
            ivt_bisect_rat_lit(&mut d, p, 3, 0, false), // 3
        ),
        (
            "v = -3 (maximum at the LEFT endpoint)",
            neg_three,
            ivt_bisect_rat_lit(&mut d, p, 0, 0, false), // 0
            ivt_bisect_rat_lit(&mut d, p, 3, 0, true),  // -3
        ),
    ];

    for (label, v, expect_lo, expect_hi) in cases {
        let at_zero = d.const_app(p.extreme_value.evt_linear, &[v, zero_c]);
        let at_one = d.const_app(p.extreme_value.evt_linear, &[v, one_c]);
        let lo = d.const_app(p.seq, &[at_zero, idx0]);
        let hi = d.const_app(p.seq, &[at_one, idx0]);
        assert!(
            ivt_bisect_rat_eq(&mut d, p, lo, expect_lo),
            "{label}: evtLinear v zero did not reduce to the expected rational"
        );
        assert!(
            ivt_bisect_rat_eq(&mut d, p, hi, expect_hi),
            "{label}: evtLinear v one did not reduce to the expected rational"
        );
    }

    // And the comparison itself flips, which is the whole point: at v = 3 the
    // right endpoint strictly dominates the left, at v = -3 strictly the
    // reverse. Checked by reduction, not by reading the numbers above.
    let mk = |d: &mut IntDev<'_>, v: ExprId, t: ExprId| -> ExprId {
        let at = d.const_app(p.extreme_value.evt_linear, &[v, t]);
        d.const_app(p.seq, &[at, idx0])
    };
    let pos_lo = mk(&mut d, three, zero_c);
    let pos_hi = mk(&mut d, three, one_c);
    assert!(
        ivt_bisect_rat_lt(&mut d, p, pos_lo, pos_hi),
        "at v = 3 the right endpoint must strictly dominate"
    );
    let neg_lo = mk(&mut d, neg_three, zero_c);
    let neg_hi = mk(&mut d, neg_three, one_c);
    assert!(
        ivt_bisect_rat_lt(&mut d, p, neg_hi, neg_lo),
        "at v = -3 the LEFT endpoint must strictly dominate -- the maximiser \
         moved, which is the sign decision an argmax operator would be making"
    );
}

/// **Mandatory concrete instantiation** for `CReal.sumRange_reblock`
/// (`creal/integral.rs`): `g i := CReal.ofNat i`, checked at TWO different
/// block sizes over the SAME six terms `g 0, …, g 5` (`0+1+2+3+4+5 = 15`).
///
/// - `k = 3`, block size `n+1 = 2` (three pairs): `(0+1)+(2+3)+(4+5)`.
/// - `k = 2`, block size `n+1 = 3` (two triples, the NON-SQUARE case):
///   `(0+1+2)+(3+4+5)`. `k = n+1` in the first case cannot distinguish a
///   transposed pair of indices (`i·(n+1)+j` vs. `j·k+i`); this second case
///   can, because `3 ≠ 2` makes the two block shapes genuinely different
///   partitions of the same six terms.
///
/// Each instance is checked two ways: (1) the theorem's OWN instantiated
/// type, via `Kernel::infer`, must render identically to an INDEPENDENTLY
/// reconstructed expected type (catching an argument-position defect that a
/// mere "does it type-check" pass would not: a transposed `mul` argument
/// order is often still well-typed, just wrong); (2) both the original sum
/// and the reblocked sum must reduce, by `Eq.refl` alone (genuine
/// computation, not merely type-checking), to the SAME numeral, `15`.
#[test]
fn sum_range_reblock_regroups_zero_through_five_two_ways() {
    use crate::expr::ExprId;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rrefl};

    /// Reconstruction of `creal/integral.rs`'s private `reblock_block`,
    /// verbatim (that function is not visible from this sibling module):
    /// `fun i => sumRange (fun j => g (Nat.add (Nat.mul bs i) j)) bs`.
    fn expected_block(d: &mut IntDev<'_>, p: CRealPrelude, g: ExprId, bs: ExprId) -> ExprId {
        let nat = d.nat_ty();
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let offset = NatOps::mul(d, bs, i);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let nat_add = d.prelude().add;
        let offset_j = d.const_app(nat_add, &[offset, j]);
        let gj = d.apply(g, &[offset_j]);
        let inner = d.lam_fv(j_fv, nat, gj);
        let body = d.const_app(p.sum_range, &[inner, bs]);
        d.lam_fv(i_fv, nat, body)
    }

    /// Apply `sumRange_reblock` at `n_lit`/`k_lit`, check its instantiated
    /// type renders identically to the independently-reconstructed expected
    /// type, then check both the original and reblocked sums compute (by
    /// `Eq.refl`) to `fifteen_seq` at `index`.
    #[allow(clippy::too_many_arguments)]
    fn check_instance(
        d: &mut IntDev<'_>,
        p: CRealPrelude,
        g: ExprId,
        index: ExprId,
        fifteen_seq: ExprId,
        n_lit: u32,
        k_lit: u32,
        label: &str,
    ) {
        let n_val = d.num(n_lit);
        let k_val = d.num(k_lit);
        let bs = d.succ(n_val);

        let reblock = d.kernel().const_(p.sum_range_reblock, vec![]);
        let inst = d.apply(reblock, &[g, n_val, k_val]);
        let ty = d.kernel().infer(inst).unwrap_or_else(|error| {
            panic!("sumRange_reblock at n={n_lit} k={k_lit} ({label}) refused: {error:?}")
        });

        let total = NatOps::mul(d, bs, k_val);
        let lhs_ty = d.const_app(p.sum_range, &[g, total]);
        let block = expected_block(d, p, g, bs);
        let rhs_ty = d.const_app(p.sum_range, &[block, k_val]);
        let expected_ty = super::equiv(d, p, lhs_ty, rhs_ty);

        let rendered = d.kernel().render_lean(ty);
        let expected_rendered = d.kernel().render_lean(expected_ty);
        assert_eq!(
            rendered, expected_rendered,
            "sumRange_reblock at n={n_lit} k={k_lit} ({label}): instantiated type must \
             match the independently-reconstructed `i*(n+1)+j` block formula exactly \
             -- a transposed index argument is often still well-typed, just wrong"
        );

        let lhs_seq = d.const_app(p.seq, &[lhs_ty, index]);
        let rhs_seq = d.const_app(p.seq, &[rhs_ty, index]);

        let anon = d.kernel().anon();

        let stmt_lhs = req(d, lhs_seq, fifteen_seq);
        let proof_lhs = rrefl(d, lhs_seq);
        let name_lhs = d.kernel().name_str(anon, format!("__reblock_lhs_{label}"));
        d.kernel()
            .add_declaration(Declaration::Theorem {
                name: name_lhs,
                uparams: vec![],
                ty: stmt_lhs,
                value: proof_lhs,
            })
            .unwrap_or_else(|error| {
                panic!("sumRange g (mul bs k) ({label}) did NOT compute to 15: {error:?}")
            });

        let stmt_rhs = req(d, rhs_seq, fifteen_seq);
        let proof_rhs = rrefl(d, rhs_seq);
        let name_rhs = d.kernel().name_str(anon, format!("__reblock_rhs_{label}"));
        d.kernel()
            .add_declaration(Declaration::Theorem {
                name: name_rhs,
                uparams: vec![],
                ty: stmt_rhs,
                value: proof_rhs,
            })
            .unwrap_or_else(|error| {
                panic!("sumRange (reblocked) k ({label}) did NOT compute to 15: {error:?}")
            });
    }

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();

    // g := fun i : Nat => CReal.ofNat i.
    let g = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = d.const_app(p.of_nat, &[i]);
        d.lam_fv(i_fv, nat, body)
    };

    let index = d.num(0); // arbitrary: `ofNat`-built sums carry no error term.
    let fifteen = {
        let fifteen_nat = d.num(15);
        d.const_app(p.of_nat, &[fifteen_nat])
    };
    let fifteen_seq = d.const_app(p.seq, &[fifteen, index]);

    // k = 3, block size n+1 = 2: three pairs, (0+1)+(2+3)+(4+5).
    check_instance(&mut d, p, g, index, fifteen_seq, 1, 3, "k3_blocksize2");
    // k = 2, block size n+1 = 3 (non-square): two triples, (0+1+2)+(3+4+5).
    check_instance(&mut d, p, g, index, fifteen_seq, 2, 2, "k2_blocksize3");
}

/// **Mandatory concrete instantiation** for `CReal.constant_of_zero_deriv`:
/// the constant function `fun _ => one` on `[0, 1]`, whose derivative is the
/// constant `zero` everywhere (`hasDerivative_const`), applied at `x :=
/// zero`, `y := one`. `x` and `y` are distinct so a transposed-endpoint
/// defect (both statements hold trivially by reflexivity at `x = y`) cannot
/// hide; the expected conclusion is pinned by `render_lean` comparison
/// against `Equiv (F zero) (F one)` built the SAME way, not just any
/// `CReal.Equiv` statement.
#[test]
fn constant_of_zero_deriv_applies_to_a_constant_on_0_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    // const_one_fn := fun _ => one; const_zero_fn := fun _ => zero.
    let const_one_fn = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, one_c)
    };
    let const_zero_fn = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, zero_c)
    };

    let hf = d.lemma(p.has_derivative_const, &[one_c, zero_c, one_c]);

    // hderiv : ∀ z, le zero z -> le z one -> Equiv (const_zero_fn z) zero,
    // i.e. Equiv zero zero regardless of z (const_zero_fn z beta-reduces to
    // zero) -- `equiv_refl` alone.
    let hderiv = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_ty = d.const_app(p.le, &[zero_c, z]);
        let hzb_ty = d.const_app(p.le, &[z, one_c]);
        let haz_fv = d.fresh_fvar();
        let hzb_fv = d.fresh_fvar();
        let refl = d.lemma(p.equiv_refl, &[zero_c]);
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, refl);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };

    let le_zero_one = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero_c, one_c, lt])
    };
    let hax = d.lemma(p.le_refl, &[zero_c]);
    let hxy = le_zero_one;
    let hyb = d.lemma(p.le_refl, &[one_c]);

    let instance = d.lemma(
        p.constant_of_zero_deriv,
        &[
            const_one_fn,
            const_zero_fn,
            zero_c,
            one_c,
            hf,
            hderiv,
            zero_c,
            one_c,
            hax,
            hxy,
            hyb,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("constant_of_zero_deriv refused at the constant function on [0,1]: {error:?}")
    });

    let expected_fx = d.apply(const_one_fn, &[zero_c]);
    let expected_fy = d.apply(const_one_fn, &[one_c]);
    let expected_ty = d.const_app(p.equiv, &[expected_fx, expected_fy]);
    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected_ty);
    assert_eq!(
        rendered, expected_rendered,
        "must conclude exactly `Equiv (F zero) (F one)` (F is the constant one), not some other CReal.Equiv statement"
    );
    assert!(
        rendered.contains("CReal.zero") && rendered.contains("CReal.one"),
        "the endpoints must be zero and one, not some other pair: {rendered}"
    );
}

/// **Mandatory concrete instantiation** for `CReal.antitone_of_nonpos_deriv`:
/// `F := fun r => neg r` on `[0, 1]`, whose derivative is the constant `neg
/// one` everywhere (`hasDerivative_neg` applied to `hasDerivative_id`),
/// applied at `x := zero`, `y := one`. Distinct `x`/`y` again rules out the
/// trivial-by-reflexivity degenerate case; the expected conclusion is
/// pinned to `le (F one) (F zero)` (note the endpoints are ALREADY reversed
/// in the conclusion -- this is the antitone direction, not `monotone`'s).
#[test]
fn antitone_of_nonpos_deriv_applies_to_negated_identity_on_0_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    // identity := fun r => r; const_one := fun _ => one (F' before negation).
    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let const_one = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, one_c)
    };

    let hf_id = d.lemma(p.has_derivative_id, &[zero_c, one_c]);
    // hf : HasDerivativeOn (fun r => neg r) (fun r => neg one) zero one.
    let hf = d.lemma(
        p.has_derivative_neg,
        &[identity, const_one, zero_c, one_c, hf_id],
    );

    let neg_r = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let nr = d.const_app(p.neg, &[r]);
        d.lam_fv(r_fv, carrier, nr)
    };
    let neg_one = {
        let r_fv = d.fresh_fvar();
        let no = d.const_app(p.neg, &[one_c]);
        d.lam_fv(r_fv, carrier, no)
    };

    // le (neg one) zero, from `zero_lt_one`/`le_of_lt` and `neg_le_neg`
    // against `neg_zero_equiv` (built inline, matching the theorem's own
    // route): le zero one -> le (neg one) (neg zero) -> le (neg one) zero.
    let le_neg_one_zero = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        let le_zero_one = d.lemma(p.le_of_lt, &[zero_c, one_c, lt]);
        let flipped = d.lemma(p.neg_le_neg, &[zero_c, one_c, le_zero_one]);
        // flipped : le (neg one) (neg zero)
        let neg_zero = d.const_app(p.neg, &[zero_c]);
        let neg_one_c = d.const_app(p.neg, &[one_c]);
        let nz_symm = {
            let hn = d.lemma(p.add_zero, &[neg_zero]);
            let padded = d.const_app(p.add, &[neg_zero, zero_c]);
            let comm = d.lemma(p.add_comm, &[neg_zero, zero_c]);
            let flip = d.const_app(p.add, &[zero_c, neg_zero]);
            let an = d.lemma(p.add_neg, &[zero_c]);
            let s1 = d.lemma(p.equiv_symm, &[padded, neg_zero, hn]);
            let s2 = d.lemma(p.equiv_trans, &[neg_zero, padded, flip, s1, comm]);
            d.lemma(p.equiv_trans, &[neg_zero, flip, zero_c, s2, an])
        };
        let refl_neg_one = d.lemma(p.equiv_refl, &[neg_one_c]);
        d.lemma(
            p.le_congr,
            &[
                neg_one_c,
                neg_one_c,
                neg_zero,
                zero_c,
                refl_neg_one,
                nz_symm,
                flipped,
            ],
        )
    };

    // hderiv : ∀ z, le zero z -> le z one -> le (neg_one z) zero, i.e.
    // le (neg one) zero regardless of z.
    let hderiv = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_ty = d.const_app(p.le, &[zero_c, z]);
        let hzb_ty = d.const_app(p.le, &[z, one_c]);
        let haz_fv = d.fresh_fvar();
        let hzb_fv = d.fresh_fvar();
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, le_neg_one_zero);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };

    let le_zero_one = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero_c, one_c, lt])
    };
    let hax = d.lemma(p.le_refl, &[zero_c]);
    let hxy = le_zero_one;
    let hyb = d.lemma(p.le_refl, &[one_c]);

    let instance = d.lemma(
        p.antitone_of_nonpos_deriv,
        &[
            neg_r, neg_one, zero_c, one_c, hf, hderiv, zero_c, one_c, hax, hxy, hyb,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("antitone_of_nonpos_deriv refused at negated identity on [0,1]: {error:?}")
    });

    let expected_fy = d.apply(neg_r, &[zero_c]);
    let expected_fx = d.apply(neg_r, &[one_c]);
    let expected_ty = d.const_app(p.le, &[expected_fx, expected_fy]);
    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected_ty);
    assert_eq!(
        rendered, expected_rendered,
        "must conclude exactly `le (F one) (F zero)` (F is negated identity), not some other CReal.le statement"
    );
    assert!(
        rendered.contains("CReal.zero") && rendered.contains("CReal.one"),
        "the endpoints must be zero and one, not some other pair: {rendered}"
    );
}

/// **Mandatory concrete instantiation** for `CReal.strict_antitone_of_neg_deriv`:
/// `F := fun r => neg r` on `[0, 1]`, whose derivative is the constant `neg
/// one` everywhere (`hasDerivative_neg` applied to `hasDerivative_id`),
/// uniformly bounded above by `neg (embed (natDivSucc 1 0))` -- i.e. `neg
/// one` itself, via `ratUnitEqOne` bridging `natDivSucc 1 0` to `Rat.one`
/// exactly as `strict_mono_of_pos_deriv_applies_to_the_identity_on_0_1`
/// does -- applied at `x := zero`, `y := one` with the STRICT input gap
/// `CReal.zero_lt_one`. Distinct `x`/`y` rules out the trivial-by-reflexivity
/// degenerate case; the expected conclusion is pinned to exactly
/// `lt (F one) (F zero)`, i.e. `lt (neg one) (neg zero)` -- genuinely
/// reversed, and strict, not merely `le`.
#[test]
fn strict_antitone_of_neg_deriv_applies_to_negated_identity_on_0_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::rat_eq_rewrite;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_nat = d.num(0);
    let one_nat = d.num(1);

    // identity := fun r => r; const_one := fun _ => one (F' before negation).
    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let const_one = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, one_c)
    };

    let hf_id = d.lemma(p.has_derivative_id, &[zero_c, one_c]);
    // hf : HasDerivativeOn (fun r => neg r) (fun r => neg one) zero one.
    let hf = d.lemma(
        p.has_derivative_neg,
        &[identity, const_one, zero_c, one_c, hf_id],
    );

    let neg_r = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let nr = d.const_app(p.neg, &[r]);
        d.lam_fv(r_fv, carrier, nr)
    };
    let neg_one = {
        let r_fv = d.fresh_fvar();
        let no = d.const_app(p.neg, &[one_c]);
        d.lam_fv(r_fv, carrier, no)
    };

    // le (embed (natDivSucc 1 0)) one_c, via `CReal.ratUnitEqOne` bridging
    // `natDivSucc 1 0` to `Rat.one` (same technique
    // `strict_mono_of_pos_deriv_applies_to_the_identity_on_0_1` uses).
    let unit_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
    let unit_embed = d.const_app(p.of_rat, &[unit_rat]);
    let embed_le_one = {
        let one_rat = d.kernel().const_(p.rat.one, vec![]);
        let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
        let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
        let bridge = rat_eq_rewrite(
            &mut d,
            unit_rat,
            one_rat,
            unit_eq_one,
            refl_start,
            &|d, t| {
                let embedded = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[unit_embed, embedded])
            },
        );
        // bridge : Equiv unit_embed (ofRat one_rat), defeq Equiv unit_embed one_c.
        d.lemma(p.le_of_equiv, &[unit_embed, one_c, bridge])
    };

    // le (neg one) (neg (embed (natDivSucc 1 0))), from `embed_le_one` via
    // `neg_le_neg` directly -- no `double_neg` needed since `neg_le_neg`
    // already lands on `neg (neg a_0)`'s mirror, `neg one`, on the nose.
    let neg_one_le_neg_a0 = d.lemma(p.neg_le_neg, &[unit_embed, one_c, embed_le_one]);

    // hderiv : ∀ z, le zero z -> le z one -> le (neg_one z) (neg (embed (natDivSucc 1 0))).
    let hderiv = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_ty = d.const_app(p.le, &[zero_c, z]);
        let hzb_ty = d.const_app(p.le, &[z, one_c]);
        let haz_fv = d.fresh_fvar();
        let hzb_fv = d.fresh_fvar();
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, neg_one_le_neg_a0);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };

    let hax = d.lemma(p.le_refl, &[zero_c]);
    let hxy = d.lemma(p.zero_lt_one, &[]);
    let hyb = d.lemma(p.le_refl, &[one_c]);

    let instance = d.lemma(
        p.strict_antitone_of_neg_deriv,
        &[
            neg_r, neg_one, zero_c, one_c, hf, zero_nat, hderiv, zero_c, one_c, hax, hxy, hyb,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("strict_antitone_of_neg_deriv refused at negated identity on [0,1]: {error:?}")
    });

    let expected_fy = d.apply(neg_r, &[one_c]);
    let expected_fx = d.apply(neg_r, &[zero_c]);
    let expected_ty = d.const_app(p.lt, &[expected_fy, expected_fx]);
    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected_ty);
    assert_eq!(
        rendered, expected_rendered,
        "must conclude exactly `lt (F one) (F zero)` (F is negated identity), not `le`, and not some other CReal.lt statement"
    );
    assert!(
        rendered.contains("CReal.zero") && rendered.contains("CReal.one"),
        "the endpoints must be zero and one, not some other pair: {rendered}"
    );
}

/// **Mandatory concrete instantiation** for `CReal.strict_mono_comp`:
/// `F := G := fun r => r` (the identity), both strictly increasing on
/// `[0, 1]` by the trivial witness `fun x y _ hxy _ => hxy` (since
/// `identity x = x` beta-reduces, the conclusion `lt (F x) (F y)` literally
/// IS the hypothesis `lt x y`), and the identity trivially maps `[0, 1]`
/// into itself (`hrange_lo := fun z haz _ => haz`, `hrange_hi := fun z _ hzb
/// => hzb`). Applied at `x := zero`, `y := one` with the STRICT input gap
/// `CReal.zero_lt_one`; distinct `x`/`y` rules out the degenerate case. The
/// expected conclusion, after both identities beta-reduce away, is exactly
/// `lt zero one`.
#[test]
fn strict_mono_comp_applies_to_the_identity_composed_with_itself_on_0_1() {
    use crate::expr::ExprId;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    // A strict-monotonicity witness for the identity on [lo, hi]: the
    // conclusion `lt (identity x) (identity y)` is beta-defeq to `lt x y`,
    // so the body is just the middle hypothesis itself.
    let id_strict_mono = |d: &mut IntDev<'_>, lo: ExprId, hi: ExprId| {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_ty = d.const_app(p.le, &[lo, x]);
        let hax_fv = d.fresh_fvar();
        let hxy_ty = d.const_app(p.lt, &[x, y]);
        let hxy_fv = d.fresh_fvar();
        let hxy = d.kernel().fvar(hxy_fv);
        let hyb_ty = d.const_app(p.le, &[y, hi]);
        let hyb_fv = d.fresh_fvar();
        let with_hyb = d.lam_fv(hyb_fv, hyb_ty, hxy);
        let with_hxy = d.lam_fv(hxy_fv, hxy_ty, with_hyb);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxy);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let hf = id_strict_mono(&mut d, zero_c, one_c);
    let hg = id_strict_mono(&mut d, zero_c, one_c);

    // The identity trivially maps [0, 1] into [0, 1].
    let hrange_lo = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_ty = d.const_app(p.le, &[zero_c, z]);
        let haz_fv = d.fresh_fvar();
        let haz = d.kernel().fvar(haz_fv);
        let hzb_ty = d.const_app(p.le, &[z, one_c]);
        let hzb_fv = d.fresh_fvar();
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, haz);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };
    let hrange_hi = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let haz_ty = d.const_app(p.le, &[zero_c, z]);
        let haz_fv = d.fresh_fvar();
        let hzb_ty = d.const_app(p.le, &[z, one_c]);
        let hzb_fv = d.fresh_fvar();
        let hzb = d.kernel().fvar(hzb_fv);
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, hzb);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };

    let hax = d.lemma(p.le_refl, &[zero_c]);
    let hxy = d.lemma(p.zero_lt_one, &[]);
    let hyb = d.lemma(p.le_refl, &[one_c]);

    let instance = d.lemma(
        p.strict_mono_comp,
        &[
            identity, identity, zero_c, one_c, zero_c, one_c, hf, hg, hrange_lo, hrange_hi, zero_c,
            one_c, hax, hxy, hyb,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("strict_mono_comp refused at identity-composed-with-itself on [0,1]: {error:?}")
    });

    // The conclusion is `lt (G (F zero)) (G (F one))`, un-reduced (`render_lean`
    // does not beta-reduce): with `F := G := identity` that is
    // `lt (identity (identity zero)) (identity (identity one))`, defeq to
    // (but not syntactically) `lt zero one`.
    let inner_zero = d.apply(identity, &[zero_c]);
    let expected_gfzero = d.apply(identity, &[inner_zero]);
    let inner_one = d.apply(identity, &[one_c]);
    let expected_gfone = d.apply(identity, &[inner_one]);
    let expected_ty = d.const_app(p.lt, &[expected_gfzero, expected_gfone]);
    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected_ty);
    assert_eq!(
        rendered, expected_rendered,
        "must conclude exactly `lt (identity (identity zero)) (identity (identity one))`"
    );

    // And separately confirm it really is defeq to the reduced statement
    // `lt zero one`, so the theorem did not smuggle in some other pair.
    let reduced_ty = d.const_app(p.lt, &[zero_c, one_c]);
    assert!(
        d.kernel().def_eq(ty, reduced_ty),
        "the conclusion must be defeq to `lt zero one`, got {rendered}"
    );
}

/// **Mandatory concrete instantiation** for `CReal.hasDerivative_unique`:
/// `F := fun r => r` (the identity, `hasDerivative_id`) on `[0, 1]`, with
/// BOTH candidate derivatives the constant `one` -- the same witness
/// `hasDerivative_id` supplies twice, matching the task's own instruction
/// ("both derivatives const one"). `a := zero`, `b := one` so `lt a b` is
/// genuinely DISCHARGED via `CReal.zero_lt_one`, not assumed at a
/// degenerate interval (`a = b`) the way the refuted naive statement would
/// need -- that refutation is exactly why this theorem carries `lt a b` at
/// all. `z := zero` (the left endpoint; `hasDerivative_unique` holds at any
/// `z` with `le a z` and `le z b`, endpoints included).
#[test]
fn has_derivative_unique_applies_to_the_identity_on_0_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let one_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, one_c)
    };

    let hf1 = d.lemma(p.has_derivative_id, &[zero_c, one_c]);
    let hf2 = d.lemma(p.has_derivative_id, &[zero_c, one_c]);
    let hab = d.lemma(p.zero_lt_one, &[]);

    let haz = d.lemma(p.le_refl, &[zero_c]);
    let hzb = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero_c, one_c, lt])
    };

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let instance = d.lemma(
        p.deriv_unique.has_derivative_unique,
        &[
            identity, one_fn, one_fn, zero_c, one_c, hf1, hf2, hab, zero_c, haz, hzb,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("hasDerivative_unique refused at the identity on [0,1]: {error:?}")
    });

    let expected_f1z = d.apply(one_fn, &[zero_c]);
    let expected_f2z = d.apply(one_fn, &[zero_c]);
    let expected_ty = d.const_app(p.equiv, &[expected_f1z, expected_f2z]);
    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected_ty);
    assert_eq!(
        rendered, expected_rendered,
        "must conclude exactly `Equiv (F1 zero) (F2 zero)` (both const one), not some other CReal.Equiv statement"
    );
    assert!(
        rendered.contains("CReal.one"),
        "both candidate derivatives are the constant one: {rendered}"
    );
}

/// **Mandatory concrete instantiation** for
/// `CReal.hasDerivative_integral_const`: `c := zero`, `a := zero`, `b :=
/// one`, `k := 0` — the zero function's antiderivative on `[0, 1]` has
/// derivative `zero`. Chosen over a nonzero `c` so the archimedean-style
/// magnitude hypothesis `le (abs c) (ofRat (natDivSucc 1 0))` discharges
/// from base group laws alone (`abs zero = max zero (neg zero)`, `neg zero ~
/// zero` via `add_zero`/`add_comm`/`add_neg`), with no `archimedean`/`bound`
/// plumbing needed. Confirms the kernel accepts the application and that the
/// concluded type is EXACTLY `HasDerivativeOn G (fun _ => zero) zero one`
/// for the expected clamp-based `G` (built the same way the declaration
/// itself builds it), not merely some `HasDerivativeOn` statement — and,
/// as a negative control, that the same instance is NOT defeq to the WRONG
/// derivative claim `HasDerivativeOn G (fun _ => one) zero one` (guards
/// against a vacuous `hasDerivative_congr` application that would accept any
/// target).
#[test]
fn has_derivative_integral_const_applies_to_the_zero_function_on_0_1() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let k_c = d.num(0);
    let zero_idx = d.num(0);

    // hbound : le (abs zero) (ofRat (natDivSucc (Nat.succ 0) 0))
    let succ_k = d.succ(k_c);
    let bound_rat = d.const_app(p.rat.nat_div_succ, &[succ_k, zero_idx]);
    let bound_real = d.const_app(p.of_rat, &[bound_rat]);

    let rat_nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[succ_k, zero_idx]);
    let rzero_expr = crate::rat_prelude::ops::rzero(&mut d, p.rat);
    let bound_nonneg = d.lemma(p.of_rat_le, &[rzero_expr, bound_rat, rat_nonneg]);
    // bound_nonneg : le (ofRat rzero_expr) bound_real -- defeq `le zero_c
    // bound_real` since `CReal.zero` is *defined* as `ofRat Rat.zero`.

    let neg_zero_c = d.const_app(p.neg, &[zero_c]);
    let padded = d.const_app(p.add, &[neg_zero_c, zero_c]);
    let flipped = d.const_app(p.add, &[zero_c, neg_zero_c]);
    let add_zero_negzero = d.lemma(p.add_zero, &[neg_zero_c]); // padded ~ neg_zero_c
    let s1 = d.lemma(p.equiv_symm, &[padded, neg_zero_c, add_zero_negzero]); // neg_zero_c ~ padded
    let comm = d.lemma(p.add_comm, &[neg_zero_c, zero_c]); // padded ~ flipped
    let s2 = d.lemma(p.equiv_trans, &[neg_zero_c, padded, flipped, s1, comm]); // neg_zero_c ~ flipped
    let cancel = d.lemma(p.add_neg, &[zero_c]); // flipped ~ zero_c
    let nz_eq = d.lemma(p.equiv_trans, &[neg_zero_c, flipped, zero_c, s2, cancel]); // neg_zero_c ~ zero_c
    let neg_zero_le_zero = d.lemma(p.le_of_equiv, &[neg_zero_c, zero_c, nz_eq]);
    let neg_zero_le_bound = d.lemma(
        p.le_trans,
        &[
            neg_zero_c,
            zero_c,
            bound_real,
            neg_zero_le_zero,
            bound_nonneg,
        ],
    );

    let hbound = d.lemma(
        p.abs_le,
        &[zero_c, bound_real, bound_nonneg, neg_zero_le_bound],
    );

    let instance = d.lemma(
        p.has_derivative_integral_const,
        &[zero_c, zero_c, one_c, k_c, hbound],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("hasDerivative_integral_const refused at c=a=zero, b=one, k=0: {error:?}")
    });

    // Expected conclusion, built the SAME way the declaration itself builds
    // its `G`: `HasDerivativeOn G (fun _ => zero) zero one`.
    let const_zero_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, zero_c)
    };
    let g_fn = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let mn = d.const_app(p.min, &[x, one_c]);
        let clamp_x = d.const_app(p.max, &[zero_c, mn]);
        let hacx = d.lemma(p.le_max_left, &[zero_c, mn]);
        let const_zero_inner = {
            let ignore_fv2 = d.fresh_fvar();
            d.lam_fv(ignore_fv2, carrier, zero_c)
        };
        let ucx = d.const_app(p.uniformly_continuous_const, &[zero_c, zero_c, clamp_x]);
        let integral_val = d.const_app(p.integral, &[const_zero_inner, zero_c, clamp_x, hacx, ucx]);
        d.lam_fv(x_fv, carrier, integral_val)
    };
    let expected_ty = d.const_app(p.has_derivative_on, &[g_fn, const_zero_fn, zero_c, one_c]);

    let rendered = d.kernel().render_lean(ty);
    let expected_rendered = d.kernel().render_lean(expected_ty);
    assert_eq!(
        rendered, expected_rendered,
        "must conclude exactly `HasDerivativeOn G (fun _=>zero) zero one` for the clamp-based G"
    );
    assert!(
        rendered.contains("CReal.integral"),
        "the antiderivative must be stated via `CReal.integral`: {rendered}"
    );

    // Negative control: NOT defeq to the WRONG derivative claim.
    let const_one_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, one_c)
    };
    let wrong_ty = d.const_app(p.has_derivative_on, &[g_fn, const_one_fn, zero_c, one_c]);
    assert!(
        !d.kernel().def_eq(ty, wrong_ty),
        "must NOT be defeq to `HasDerivativeOn G (fun _=>one) zero one` (wrong derivative)"
    );
}

/// **Mandatory concrete instantiation for `CReal.pow_half_le_natDivSucc`.**
/// At `n = 3`: `(1/2)³ = 1/8 ≤ 1/4 = natDivSucc 1 3`, checked against the
/// literal statement (not merely SOME `le` proposition). `n = 0` and `n = 1`
/// hold with equality (`1 ≤ 1`, `1/2 ≤ 1/2`) and cannot detect a
/// wrong-direction bound, which is why this checks `n = 3` specifically.
#[test]
fn pow_half_le_nat_div_succ_at_three_bounds_one_eighth_by_one_quarter() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let three_nat = d.num(3);
    let one_nat = d.num(1);

    let value = d.const_app(p.pow_half_le_nat_div_succ, &[three_nat]);

    let half = super::div_succ(&mut d, p, 1, one_nat);
    let half_creal = super::embed(&mut d, p, half);
    let pow_half_3 = d.const_app(p.pow, &[half_creal, three_nat]);
    let nat_div_1_3 = super::div_succ(&mut d, p, 1, three_nat);
    let bound = super::embed(&mut d, p, nat_div_1_3);
    let ty = d.const_app(p.le, &[pow_half_3, bound]);

    let anon = kernel.anon();
    let name = kernel.name_str(
        anon,
        "__pow_half_le_nat_div_succ_at_three_bounds_one_eighth_by_one_quarter",
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.pow_half_le_natDivSucc 3 did NOT check against \
                 le (pow (ofRat (natDivSucc 1 1)) 3) (ofRat (natDivSucc 1 3)) \
                 (not merely SOME le statement): {error:?}"
            )
        });
}

/// The mandatory non-tight concrete instantiation for the newly-public
/// `CReal.abs_add_le`: `a := one`, `b := neg one`. `abs (1 + (-1)) = abs 0 =
/// 0`, `abs 1 + abs(-1) = 1 + 1 = 2`, so the bound has slack (`0 ≤ 2`), not
/// zero on both sides -- this is deliberately NOT `a = b = 0`, which would
/// hide a factor error (the module doc for `abs_add_le_at_one_and_one_is_tight`
/// below is the tight companion). The expected conclusion is reconstructed
/// independently of `CReal.abs_add_le`'s own proof term, so a swapped
/// `add`/`abs` argument or a wrong-orientation `le` would fail this even if
/// the general theorem's own type happened to still check.
#[test]
fn abs_add_le_at_one_and_neg_one_has_slack() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_one = d.const_app(p.neg, &[one]);

    let value = d.lemma(p.abs_add_le, &[one, neg_one]);

    // Independently reconstruct: le (abs (add one neg_one)) (add (abs one) (abs neg_one)).
    let sum = d.const_app(p.add, &[one, neg_one]);
    let abs_sum = d.const_app(p.abs, &[sum]);
    let abs_one = d.const_app(p.abs, &[one]);
    let abs_neg_one = d.const_app(p.abs, &[neg_one]);
    let bound = d.const_app(p.add, &[abs_one, abs_neg_one]);
    let ty = d.const_app(p.le, &[abs_sum, bound]);

    let anon = kernel.anon();
    let name = kernel.name_str(anon, "__abs_add_le_at_one_neg_one");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.abs_add_le at (1, -1) did NOT check against \
                 le (abs (add 1 (neg 1))) (add (abs 1) (abs (neg 1))) \
                 -- i.e. le (abs 0) 2: {error:?}"
            )
        });
}

/// The mandatory TIGHT concrete instantiation for `CReal.abs_add_le`: `a :=
/// one`, `b := one`. `abs (1 + 1) = 2`, `abs 1 + abs 1 = 2`, so the bound is
/// met with equality (`2 ≤ 2`) -- a bound that is never exercised at
/// equality can hide a factor error the slack case above would not catch.
#[test]
fn abs_add_le_at_one_and_one_is_tight() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let one = d.kernel().const_(p.one, vec![]);

    let value = d.lemma(p.abs_add_le, &[one, one]);

    // Independently reconstruct: le (abs (add one one)) (add (abs one) (abs one)).
    let sum = d.const_app(p.add, &[one, one]);
    let abs_sum = d.const_app(p.abs, &[sum]);
    let abs_one = d.const_app(p.abs, &[one]);
    let bound = d.const_app(p.add, &[abs_one, abs_one]);
    let ty = d.const_app(p.le, &[abs_sum, bound]);

    let anon = kernel.anon();
    let name = kernel.name_str(anon, "__abs_add_le_at_one_one_tight");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.abs_add_le at (1, 1) did NOT check against \
                 le (abs (add 1 1)) (add (abs 1) (abs 1)) -- i.e. le (abs 2) 2: {error:?}"
            )
        });
}

/// The mandatory wiring-check instantiation for
/// `CReal.converges_comp_eventually`: `F := fun r => r` on `[0, 1]`, `f :=
/// fun _ => zero`, `L := zero` (`CReal.converges_of_const`) -- `F` is the
/// identity, so the conclusion collapses to (a weakened form of) the
/// hypothesis, and this only checks the theorem's own plumbing (the
/// `UniformlyContinuousOn.spec` application, the `exists_intro`/`exists_elim`
/// shapes) rather than any genuine rational estimate.
#[test]
fn converges_comp_eventually_applies_at_the_identity_and_a_constant_sequence() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();
    let carrier = d.kernel().const_(p.creal, vec![]);

    let identity_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let u = d.lemma(p.uniformly_continuous_id, &[zero_c, one_c]);

    // f := fun _ => zero (the constant sequence).
    let f = {
        let n_fv = d.fresh_fvar();
        let _n = d.kernel().fvar(n_fv);
        d.lam_fv(n_fv, nat, zero_c)
    };
    let l = zero_c;

    // h_lo : forall n, le zero (f n) -- reduces to le zero zero, le_refl.
    let h_lo = {
        let n_fv = d.fresh_fvar();
        let _n = d.kernel().fvar(n_fv);
        let body = d.lemma(p.le_refl, &[zero_c]);
        d.lam_fv(n_fv, nat, body)
    };
    // h_hi : forall n, le (f n) one -- reduces to le zero one, le_of_lt zero_lt_one.
    let h_hi = {
        let n_fv = d.fresh_fvar();
        let _n = d.kernel().fvar(n_fv);
        let lt01 = d.const_app(p.zero_lt_one, &[]);
        let body = d.lemma(p.le_of_lt, &[zero_c, one_c, lt01]);
        d.lam_fv(n_fv, nat, body)
    };
    let hconv = d.lemma(p.converges_of_const, &[zero_c]);
    let e = d.num(3);

    let instance = d.lemma(
        p.converges_comp_eventually,
        &[identity_fn, zero_c, one_c, u, f, l, h_lo, h_hi, hconv, e],
    );

    let inferred = d.kernel().infer(instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!("converges_comp_eventually refused at F := id, f := L := zero, e := 3: {error:?}")
    });
    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Exists"),
        "the instantiated conclusion is not an existential: {rendered}"
    );
}

/// The mandatory MOVING-limit instantiation: `F := fun r => add r one`
/// (`x + 1`, via `uniformly_continuous_add` composing `uniformly_continuous_id`
/// and `uniformly_continuous_const`), same `f := L := zero`. `F L = one ≠
/// zero = L`, so this exercises the theorem where the conclusion's target
/// (`F L`) genuinely differs from the hypothesis' own limit `L` -- unlike the
/// identity instantiation above, `F L` and `L` transposed would be a
/// DIFFERENT (and wrong) claim.
#[test]
fn converges_comp_eventually_applies_at_x_plus_one_where_the_limit_moves() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();
    let carrier = d.kernel().const_(p.creal, vec![]);

    let identity_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let const_one_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, one_c)
    };
    let f_big = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let added = d.const_app(p.add, &[r, one_c]);
        d.lam_fv(r_fv, carrier, added)
    };

    let u_id = d.lemma(p.uniformly_continuous_id, &[zero_c, one_c]);
    let u_const = d.lemma(p.uniformly_continuous_const, &[one_c, zero_c, one_c]);
    let u = d.lemma(
        p.uniformly_continuous_add,
        &[identity_fn, const_one_fn, zero_c, one_c, u_id, u_const],
    );

    let f = {
        let n_fv = d.fresh_fvar();
        let _n = d.kernel().fvar(n_fv);
        d.lam_fv(n_fv, nat, zero_c)
    };
    let l = zero_c;

    let h_lo = {
        let n_fv = d.fresh_fvar();
        let _n = d.kernel().fvar(n_fv);
        let body = d.lemma(p.le_refl, &[zero_c]);
        d.lam_fv(n_fv, nat, body)
    };
    let h_hi = {
        let n_fv = d.fresh_fvar();
        let _n = d.kernel().fvar(n_fv);
        let lt01 = d.const_app(p.zero_lt_one, &[]);
        let body = d.lemma(p.le_of_lt, &[zero_c, one_c, lt01]);
        d.lam_fv(n_fv, nat, body)
    };
    let hconv = d.lemma(p.converges_of_const, &[zero_c]);
    let e = d.num(3);

    let instance = d.lemma(
        p.converges_comp_eventually,
        &[f_big, zero_c, one_c, u, f, l, h_lo, h_hi, hconv, e],
    );

    let inferred = d.kernel().infer(instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!(
            "converges_comp_eventually refused at F := (fun r => r + 1), \
             f := L := zero, e := 3: {error:?}"
        )
    });
    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Exists"),
        "the instantiated conclusion is not an existential: {rendered}"
    );
}

/// **Mandatory concrete instantiation** for `CReal.scale_cancel_le`, kernel-
/// checked rather than verified on paper: `m := 1`, `u := 2`, `v := 1`.
///
/// Both directions are TIGHT, which is exactly what would catch an off-by-one
/// factor: the hypothesis is `(1/2)*2 = 1 <= 1` (an equality dressed as a
/// bound) and the conclusion is `2 <= 2*1 = 2` (likewise). `u` is built as
/// `CReal.ofRat (Rat.natDivSucc 2 0)` -- the theorem's own `Nat.succ m`
/// reciprocal shape at `m := 1` -- rather than some other representation of
/// "2", so the hypothesis proof is exactly the field identity
/// `declare_scale_cancel_le` itself needs internally
/// (`Rat.mul_inv_cancel` + `Rat.inv_natDivSucc`), reconstructed here at a
/// concrete literal instead of the free `m` the production declaration
/// carries.
#[test]
fn scale_cancel_le_applies_at_one_two_one_and_is_tight() {
    use crate::rat_prelude::ops::{rat_eq_rewrite, req, rmul, rone};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let rat = p.rat;

    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let m = d.num(1); // m := 1
    let sm = d.succ(m); // Nat.succ 1 = 2

    // c := CReal.ofRat (Rat.natDivSucc 1 1) = 1/2
    let c_rat = d.const_app(rat.nat_div_succ, &[one_nat, m]);
    let c = d.const_app(p.of_rat, &[c_rat]);
    // u := CReal.ofRat (Rat.natDivSucc 2 0) -- defeq `CReal.ofNat 2`.
    let succ_rat = d.const_app(rat.nat_div_succ, &[sm, zero_nat]);
    let u = d.const_app(p.of_rat, &[succ_rat]);
    // v := CReal.ofRat Rat.one -- defeq `CReal.one`.
    let one_rat = rone(&mut d, rat);
    let v = d.const_app(p.of_rat, &[one_rat]);

    // --- Rat level: c_rat * succ_rat = Rat.one, exactly (m := 1) -----------
    let unit_le = d.lemma(rat.int.nat.le_refl, &[one_nat]); // Nat.le 1 1
    let c_pos = d.lemma(rat.nat_div_succ_pos, &[one_nat, m, unit_le]);
    // c_pos : Rat.lt Rat.zero c_rat
    let inv_term = d.const_app(rat.inv, &[c_rat]);
    let cancel = d.lemma(rat.mul_inv_cancel, &[c_rat, c_pos]);
    // cancel : Eq Rat (Rat.mul c_rat inv_term) Rat.one
    let inv_eq = d.lemma(rat.inv_nat_div_succ, &[m]);
    // inv_eq : Eq Rat inv_term succ_rat
    let key_rat_eq = rat_eq_rewrite(&mut d, inv_term, succ_rat, inv_eq, cancel, &|d, t| {
        let prod = rmul(d, c_rat, t);
        req(d, prod, one_rat)
    });
    // key_rat_eq : Eq Rat (Rat.mul c_rat succ_rat) Rat.one

    // --- lift to CReal: Equiv (mul c u) v -----------------------------------
    let prod_real = d.const_app(p.mul, &[c, u]);
    let rat_prod = rmul(&mut d, c_rat, succ_rat);
    let of_rat_mul_proof = d.lemma(p.of_rat_mul, &[c_rat, succ_rat]);
    // of_rat_mul_proof : Equiv prod_real (ofRat rat_prod)
    let prod_equiv_v = rat_eq_rewrite(
        &mut d,
        rat_prod,
        one_rat,
        key_rat_eq,
        of_rat_mul_proof,
        &|d, t| {
            let embedded = d.const_app(p.of_rat, &[t]);
            d.const_app(p.equiv, &[prod_real, embedded])
        },
    );
    // prod_equiv_v : Equiv prod_real v  (v is syntactically `ofRat one_rat`)

    let hyp_proof = d.lemma(p.le_of_equiv, &[prod_real, v, prod_equiv_v]);
    // hyp_proof : le (mul c u) v  -- i.e. (1/2)*2 <= 1, tight.

    let instance = d.lemma(p.scale_cancel_le, &[m, u, v, hyp_proof]);

    // Independently reconstruct the expected conclusion:
    // le u (mul (ofNat (Nat.succ m)) v) = le 2 (mul (ofNat 2) v), tight.
    let nice_succ_factor = d.const_app(p.of_nat, &[sm]);
    let nice_bound = d.const_app(p.mul, &[nice_succ_factor, v]);
    let ty = d.const_app(p.le, &[u, nice_bound]);

    let anon = kernel.anon();
    let name = kernel.name_str(anon, "__scale_cancel_le_at_1_2_1");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value: instance,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.scale_cancel_le at (m=1, u=2, v=1) did NOT check against \
                 le u (mul (ofNat 2) v) -- i.e. le 2 (mul 2 1): {error:?}"
            )
        });
}

/// **Mandatory concrete instantiation** for
/// `CReal.diff_le_of_strict_mono_magnitude`, kernel-checked rather than
/// verified on paper: `F := id` (`CReal.hasDerivative_id`, itself already
/// `∀ a b`, so no bespoke `HasDerivativeOn` witness is needed -- applying it
/// at `a := zero, b := one` IS the whole instantiation cost), `k := 0`,
/// `x := 0`, `y := 1`.
///
/// The `hderiv` hypothesis this needs is `1/(0+1) = 1 <= F'(z) = 1` -- an
/// equality dressed as a bound, built the same way
/// `CReal.of_nat_one_equiv_local`'s (private, out-of-module) route does:
/// `ofRat (natDivSucc 1 0)` and `CReal.one` each unfold one delta step to an
/// `embed`, bridged by [`CRealPrelude::rat_unit_eq_one`] at the `Rat` level.
#[test]
fn diff_le_of_strict_mono_magnitude_applies_to_the_identity_at_zero_zero_one() {
    use crate::rat_prelude::ops::{rat_eq_rewrite, rone};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let rat = p.rat;
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let k = d.num(0); // k := 0
    let one_nat = d.num(1);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let one_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, one_c)
    };

    let hf = d.lemma(p.has_derivative_id, &[zero_c, one_c]);

    // --- hderiv : forall z, le zero z -> le z one -> le (ofRat (natDivSucc 1
    // k)) (F' z) -- constant in z, since `k := 0` makes the bound exactly
    // `CReal.one`, matching `F' z`'s own constant value.
    let c_rat = d.const_app(rat.nat_div_succ, &[one_nat, k]); // natDivSucc 1 0
    let c = d.const_app(p.of_rat, &[c_rat]);
    let one_rat = rone(&mut d, rat);
    let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]); // Eq Rat c_rat one_rat
    let refl_start = d.lemma(p.equiv_refl, &[c]);
    let c_equiv_one = rat_eq_rewrite(&mut d, c_rat, one_rat, unit_eq_one, refl_start, &|d, t| {
        let embedded = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[c, embedded])
    });
    // c_equiv_one : Equiv c (ofRat one_rat) -- defeq Equiv c one_c
    let embed_one_rat = d.const_app(p.of_rat, &[one_rat]);
    let hderiv_body = d.lemma(p.le_of_equiv, &[c, embed_one_rat, c_equiv_one]);
    // hderiv_body : le c embed_one_rat -- defeq le c one_c, matching `le c (F' z)`.

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let haz_ty = d.const_app(p.le, &[zero_c, z]);
    let haz_fv = d.fresh_fvar();
    let hzb_ty = d.const_app(p.le, &[z, one_c]);
    let hzb_fv = d.fresh_fvar();
    let with_hzb = d.lam_fv(hzb_fv, hzb_ty, hderiv_body);
    let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
    let hderiv = d.lam_fv(z_fv, carrier, with_haz);

    // --- x := zero, y := one, a := zero, b := one -------------------------
    let hax = d.lemma(p.le_refl, &[zero_c]); // le zero zero
    let lt01 = d.lemma(p.zero_lt_one, &[]);
    let hxy = d.lemma(p.le_of_lt, &[zero_c, one_c, lt01]); // le zero one
    let hyb = d.lemma(p.le_refl, &[one_c]); // le one one

    let instance = d.lemma(
        p.diff_le_of_strict_mono_magnitude,
        &[
            identity, one_fn, zero_c, one_c, hf, k, hderiv, zero_c, one_c, hax, hxy, hyb,
        ],
    );

    // Independently reconstruct the expected conclusion:
    // le (add one (neg zero)) (mul (ofNat (Nat.succ (Nat.succ (Nat.mul 2
    // 0)))) (add (abs (F zero)) (abs (F one)))).
    let two_nat = d.num(2);
    let doubled = d.mul(two_nat, k); // Nat.mul 2 0
    let e_acc = d.succ(doubled); // Nat.succ (Nat.mul 2 0)
    let sm = d.succ(e_acc); // Nat.succ (Nat.succ (Nat.mul 2 0))
    let nice_factor = d.const_app(p.of_nat, &[sm]);
    let fx = d.apply(identity, &[zero_c]);
    let fy = d.apply(identity, &[one_c]);
    let abs_fx = d.const_app(p.abs, &[fx]);
    let abs_fy = d.const_app(p.abs, &[fy]);
    let sum_fx_fy = d.const_app(p.add, &[abs_fx, abs_fy]);
    let nice_bound = d.const_app(p.mul, &[nice_factor, sum_fx_fy]);
    let neg_x = d.const_app(p.neg, &[zero_c]);
    let diff = d.const_app(p.add, &[one_c, neg_x]);
    let ty = d.const_app(p.le, &[diff, nice_bound]);

    let anon = kernel.anon();
    let name = kernel.name_str(anon, "__diff_le_of_strict_mono_magnitude_at_id_0_0_1");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value: instance,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.diff_le_of_strict_mono_magnitude at (F=id, k=0, x=0, y=1) \
                 did NOT check against \
                 le (add one (neg zero)) (mul (ofNat 2) (add (abs zero) (abs one))): \
                 {error:?}"
            )
        });
}

/// `CReal.bucketIndex (CReal.ofNat 2) 0` computes to the literal `2`, and the
/// two floor bounds instantiate to the (trivially true, since `q` lands
/// exactly ON the grid) statement `Rat.le (natDivSucc 2 0) (natDivSucc 2 0)`
/// twice over. The on-grid case is the one where a transposed `<`/`<=` or an
/// off-by-one in `bucket_index`'s own recipe is easiest to miss, because both
/// directions happen to coincide.
#[test]
fn bucket_index_floor_bounds_apply_on_grid_at_ofnat_two_and_zero() {
    use crate::rat_prelude::ops::{req, rle, rrefl, rzero};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let two_nat = d.num(2);
    let w = d.const_app(p.of_nat, &[two_nat]);
    let zero_nat = d.num(0);

    // `bucketIndex (ofNat 2) 0` reduces to the literal `2`: j = 1*1 = 1,
    // seq w 1 = natDivSucc 2 0 (the constant sequence), q = max(2/1, 0) =
    // 2/1, a = natAbs 2 = 2, b = 1, scaled = 2*1 = 2, m = Nat.div 2 1 = 2.
    let m = d.const_app(p.bucket_index, &[w, zero_nat]);
    let two_nat_again = d.num(2);
    let m_eq_two = NatOps::eq(&mut d, m, two_nat_again);
    let m_proof = NatOps::refl(&mut d, m);
    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__bucket_index_on_grid_reduces_to_two");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: m_eq_two,
            value: m_proof,
        })
        .unwrap_or_else(|error| {
            panic!("bucketIndex (ofNat 2) 0 must reduce to 2 by refl: {error:?}")
        });

    // `Rat.max (seq (ofNat 2) 1) Rat.zero` reduces to the literal `natDivSucc
    // 2 0` -- confirming `q` itself is exactly `2`, not merely that the Nat
    // arithmetic downstream of it works out.
    let one_nat = d.num(1);
    let sample_w1 = d.const_app(p.seq, &[w, one_nat]);
    let zero_rat = rzero(&mut d, p.rat);
    let q = d.const_app(p.rat.max, &[sample_w1, zero_rat]);
    let two_over_one = d.const_app(p.rat.nat_div_succ, &[two_nat, zero_nat]);
    let q_eq = req(&mut d, q, two_over_one);
    let q_proof = rrefl(&mut d, q);
    let name2 = d
        .kernel()
        .name_str(anon, "__bucket_index_on_grid_q_reduces_to_two_over_one");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name: name2,
            uparams: vec![],
            ty: q_eq,
            value: q_proof,
        })
        .unwrap_or_else(|error| {
            panic!("Rat.max (seq (ofNat 2) 1) 0 must reduce to natDivSucc 2 0: {error:?}")
        });

    // The two floor bounds, applied at these concrete `w, k`, both instantiate
    // to `Rat.le (natDivSucc 2 0) (natDivSucc 2 0)` -- the same statement
    // twice, because `q` sits exactly on `bucketIndex`'s own grid point here.
    let lower = d.const_app(p.bucket_index_floor_lower, &[w, zero_nat]);
    let upper = d.const_app(p.bucket_index_floor_upper, &[w, zero_nat]);
    // Lower: `natDivSucc m k <= q` at `m = 2` is the tight `2/1 <= 2/1`.
    let lower_tight_ty = rle(&mut d, p.rat, two_over_one, two_over_one);
    let name3 = d
        .kernel()
        .name_str(anon, "__bucket_index_on_grid_lower_is_tight");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name: name3,
            uparams: vec![],
            ty: lower_tight_ty,
            value: lower,
        })
        .unwrap_or_else(|error| {
            panic!("bucket_index_floor_lower at (ofNat 2, 0) must read as 2/1 <= 2/1: {error:?}")
        });
    // Upper: `q <= natDivSucc (succ m) k` compares against `m + 1 = 3`, NOT
    // `m` -- `q = 2 <= 3`, one full step above the lower bound's own target,
    // not a second copy of the same tight inequality.
    let three_nat = d.num(3);
    let three_over_one = d.const_app(p.rat.nat_div_succ, &[three_nat, zero_nat]);
    let upper_ty = rle(&mut d, p.rat, two_over_one, three_over_one);
    let name4 = d
        .kernel()
        .name_str(anon, "__bucket_index_on_grid_upper_is_one_step_above");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name: name4,
            uparams: vec![],
            ty: upper_ty,
            value: upper,
        })
        .unwrap_or_else(|error| {
            panic!("bucket_index_floor_upper at (ofNat 2, 0) must read as 2/1 <= 3/1: {error:?}")
        });
}

/// `CReal.bucketIndex (CReal.ofRat (1/3)) 1` computes to `0` -- `q = 1/3`
/// lands STRICTLY between the grid points `0/2` and `1/2`, so this exercises
/// the genuine floor (not merely the on-grid coincidence the sibling test
/// above cannot rule out a transposition with).
#[test]
fn bucket_index_floor_bounds_apply_strictly_between_grid_points_at_one_third_and_one() {
    use crate::rat_prelude::ops::rle;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let one_third = d.const_app(p.rat.nat_div_succ, &[one_nat, two_nat]); // 1/3
    let w = d.const_app(p.of_rat, &[one_third]);

    // k := 1, so k1 = 2, step = natDivSucc 1 1 = 1/2, j = 2*2 = 4.
    let m = d.const_app(p.bucket_index, &[w, one_nat]);
    let zero_nat = d.num(0);
    let m_eq_zero = NatOps::eq(&mut d, m, zero_nat);
    let m_proof = NatOps::refl(&mut d, m);
    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__bucket_index_between_grid_points_reduces_to_zero");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: m_eq_zero,
            value: m_proof,
        })
        .unwrap_or_else(|error| {
            panic!("bucketIndex (ofRat 1/3) 1 must reduce to 0 by refl: {error:?}")
        });

    // The lower bound instantiates to `natDivSucc 0 1 <= q` (i.e. `0 <= 1/3`)
    // and the upper bound to `q <= natDivSucc 1 1` (i.e. `1/3 <= 1/2`) --
    // genuinely different rationals on each side, unlike the on-grid case.
    let lower = d.const_app(p.bucket_index_floor_lower, &[w, one_nat]);
    let upper = d.const_app(p.bucket_index_floor_upper, &[w, one_nat]);

    let four_nat = d.num(4);
    let sample_w4 = d.const_app(p.seq, &[w, four_nat]);
    let zero_rat = crate::rat_prelude::ops::rzero(&mut d, p.rat);
    let q = d.const_app(p.rat.max, &[sample_w4, zero_rat]);
    let zero_over_one = d.const_app(p.rat.nat_div_succ, &[zero_nat, one_nat]); // 0/2
    let one_over_one = d.const_app(p.rat.nat_div_succ, &[one_nat, one_nat]); // 1/2

    let lower_ty = rle(&mut d, p.rat, zero_over_one, q);
    let name2 = d
        .kernel()
        .name_str(anon, "__bucket_index_between_grid_points_lower");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name: name2,
            uparams: vec![],
            ty: lower_ty,
            value: lower,
        })
        .unwrap_or_else(|error| {
            panic!("bucket_index_floor_lower at (1/3, 1) must read as 0/2 <= q: {error:?}")
        });
    let upper_ty = rle(&mut d, p.rat, q, one_over_one);
    let name3 = d
        .kernel()
        .name_str(anon, "__bucket_index_between_grid_points_upper");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name: name3,
            uparams: vec![],
            ty: upper_ty,
            value: upper,
        })
        .unwrap_or_else(|error| {
            panic!("bucket_index_floor_upper at (1/3, 1) must read as q <= 1/2: {error:?}")
        });
}

/// `CReal.bucketClampUpper CReal.zero 0` instantiates the additive constant
/// step 1's upper half adds to `2/(j+1)` with `j = 1`: `w`'s own sample
/// collapses `q` to `Rat.zero` (`CReal.zero` samples constantly at `0`), so
/// the resulting statement is `CReal.le CReal.zero (CReal.ofRat (Rat.zero +
/// natDivSucc 2 1))`. This is exactly the check that catches a transposed
/// `sub` for `add` or a `3` in place of the `2` step 1's own doc comment
/// claims: either would make this `add_declaration` fail with a type
/// mismatch, since the constant here is independently recomputed, not
/// copied from the proof term.
#[test]
fn bucket_clamp_upper_at_zero_and_zero_reduces_to_zero_plus_two_over_two() {
    use crate::rat_prelude::ops::{radd, rzero};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let czero = d.kernel().const_(p.zero, vec![]);

    let proof = d.const_app(p.bucket_clamp_upper, &[czero, zero_nat]);

    // j = (succ 0)*(succ 0) = 1, bound2j = natDivSucc 2 1 (== 1).
    let bound2j = d.const_app(p.rat.nat_div_succ, &[two_nat, one_nat]);
    let zero_rat = rzero(&mut d, p.rat);
    let target = radd(&mut d, zero_rat, bound2j);
    let embedded_target = d.const_app(p.of_rat, &[target]);
    let expected_ty = d.const_app(p.le, &[czero, embedded_target]);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__bucket_clamp_upper_at_zero_zero");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "bucket_clamp_upper at (CReal.zero, 0) must read as \
                 CReal.le CReal.zero (CReal.ofRat (Rat.zero + natDivSucc 2 1)): {error:?}"
            )
        });
}

/// `CReal.bucketClampLower CReal.zero 0 (le_refl CReal.zero)` instantiates
/// the additive constant step 1's lower half SUBTRACTS: `3/(j+1)` with
/// `j = 1`, giving `CReal.le (CReal.ofRat (Rat.zero - natDivSucc 3 1))
/// CReal.zero`. Distinct from the sibling test above in the constant (`3`,
/// not `2`) AND the operation (`sub`, not `add`) AND the direction of the
/// `CReal.le` (the bound is now the LEFT argument) -- a proof that silently
/// reused the upper half's shape, or swapped which side is smaller, fails
/// this `add_declaration` with a type mismatch.
#[test]
fn bucket_clamp_lower_at_zero_and_zero_reduces_to_zero_minus_three_over_two() {
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::rzero;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let three_nat = d.num(3);
    let czero = d.kernel().const_(p.zero, vec![]);

    let hzw = d.lemma(p.le_refl, &[czero]); // CReal.le CReal.zero CReal.zero
    let proof = d.const_app(p.bucket_clamp_lower, &[czero, zero_nat, hzw]);

    // j = (succ 0)*(succ 0) = 1, bound3j = natDivSucc 3 1 (== 3/2).
    let bound3j = d.const_app(p.rat.nat_div_succ, &[three_nat, one_nat]);
    let zero_rat = rzero(&mut d, p.rat);
    let target2 = rsub(&mut d, p.rat, zero_rat, bound3j);
    let embedded_target2 = d.const_app(p.of_rat, &[target2]);
    let expected_ty = d.const_app(p.le, &[embedded_target2, czero]);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__bucket_clamp_lower_at_zero_zero");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "bucket_clamp_lower at (CReal.zero, 0, le_refl) must read as \
                 CReal.le (CReal.ofRat (Rat.zero - natDivSucc 3 1)) CReal.zero: {error:?}"
            )
        });
}

/// **Mandatory concrete instantiation for `CReal.bucketIndexBound`.** At
/// `w := CReal.zero`, `bnd := CReal.zero`, `k := 0`,
/// `hle := CReal.le_refl CReal.zero`: `CReal.bound CReal.zero` samples `seq
/// CReal.zero 0 = Rat.zero`, so `bound = natAbs (num Rat.zero) + 1 = 0 + 1
/// = 1`, and the computed bound formula `(succ (bound bnd) + 2) * succ k`
/// reduces to `(succ 1 + 2) * succ 0 = 4 * 1 = 4`. `bucketIndex CReal.zero
/// 0` samples at `j = (succ 0)*(succ 0) = 1`, clamps `Rat.zero` to itself,
/// and floor-divides `natAbs 0 * 1 / 1 = 0`.
///
/// The expected type is the RAW literal `Nat.le 0 4` -- no reference to
/// `bucket_index`, `bound`, or any of the proof's own intermediate terms --
/// so the kernel has to reduce BOTH sides of the theorem's own statement
/// (`CReal.bucketIndex czero 0` and the `(bound+3)*(k+1)` scaling formula)
/// down to these numerals, not merely accept a restatement of the same
/// unevaluated expression. This is what would catch a transposed `bound
/// bnd`/`bound w`, an off-by-one in the `+2`/`+3` split (the same slack
/// [`CRealPrelude::bucket_clamp_upper`]/[`CRealPrelude::bucket_clamp_lower`]
/// warn about), or a swapped `mul`/`add` in the final scaling.
#[test]
fn bucket_index_bound_at_zero_zero_and_zero_computes_to_zero_le_four() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let four_nat = d.num(4);
    let czero = d.kernel().const_(p.zero, vec![]);

    let hle = d.lemma(p.le_refl, &[czero]); // CReal.le CReal.zero CReal.zero
    let proof = d.const_app(p.bucket_index_bound, &[czero, czero, zero_nat, hle]);

    let expected_ty = NatOps::le(&mut d, zero_nat, four_nat);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__bucket_index_bound_at_zero_zero_zero");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "bucket_index_bound at (CReal.zero, CReal.zero, 0, le_refl) must \
                 reduce to Nat.le 0 4: {error:?}"
            )
        });
}

/// **Mandatory concrete instantiation for `CReal.sampleUpperBound`.** At
/// `x := CReal.zero`, `m := 0`: `seq CReal.zero 0 = Rat.zero`,
/// `Rat.natDivSucc 1 0 = 1/(0+1) = Rat.one`, so the target is
/// `Rat.zero + Rat.one`, which the kernel must reduce to `Rat.one` itself
/// (built independently via `rat_prelude::ops::rone`, never referencing
/// `sample`/`div_succ`/`radd` the way the proof's own statement does) to
/// accept this ascription.
#[test]
fn sample_upper_bound_at_zero_and_zero_types_at_zero_le_ofrat_one() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let czero = d.kernel().const_(p.zero, vec![]);
    let proof = d.const_app(p.sample_upper_bound, &[czero, zero_nat]);

    let rat_one = crate::rat_prelude::ops::rone(&mut d, p.rat);
    let embedded_one = super::embed(&mut d, p, rat_one);
    let expected_ty = super::cle(&mut d, p, czero, embedded_one);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__sample_upper_bound_at_zero_zero");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "sample_upper_bound at (CReal.zero, 0) must reduce to \
                 CReal.le CReal.zero (CReal.ofRat Rat.one): {error:?}"
            )
        });
}

/// **Negative control for `CReal.sampleUpperBound`.** The SAME proof term,
/// ascribed to the REVERSED statement `CReal.le (CReal.ofRat Rat.one)
/// CReal.zero` (i.e. `1 ≤ 0`, genuinely false over `ℚ`, not a degenerate
/// collapse) -- confirming the kernel actually discriminates direction here
/// rather than accepting any two-argument application of `CReal.le`.
#[test]
fn sample_upper_bound_proof_is_rejected_at_the_reversed_statement() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let czero = d.kernel().const_(p.zero, vec![]);
    let proof = d.const_app(p.sample_upper_bound, &[czero, zero_nat]);

    let rat_one = crate::rat_prelude::ops::rone(&mut d, p.rat);
    let embedded_one = super::embed(&mut d, p, rat_one);
    let reversed_ty = super::cle(&mut d, p, embedded_one, czero);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__sample_upper_bound_reversed_must_fail");
    let outcome = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: reversed_ty,
        value: proof,
    });
    assert!(
        outcome.is_err(),
        "sample_upper_bound's proof must NOT typecheck against the reversed \
         (false) statement CReal.le (CReal.ofRat Rat.one) CReal.zero"
    );
}

/// **Mandatory concrete instantiation for `CReal.sampleLowerBound`.** At
/// `x := CReal.zero`, `m := 0`: the target is `Rat.zero - Rat.natDivSucc 1
/// 0 = Rat.zero - Rat.one`, which the kernel must reduce to `Rat.neg
/// Rat.one` (built independently via `rat_prelude::ops::rone`/`rneg`).
#[test]
fn sample_lower_bound_at_zero_and_zero_types_at_neg_one_le_zero() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let czero = d.kernel().const_(p.zero, vec![]);
    let proof = d.const_app(p.sample_lower_bound, &[czero, zero_nat]);

    let rat_one = crate::rat_prelude::ops::rone(&mut d, p.rat);
    let neg_one = crate::rat_prelude::ops::rneg(&mut d, rat_one);
    let embedded_neg_one = super::embed(&mut d, p, neg_one);
    let expected_ty = super::cle(&mut d, p, embedded_neg_one, czero);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__sample_lower_bound_at_zero_zero");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "sample_lower_bound at (CReal.zero, 0) must reduce to \
                 CReal.le (CReal.ofRat (Rat.neg Rat.one)) CReal.zero: {error:?}"
            )
        });
}

/// **Negative control for `CReal.sampleLowerBound`.** The SAME proof term,
/// ascribed to the REVERSED statement `CReal.le CReal.zero (CReal.ofRat
/// (Rat.neg Rat.one))` (i.e. `0 ≤ -1`, genuinely false), confirming the
/// direction is load-bearing.
#[test]
fn sample_lower_bound_proof_is_rejected_at_the_reversed_statement() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let czero = d.kernel().const_(p.zero, vec![]);
    let proof = d.const_app(p.sample_lower_bound, &[czero, zero_nat]);

    let rat_one = crate::rat_prelude::ops::rone(&mut d, p.rat);
    let neg_one = crate::rat_prelude::ops::rneg(&mut d, rat_one);
    let embedded_neg_one = super::embed(&mut d, p, neg_one);
    let reversed_ty = super::cle(&mut d, p, czero, embedded_neg_one);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__sample_lower_bound_reversed_must_fail");
    let outcome = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: reversed_ty,
        value: proof,
    });
    assert!(
        outcome.is_err(),
        "sample_lower_bound's proof must NOT typecheck against the reversed \
         (false) statement CReal.le CReal.zero (CReal.ofRat (Rat.neg Rat.one))"
    );
}

/// **Mandatory computation test for `CReal.sqrtApproxSqBracket`.** At
/// `x := CReal.ofNat 4`, `n := 0`: `d = 1`, `j = 1`, the clamped sample is
/// `4`, `natSqrt 4 = 2` (`2*2 = 4 ≤ 4`, and `4 < 3*3 = 9`), so the bracket's
/// two halves are `Rat.le (2*2) 4` and `Rat.lt 4 (3*3)` — `4 ≤ 4` and
/// `4 < 9`, both true. Checked against an INDEPENDENTLY built expected type
/// (`Rat.natDivSucc k 0` for the literals, not a reuse of `sqrtApprox`'s own
/// formula), so the kernel has to actually reduce `natSqrt`/`Nat.div`/
/// `Int.natAbs`/`Rat.max`/`CReal.seq` down to these numerals, not merely
/// accept a restatement of the same unevaluated expression.
#[test]
fn sqrt_approx_sq_bracket_at_ofnat_four_and_zero_computes_to_four_le_four_and_four_lt_nine() {
    use crate::rat_prelude::ops::{rle, rlt, rmul};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let four_nat = d.num(4);
    let zero_nat = d.num(0);
    let two_nat = d.num(2);
    let three_nat = d.num(3);

    let x = d.const_app(p.of_nat, &[four_nat]);
    let n = zero_nat;

    let proof = d.const_app(p.sqrt_approx_sq_bracket, &[x, n]);

    let literal = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        d.const_app(p.rat.nat_div_succ, &[k, zero_nat])
    };
    let four_rat = literal(&mut d, four_nat);
    let two_rat = literal(&mut d, two_nat);
    let three_rat = literal(&mut d, three_nat);

    let two_sq = rmul(&mut d, two_rat, two_rat);
    let three_sq = rmul(&mut d, three_rat, three_rat);
    let lower_ty = rle(&mut d, p.rat, two_sq, four_rat);
    let upper_ty = rlt(&mut d, p.rat, four_rat, three_sq);
    let and_name = p.rat.int.logic.and;
    let expected_ty = d.const_app(and_name, &[lower_ty, upper_ty]);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__sqrt_approx_sq_bracket_at_ofnat_four_and_zero");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "sqrtApproxSqBracket (ofNat 4) 0 must read as \
                 And (Rat.le (2*2) 4) (Rat.lt 4 (3*3)): {error:?}"
            )
        });

    // Negative control: the same proof does NOT check against a WRONG
    // bound (claiming the clamped sample is `3`, not `4` -- `4 <= 3` is
    // false, so a proof of the real bracket must be refused here).
    let lower_ty_wrong = rle(&mut d, p.rat, two_sq, three_rat);
    let expected_ty_wrong = d.const_app(and_name, &[lower_ty_wrong, upper_ty]);
    let name_wrong = d.kernel().name_str(
        anon,
        "__sqrt_approx_sq_bracket_wrong_bound_must_be_rejected",
    );
    let bad_proof = d.const_app(p.sqrt_approx_sq_bracket, &[x, n]);
    let result = d.kernel().add_declaration(Declaration::Theorem {
        name: name_wrong,
        uparams: vec![],
        ty: expected_ty_wrong,
        value: bad_proof,
    });
    assert!(
        result.is_err(),
        "sqrtApproxSqBracket must NOT check against the wrong bound \
         `2*2 <= 3` (4 <= 3 is false) -- a checker that accepts both the \
         right and a wrong bound cannot distinguish them"
    );
}

/// **Mandatory computation test for `CReal.sqrt`.** At `x := CReal.ofNat 4`,
/// `n := 0`: `CReal.seq (CReal.sqrt x) 0` unfolds through `speedup`'s own
/// sampling index (`mul_index 1 0 = (1+1)*0+1 = 1`) to `sqrtApprox x 1`,
/// which computes (`d = 2`, `j = 4`, clamped sample `4`, `natSqrt 16 = 4`)
/// to `Rat.normalize 4 2 _` -- reduced, by `Rat.normalize`'s own division by
/// the gcd, to the same representative `Rat.natDivSucc 2 0` (`= 2`) computes
/// to. Checked against an INDEPENDENTLY built expected value (not a reuse of
/// `sqrtApprox`'s own formula), with a negative control (`3`) the kernel
/// must reject -- otherwise an always-accepting checker could not be told
/// apart from this one.
#[test]
fn sqrt_of_ofnat_four_at_index_zero_computes_to_two() {
    use crate::rat_prelude::ops::{req, rrefl};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let four_nat = d.num(4);
    let zero_nat = d.num(0);
    let two_nat = d.num(2);
    let three_nat = d.num(3);

    let x = d.const_app(p.of_nat, &[four_nat]);
    let sqrt_x = d.const_app(p.sqrt, &[x]);
    let seq_at_zero = d.const_app(p.seq, &[sqrt_x, zero_nat]);

    let two_rat = d.const_app(p.rat.nat_div_succ, &[two_nat, zero_nat]);
    let expected_ty = req(&mut d, seq_at_zero, two_rat);
    let proof = rrefl(&mut d, seq_at_zero);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__sqrt_of_ofnat_four_at_index_zero_computes_to_two");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.seq (CReal.sqrt (CReal.ofNat 4)) 0 must reduce to \
                 Rat.natDivSucc 2 0 (= 2): {error:?}"
            )
        });

    // Negative control: the same reflexivity proof does NOT check against a
    // WRONG value (`3`) -- if it did, this checker could not distinguish a
    // correct computed square root from an arbitrary one.
    let three_rat = d.const_app(p.rat.nat_div_succ, &[three_nat, zero_nat]);
    let expected_ty_wrong = req(&mut d, seq_at_zero, three_rat);
    let proof_wrong = rrefl(&mut d, seq_at_zero);
    let name_wrong = d
        .kernel()
        .name_str(anon, "__sqrt_of_ofnat_four_wrong_value_must_be_rejected");
    let result = d.kernel().add_declaration(Declaration::Theorem {
        name: name_wrong,
        uparams: vec![],
        ty: expected_ty_wrong,
        value: proof_wrong,
    });
    assert!(
        result.is_err(),
        "CReal.seq (CReal.sqrt (CReal.ofNat 4)) 0 must NOT check as equal \
         to 3 -- a checker that accepts both 2 and 3 cannot be trusted to \
         have computed anything"
    );
}

/// **Mandatory concrete instantiation of `CReal.mul_self_sqrt`.** `Equiv` is
/// not decidable by computation (unlike `CReal.seq`'s own reduction, which
/// the sibling `sqrt_of_ofnat_four...` test above exercises), so the check
/// here is: instantiate the theorem at a genuinely CONCRETE `x := CReal.ofNat
/// 4` and `hx : le zero (ofNat 4)` (built the same `of_rat_le`-across-`ofRat`
/// route `riemann_sample_in_bounds_at_...`'s own `hab` uses), then declare
/// the application against an INDEPENDENTLY constructed expected type
/// (`Equiv (mul (sqrt (ofNat 4)) (sqrt (ofNat 4))) (ofNat 4)`) rather than
/// trusting `Kernel::infer` on the theorem's own instantiation. The negative
/// control swaps the right-hand side to `ofNat 5`: `CReal.ofNat 4` and
/// `CReal.ofNat 5` are built from different Nat literals with no reduction
/// path relating them, so the kernel must refuse the mismatched Prop -- the
/// same mandatory-instantiation-plus-negative-control shape
/// `sqrt_of_ofnat_four_at_index_zero_computes_to_two` uses for `CReal.sqrt`
/// itself, applied here to a law about it instead of to `CReal.seq`'s
/// reduction.
#[test]
fn mul_self_sqrt_at_ofnat_four_type_checks_against_the_independent_statement() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let four_nat = d.num(4);
    let five_nat = d.num(5);
    let zero_nat = d.num(0);

    let x4 = d.const_app(p.of_nat, &[four_nat]);
    let x5 = d.const_app(p.of_nat, &[five_nat]);

    // hx4 : CReal.le CReal.zero (CReal.ofNat 4), via `Rat.zero_le_natDivSucc`
    // lifted across `CReal.of_rat_le` -- `CReal.zero` and `CReal.ofNat 4` are
    // each one delta-step from an `ofRat` of a `Rat.natDivSucc`.
    let hx4 = {
        let rat_4 = d.const_app(p.rat.nat_div_succ, &[four_nat, zero_nat]);
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[four_nat, zero_nat]);
        d.lemma(p.of_rat_le, &[rzero, rat_4, rle])
    };

    let concrete_proof = d.const_app(p.mul_self_sqrt, &[x4, hx4]);

    let sqrt_x4 = d.const_app(p.sqrt, &[x4]);
    let lhs4 = d.const_app(p.mul, &[sqrt_x4, sqrt_x4]);
    let expected_ty = d.const_app(p.equiv, &[lhs4, x4]);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__mul_self_sqrt_at_ofnat_four_instance");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: concrete_proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.mul_self_sqrt (CReal.ofNat 4) hx4 must check against \
                 Equiv (mul (sqrt (ofNat 4)) (sqrt (ofNat 4))) (ofNat 4): \
                 {error:?}"
            )
        });

    // Negative control: the SAME proof does NOT check against the WRONG
    // right-hand side `ofNat 5` -- if it did, this checker could not
    // distinguish `mul_self_sqrt`'s real conclusion from an arbitrary one.
    let wrong_ty = d.const_app(p.equiv, &[lhs4, x5]);
    let name_wrong = d.kernel().name_str(
        anon,
        "__mul_self_sqrt_at_ofnat_four_wrong_rhs_must_be_rejected",
    );
    let result = d.kernel().add_declaration(Declaration::Theorem {
        name: name_wrong,
        uparams: vec![],
        ty: wrong_ty,
        value: concrete_proof,
    });
    assert!(
        result.is_err(),
        "CReal.mul_self_sqrt (CReal.ofNat 4) hx4 must NOT check against \
         Equiv (mul (sqrt (ofNat 4)) (sqrt (ofNat 4))) (ofNat 5) -- a \
         checker that accepts both 4 and 5 on the right cannot be trusted \
         to have proved anything about `ofNat 4` specifically"
    );
}

/// **Mandatory concrete instantiation of `CReal.sqrt_mul`.** `x := CReal.ofNat
/// 4`, `y := CReal.ofNat 1`, `hx4`/`hy1` built the same `of_rat_le`-across-
/// `ofRat` route the `mul_self_sqrt` instance above uses. Checked against an
/// INDEPENDENTLY constructed `Equiv (sqrt (mul (ofNat 4) (ofNat 1))) (mul
/// (sqrt (ofNat 4)) (sqrt (ofNat 1)))`, with a negative control that swaps
/// the right factor to `sqrt (ofNat 4)` again (`mul (sqrt x4) (sqrt x4)`
/// instead of `mul (sqrt x4) (sqrt y1)`) -- the natural "forgot which
/// argument this factor comes from" bug a copy-paste of `x` for `y` would
/// produce.
#[test]
fn sqrt_mul_at_ofnat_four_and_one_type_checks_against_the_independent_statement() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let four_nat = d.num(4);
    let one_nat = d.num(1);
    let zero_nat = d.num(0);

    let x4 = d.const_app(p.of_nat, &[four_nat]);
    let y1 = d.const_app(p.of_nat, &[one_nat]);

    let hx4 = {
        let rat_4 = d.const_app(p.rat.nat_div_succ, &[four_nat, zero_nat]);
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[four_nat, zero_nat]);
        d.lemma(p.of_rat_le, &[rzero, rat_4, rle])
    };
    let hy1 = {
        let rat_1 = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, zero_nat]);
        d.lemma(p.of_rat_le, &[rzero, rat_1, rle])
    };

    let concrete_proof = d.const_app(p.sqrt_mul, &[x4, y1, hx4, hy1]);

    let sqrt_x4 = d.const_app(p.sqrt, &[x4]);
    let sqrt_y1 = d.const_app(p.sqrt, &[y1]);
    let xy = d.const_app(p.mul, &[x4, y1]);
    let sqrt_xy = d.const_app(p.sqrt, &[xy]);
    let rhs = d.const_app(p.mul, &[sqrt_x4, sqrt_y1]);
    let expected_ty = d.const_app(p.equiv, &[sqrt_xy, rhs]);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__sqrt_mul_at_ofnat_four_and_one_instance");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: concrete_proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.sqrt_mul (CReal.ofNat 4) (CReal.ofNat 1) hx4 hy1 must \
                 check against Equiv (sqrt (mul (ofNat 4) (ofNat 1))) (mul \
                 (sqrt (ofNat 4)) (sqrt (ofNat 1))): {error:?}"
            )
        });

    // Negative control: the SAME proof does NOT check against the WRONG
    // right-hand side `mul (sqrt (ofNat 4)) (sqrt (ofNat 4))` -- the
    // "forgot which argument this factor comes from" bug a copy-paste of
    // `x4` for `y1` would produce.
    let wrong_rhs = d.const_app(p.mul, &[sqrt_x4, sqrt_x4]);
    let wrong_ty = d.const_app(p.equiv, &[sqrt_xy, wrong_rhs]);
    let name_wrong = d.kernel().name_str(
        anon,
        "__sqrt_mul_at_ofnat_four_and_one_wrong_rhs_must_be_rejected",
    );
    let result = d.kernel().add_declaration(Declaration::Theorem {
        name: name_wrong,
        uparams: vec![],
        ty: wrong_ty,
        value: concrete_proof,
    });
    assert!(
        result.is_err(),
        "CReal.sqrt_mul (CReal.ofNat 4) (CReal.ofNat 1) hx4 hy1 must NOT \
         check against Equiv (sqrt (mul (ofNat 4) (ofNat 1))) (mul (sqrt \
         (ofNat 4)) (sqrt (ofNat 4))) -- a checker that accepts both the \
         real second factor and a copy of the first cannot be trusted to \
         have proved anything about `ofNat 1` specifically"
    );
}

/// **Mandatory concrete instantiation of `CReal.le_of_sq_le`.** `t :=
/// CReal.ofNat 0`, `s := CReal.ofNat 1`: `t*t ~ ofNat 0`, `s*s ~ ofNat 1`
/// (`CReal.ofNat_mul` at `(0,0)`/`(1,1)`, `Nat.mul` computing away by
/// defeq), and `CReal.ofNat_le` at the `Nat.le 0 1` witness
/// (`Nat.zero_le`) gives `le (ofNat 0) (ofNat 1)`, transported across both
/// products by `le_congr` to the required `le (mul t t) (mul s s)`
/// hypothesis. `ht`/`hs` are built the same `of_rat_le`-across-`ofRat`
/// route the `mul_self_sqrt`/`sqrt_mul` instances above use. The negative
/// control checks the SAME proof against the swapped conclusion `le s t`
/// (`le (ofNat 1) (ofNat 0)`, genuinely false, not a vacuous swap) --
/// `CReal.ofNat 0` and `CReal.ofNat 1` are built from different `Nat`
/// literals with no reduction path relating them, so a checker that
/// accepted both directions could not be trusted to have proved `t ≤ s`
/// specifically.
#[test]
fn le_of_sq_le_at_ofnat_zero_and_one_type_checks_against_the_independent_statement() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);

    let t = d.const_app(p.of_nat, &[zero_nat]);
    let s = d.const_app(p.of_nat, &[one_nat]);

    // ht : le zero (ofNat 0), hs : le zero (ofNat 1) -- the same
    // `of_rat_le`-across-`ofRat` route `mul_self_sqrt_at_ofnat_four...`
    // above uses.
    let ht = {
        let rat_0 = d.const_app(p.rat.nat_div_succ, &[zero_nat, zero_nat]);
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[zero_nat, zero_nat]);
        d.lemma(p.of_rat_le, &[rzero, rat_0, rle])
    };
    let hs = {
        let rat_1 = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, zero_nat]);
        d.lemma(p.of_rat_le, &[rzero, rat_1, rle])
    };

    let tt = d.const_app(p.mul, &[t, t]);
    let ss = d.const_app(p.mul, &[s, s]);

    // eq_t : Equiv (ofNat (Nat.mul 0 0)) tt, defeq Equiv (ofNat 0) tt
    // (`Nat.mul 0 0` computes to `0`).
    let eq_t = d.lemma(p.of_nat_mul, &[zero_nat, zero_nat]);
    // eq_s : Equiv (ofNat (Nat.mul 1 1)) ss, defeq Equiv (ofNat 1) ss.
    let eq_s = d.lemma(p.of_nat_mul, &[one_nat, one_nat]);

    let nat_zero_le_one = d.lemma(p.rat.int.nat.zero_le, &[one_nat]);
    let le_0_1 = d.const_app(p.of_nat_le, &[zero_nat, one_nat, nat_zero_le_one]);
    // h : le tt ss, via le_congr transporting `le (ofNat 0) (ofNat 1)`
    // across both `ofNat_mul` equivalences at once.
    let h = d.lemma(p.le_congr, &[t, tt, s, ss, eq_t, eq_s, le_0_1]);

    let concrete_proof = d.const_app(p.le_of_sq_le, &[t, s, ht, hs, h]);

    let expected_ty = d.const_app(p.le, &[t, s]);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__le_of_sq_le_at_ofnat_zero_and_one_instance");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: concrete_proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.le_of_sq_le (CReal.ofNat 0) (CReal.ofNat 1) ht hs h \
                 must check against CReal.le (ofNat 0) (ofNat 1): {error:?}"
            )
        });

    // Negative control: the SAME proof does NOT check against the SWAPPED
    // conclusion `le s t` -- `le (ofNat 1) (ofNat 0)` is genuinely false,
    // not a vacuous relabeling.
    let wrong_ty = d.const_app(p.le, &[s, t]);
    let name_wrong = d.kernel().name_str(
        anon,
        "__le_of_sq_le_at_ofnat_zero_and_one_wrong_direction_must_be_rejected",
    );
    let result = d.kernel().add_declaration(Declaration::Theorem {
        name: name_wrong,
        uparams: vec![],
        ty: wrong_ty,
        value: concrete_proof,
    });
    assert!(
        result.is_err(),
        "CReal.le_of_sq_le (CReal.ofNat 0) (CReal.ofNat 1) ht hs h must NOT \
         check against CReal.le (ofNat 1) (ofNat 0) -- a checker that \
         accepts both directions cannot be trusted to have proved `t ≤ s` \
         specifically"
    );
}

/// **Mandatory computation test for `CReal.sqrt_one`.** At `n := 0`:
/// `CReal.seq (CReal.sqrt CReal.one) 0` unfolds through `speedup`'s sampling
/// index (`mul_index 1 0 = (1+1)*0+1 = 1`) to `sqrtApprox one 1`, which
/// computes (`d = 2`, `j = 4`, clamped sample `1` since `one`'s sequence is
/// constant, `natSqrt 4 = 2`) to `Rat.normalize 2 2 _` -- reduced, by
/// `Rat.normalize`'s own division by the gcd, to the same representative
/// `Rat.natDivSucc 1 0` (`= 1`) computes to. Checked against an
/// INDEPENDENTLY built expected value, with a negative control (`2`) the
/// kernel must reject -- otherwise an always-accepting checker could not be
/// told apart from this one.
#[test]
fn sqrt_of_one_at_index_zero_computes_to_one() {
    use crate::rat_prelude::ops::{req, rrefl};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    let one_real = d.kernel().const_(p.one, vec![]);
    let sqrt_one = d.const_app(p.sqrt, &[one_real]);
    let seq_at_zero = d.const_app(p.seq, &[sqrt_one, zero_nat]);

    let one_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
    let expected_ty = req(&mut d, seq_at_zero, one_rat);
    let proof = rrefl(&mut d, seq_at_zero);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__sqrt_of_one_at_index_zero_computes_to_one");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!(
                "CReal.seq (CReal.sqrt CReal.one) 0 must reduce to \
                 Rat.natDivSucc 1 0 (= 1): {error:?}"
            )
        });

    // Negative control: the same reflexivity proof does NOT check against a
    // WRONG value (`2`) -- if it did, this checker could not distinguish a
    // correct computed square root from an arbitrary one.
    let two_rat = d.const_app(p.rat.nat_div_succ, &[two_nat, zero_nat]);
    let expected_ty_wrong = req(&mut d, seq_at_zero, two_rat);
    let proof_wrong = rrefl(&mut d, seq_at_zero);
    let name_wrong = d
        .kernel()
        .name_str(anon, "__sqrt_of_one_wrong_value_must_be_rejected");
    let result = d.kernel().add_declaration(Declaration::Theorem {
        name: name_wrong,
        uparams: vec![],
        ty: expected_ty_wrong,
        value: proof_wrong,
    });
    assert!(
        result.is_err(),
        "CReal.seq (CReal.sqrt CReal.one) 0 must NOT check as equal to 2 \
         -- a checker that accepts both 1 and 2 cannot be trusted to have \
         computed anything"
    );
}

/// **Mandatory computation test for `CReal.sqrt_zero`.** At `n := 0`:
/// `CReal.seq (CReal.sqrt CReal.zero) 0` unfolds through `speedup`'s
/// sampling index (`mul_index 1 0 = 1`) to `sqrtApprox zero 1`, which
/// computes (`d = 2`, `j = 4`, clamped sample `0` since `zero`'s sequence is
/// constant, `natSqrt 0 = 0`) to `Rat.normalize 0 2 _` -- reduced, by
/// `Rat.normalize`'s own division, to the same representative `Rat.zero`
/// computes to. Checked against an INDEPENDENTLY built expected value, with
/// a negative control (`Rat.natDivSucc 1 0 = 1`) the kernel must reject.
#[test]
fn sqrt_of_zero_at_index_zero_computes_to_zero() {
    use crate::rat_prelude::ops::{req, rrefl, rzero};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);

    let zero_real = d.kernel().const_(p.zero, vec![]);
    let sqrt_zero = d.const_app(p.sqrt, &[zero_real]);
    let seq_at_zero = d.const_app(p.seq, &[sqrt_zero, zero_nat]);

    let zero_rat = rzero(&mut d, p.rat);
    let expected_ty = req(&mut d, seq_at_zero, zero_rat);
    let proof = rrefl(&mut d, seq_at_zero);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__sqrt_of_zero_at_index_zero_computes_to_zero");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected_ty,
            value: proof,
        })
        .unwrap_or_else(|error| {
            panic!("CReal.seq (CReal.sqrt CReal.zero) 0 must reduce to Rat.zero: {error:?}")
        });

    // Negative control: the same reflexivity proof does NOT check against a
    // WRONG value (`1`).
    let one_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
    let expected_ty_wrong = req(&mut d, seq_at_zero, one_rat);
    let proof_wrong = rrefl(&mut d, seq_at_zero);
    let name_wrong = d
        .kernel()
        .name_str(anon, "__sqrt_of_zero_wrong_value_must_be_rejected");
    let result = d.kernel().add_declaration(Declaration::Theorem {
        name: name_wrong,
        uparams: vec![],
        ty: expected_ty_wrong,
        value: proof_wrong,
    });
    assert!(
        result.is_err(),
        "CReal.seq (CReal.sqrt CReal.zero) 0 must NOT check as equal to 1 \
         -- a checker that accepts both 0 and 1 cannot be trusted to have \
         computed anything"
    );
}

/// `CReal.bounded_of_uniformly_continuous` instantiated at `F := identity`,
/// `[a,b] := [0, mag_bound 0]` (`= [0,1]`), using
/// `CReal.uniformly_continuous_id`. `K` is recomputed from scratch here by
/// literally re-running `declare_bounded_of_uniformly_continuous`'s own
/// documented formula (`succ(add(succ(bound(F a)), mul(add(succ(bound
/// bnd)),2)(succ k)))`, `k := add(mul(succ(succ(succ(succ(zero)))), modulus
/// 0), succ(succ(succ(zero))))`) over PUBLIC `CRealPrelude` fields only --
/// never by reusing `uniform_continuity.rs`'s own private helpers -- so this
/// is a genuine independent check that the theorem's declared type still
/// matches its documentation, not a tautology.
///
/// Negative control: the SAME proof term does NOT check against `K` with the
/// final `succ` dropped (`t_m_bound` instead of `succ(t_m_bound)`) -- a
/// genuinely different (and non-degenerate: dropping the last
/// `mag_bound_fuse_succ` step is exactly the off-by-one a hand-written proof
/// of this shape is most likely to make) Nat value, not a vacuous or
/// accidentally-true rewording.
#[test]
fn bounded_of_uniformly_continuous_instantiates_on_identity() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = super::creal_ty(&mut d, p);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three_nat = d.num(3);

    let czero = d.kernel().const_(p.zero, vec![]);
    let nds10 = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
    let unit = d.const_app(p.of_rat, &[nds10]);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let huc_id = d.const_app(p.uniformly_continuous_id, &[czero, unit]);

    let rzero_expr = crate::rat_prelude::ops::rzero(&mut d, p.rat);
    let zero_le_nds10 = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, zero_nat]);
    let hab = d.lemma(p.of_rat_le, &[rzero_expr, nds10, zero_le_nds10]);

    // --- recompute `K` from the documented formula, independently. ---------
    let modulus = d.const_app(p.uc_modulus, &[identity, czero, unit, huc_id]);
    let m0 = d.apply(modulus, &[zero_nat]);
    let succ_three = d.succ(three_nat);
    let mul_km = NatOps::mul(&mut d, succ_three, m0);
    let k = NatOps::add(&mut d, mul_km, three_nat);
    let k1 = d.succ(k);

    let f_a = d.apply(identity, &[czero]);
    let k_bound = d.const_app(p.bound, &[f_a]);
    let succ_k_bound = d.succ(k_bound);

    let neg_czero = d.const_app(p.neg, &[czero]);
    let bnd = d.const_app(p.add, &[unit, neg_czero]);
    let bound_bnd = d.const_app(p.bound, &[bnd]);
    let succ_bound_bnd = d.succ(bound_bnd);
    let m_bound_base = NatOps::add(&mut d, succ_bound_bnd, two_nat);
    let m_bound = NatOps::mul(&mut d, m_bound_base, k1);
    let t_m_bound = NatOps::add(&mut d, succ_k_bound, m_bound);
    let k_final = d.succ(t_m_bound);

    let value = d.const_app(
        p.bounded_of_uniformly_continuous,
        &[identity, czero, unit, huc_id, hab],
    );
    let ty = d.const_app(p.bounded_on, &[identity, czero, unit, k_final]);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__bounded_of_uniformly_continuous_id_positive");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|error| {
            panic!(
                "bounded_of_uniformly_continuous applied to identity on \
                 [0, mag_bound 0] must check against the documented K \
                 formula, recomputed independently here: {error:?}"
            )
        });

    // Negative control: the same proof does NOT check against `t_m_bound`
    // (K minus the theorem's own final `succ`).
    let value_again = d.const_app(
        p.bounded_of_uniformly_continuous,
        &[identity, czero, unit, huc_id, hab],
    );
    let ty_wrong = d.const_app(p.bounded_on, &[identity, czero, unit, t_m_bound]);
    let name_wrong = d
        .kernel()
        .name_str(anon, "__bounded_of_uniformly_continuous_id_off_by_one");
    let result = d.kernel().add_declaration(Declaration::Theorem {
        name: name_wrong,
        uparams: vec![],
        ty: ty_wrong,
        value: value_again,
    });
    assert!(
        result.is_err(),
        "bounded_of_uniformly_continuous applied to identity must NOT check \
         against K's own predecessor (t_m_bound, without the final succ) \
         -- a checker that accepts both K and K-1 has not verified the bound"
    );
}

/// `CReal.crossingIndex CReal.zero (CReal.ofRat (5/2)) Rat.one` computes to
/// the literal `2` -- `a := 0`, `Δ := 1`, `c := 5/2`, so the crossing lands
/// between the 2nd and 3rd unit step, matching a hand computation
/// (`floor(5/2) = 2`). Checked by `Eq.refl`, so this exercises the FULL
/// reduction: `Rat.inv 1 = 1`, `CReal.add`'s index shift, `CReal.mul`'s
/// `mulShift`-dependent sampling index, `Rat.max`, `Int.natAbs` and
/// `Nat.div`, not merely `bucketIndex`'s own final division step.
#[test]
fn crossing_index_at_zero_one_five_halves_reduces_to_two() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let a = d.kernel().const_(p.zero, vec![]);
    let five = d.num(5);
    let one_idx = d.num(1);
    let five_halves = d.const_app(p.rat.nat_div_succ, &[five, one_idx]); // 5/2
    let c = d.const_app(p.of_rat, &[five_halves]);
    let delta = crate::rat_prelude::ops::rone(&mut d, p.rat);

    let i0 = d.const_app(p.crossing.crossing_index, &[a, c, delta]);
    let two_nat = d.num(2);
    let i0_eq_two = NatOps::eq(&mut d, i0, two_nat);
    let i0_proof = NatOps::refl(&mut d, i0);
    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "__crossing_index_zero_one_five_halves_reduces_to_two");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: i0_eq_two,
            value: i0_proof,
        })
        .unwrap_or_else(|error| {
            panic!("crossingIndex 0 (5/2) 1 must reduce to 2 by refl: {error:?}")
        });
}

/// `CReal.crossingIndex CReal.zero (CReal.ofRat (7/2)) Rat.one` computes to
/// the literal `3` -- a DIFFERENT concrete case from the sibling test above,
/// with a DIFFERENT expected output. A construction that (wrongly) returned
/// a constant regardless of its arguments would pass a single concrete
/// check; it cannot pass two concrete checks that disagree.
#[test]
fn crossing_index_at_zero_one_seven_halves_reduces_to_three() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let a = d.kernel().const_(p.zero, vec![]);
    let seven = d.num(7);
    let one_idx = d.num(1);
    let seven_halves = d.const_app(p.rat.nat_div_succ, &[seven, one_idx]); // 7/2
    let c = d.const_app(p.of_rat, &[seven_halves]);
    let delta = crate::rat_prelude::ops::rone(&mut d, p.rat);

    let i0 = d.const_app(p.crossing.crossing_index, &[a, c, delta]);
    let three_nat = d.num(3);
    let i0_eq_three = NatOps::eq(&mut d, i0, three_nat);
    let i0_proof = NatOps::refl(&mut d, i0);
    let anon = d.kernel().anon();
    let name = d.kernel().name_str(
        anon,
        "__crossing_index_zero_one_seven_halves_reduces_to_three",
    );
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: i0_eq_three,
            value: i0_proof,
        })
        .unwrap_or_else(|error| {
            panic!("crossingIndex 0 (7/2) 1 must reduce to 3 by refl: {error:?}")
        });
}

/// **The base-`1/2` cross-check.** [`CReal::geomCauchyOfLt`] generalizes
/// `geomCauchy`/`geomCauchyOrderedHalf`'s own base-`1/2` derivation to a
/// symbolic ratio; this test instantiates the GENERAL theorem at `x := half`
/// with the SAME concrete witnesses `geomCauchy`'s own route builds
/// internally (`k := 1`, `h := geom_half_a_real_pos_bound`'s
/// `PosBound (1 - half) 1`), and checks the resulting proof against
/// `geomCauchy`'s OWN stored type — not a type this test reconstructs by
/// hand, so there is no way for the two routes to agree by both sides
/// independently making the same mistake.
///
/// A concrete instantiation catches what a symbolic proof alone cannot: a
/// transposed argument, a swapped `x`/`1-x`, or a leaf-bound witness that
/// silently does not line up with the one `geomCauchyOfLtOrdered`'s own
/// derivation expects. If this test fails, that mismatch — not the symbolic
/// derivation above — is the most valuable finding this file can report.
#[test]
fn geom_cauchy_of_lt_matches_geom_cauchy_at_half() {
    use super::exponential::{geom_half_a_real_pos_bound, half, half_add_half_equiv_one, half_rat};
    use crate::int_prelude::ops::IntDev;
    use crate::rat_prelude::ops::{rlt, rzero};

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();

    // Fetch `geomCauchy`'s OWN stored type before `d` borrows `kernel`
    // mutably -- the strongest form of this check compares against the type
    // the base-1/2 route already proved, not a type reconstructed by hand.
    let expected_ty = match kernel
        .environment()
        .get(p.geom_cauchy)
        .expect("CReal.geomCauchy must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("CReal.geomCauchy is {other:?}, not a Theorem"),
    };

    let mut d = IntDev::new(&mut kernel, rat.int);

    let h = half(&mut d, p);
    let hr = half_rat(&mut d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let one_nat = d.num(1);

    // hx0 : le zero half, via `Rat.zero_le_natDivSucc 1 1` and `CReal.of_rat_le`
    // -- the same route `exponential.rs::half_nonneg_proof` uses (private
    // there; reproduced here rather than widened, since it is one line).
    let hx0 = {
        let zero_rat = rzero(&mut d, rat);
        let half_le_zero = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, one_nat]);
        d.lemma(p.of_rat_le, &[zero_rat, hr, half_le_zero])
    };

    // hlt : lt half one, via the rational gap q := half_rat -- `0 < 1/2` and
    // `half + half <= one` (from `half_add_half_equiv_one`, widened this
    // session).
    let hlt = {
        let zero_rat = rzero(&mut d, rat);
        let one_le_one = d.lemma(rat.int.nat.le_refl, &[one_nat]);
        let positive = d.lemma(rat.nat_div_succ_pos, &[one_nat, one_nat, one_le_one]);
        let positive_ty = rlt(&mut d, rat, zero_rat, hr);

        let hh = super::cadd(&mut d, p, h, h);
        let hh_equiv_one = half_add_half_equiv_one(&mut d, p);
        let bounded = d.lemma(p.le_of_equiv, &[hh, one_c, hh_equiv_one]);
        let bounded_ty = super::cle(&mut d, p, hh, one_c);

        let pair = super::and_intro(&mut d, p, positive_ty, bounded_ty, positive, bounded);
        super::gap_intro(&mut d, p, h, one_c, hr, pair)
    };

    // (k, h) := (1, PosBound (1 - half) 1) -- `geom_half_a_real_pos_bound`
    // builds the IDENTICAL construction `geomHalfInvLeafBound`'s own `h_pos_a_real`
    // uses internally (its doc comment says so explicitly), so this is the
    // same witness the base-1/2 route is built from, not a fresh one.
    let (_a_real, h_pos_a_real) = geom_half_a_real_pos_bound(&mut d, p);

    let result = d.lemma(p.geom_cauchy_of_lt, &[h, hx0, hlt, one_nat, h_pos_a_real]);

    let name = d
        .kernel()
        .name_str(anon, "Check.geom_cauchy_of_lt_matches_geom_cauchy_at_half");
    let outcome = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: expected_ty,
        value: result,
    });
    assert!(
        outcome.is_ok(),
        "CReal.geomCauchyOfLt at x := half, with geomCauchy's own base-1/2 \
         witnesses (k := 1, h := geom_half_a_real_pos_bound), must check \
         against CReal.geomCauchy's OWN stored type -- a mismatch here means \
         the general and base-1/2 routes disagree about what they are \
         proving: {outcome:?}"
    );
}

/// The negative control for the cross-check above: the **same script**, with
/// `hx0`/`hlt` swapped at the `geomCauchyOfLt` call site. `hx0`'s type (`le
/// zero half`) and `hlt`'s type (`lt half one`) are unrelated Props -- one is
/// a `le`-application, the other an `Exists`-application over a rational gap
/// -- so a checker that is actually reading argument TYPES, rather than
/// merely counting positional arguments, must refuse this.
#[test]
fn the_half_cross_check_route_cannot_swap_hx0_and_hlt() {
    use super::exponential::{geom_half_a_real_pos_bound, half, half_add_half_equiv_one, half_rat};
    use crate::int_prelude::ops::IntDev;
    use crate::rat_prelude::ops::{rlt, rzero};

    let (mut kernel, p) = built();
    let rat = p.rat;

    let expected_ty = match kernel
        .environment()
        .get(p.geom_cauchy)
        .expect("CReal.geomCauchy must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("CReal.geomCauchy is {other:?}, not a Theorem"),
    };

    let mut d = IntDev::new(&mut kernel, rat.int);
    let anon = d.kernel().anon();

    let h = half(&mut d, p);
    let hr = half_rat(&mut d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let one_nat = d.num(1);

    let hx0 = {
        let zero_rat = rzero(&mut d, rat);
        let half_le_zero = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, one_nat]);
        d.lemma(p.of_rat_le, &[zero_rat, hr, half_le_zero])
    };

    let hlt = {
        let zero_rat = rzero(&mut d, rat);
        let one_le_one = d.lemma(rat.int.nat.le_refl, &[one_nat]);
        let positive = d.lemma(rat.nat_div_succ_pos, &[one_nat, one_nat, one_le_one]);
        let positive_ty = rlt(&mut d, rat, zero_rat, hr);

        let hh = super::cadd(&mut d, p, h, h);
        let hh_equiv_one = half_add_half_equiv_one(&mut d, p);
        let bounded = d.lemma(p.le_of_equiv, &[hh, one_c, hh_equiv_one]);
        let bounded_ty = super::cle(&mut d, p, hh, one_c);

        let pair = super::and_intro(&mut d, p, positive_ty, bounded_ty, positive, bounded);
        super::gap_intro(&mut d, p, h, one_c, hr, pair)
    };

    let (_a_real, h_pos_a_real) = geom_half_a_real_pos_bound(&mut d, p);

    // The one changed thing: `hlt` and `hx0` swapped at the call site.
    let value = d.lemma(p.geom_cauchy_of_lt, &[h, hlt, hx0, one_nat, h_pos_a_real]);

    let name = d
        .kernel()
        .name_str(anon, "__half_cross_check_hx0_hlt_swapped");
    let outcome = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: expected_ty,
        value,
    });
    assert!(
        outcome.is_err(),
        "swapping hx0/hlt at the geomCauchyOfLt call site must be REFUSED by \
         the trusted checker -- it was accepted, which means argument \
         positions are not actually being type-checked: {outcome:?}"
    );
}

/// **The composition control for the raw-witness family.**
/// `CReal.geomCauchyOrderedOfGap` is the entry point that makes a raw,
/// non-existential ordered geometric Cauchy witness reachable at an arbitrary
/// ratio. This eta-applies it to its OWN binders and checks the closed term
/// against its OWN stored type — so the positive half cannot pass by this test
/// and the declaration both reconstructing the same wrong statement.
///
/// Its negative half is in the same function on purpose: the identical term
/// with `hq` and the `PosBound (ofRat q) k3` argument transposed must be
/// REFUSED. Those are unrelated Props (`le (add x (ofRat q)) one` versus
/// `PosBound (ofRat q) k3`), so a checker that merely counted positional
/// arguments would accept both.
///
/// SYMBOLIC on purpose — see
/// `geometric::geom_cauchy_ordered_of_gap_self_application`. The concrete
/// counterpart is the ratio control below.
#[test]
fn geom_cauchy_ordered_of_gap_type_checks_at_its_own_binders() {
    on_a_deep_stack(geom_cauchy_ordered_of_gap_type_checks_at_its_own_binders_body);
}

fn geom_cauchy_ordered_of_gap_type_checks_at_its_own_binders_body() {
    use super::geometric::geom_cauchy_ordered_of_gap_self_application;
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();

    let expected_ty = match kernel
        .environment()
        .get(p.geom_cauchy_ordered_of_gap)
        .expect("CReal.geomCauchyOrderedOfGap must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("CReal.geomCauchyOrderedOfGap is {other:?}, not a Theorem"),
    };

    let mut d = IntDev::new(&mut kernel, rat.int);

    let good = geom_cauchy_ordered_of_gap_self_application(&mut d, p, false);
    let name_ok = d
        .kernel()
        .name_str(anon, "Check.geom_cauchy_ordered_of_gap_eta");
    let accepted = d.kernel().add_declaration(Declaration::Theorem {
        name: name_ok,
        uparams: vec![],
        ty: expected_ty,
        value: good,
    });
    assert!(
        accepted.is_ok(),
        "geomCauchyOrderedOfGap applied to its own binders must check against \
         its OWN stored type: {accepted:?}"
    );

    let bad = geom_cauchy_ordered_of_gap_self_application(&mut d, p, true);
    let name_bad = d
        .kernel()
        .name_str(anon, "__geom_cauchy_ordered_of_gap_hq_pos_bound_swapped");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name: name_bad,
        uparams: vec![],
        ty: expected_ty,
        value: bad,
    });
    assert!(
        refused.is_err(),
        "transposing `hq` and the `PosBound (ofRat q) k3` argument at the \
         geomCauchyOrderedOfGap call site must be REFUSED -- it was accepted, \
         so those hypothesis positions are not being type-checked: {refused:?}"
    );
}

/// **The ratio control.** `16/25` was chosen over the `9/16` the surrounding
/// notes once suggested for two reasons, and this test pins the second one:
/// `16/25` is a ratio at which a transposed numerator/denominator is
/// *genuinely false*, so a negative control here cannot be vacuous the way
/// one at `1/2` would be (`natDivSucc 1 1` transposes to itself).
///
/// The leg under test is the identity `x + q = 1` that
/// `geometric::ratio_16_over_25_witnesses` needs. At `(16, 9, 24)` — i.e.
/// `16/25 + 9/25 = 25/25 = 1` — it must be ACCEPTED. Transposing numerator
/// and denominator index to `(24, 9, 16)` gives `24/17 + 9/17 = 33/17`, which
/// is not `1`; and `24/17 > 1`, so the geometric series at that ratio
/// *diverges* and the theorem the witness feeds is false rather than merely
/// unproved by this route. The kernel must refuse it.
///
/// Both halves run the same three-line script with only the numerals
/// changed, so the negative half cannot pass for want of a term the positive
/// half also lacks.
#[test]
fn the_gap_identity_holds_at_16_over_25_and_fails_at_the_transposed_ratio() {
    on_a_deep_stack(the_gap_identity_holds_at_16_over_25_and_fails_at_the_transposed_ratio_body);
}

fn the_gap_identity_holds_at_16_over_25_and_fails_at_the_transposed_ratio_body() {
    use super::geometric::nat_div_succ_succ_self_eq_one;
    use crate::int_prelude::ops::IntDev;
    use crate::rat_prelude::ops::{radd, req, rone, rtrans};

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);

    // `(numerator of x, numerator of q, denominator index)`; the second row
    // is the first with the `16` and the `24` transposed.
    let cases = [((16u32, 9u32, 24u32), true), ((24, 9, 16), false)];

    for ((nx, nq, den), should_hold) in cases {
        let n_x = d.num(nx);
        let n_q = d.num(nq);
        let n_d = d.num(den);
        let x_rat = d.const_app(rat.nat_div_succ, &[n_x, n_d]);
        let q_rat = d.const_app(rat.nat_div_succ, &[n_q, n_d]);
        let sum_rat = radd(&mut d, x_rat, q_rat);
        let one_r = rone(&mut d, rat);

        let add_eq = d.lemma(rat.nat_div_succ_add, &[n_x, n_q, n_d]);
        let succ_d = d.succ(n_d);
        let mid_rat = d.const_app(rat.nat_div_succ, &[succ_d, n_d]);
        let self_one = nat_div_succ_succ_self_eq_one(&mut d, p, n_d);
        let value = rtrans(&mut d, sum_rat, mid_rat, one_r, add_eq, self_one);
        let ty = req(&mut d, sum_rat, one_r);

        let label = format!("Check.gap_identity_{nx}_{nq}_{den}");
        let name = d.kernel().name_str(anon, &label);
        let outcome = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert_eq!(
            outcome.is_ok(),
            should_hold,
            "natDivSucc {nx} {den} + natDivSucc {nq} {den} = 1 should be \
             {should_hold} (numerators must sum to den+1); the kernel said \
             {outcome:?}"
        );
    }
}

/// `CReal.crossingSampleUpper`/`CReal.crossingSampleLower` APPLY at the SAME
/// concrete `(a, c, delta) := (0, 5/2, 1)` worked example as
/// `crossing_index_at_zero_one_five_halves_reduces_to_two` above (where
/// `crossingIndex` reduces to the literal `2`), with `0 < delta`/`a ≤ c` left
/// as FRESH free variables — mirroring `integral.rs`'s own
/// `le_add_of_abs_sub_le_applies_at_three_two_and_one` idiom: this is a
/// concrete-ARGUMENT check (`CReal.le` is not decidable by `refl`, so the
/// hypothesis proofs cannot be filled in), not a claim that the inequality
/// itself is verified numerically. It confirms the two theorems apply at
/// real numeric arguments and that their conclusions' shapes — reconstructed
/// here independently, using ONLY public `CRealPrelude`/`RatPrelude` fields,
/// never `crossing.rs`'s own private helpers — match what
/// `declare_crossing_sample_upper`/`declare_crossing_sample_lower` actually
/// build.
#[test]
fn crossing_sample_upper_and_lower_apply_at_zero_five_halves_one() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let a = d.kernel().const_(p.zero, vec![]);
    let five = d.num(5);
    let one_idx = d.num(1);
    let five_halves = d.const_app(p.rat.nat_div_succ, &[five, one_idx]); // 5/2
    let c = d.const_app(p.of_rat, &[five_halves]);
    let delta = crate::rat_prelude::ops::rone(&mut d, p.rat);

    let zero_rat = crate::rat_prelude::ops::rzero(&mut d, p.rat);
    let hpos_ty = d.const_app(p.rat.lt, &[zero_rat, delta]);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);
    let hac_ty = d.const_app(p.le, &[a, c]);
    let hac_fv = d.fresh_fvar();
    let hac = d.kernel().fvar(hac_fv);

    // Reconstruct the shared pieces `declare_crossing_sample_upper`/
    // `declare_crossing_sample_lower` build internally, at these SAME
    // concrete arguments -- deliberately left as `crossingIndex a c delta`
    // rather than forced down to the literal `2` (a SEPARATE test above
    // already pins that reduction); this test's own job is the SHAPE of the
    // sample-point conclusion, not re-proving the index computation.
    let i0 = d.const_app(p.crossing.crossing_index, &[a, c, delta]);
    let delta_embed = d.const_app(p.of_rat, &[delta]);
    let of_nat_i0 = d.const_app(p.of_nat, &[i0]);
    let sample_term = d.const_app(p.mul, &[of_nat_i0, delta_embed]);
    let sample_point = d.const_app(p.add, &[a, sample_term]);

    let zero_nat_for_j = d.num(0);
    let k1 = d.succ(zero_nat_for_j);
    let j = NatOps::mul(&mut d, k1, k1);
    let two_nat = d.num(2);
    let bound2j = d.const_app(p.rat.nat_div_succ, &[two_nat, j]);
    let embed_bound2j = d.const_app(p.of_rat, &[bound2j]);
    let bound2j_term = d.const_app(p.mul, &[delta_embed, embed_bound2j]);
    let slack_upper = d.const_app(p.add, &[delta_embed, bound2j_term]);
    let target_upper = d.const_app(p.add, &[sample_point, slack_upper]);
    let expected_upper = d.const_app(p.le, &[c, target_upper]);

    let three_nat = d.num(3);
    let bound3j = d.const_app(p.rat.nat_div_succ, &[three_nat, j]);
    let neg_bound3j = crate::rat_prelude::ops::rneg(&mut d, bound3j);
    let embed_neg_bound3j = d.const_app(p.of_rat, &[neg_bound3j]);
    let slack_lower = d.const_app(p.mul, &[delta_embed, embed_neg_bound3j]);
    let target_lower = d.const_app(p.add, &[sample_point, slack_lower]);
    let expected_lower = d.const_app(p.le, &[target_lower, c]);

    let applied_upper = d.const_app(p.crossing.crossing_sample_upper, &[a, c, delta, hpos]);
    let applied_lower = d.const_app(p.crossing.crossing_sample_lower, &[a, c, delta, hpos, hac]);

    let ty_upper = d.arrow(hpos_ty, expected_upper);
    let value_upper = d.lam_fv(hpos_fv, hpos_ty, applied_upper);
    let anon = d.kernel().anon();
    let name_upper = d
        .kernel()
        .name_str(anon, "crossingSampleUpperZeroFiveHalvesOneSmoke");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name: name_upper,
            uparams: vec![],
            ty: ty_upper,
            value: value_upper,
        })
        .unwrap_or_else(|error| panic!("crossingSampleUpper must apply at (0, 5/2, 1): {error:?}"));

    let ty_lower = {
        let with_hac = d.arrow(hac_ty, expected_lower);
        d.arrow(hpos_ty, with_hac)
    };
    let value_lower = {
        let with_hac = d.lam_fv(hac_fv, hac_ty, applied_lower);
        d.lam_fv(hpos_fv, hpos_ty, with_hac)
    };
    let name_lower = d
        .kernel()
        .name_str(anon, "crossingSampleLowerZeroFiveHalvesOneSmoke");
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name: name_lower,
            uparams: vec![],
            ty: ty_lower,
            value: value_lower,
        })
        .unwrap_or_else(|error| panic!("crossingSampleLower must apply at (0, 5/2, 1): {error:?}"));
}

// ---------------------------------------------------------------------------
// `creal/polynomial.rs` concrete-instantiation corroboration.
//
// Every homomorphism `creal/polynomial.rs` proves is proved SYMBOLICALLY,
// over free variables. These tests instantiate at CONCRETE, DISTINCT closed
// `CReal` terms (`one` and `two := add one one`, never two copies of the
// same constant) and re-declare the instantiated statement as a fresh
// `Theorem`, forcing the kernel to independently re-check that specific
// instantiation rather than trusting that a universally-quantified
// statement that type-checks is the statement intended -- mirroring
// `complex_tests.rs::poly_eval_poly_add_concrete_instantiation`'s own
// discipline exactly.
// ---------------------------------------------------------------------------

/// `CReal.polyEval_polyAdd` at `c := fun _ => one`, `g := fun _ => two`,
/// `n := 2`, `x := one` -- two DISTINCT constant coefficient functions, not
/// two copies of the same constant, so a `c`/`g` swap in the production code
/// would produce a term that does not match this independently-built
/// expected type (`add` is not *definitionally* commutative here, only
/// `CReal.add_comm`-provably so).
#[test]
fn poly_eval_poly_add_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);

    let nat = d.nat_ty();
    let one_c = d.kernel().const_(p.one, vec![]);
    let two_c = d.const_app(p.add, &[one_c, one_c]);

    let c_i_fv = d.fresh_fvar();
    let c = d.lam_fv(c_i_fv, nat, one_c);
    let g_i_fv = d.fresh_fvar();
    let g = d.lam_fv(g_i_fv, nat, two_c);

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);
    let x = one_c;

    // Equiv (polyEval (polyAdd c g) 2 one) (add (polyEval c 2 one) (polyEval g 2 one)).
    let proof = d.lemma(p.polynomial.poly_eval_poly_add, &[c, g, two_n, x]);

    let poly_add_cg = d.const_app(p.polynomial.poly_add, &[c, g]);
    let lhs_stmt = d.const_app(p.polynomial.poly_eval, &[poly_add_cg, two_n, x]);
    let eval_c = d.const_app(p.polynomial.poly_eval, &[c, two_n, x]);
    let eval_g = d.const_app(p.polynomial.poly_eval, &[g, two_n, x]);
    let rhs_stmt = d.const_app(p.add, &[eval_c, eval_g]);
    let ty = super::equiv(&mut d, p, lhs_stmt, rhs_stmt);

    let name = d
        .kernel()
        .name_str(anon, "Check.poly_eval_poly_add_concrete");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: proof,
    });
    assert!(
        admitted.is_ok(),
        "polyEval_polyAdd at (c := const one, g := const two, n := 2, x := one) \
         must give EXACTLY Equiv (polyEval (polyAdd c g) 2 one) \
         (add (polyEval c 2 one) (polyEval g 2 one)): {admitted:?}"
    );
}

/// `CReal.polyEval_polyScale` at a scalar `a := two` distinct from the
/// constant coefficient function `c := fun _ => one`.
#[test]
fn poly_eval_poly_scale_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);

    let nat = d.nat_ty();
    let one_c = d.kernel().const_(p.one, vec![]);
    let two_c = d.const_app(p.add, &[one_c, one_c]);

    let a = two_c;
    let c_i_fv = d.fresh_fvar();
    let c = d.lam_fv(c_i_fv, nat, one_c);

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);
    let x = one_c;

    // Equiv (polyEval (polyScale two c) 2 one) (mul two (polyEval c 2 one)).
    let proof = d.lemma(p.polynomial.poly_eval_poly_scale, &[a, c, two_n, x]);

    let poly_scale_ac = d.const_app(p.polynomial.poly_scale, &[a, c]);
    let lhs_stmt = d.const_app(p.polynomial.poly_eval, &[poly_scale_ac, two_n, x]);
    let eval_c = d.const_app(p.polynomial.poly_eval, &[c, two_n, x]);
    let rhs_stmt = d.const_app(p.mul, &[a, eval_c]);
    let ty = super::equiv(&mut d, p, lhs_stmt, rhs_stmt);

    let name = d
        .kernel()
        .name_str(anon, "Check.poly_eval_poly_scale_concrete");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: proof,
    });
    assert!(
        admitted.is_ok(),
        "polyEval_polyScale at (a := two, c := const one, n := 2, x := one) \
         must give EXACTLY Equiv (polyEval (polyScale a c) 2 one) \
         (mul a (polyEval c 2 one)): {admitted:?}"
    );
}

/// Negative control for `CReal.polyEval_polyAdd`: its proof must NOT
/// type-check against a `mul`-shaped conclusion (`mul (polyEval c n x)
/// (polyEval g n x)` in place of `add (...) (...)`) -- otherwise the
/// homomorphism statement would be too weak to distinguish `polyAdd`'s
/// evaluation behaviour from `polyScale`'s, or from no homomorphism at all.
#[test]
fn poly_eval_poly_add_would_reject_mul_instead_of_add() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let rat = p.rat;
    let mut d = IntDev::new(&mut kernel, rat.int);

    let nat = d.nat_ty();
    let one_c = d.kernel().const_(p.one, vec![]);
    let two_c = d.const_app(p.add, &[one_c, one_c]);

    let c_i_fv = d.fresh_fvar();
    let c = d.lam_fv(c_i_fv, nat, one_c);
    let g_i_fv = d.fresh_fvar();
    let g = d.lam_fv(g_i_fv, nat, two_c);

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);
    let x = one_c;

    let proof = d.lemma(p.polynomial.poly_eval_poly_add, &[c, g, two_n, x]);

    let poly_add_cg = d.const_app(p.polynomial.poly_add, &[c, g]);
    let lhs_stmt = d.const_app(p.polynomial.poly_eval, &[poly_add_cg, two_n, x]);
    let eval_c = d.const_app(p.polynomial.poly_eval, &[c, two_n, x]);
    let eval_g = d.const_app(p.polynomial.poly_eval, &[g, two_n, x]);
    let wrong_rhs = d.const_app(p.mul, &[eval_c, eval_g]);
    let wrong_ty = super::equiv(&mut d, p, lhs_stmt, wrong_rhs);

    let anon = d.kernel().anon();
    let name = d
        .kernel()
        .name_str(anon, "Check.poly_eval_poly_add_wrong_mul");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: wrong_ty,
        value: proof,
    });
    assert!(
        admitted.is_err(),
        "polyEval_polyAdd's proof must NOT type-check against a `mul`-shaped \
         conclusion: {admitted:?}"
    );
}

/// `CReal.uniform_converges_add` at a GENUINELY non-degenerate pair: `F n x
/// := x` (via `uniform_converges_id`, instantiated at `[0, 1]`) and `H n x
/// := x * (1/2)^n` (via `uniform_converges_geom_half`, already at `[0, 1]`)
/// -- two structurally DIFFERENT sequences (at `n = 0`, `F 0 x = x` while `H
/// 0 x = x * 1`, and they diverge at every later `n`), converging to two
/// DIFFERENT limits (`id` vs. the constant `0`). This is deliberately NOT
/// the `F = H` case: a lane's own prior control accidentally picked an
/// index where both sides were the same term, and this instance avoids that
/// by construction (`seq_identity` and `geom_half`'s own `seq_fn` have no
/// shared head symbol).
#[test]
fn uniform_converges_add_applies_to_id_plus_geom_half() {
    use super::exponential::half;
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = super::creal_ty(&mut d, p);
    let nat = d.nat_ty();

    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    // seq_identity := fun n x => x, identity := fun x => x (the witness
    // `uniform_converges_id` uses internally).
    let seq_identity = {
        let n_fv = d.fresh_fvar();
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let inner = d.lam_fv(x_fv, carrier, x);
        d.lam_fv(n_fv, nat, inner)
    };
    let identity = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        d.lam_fv(x_fv, carrier, x)
    };

    // seq_geom := fun n x => x * half^n, const_zero := fun x => zero (the
    // witness `uniform_converges_geom_half` uses internally).
    let half = half(&mut d, p);
    let seq_geom = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let pow_half_n = d.const_app(p.pow, &[half, n]);
        let w = d.const_app(p.mul, &[x, pow_half_n]);
        let inner = d.lam_fv(x_fv, carrier, w);
        d.lam_fv(n_fv, nat, inner)
    };
    let const_zero = {
        let x_fv = d.fresh_fvar();
        d.lam_fv(x_fv, carrier, zero)
    };

    let hu1 = d.lemma(p.uniform_converges_id, &[zero, one]);
    let hu2 = d.kernel().const_(p.uniform_converges_geom_half, vec![]);

    let instance = d.lemma(
        p.uniform_converges_add,
        &[
            seq_identity,
            seq_geom,
            identity,
            const_zero,
            zero,
            one,
            hu1,
            hu2,
        ],
    );

    let inferred = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!("uniform_converges_add refused at id + geom_half: {error:?}")
    });

    let rendered = kernel.render_lean(inferred);
    assert!(
        rendered.contains("UniformConvergesOn"),
        "the instantiated conclusion is not a `UniformConvergesOn` fact: {rendered}"
    );
}

/// `CReal.uniform_converges_add` REFUSES an argument-position swap: passing
/// `uniform_converges_geom_half`'s witness where `uniform_converges_id`'s is
/// expected (both slots are `UniformConvergesOn _ _ zero one`, so the TYPES
/// only differ in which functions they name -- if this were accepted, it
/// would mean the two hypothesis slots are not actually checked against
/// their own `F, G` / `H, K` arguments).
#[test]
fn uniform_converges_add_cannot_swap_the_two_hypotheses() {
    use super::exponential::half;
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = super::creal_ty(&mut d, p);
    let nat = d.nat_ty();

    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    let seq_identity = {
        let n_fv = d.fresh_fvar();
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let inner = d.lam_fv(x_fv, carrier, x);
        d.lam_fv(n_fv, nat, inner)
    };
    let identity = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        d.lam_fv(x_fv, carrier, x)
    };

    let half = half(&mut d, p);
    let seq_geom = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let pow_half_n = d.const_app(p.pow, &[half, n]);
        let w = d.const_app(p.mul, &[x, pow_half_n]);
        let inner = d.lam_fv(x_fv, carrier, w);
        d.lam_fv(n_fv, nat, inner)
    };
    let const_zero = {
        let x_fv = d.fresh_fvar();
        d.lam_fv(x_fv, carrier, zero)
    };

    let hu1 = d.lemma(p.uniform_converges_id, &[zero, one]);
    let hu2 = d.kernel().const_(p.uniform_converges_geom_half, vec![]);

    // Swapped: `hu2` (about `seq_geom`/`const_zero`) passed where the FIRST
    // hypothesis (about `seq_identity`/`identity`) is required.
    let instance = d.lemma(
        p.uniform_converges_add,
        &[
            seq_identity,
            seq_geom,
            identity,
            const_zero,
            zero,
            one,
            hu2,
            hu1,
        ],
    );

    let outcome = d.kernel().infer(instance);
    assert!(
        outcome.is_err(),
        "uniform_converges_add accepted its two hypotheses SWAPPED -- \
         argument positions are not actually being type-checked: {outcome:?}"
    );
}

/// Concrete corroboration for the power-series domination package
/// ([`CRealPrelude::power_series_term_abs_le`]): the geometric series
/// itself, `c j := one`, at `M := abs one` (so the coefficient bound is
/// `le_refl` alone), `x := zero`, `r := one`, `j := 3` -- a genuinely
/// CONCRETE instantiation (a Nat literal `j`, not a bound `fvar`), which is
/// exactly where a transposed `x`/`r` or a wrong `mul_congr`/`abs_le` slot
/// would show up as a rejected proof rather than an opaque symbolic
/// mismatch (this file's own history: `powerSeriesTerm_congr`'s first
/// version passed the raw base points into `mul_congr`'s factor slots
/// instead of `pow pp j`/`pow qq j`, and only the kernel's own rejection
/// caught it -- a purely symbolic reading of the proof term looked fine).
#[test]
fn power_series_term_abs_le_applies_to_the_geometric_series_at_a_concrete_index() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();

    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    // c := fun _ => one -- the constant-one coefficient sequence, i.e. the
    // geometric series itself.
    let c = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, nat, one)
    };
    let m = d.const_app(p.abs, &[one]);

    // hbound : ∀ j, le (abs (c j)) m -- beta-reduces to `le (abs one) (abs
    // one)`, closed by `le_refl` alone.
    let hbound = {
        let j_fv = d.fresh_fvar();
        let abs_one = d.const_app(p.abs, &[one]);
        let body = d.lemma(p.le_refl, &[abs_one]);
        d.lam_fv(j_fv, nat, body)
    };

    let zlt1 = d.lemma(p.zero_lt_one, &[]);
    let hxr = d.lemma(p.le_of_lt, &[zero, one, zlt1]); // le zero one
    let hx0 = d.lemma(p.le_refl, &[zero]); // le zero zero

    let three = d.num(3);

    let instance = d.lemma(
        p.power_series_term_abs_le,
        &[c, m, hbound, zero, one, hx0, hxr, three],
    );

    let inferred = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!(
            "powerSeriesTerm_abs_le refused at the geometric series, x = 0, \
             r = 1, j = 3: {error:?}"
        )
    });

    let rendered = kernel.render_lean(inferred);
    assert!(
        rendered.contains("le") && rendered.contains("abs") && rendered.contains("pow"),
        "the instantiated conclusion does not look like a `pow`/`abs` bound: {rendered}"
    );
}

/// [`CRealPrelude::power_series_term_abs_le`] REFUSES its two order
/// hypotheses swapped: `hx0 : le zero x` and `hxr : le x r` are DIFFERENT
/// statements once `x != r` (here `le zero zero` vs. `le zero one`), so
/// passing each where the other is expected is a genuine type error, not
/// merely a relabelling -- if this were accepted, the two positions would
/// not actually be checked against their own `x`/`r`.
#[test]
fn power_series_term_abs_le_cannot_swap_the_order_hypotheses() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();

    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    let c = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, nat, one)
    };
    let m = d.const_app(p.abs, &[one]);
    let hbound = {
        let j_fv = d.fresh_fvar();
        let abs_one = d.const_app(p.abs, &[one]);
        let body = d.lemma(p.le_refl, &[abs_one]);
        d.lam_fv(j_fv, nat, body)
    };

    let zlt1 = d.lemma(p.zero_lt_one, &[]);
    let hxr = d.lemma(p.le_of_lt, &[zero, one, zlt1]); // le zero one
    let hx0 = d.lemma(p.le_refl, &[zero]); // le zero zero

    let three = d.num(3);

    // Swapped: `hxr` (`le zero one`) passed where `hx0 : le zero zero` is
    // expected, and vice versa.
    let instance = d.lemma(
        p.power_series_term_abs_le,
        &[c, m, hbound, zero, one, hxr, hx0, three],
    );

    let outcome = d.kernel().infer(instance);
    assert!(
        outcome.is_err(),
        "powerSeriesTerm_abs_le accepted its two order hypotheses SWAPPED: {outcome:?}"
    );
}

/// `CReal.close_within_of_within_indexed` at a GENUINELY TWO-INDEPENDENT-INDEX
/// instance: `x = y = z` (a generic, universally-quantified `CReal` — a fresh
/// fvar, not a concrete numeral, so this does not fall into the "concrete
/// instantiation hides the defeq bug a symbolic one exposes" trap), sampled
/// at two DISTINCT CONCRETE indices `i = 1`, `e = 2` (never `i = e`, which is
/// exactly the shared-index case `close_within_of_within` already covers and
/// would not exercise the generalization at all).
///
/// `hp := CReal.regular z 1 2 : Within (sub (seq z 1) (seq z 2)) (modulus 1
/// 2)` is `z`'s own regularity between those two indices — an EXISTING,
/// already-checked fact for an arbitrary `z`, not a hand-built trivial one,
/// so this genuinely exercises the two-index bridge rather than a degenerate
/// zero-diff shortcut. The theorem must then produce `le (abs (add z (neg
/// z))) (ofRat …)`, and the render must show a real `le`/`abs` conclusion,
/// not `True` or some other vacuous stand-in.
#[test]
fn close_within_of_within_indexed_specializes_to_one_reals_own_regularity_at_two_indices() {
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = super::creal_ty(&mut d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let one_idx = d.num(1);
    let two_idx = d.num(2);

    // hp : Within (sub (seq z 1) (seq z 2)) (modulus 1 2), z's OWN
    // regularity -- an existing fact about an arbitrary `z`, never assumed.
    let hp = d.lemma(p.regular, &[z, one_idx, two_idx]);

    // q must match `CRealPrelude::regular`'s own bound EXACTLY: `modulus 1
    // 2 = add (natDivSucc 1 1) (natDivSucc 1 2)`, built the identical way
    // `super::modulus` builds it, so the two calls intern to the same
    // `ExprId`.
    let q = {
        let one_nat = d.num(1);
        let m1 = d.const_app(p.rat.nat_div_succ, &[one_nat, one_idx]);
        let m2 = d.const_app(p.rat.nat_div_succ, &[one_nat, two_idx]);
        crate::rat_prelude::ops::radd(&mut d, m1, m2)
    };

    let instance = d.lemma(
        p.close_within_of_within_indexed,
        &[z, z, one_idx, two_idx, q, hp],
    );
    // `z` is a genuinely free `fvar`, unbound in `Kernel::infer`'s own fresh
    // `LocalContext` unless something actually BINDS it -- close over it with
    // a lambda so inference (which pushes the binder's own type while
    // traversing the `Lam`) can resolve `z`'s type.
    let closed_instance = d.lam_fv(z_fv, carrier, instance);

    let inferred = d.kernel().infer(closed_instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!(
            "close_within_of_within_indexed refused at z's own regularity \
             between two DISTINCT indices (1, 2): {error:?}"
        )
    });

    // A genuine negative control: swapping the two indices (`hp` built at
    // (1, 2) but applied as if the bridge's own `i, e` were (2, 1)) must be
    // REJECTED -- `hp`'s type would then mismatch the expected `Within (sub
    // (seq z 2) (seq z 1)) …` shape.
    let swapped = d.lemma(
        p.close_within_of_within_indexed,
        &[z, z, two_idx, one_idx, q, hp],
    );
    let closed_swapped = d.lam_fv(z_fv, carrier, swapped);
    let swapped_outcome = d.kernel().infer(closed_swapped);
    assert!(
        swapped_outcome.is_err(),
        "close_within_of_within_indexed accepted `hp` at the WRONG index order: {swapped_outcome:?}"
    );

    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("le") && rendered.contains("abs"),
        "the instantiated conclusion is not a genuine `le (abs …) …` bound: {rendered}"
    );
}

// ---------------------------------------------------------------------------
// STEPS build-order table (level 1 of the phase-order fix)
// ---------------------------------------------------------------------------
//
// Mirrors `complex_tests`'s own `order_violation_*`/`steps_table_matches_*`
// tests (the prototype: `docs/research/11-design-review/
// 2026-08-27-prelude-build-spike.md`), applied here to `creal.rs`'s own
// `STEPS`/`validate_step_order`/`BuildStep`.

/// The build order `STEPS` is generated from -- one label per top-level call
/// in `build_creal_prelude_uncached`'s existing sequence, extracted by static
/// analysis (see the module docs above `STEPS` in `creal.rs`). Pinned here so
/// a silent reorder or drop in `STEPS` fails naming which position changed,
/// rather than showing up as an opaque `Kernel::add_declaration` rejection
/// several steps later.
const EXPECTED_STEP_ORDER: &[&str] = &[
    "declare_predicates",
    "declare_carrier",
    "declare_projections",
    "declare_equiv",
    "declare_reflexivity",
    "declare_symmetry",
    "declare_transitivity",
    "declare_of_rat",
    "declare_discrimination",
    "declare_constants",
    "declare_pointwise",
    "declare_negation",
    "declare_addition",
    "declare_additive_laws",
    "declare_of_rat_add",
    "declare_of_rat_neg",
    "declare_of_rat_sub",
    "declare_order",
    "declare_neg_le_neg",
    "declare_strict_order",
    "order_extra::declare_order_extra",
    "product::declare_product",
    "algebra_instance::declare_comm_ring_s",
    "algebra_instance::declare_ordered_ring_s",
    "algebra_instance::declare_add_group_s",
    "field::declare_field",
    "inverse::declare_inverse",
    "cancellation::declare_cancellation",
    "lattice::declare_lattice",
    "product::declare_mul_self_abs",
    "order_extra::declare_order_extra_abs",
    "lattice::declare_lattice_extra",
    "uniform_convergence::declare_uniform_converges_on",
    "archimedean_squeeze::declare_archimedean_squeeze",
    "archimedean::declare_archimedean",
    "density::declare_density",
    "cotransitivity::declare_cotransitivity",
    "completeness::declare_completeness",
    "convergence::declare_convergence",
    "uniform_continuity::declare_abs_add_le",
    "uniform_continuity::declare_uniform_continuity",
    "uniform_continuity::declare_uniformly_continuous_on_restrict",
    "crossing::declare_crossing",
    "convergence::declare_converges_comp_eventually",
    "derivative::declare_derivative",
    "deriv_unique::declare_deriv_unique",
    "fermat::declare_fermat",
    "rolle::declare_rolle",
    "mvt::declare_mvt",
    "uniform_continuity::declare_uniform_continuity_products",
    "uniform_continuity::declare_bucket_close",
    "uniform_continuity::declare_abs_bound_of_self",
    "uniform_continuity::declare_bounded_of_uniformly_continuous",
    "mul_self_zero::declare_mul_self_zero",
    "crossing::declare_crossing_sample",
    "crossing::declare_crossing_close",
    "crossing::declare_crossing_close_clamped",
    "crossing::declare_crossing_sample_pairing_close",
    "sqrt::declare_sqrt",
    "speedup::declare_speedup",
    "sqrt::declare_sqrt_approx_kregular",
    "sqrt::declare_sqrt_ctor",
    "sqrt::declare_sqrt_congr",
    "sqrt::declare_sqrt_le_sqrt",
    "sqrt::declare_sqrt_one",
    "sqrt::declare_sqrt_zero",
    "sqrt::declare_sqrt_sq",
    "sqrt::declare_sqrt_nonneg",
    "sqrt::declare_mul_self_sqrt",
    "sqrt::declare_sqrt_mul",
    "sqrt::declare_le_of_sq_le",
    "convergence::declare_cauchy_convergence",
    "series::declare_series",
    "uniform_continuity::declare_uniform_continuity_sums",
    "monotone::declare_monotone",
    "integral::declare_integral",
    "integral::declare_sum_range_double",
    "integral::declare_sum_range_reblock",
    "integral::declare_within_of_two_sided_le",
    "integral::declare_le_add_of_abs_sub_le",
    "integral::declare_two_sided_of_abs_sub_le",
    "uniform_convergence::declare_uniform_convergence_continuity",
    "uniform_convergence::declare_uniform_converges_add",
    "uniform_convergence::declare_close_within_of_within",
    "integral::declare_close_within_of_within_indexed",
    "uniform_convergence::declare_weierstrass_m_test",
    "integral::declare_of_nat_hom",
    "monotone::declare_monotone_of_nonneg_deriv_all",
    "derivative::declare_abs_diff_le_of_deriv_bound",
    "derivative::declare_lipschitz_of_deriv_bound",
    "derivative::declare_abs_diff_sub_le_of_deriv_bound",
    "uniform_convergence::declare_has_derivative_uniform_limit",
    "integral::declare_fine_sample_in_bounds",
    "integral::declare_fine_sample_close",
    "integral::declare_fine_block_sum_close",
    "integral::declare_mesh_reciprocal_mul",
    "integral::declare_equiv_abs_diff_le",
    "integral::declare_sample_point_reblock",
    "integral::declare_reblock_block_eq_fine_block_sum",
    "integral::declare_riemann_sum_reblock_close",
    "integral::declare_riemann_sum_cauchy",
    "integral::declare_shared_index_to_canonical",
    "integral::declare_riemann_sum_shared_accuracy_close",
    "integral::declare_riemann_sum_shared_accuracy_close_at",
    "integral::declare_riemann_sum_total_eps_le",
    "integral::declare_riemann_sum_deep_cauchy",
    "integral::declare_riemann_sum_deep_cauchy_folded",
    "integral::declare_riemann_sum_deep_cauchy_cross",
    "integral::declare_riemann_sum_deep_cauchy_cross_folded",
    "integral::declare_riemann_sum_add_cauchy_cross",
    "integral::declare_creal_integral",
    "integral::declare_integral_converges",
    "integral::declare_integral_const",
    "integral::declare_integral_witness_independent",
    "integral::declare_integral_add",
    "integral::declare_integral_le",
    "integral::declare_integral_scale",
    "integral::declare_riemann_sum_integral_close",
    "integral::declare_riemann_sum_split_exact",
    "integral::declare_riemann_sum_split_scale_invariant",
    "integral::declare_congr_of_uniformly_continuous",
    "integral::declare_riemann_sum_split_exact_of_uc",
    "integral::declare_integral_split",
    "integral::declare_split_point_approx",
    "integral::declare_integral_endpoint_close",
    "integral::declare_integral_split_arbitrary",
    "integral::declare_integral_abs_le",
    "integral::declare_ftc_estimates",
    "integral::declare_integral_eq_antideriv_diff",
    "integral::declare_integral_by_parts",
    "integral::declare_ftc_of_uc",
    "derivative::declare_has_derivative_integral_const",
    "inverse_fn::declare_order_reflect_of_pos_deriv",
    "monotone::declare_inverse_lipschitz_of_pos_deriv",
    "power::declare_power",
    "power::declare_power_series_term",
    "power::declare_power_series_term_congr",
    "derivative::declare_has_derivative_pow_two",
    "derivative::declare_has_derivative_pow",
    "geometric::declare_geometric",
    "power::declare_power_series_term_abs_le",
    "uniform_convergence::declare_power_series_uniform_converges",
    "uniform_convergence::declare_converges_of_abs_diff_le",
    "uniform_convergence::declare_uniform_converges_geom",
    "geometric::declare_geom_cauchy_of_lt_family",
    "exponential::declare_exponential",
    "exponential::declare_geom_cauchy_family",
    "exponential::declare_exp_convergence",
    "ratio_test::declare_geom_scaled_cauchy_of_lt",
    "ratio_test::declare_sum_range_ratio_test",
    "exponential::declare_e_family",
    "trig::declare_trig",
    "trig::declare_sin_trig",
    "cos_sign::declare_converges_upper_bound_shift",
    "alternating::declare_alternating",
    "cos_sign::declare_alternating_upper_bound_tail",
    "trig::declare_trig_alternating_bounds",
    "trig::declare_sin_trig_alternating_bounds",
    "ivt::declare_ivt",
    "inverse_fn::declare_ivt_exact_root_at",
    "polynomial::declare_polynomial",
    "congruence::declare_congruence_extras",
    "uniform_continuity::declare_bounded_on_id_zero_one",
    "extreme_value::declare_extreme_value",
    "ivt_boundary::declare_ivt_boundary",
    "lub_boundary::declare_lub_boundary",
    "omniscience::declare_omniscience",
    "trig_fn::declare_cos_fn_family",
    "trig_fn::declare_cos_fn_equiv_cos_one",
    "trig_fn::declare_cos_fn_wide_progress",
    "trig_fn::declare_cos_fn_wide",
    "trig_fn::declare_cos_fn_wide_uniformly_continuous",
    "trig_fn::declare_cos_fn_wide_at_one",
    "trig_fn::declare_has_derivative_on_restrict",
    "trig_fn::declare_sin_fn_term_family",
    "trig_fn::declare_sin_fn_dominant",
    "trig_fn::declare_sin_fn",
    "trig_fn::declare_sin_fn_uniformly_continuous",
    "trig_fn::declare_cos_fn_derivative",
    "trig_fn::declare_cos_fn_wide_derivative",
    "trig_fn::declare_sin_fn_lower_bound",
    "exp_fn::declare_exp_fn_family",
    "exp_fn::declare_exp_fn_equiv_e",
    "supremum::declare_max_range",
    "supremum::declare_max_range_transport",
    "supremum::declare_mesh_level_count",
    "supremum::declare_mesh_level_count_pow",
    "supremum::declare_mesh_level_count_ge_of_size",
    "supremum::declare_mesh_max",
    "supremum::declare_mesh_max_step_le",
    "supremum::declare_mesh_max_mono",
    "supremum::declare_exp_of_modulus",
    "supremum::declare_true_exp_of_modulus",
    "supremum::declare_true_exp_of_modulus_step_le",
    "supremum::declare_true_exp_of_modulus_mono",
    "supremum::declare_exp_of_modulus_le_true_exp_of_modulus",
    "supremum::declare_mesh_point_near_coarse",
    "supremum::declare_max_range_le_add_of_exists",
    "supremum::declare_mesh_max_le_add_of_step_close",
    "supremum::declare_mesh_max_le_add_of_modulus",
    "supremum::declare_sup_seq",
    "supremum::declare_sup_seq_cauchy",
    "supremum::declare_sup_on",
    "sup_laws::declare_max_range_attained_approx",
    "sup_laws::declare_sup_seq_le_shift",
    "sup_laws::declare_sup_on_approx_lub",
    "sup_laws::declare_sup_on_ub_at_sup_seq_point",
    "sup_laws::declare_step_family_locate",
    "sup_laws::declare_sup_on_ub_at_fine_mesh_point",
    "sup_laws::declare_sup_on_ub",
    "evt_row1::declare_evt_approx_max",
    "cos_sign::declare_cos_wide_tail_nonneg",
    "cos_sign::declare_cos_wide_tail_antitone",
    "cos_sign::declare_cos_wide_series_converges",
    "cos_sign::declare_cos_wide_nonpositive",
    "pi::declare_pi_family",
    // ADR-1627: `CReal.fieldS : AlgS.Field` and its four supports. Last,
    // because the existential inverse consumes `inverse`'s `mul_inv_cancel`,
    // `cotransitivity`'s `apart_cotrans` and `algebra_instance`'s
    // `commRingS`, and nothing consumes it.
    "field_setoid_instance::declare_field_s_all",
];

/// `STEPS` (the data-driven build order that replaced the hand-written call
/// sequence) reproduces that sequence exactly, in order. A silent reorder or
/// drop fails here, naming which position changed, rather than showing up as
/// an opaque `Kernel::add_declaration` rejection several steps later.
///
/// **What this pins changed when the builder started sorting.** The array
/// order is now only `plan_step_order`'s tie-break, so a REORDER no longer
/// changes what the kernel sees -- `planned_order_is_the_array_order_today`
/// is the test that would notice that. What this one still catches, and
/// nothing else does, is a step DROPPED from the table: a missing entry is
/// not a phase-order bug the planner can repair, it is a declaration that
/// never happens.
#[test]
fn steps_table_matches_recorded_extraction() {
    let labels: Vec<&str> = super::STEPS.iter().map(|s| s.label).collect();
    assert_eq!(
        labels.as_slice(),
        EXPECTED_STEP_ORDER,
        "STEPS no longer matches the recorded build order -- see \
         docs/research/11-design-review/2026-08-27-prelude-build-spike.md"
    );
}

/// The existing, hand-written build order is already a valid topological
/// order for the dependencies `STEPS` declares: every `requires` entry is
/// satisfied by a strictly earlier step. This is the level-2 question the
/// architecture review asks (§1) -- answered here structurally, without
/// reordering anything at runtime.
#[test]
fn existing_step_order_is_topologically_valid() {
    let (_, prelude) = built();
    let result = super::validate_step_order(prelude, super::STEPS);
    assert!(
        result.is_ok(),
        "the existing STEPS order should already be topologically valid, \
         found: {result:?}"
    );
}

/// The deliberate-failure control: a two-step order where the consumer comes
/// BEFORE its provider must be rejected, and the rejection must be precise --
/// naming the missing declaration, the step that would produce it, and both
/// steps' positions. This is what proves `validate_step_order` can actually
/// fail, not merely that it passes on the one order it has ever seen.
static BROKEN_ORDER: &[super::BuildStep] = &[
    super::BuildStep {
        label: "consumer_before_its_provider",
        requires: &[|p: CRealPrelude| p.equiv],
        provides: &[],
        run: super::declare_carrier, // never invoked; validate_step_order does not call `run`
    },
    super::BuildStep {
        label: "provider_after_its_consumer",
        requires: &[],
        provides: &[|p: CRealPrelude| p.equiv],
        run: super::declare_equiv, // never invoked; validate_step_order does not call `run`
    },
];

#[test]
fn order_violation_is_detected_and_precise() {
    let (_, prelude) = built();
    let violation = super::validate_step_order(prelude, BROKEN_ORDER)
        .expect_err("a consumer placed before its provider must be rejected");
    assert_eq!(violation.consumer_index, 0);
    assert_eq!(violation.consumer_label, "consumer_before_its_provider");
    assert_eq!(
        violation.missing, prelude.equiv,
        "must name the exact missing declaration, not merely that one is missing"
    );
    assert_eq!(
        violation.provider,
        Some((1, "provider_after_its_consumer")),
        "must name which step provides the missing declaration and at what position"
    );
}

/// A dependency table naming a declaration nothing in the order provides is a
/// bug in the table itself, not merely a misordering -- and must still be
/// reported precisely (`provider: None`), not panic or silently pass.
static INCOMPLETE_ORDER: &[super::BuildStep] = &[super::BuildStep {
    label: "requires_something_nobody_provides",
    requires: &[|p: CRealPrelude| p.equiv],
    provides: &[],
    run: super::declare_carrier, // never invoked
}];

#[test]
fn order_violation_reports_missing_provider_as_table_bug() {
    let (_, prelude) = built();
    let violation = super::validate_step_order(prelude, INCOMPLETE_ORDER)
        .expect_err("a requirement nobody provides must be rejected");
    assert_eq!(violation.consumer_index, 0);
    assert_eq!(violation.missing, prelude.equiv);
    assert_eq!(
        violation.provider, None,
        "no step in this table provides `equiv`, so provider must be None"
    );
}

/// `STEPS` with `consumer` lifted to `provider`'s position, addressed by LABEL.
///
/// By label and never by index: an index is right until someone adds a step
/// above it, and then the test silently permutes a different pair and keeps
/// passing.
///
/// A MOVE, not a swap, and the difference is the whole point. Swapping the two
/// also displaces every step between them relative to the provider, so the
/// resulting violation can be some third step's -- and here it is: the sibling
/// `integral::declare_riemann_sum_shared_accuracy_close` sits between them and
/// reads the same declaration through an edge the hand-written table DID name.
/// A swap therefore fires for a reason that has nothing to do with the omitted
/// edge, which is a control that looks rigorous and measures the wrong thing.
fn steps_with_consumer_lifted(consumer: &str, provider: &str) -> &'static [super::BuildStep] {
    let position = |label: &str| {
        super::STEPS
            .iter()
            .position(|s| s.label == label)
            .unwrap_or_else(|| panic!("no STEPS entry labelled '{label}'"))
    };
    let (from, to) = (position(consumer), position(provider));
    assert!(
        to < from,
        "the provider must currently precede the consumer, or there is nothing \
         to invert"
    );
    let mut permuted: Vec<super::BuildStep> = super::STEPS
        .iter()
        .map(|s| super::BuildStep {
            label: s.label,
            requires: s.requires,
            provides: s.provides,
            run: s.run,
        })
        .collect();
    let moved = permuted.remove(from);
    permuted.insert(to, moved);
    Box::leak(permuted.into_boxed_slice())
}

/// An inversion on an edge the HAND-WRITTEN table never named is refused.
///
/// This is the finding the generated table exists to close, pinned as a test
/// rather than as a paragraph. `integral::declare_riemann_sum_shared_accuracy_close_at`
/// reads `CReal.sharedIndexToCanonical`, declared two steps earlier by
/// `integral::declare_shared_index_to_canonical`. The hand-written table did
/// not name that edge -- it is one of the 977 it omitted -- so lifting the
/// consumer above its provider produced **zero** violations from
/// `validate_step_order` and then a bare `UnknownConst` from the kernel.
///
/// Reproducing the "before" half from history, since the old table is gone:
///
/// ```text
/// git show a503a9241:artifacts/refactor/creal-declare-deps.json
/// ```
///
/// carries each step's `declared_requires` (the hand-written table) beside its
/// `measured_requires`; replaying the same MOVE against the first gives 0
/// violations and against the second gives 1, naming
/// `CReal.sharedIndexToCanonical`. Measured 2026-09-01.
///
/// Note what this does NOT assert: that the build fails. It does not, because
/// `plan_step_order` now moves the step back -- which is the level-2 behaviour
/// and is checked by `planned_order_repairs_a_consumer_placed_before_its_provider`.
/// What changed here is that the edge is *visible* at all; without it in the
/// table the planner has nothing to repair.
#[test]
fn an_edge_the_hand_written_table_never_named_is_now_enforced() {
    let (kernel, prelude) = built();
    let permuted = steps_with_consumer_lifted(
        "integral::declare_riemann_sum_shared_accuracy_close_at",
        "integral::declare_shared_index_to_canonical",
    );
    let violation = super::validate_step_order(prelude, permuted)
        .expect_err("the level-1 preflight must reject this inversion");
    let missing = super::render_name(&kernel, violation.missing);
    assert_eq!(
        violation.consumer_label, "integral::declare_riemann_sum_shared_accuracy_close_at",
        "the violation must name the consumer, found {violation:?}"
    );
    assert_eq!(
        missing, "CReal.sharedIndexToCanonical",
        "the violation must name the edge the hand-written table omitted"
    );
    assert!(
        violation.provider.is_some(),
        "the edge has a provider in the table -- it is misordered, not absent: {violation:?}"
    );

    // The control, in the same test so it cannot rot separately: the
    // UNPERMUTED table is clean. Without it, a `validate_step_order` that
    // rejected everything would pass the assertions above.
    assert!(
        super::validate_step_order(prelude, super::STEPS).is_ok(),
        "control: the unpermuted table must validate, or the rejection above \
         says nothing about the swap"
    );
}

// ---------------------------------------------------------------------------
// `plan_step_order`: the build order is COMPUTED (level 2 of the phase-order
// fix, architecture review §1)
// ---------------------------------------------------------------------------

/// The plan is the array order, exactly, for `STEPS` as it stands.
///
/// This is the no-behaviour-change pin: the kernel must see the identical
/// sequence of `add_declaration` calls before and after the builder started
/// sorting. It holds because the array order is already valid and the
/// tie-break is the array index, so the lexicographically smallest valid
/// topological order IS the array order. If this ever fails, the build's
/// declaration ORDER changed and the projection must be re-diffed.
#[test]
fn planned_order_is_the_array_order_today() {
    let (_, prelude) = built();
    let plan = super::plan_step_order(prelude, super::STEPS)
        .expect("STEPS must be plannable: no duplicate provider, no cycle");
    let identity: Vec<usize> = (0..super::STEPS.len()).collect();
    assert_eq!(
        plan, identity,
        "the planned order must reproduce the array order byte-for-byte while \
         the array order is itself valid"
    );
}

/// A step placed BEFORE its provider is moved back, rather than aborting the
/// build.
///
/// This is the whole point of level 2, and it is the case level 1 could only
/// report. `BROKEN_ORDER` is the same fixture
/// `order_violation_is_detected_and_precise` uses to show
/// `validate_step_order` rejects it -- so the two tests together are the
/// before/after of one input.
#[test]
fn planned_order_repairs_a_consumer_placed_before_its_provider() {
    let (_, prelude) = built();
    assert!(
        super::validate_step_order(prelude, BROKEN_ORDER).is_err(),
        "precondition: the level-1 check must REJECT this order, or this test \
         proves nothing about the sort"
    );
    let plan = super::plan_step_order(prelude, BROKEN_ORDER)
        .expect("a mis-ordered but acyclic table must be plannable");
    assert_eq!(
        plan,
        vec![1, 0],
        "the provider (index 1) must be scheduled before its consumer (index 0)"
    );
}

/// A requirement nothing provides is still a table bug, reported precisely --
/// the sort must not silently drop the step or invent a provider.
#[test]
fn planned_order_reports_an_unprovided_requirement() {
    let (_, prelude) = built();
    let error = super::plan_step_order(prelude, INCOMPLETE_ORDER)
        .expect_err("a requirement nobody provides must be rejected");
    match error {
        super::PlanError::Order(violation) => {
            assert_eq!(violation.consumer_index, 0);
            assert_eq!(violation.missing, prelude.equiv);
            assert_eq!(violation.provider, None);
        }
        other @ super::PlanError::Duplicate(_) => {
            panic!("expected an order violation, got {other:?}")
        }
    }
}

/// Two steps claiming one declaration is unorderable, and must be named as a
/// TABLE bug rather than silently resolved to one of them.
///
/// This guard is why `mul_self_zero::declare_mul_self_zero` no longer claims
/// `p.seq` and `p.shared_index_to_canonical`: it declares neither, and the
/// false claim told `validate_step_order` that
/// `CReal.sharedIndexToCanonical` was available 48 steps before its real
/// provider (measured by `scripts/creal-declare-deps.py`, 2026-09-01).
static DUPLICATE_PROVIDER_ORDER: &[super::BuildStep] = &[
    super::BuildStep {
        label: "the_real_provider",
        requires: &[],
        provides: &[|p: CRealPrelude| p.equiv],
        run: super::declare_equiv, // never invoked; planning does not call `run`
    },
    super::BuildStep {
        label: "claims_what_it_does_not_declare",
        requires: &[],
        provides: &[|p: CRealPrelude| p.equiv],
        run: super::declare_carrier, // never invoked
    },
];

#[test]
fn duplicate_provider_is_reported_as_a_table_bug() {
    let (_, prelude) = built();
    let error = super::plan_step_order(prelude, DUPLICATE_PROVIDER_ORDER)
        .expect_err("two steps claiming one declaration must be rejected");
    match error {
        super::PlanError::Duplicate(duplicate) => {
            assert_eq!(duplicate.name, prelude.equiv);
            assert_eq!(duplicate.first, (0, "the_real_provider"));
            assert_eq!(duplicate.second, (1, "claims_what_it_does_not_declare"));
        }
        other @ super::PlanError::Order(_) => {
            panic!("expected a duplicate-provider error, got {other:?}")
        }
    }
}

/// `STEPS` itself has no duplicate provider -- the positive control for the
/// guard above, and the assertion that the two false claims stay deleted.
///
/// Derived from `STEPS`, never from a literal list, so it measures the table
/// rather than the maintainer's memory.
#[test]
fn every_steps_declaration_has_exactly_one_provider() {
    let (_, prelude) = built();
    let mut seen: std::collections::HashMap<crate::NameId, &'static str> =
        std::collections::HashMap::new();
    let mut duplicates: Vec<String> = Vec::new();
    for step in super::STEPS {
        for &provides in step.provides {
            let name = provides(prelude);
            if let Some(first) = seen.insert(name, step.label) {
                duplicates.push(format!("{first} and {}", step.label));
            }
        }
    }
    assert!(
        duplicates.is_empty(),
        "every STEPS declaration must have exactly one provider, found: \
         {duplicates:?}"
    );
}

/// A cycle is unorderable and must be reported as one -- not looped forever,
/// and not silently truncated to the steps that could be scheduled.
static CYCLIC_ORDER: &[super::BuildStep] = &[
    super::BuildStep {
        label: "needs_what_the_other_provides",
        requires: &[|p: CRealPrelude| p.equiv],
        provides: &[|p: CRealPrelude| p.creal],
        run: super::declare_carrier, // never invoked
    },
    super::BuildStep {
        label: "needs_what_the_first_provides",
        requires: &[|p: CRealPrelude| p.creal],
        provides: &[|p: CRealPrelude| p.equiv],
        run: super::declare_equiv, // never invoked
    },
];

#[test]
fn planned_order_reports_a_cycle_rather_than_dropping_steps() {
    let (_, prelude) = built();
    let error = super::plan_step_order(prelude, CYCLIC_ORDER)
        .expect_err("mutually dependent steps must be rejected");
    match error {
        super::PlanError::Order(violation) => {
            assert_eq!(violation.consumer_index, 0);
            assert_eq!(violation.missing, prelude.equiv);
            assert_eq!(
                violation.provider,
                Some((1, "needs_what_the_first_provides")),
                "must name the step that provides it and is itself blocked"
            );
        }
        other @ super::PlanError::Duplicate(_) => {
            panic!("expected an order violation, got {other:?}")
        }
    }
}

/// **Concrete corroboration for `CReal.maxRange`** — not `CReal.supOn`, which
/// this session did not land (see `creal/supremum.rs`'s own module
/// documentation for exactly why). `f i := ofNat (i · (2 − i))` over `i = 0,
/// 1, 2` takes values `0, 1, 0`: the maximum sits at the MIDDLE index, not
/// the last one, so a defect that returned `f n` (the last sampled term)
/// instead of the genuine running maximum would still pass a monotonically
/// increasing `f` and only fails here.
#[test]
fn max_range_finds_the_true_maximum_not_the_last_term() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();

    let f = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let two_nat = d.num(2);
        let diff = NatOps::sub(&mut d, two_nat, i);
        let prod = NatOps::mul(&mut d, i, diff);
        let val = d.const_app(p.of_nat, &[prod]);
        d.lam_fv(i_fv, nat, val)
    };

    let two = d.num(2);
    let mr = d.const_app(p.max_range, &[f, two]);
    let idx0 = d.zero();
    let got = d.const_app(p.seq, &[mr, idx0]);
    let expected_one = ivt_bisect_rat_lit(&mut d, p, 1, 0, false); // 1/(0+1) = 1
    assert!(
        ivt_bisect_rat_eq(&mut d, p, got, expected_one),
        "maxRange f 2 must reduce to 1 (the middle term's value), not 0 \
         (every other term's value)"
    );

    // Negative control: the LAST term alone is 0, not 1 -- confirms `1`
    // genuinely discriminates "true running maximum" from "last term".
    let two_nat2 = d.num(2);
    let last_only = d.apply(f, &[two_nat2]);
    let last_val = d.const_app(p.seq, &[last_only, idx0]);
    let expected_zero = ivt_bisect_rat_lit(&mut d, p, 0, 0, false);
    assert!(
        ivt_bisect_rat_eq(&mut d, p, last_val, expected_zero),
        "sanity: f(2) itself must be 0, or this test does not discriminate \
         a last-term defect from a genuine maximum"
    );
}

/// **`CReal.ivt_exact_root` is not vacuous.** Every hypothesis is discharged
/// at a concrete instance, so the theorem is about an inhabited situation
/// rather than an empty one.
///
/// `F := fun r => r` on `[0, 1]`, derivative `fun _ => one`, modulus index
/// `k := 0` (so the derivative bound reads `1/(0+1) <= 1`, discharged through
/// [`crate::CRealPrelude::rat_unit_eq_one`]). The root the theorem then
/// asserts to exist is `0`, and every hypothesis holds:
/// `hasDerivative_id`, `uniformly_continuous_id`, `le zero one` from
/// `zero_lt_one`, and `F 0 = 0 <= 0 <= 1 = F 1` by beta-reduction plus
/// `le_refl`.
///
/// The check is `Kernel::infer` on the closed application, the same method
/// [`sum_range_tail_within_specializes_to_the_zero_series_against_itself`]
/// uses: a hypothesis that could not be built, or one whose type did not
/// match, is a kernel rejection here rather than a green run. The rendered
/// conclusion is then asserted to mention `Equiv` -- the EXACT part of the
/// statement -- so an accidental weakening to `ivt_approx`'s `abs`-bound
/// form would fail this test rather than pass it.
#[test]
fn ivt_exact_root_is_inhabited_by_the_identity_on_the_unit_interval() {
    use crate::int_prelude::ops::IntDev;
    use crate::rat_prelude::ops::{rat_eq_rewrite, rone, rsymm};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    // `F := fun r => r`, `F' := fun _ => one` -- the two lambdas
    // `hasDerivative_id` itself names, up to alpha.
    let id_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let const_one = {
        let r_fv = d.fresh_fvar();
        let _r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, one_c)
    };

    let hf = d.lemma(p.has_derivative_id, &[zero_c, one_c]);
    let huc = d.lemma(p.uniformly_continuous_id, &[zero_c, one_c]);

    // `le zero one`, used for the interval and for `0 <= F 1`.
    let hz1 = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero_c, one_c, lt])
    };
    // `le (F 0) zero`: `(fun r => r) zero` beta-reduces to `zero`.
    let hfa = d.lemma(p.le_refl, &[zero_c]);

    let zero_nat = d.num(0);
    let one_nat = d.num(1);

    // `forall z, le zero z -> le z one -> le (ofRat (natDivSucc 1 0)) one`.
    let hderiv = {
        let unit_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let rat_one = rone(&mut d, p.rat);
        let eq = d.lemma(p.rat_unit_eq_one, &[]);
        let back = rsymm(&mut d, unit_rat, rat_one, eq);
        let base = d.lemma(p.le_refl, &[one_c]);
        let body = rat_eq_rewrite(&mut d, rat_one, unit_rat, back, base, &|d, t| {
            let ot = d.const_app(p.of_rat, &[t]);
            d.const_app(p.le, &[ot, one_c])
        });

        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let hlo_ty = d.const_app(p.le, &[zero_c, z]);
        let hlo_fv = d.fresh_fvar();
        let hhi_ty = d.const_app(p.le, &[z, one_c]);
        let hhi_fv = d.fresh_fvar();
        let over_hhi = d.lam_fv(hhi_fv, hhi_ty, body);
        let over_hlo = d.lam_fv(hlo_fv, hlo_ty, over_hhi);
        d.lam_fv(z_fv, carrier, over_hlo)
    };

    let instance = d.lemma(
        p.ivt_exact_root,
        &[
            id_fn, const_one, zero_c, one_c, hf, huc, hz1, hfa, hz1, zero_nat, hderiv,
        ],
    );

    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!(
            "ivt_exact_root refused at F = (fun r => r) on [0, 1] with k = 0 -- \
             the theorem's hypotheses are not jointly inhabitable as stated: {error:?}"
        )
    });

    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Exists"),
        "the instantiated conclusion is not an existential: {rendered}"
    );
    assert!(
        rendered.contains("Equiv"),
        "the instantiated conclusion does not assert an EXACT root -- a weakening \
         to an `abs`-bound would look like this: {rendered}"
    );
}

/// The two `cosFnWide`-at-`1` facts and the derivative restriction, pinned
/// against the STATEMENTS a π construction actually needs.
///
/// Both halves compare INTERNED TERMS this test builds itself, never a
/// rendered string and never a `Kernel::def_eq`. That is deliberate: the
/// natural negative control here is "`cosFnWide_one_nonneg` is not the
/// transposed `le (cosFnWide one) zero`", and asking the kernel to *refute*
/// that by `def_eq` would set a failing conversion loose on `cosFnWide`'s
/// whole `weierstrassMTest` definition against `zero` -- the unbounded shape
/// `CLAUDE.md`'s "a negative control must differ in a SMALL term" entry
/// records. Structural inequality of two interned ids is free and decides
/// exactly the question asked.
///
/// What each half would look like if it were vacuous, and why it is not:
/// the first would pass for `le (cosFnWide one) zero` (it does not -- that is
/// the `assert_ne!`), and the third would pass if `hasDerivativeOn_restrict`
/// returned its input unchanged (it does not -- that is the `assert_ne!`
/// against the ORIGINAL `[0, 8/5]` statement).
#[test]
fn cos_fn_wide_at_one_and_the_derivative_restriction_state_what_pi_needs() {
    use super::trig::{cle, czero, one_c};
    use super::trig_fn::{one_le_r_domain, unapp};
    use crate::int_prelude::ops::IntDev;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let zero_c = czero(&mut d, p);
    let one_cc = one_c(&mut d, p);
    let wide = d.kernel().const_(p.cos_fn_wide, vec![]);
    let wide_one = d.apply(wide, &[one_cc]);

    // --- `cos 1 >= 0`, for the wide FUNCTION -------------------------------
    let nonneg_c = d.kernel().const_(p.cos_fn_wide_one_nonneg, vec![]);
    let nonneg_ty = d
        .kernel()
        .infer(nonneg_c)
        .expect("CReal.cosFnWide_one_nonneg must infer");
    let expected = cle(&mut d, p, zero_c, wide_one);
    let transposed = cle(&mut d, p, wide_one, zero_c);
    assert_eq!(
        nonneg_ty, expected,
        "cosFnWide_one_nonneg does not state `le zero (cosFnWide one)` -- the \
         LEFT endpoint bound `ivt_exact_root` needs on [1, 8/5]"
    );
    assert_ne!(
        nonneg_ty, transposed,
        "cosFnWide_one_nonneg states the sign the WRONG way round"
    );

    // --- the equivalence that connects the function to `creal/trig.rs`'s
    //     constant, without which `cosOne_nonneg` says nothing about
    //     `cosFnWide` ------------------------------------------------------
    let equiv_c = d.kernel().const_(p.cos_fn_wide_one_equiv_cos_one, vec![]);
    let equiv_ty = d
        .kernel()
        .infer(equiv_c)
        .expect("CReal.cosFnWide_one_equiv_cosOne must infer");
    let cos_one_const = d.kernel().const_(p.cos_one, vec![]);
    let want_equiv = super::equiv(&mut d, p, wide_one, cos_one_const);
    assert_eq!(
        equiv_ty, want_equiv,
        "cosFnWide_one_equiv_cosOne does not relate `cosFnWide one` to `cosOne`"
    );

    // --- restricting cosine's own derivative to `[1, 8/5]` -----------------
    let hf = d.kernel().const_(p.cos_fn_wide_has_derivative, vec![]);
    let hf_ty = d
        .kernel()
        .infer(hf)
        .expect("CReal.cosFnWideHasDerivative must infer");
    let (inner1, b_u) = unapp(&mut d, hf_ty);
    let (inner2, a_u) = unapp(&mut d, inner1);
    let (inner3, fp_u) = unapp(&mut d, inner2);
    let (_, f_u) = unapp(&mut d, inner3);

    let hlo = {
        let lt = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero_c, one_cc, lt])
    };
    let hmid = one_le_r_domain(&mut d, p);
    let hhi = d.lemma(p.le_refl, &[b_u]);
    let restricted = d.lemma(
        p.has_derivative_on_restrict,
        &[f_u, fp_u, a_u, b_u, one_cc, b_u, hf, hlo, hmid, hhi],
    );
    let restricted_ty = d.kernel().infer(restricted).unwrap_or_else(|error| {
        panic!(
            "hasDerivativeOn_restrict refused cosine's own derivative narrowed \
             from [0, 8/5] to [1, 8/5] -- so the three hypotheses are not \
             jointly inhabitable at the interval a π construction uses: {error:?}"
        )
    });
    let want_restricted = d.const_app(p.has_derivative_on, &[f_u, fp_u, one_cc, b_u]);
    assert_eq!(
        restricted_ty, want_restricted,
        "the restricted witness is not `HasDerivativeOn F F' one (8/5)`"
    );
    assert_ne!(
        restricted_ty, hf_ty,
        "the restriction left the interval where it found it"
    );
}

/// The two general theorems π's rung 2 needs, pinned STRUCTURALLY.
///
/// Interned-id equality throughout, never `Kernel::def_eq`: a `def_eq`
/// refutation of a transposed `le` over `sumRange` sets a FAILING conversion
/// loose on the recursor with no early exit (measured elsewhere at >300 s and
/// 3.1 GB), and every distinction here is visible in the term.
///
/// Each negative control differs in a SMALL term — one transposed `le` in the
/// hypothesis, and `sumRange t 2` for `sumRange t 3` in the conclusion — never
/// by rebuilding an unrelated shape.
#[test]
fn the_eventual_upper_bound_and_the_tail_leibniz_bound_state_what_pi_rung_2_needs() {
    use super::convergence::converges_applied;
    use super::cos_sign::{build_t_lam, sum_at};
    use super::trig::{cle, czero};

    /// `∀ s f L b, (∀ n, le (f (add n s)) b) → Converges f L → le L b`, or, with
    /// `transposed`, the same shape with the hypothesis' `le` the wrong way
    /// round.
    fn upper_shift_ty(d: &mut IntDev<'_>, p: CRealPrelude, transposed: bool) -> ExprId {
        let nat = d.nat_ty();
        let carrier = super::creal_ty(d, p);
        let seq_ty = d.arrow(nat, carrier);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let hyp = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let shifted = NatOps::add(d, n, s);
            let f_at = d.apply(f, &[shifted]);
            let claim = if transposed {
                cle(d, p, b, f_at)
            } else {
                cle(d, p, f_at, b)
            };
            d.pi_fv(n_fv, nat, claim)
        };
        let conv = converges_applied(d, p, f, l);
        let target = cle(d, p, l, b);
        let after_conv = d.arrow(conv, target);
        let after_hyp = d.arrow(hyp, after_conv);
        let with_b = d.pi_fv(b_fv, carrier, after_hyp);
        let with_l = d.pi_fv(l_fv, carrier, with_b);
        let with_f = d.pi_fv(f_fv, seq_ty, with_l);
        d.pi_fv(s_fv, nat, with_f)
    }

    /// `∀ a, (∀ k, le zero (a k)) → (∀ k, le (a (succ (succ k))) (a (succ k)))
    /// → ∀ L, Converges (sumRange t) L → le L (sumRange t width)`.
    fn tail_bound_ty(d: &mut IntDev<'_>, p: CRealPrelude, width: u32) -> ExprId {
        let nat = d.nat_ty();
        let carrier = super::creal_ty(d, p);
        let fn_ty = d.arrow(nat, carrier);
        let a_fv = d.fresh_fvar();
        let a_fn = d.kernel().fvar(a_fv);
        let hnn_ty = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let zero_c = czero(d, p);
            let a_k = d.apply(a_fn, &[k]);
            let body = cle(d, p, zero_c, a_k);
            d.pi_fv(k_fv, nat, body)
        };
        let htail_ty = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sk = d.succ(k);
            let ssk = d.succ(sk);
            let a_ssk = d.apply(a_fn, &[ssk]);
            let a_sk = d.apply(a_fn, &[sk]);
            let body = cle(d, p, a_ssk, a_sk);
            d.pi_fv(k_fv, nat, body)
        };
        let t_lam = build_t_lam(d, p, a_fn);
        let f_expr = d.const_app(p.sum_range, &[t_lam]);
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let conv = converges_applied(d, p, f_expr, l);
        let idx = d.num(width);
        let bound = sum_at(d, p, t_lam, idx);
        let target = cle(d, p, l, bound);
        let after_conv = d.arrow(conv, target);
        let with_l = d.pi_fv(l_fv, carrier, after_conv);
        let with_htail = d.arrow(htail_ty, with_l);
        let with_hnn = d.arrow(hnn_ty, with_htail);
        d.pi_fv(a_fv, fn_ty, with_hnn)
    }

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    // --- the EVENTUAL upper bound `alternating.rs` says does not exist ------
    let shift_c = d
        .kernel()
        .const_(p.cos_sign.converges_upper_bound_shift, vec![]);
    let shift_ty = d
        .kernel()
        .infer(shift_c)
        .expect("CReal.converges_upper_bound_shift must infer");
    let want_shift = upper_shift_ty(&mut d, p, false);
    let transposed_shift = upper_shift_ty(&mut d, p, true);
    assert_eq!(
        shift_ty, want_shift,
        "converges_upper_bound_shift does not state the eventual UPPER bound \
         `(∀ n, le (f (add n s)) b) → Converges f L → le L b`"
    );
    assert_ne!(
        want_shift, transposed_shift,
        "the negative control is vacuous: the transposed hypothesis builds the \
         same term as the real one"
    );
    assert_ne!(
        shift_ty, transposed_shift,
        "converges_upper_bound_shift's hypothesis bounds the wrong side"
    );

    // --- the Leibniz bound needing antitonicity only from index 1 ----------
    let tail_c = d
        .kernel()
        .const_(p.cos_sign.alternating_upper_bound_tail, vec![]);
    let tail_ty = d
        .kernel()
        .infer(tail_c)
        .expect("CReal.alternatingUpperBoundTail must infer");
    let want_tail = tail_bound_ty(&mut d, p, 3);
    let narrower = tail_bound_ty(&mut d, p, 2);
    assert_eq!(
        tail_ty, want_tail,
        "alternatingUpperBoundTail does not state `le L (sumRange t 3)` under \
         the index-1 antitonicity `∀ k, le (a (succ (succ k))) (a (succ k))`"
    );
    assert_ne!(
        want_tail, narrower,
        "the negative control is vacuous: `sumRange t 2` builds the same term \
         as `sumRange t 3`"
    );
    assert_ne!(
        tail_ty, narrower,
        "alternatingUpperBoundTail bounds `L` by the wrong partial sum -- the \
         EVEN one `E 1`, which is a lower bound, not an upper one"
    );

    // The two are not each other: the tail bound must not have silently been
    // declared as the shift lemma's own statement.
    assert_ne!(
        tail_ty, shift_ty,
        "the two declarations carry the same statement"
    );
}

/// `CReal.converges_of_abs_diff_le` composes with `UniformConvergesOn.spec`
/// at a fixed point of the domain, with **no transport at all**.
///
/// The declaration itself is verified by `creal_prelude_builds` — the kernel
/// accepted its proof term or the prelude does not build. What that does NOT
/// establish, and what this lane's whole purpose rests on, is that the
/// hypothesis is the shape a real consumer HAS: `UniformConvergesOn.spec`
/// hands back `close_within (F n x) (G x) (natDivSucc rate n)` per `n`, and
/// `converges_of_abs_diff_le` wants `le (abs (add (f n) (neg L)))
/// (ofRat (natDivSucc K n))` at `f := fun n => F n x`, `L := G x`. Those
/// agree only up to β on `f n`, and only if `rate` may be supplied as the
/// `K` — neither of which is visible from the statement alone.
///
/// So this builds the composed term outright and READS ITS INFERRED TYPE. It
/// is a CLOSED term (every free variable is abstracted before inference), so
/// plain `Kernel::infer` applies — `Kernel::infer` builds a fresh, empty
/// local context and throws `UnboundFVar` on open ones.
///
/// Interned-id equality throughout, never `Kernel::def_eq`: a `def_eq`
/// refutation here would set a failing conversion loose on
/// `UniformConvergesOn`'s recursor with no early exit. The negative control
/// differs in a SMALL term — the single domain hypothesis `le a x` read the
/// wrong way round — not by rebuilding an unrelated shape.
#[test]
fn the_close_within_bridge_turns_uniform_convergence_into_converges_at_a_point() {
    use super::convergence::converges_applied;

    /// The composition's statement, or -- with `transposed` -- the same shape
    /// with the domain hypothesis `le a x` read the wrong way round.
    fn want_ty(d: &mut IntDev<'_>, p: CRealPrelude, transposed: bool) -> ExprId {
        let nat = d.nat_ty();
        let carrier = super::creal_ty(d, p);
        let func = d.arrow(carrier, carrier);
        let seqfn = {
            let inner = d.arrow(carrier, carrier);
            d.arrow(nat, inner)
        };

        let big_f_fv = d.fresh_fvar();
        let big_f = d.kernel().fvar(big_f_fv);
        let big_g_fv = d.fresh_fvar();
        let big_g = d.kernel().fvar(big_g_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let uconv_ty = d.const_app(p.uniform_converges_on, &[big_f, big_g, a, b]);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hax_ty = if transposed {
            d.const_app(p.le, &[x, a])
        } else {
            d.const_app(p.le, &[a, x])
        };
        let hxb_ty = d.const_app(p.le, &[x, b]);

        let f_at_x = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let body = d.apply(big_f, &[n, x]);
            d.lam_fv(n_fv, nat, body)
        };
        let g_at_x = d.apply(big_g, &[x]);
        let concl = converges_applied(d, p, f_at_x, g_at_x);

        let after_hxb = d.arrow(hxb_ty, concl);
        let after_hax = d.arrow(hax_ty, after_hxb);
        let with_x = d.pi_fv(x_fv, carrier, after_hax);
        let after_u = d.arrow(uconv_ty, with_x);
        let with_b = d.pi_fv(b_fv, carrier, after_u);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(big_g_fv, func, with_a);
        d.pi_fv(big_f_fv, seqfn, with_g)
    }

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let nat = d.nat_ty();
    let carrier = super::creal_ty(&mut d, p);
    let func = d.arrow(carrier, carrier);
    let seqfn = {
        let inner = d.arrow(carrier, carrier);
        d.arrow(nat, inner)
    };

    let big_f_fv = d.fresh_fvar();
    let big_f = d.kernel().fvar(big_f_fv);
    let big_g_fv = d.fresh_fvar();
    let big_g = d.kernel().fvar(big_g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let uconv_ty = d.const_app(p.uniform_converges_on, &[big_f, big_g, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hax_ty = d.const_app(p.le, &[a, x]);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hxb_ty = d.const_app(p.le, &[x, b]);
    let hxb_fv = d.fresh_fvar();
    let hxb = d.kernel().fvar(hxb_fv);

    // `f := fun n => F n x` and `L := G x` -- the sequence and limit a fixed
    // point of a uniformly convergent family gives.
    let f_at_x = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.apply(big_f, &[n, x]);
        d.lam_fv(n_fv, nat, body)
    };
    let g_at_x = d.apply(big_g, &[x]);

    let rate = d.const_app(p.uconv_rate, &[big_f, big_g, a, b, u]);
    let spec = d.const_app(p.uconv_spec, &[big_f, big_g, a, b, u]);

    // `fun n => spec n x hax hxb` -- the per-index `close_within` fact, at the
    // fixed point. This is the term whose type must be `converges_of_abs_diff_le`'s
    // hypothesis; nothing here transports it.
    let per_n = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.apply(spec, &[n, x, hax, hxb]);
        d.lam_fv(n_fv, nat, body)
    };

    let applied = d.lemma(p.converges_of_abs_diff_le, &[f_at_x, g_at_x, rate, per_n]);

    let closed = {
        let with_hxb = d.lam_fv(hxb_fv, hxb_ty, applied);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxb);
        let with_x = d.lam_fv(x_fv, carrier, with_hax);
        let with_u = d.lam_fv(u_fv, uconv_ty, with_x);
        let with_b = d.lam_fv(b_fv, carrier, with_u);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_g = d.lam_fv(big_g_fv, func, with_a);
        d.lam_fv(big_f_fv, seqfn, with_g)
    };

    let got = d
        .kernel()
        .infer(closed)
        .expect("the composed close_within -> Converges term must infer");

    let want = want_ty(&mut d, p, false);
    let transposed = want_ty(&mut d, p, true);

    assert_eq!(
        got, want,
        "`converges_of_abs_diff_le` applied to `UniformConvergesOn.spec` at a \
         fixed point must yield exactly `Converges (fun n => F n x) (G x)` -- \
         with the family's own `rate` as the numerator and no transport"
    );
    assert_ne!(
        want, transposed,
        "the negative control is vacuous: `le a x` builds the same term as \
         `le x a`"
    );
    assert_ne!(
        got, transposed,
        "the composition reads its own domain hypothesis backwards"
    );
}

/// **`CReal.ivtPlateau` evaluated at both endpoints, for both signs of `v`,
/// and the root ENDPOINT flips.** The evaluation test `CLAUDE.md` requires of
/// every new `Definition`: `add_declaration` type-checks a definition's body
/// but has nothing to compare it against, so a family that computes something
/// other than the intended clamp would be admitted, would carry an empty axiom
/// footprint, and would make
/// [`IvtBoundaryNames::ivt_exact_root_decides_sign`] a theorem about the wrong
/// function.
///
/// `ivtPlateau v := fun x => min x (max (x + (−1)) v)`, and `min`/`max`/`neg`
/// take no index shift, so index `0` of a constant-sequence argument is the
/// value itself. The four expected rationals are computed by hand:
///
/// | `v` | `F 0` | `F 1` |
/// | --- | --- | --- |
/// | `3` | `min 0 (max (−1) 3) = 0` | `min 1 (max 0 3) = 1` |
/// | `−3` | `min 0 (max (−1) (−3)) = −1` | `min 1 (max 0 (−3)) = 0` |
///
/// The **root is at the left endpoint when `v > 0` and at the right endpoint
/// when `v < 0`**, which is the entire content of the counterexample. The
/// numerals deliberately differ from
/// `evt_linear_endpoint_values_reduce_and_flip_with_the_sign_of_v`'s (`0`/`3`
/// and `0`/`−3`) so a copy-paste between the two tests fails loudly.
#[test]
fn ivt_plateau_endpoint_values_reduce_and_the_root_endpoint_flips_with_the_sign_of_v() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let idx0 = d.zero();

    let three_nat = d.num(3);
    let three = d.const_app(p.of_nat, &[three_nat]);
    let neg_three = d.const_app(p.neg, &[three]);

    let sample_at = |d: &mut IntDev<'_>, v: ExprId, x: ExprId| -> ExprId {
        let at = d.const_app(p.ivt_boundary.ivt_plateau, &[v, x]);
        d.const_app(p.seq, &[at, idx0])
    };

    // v = 3: the root is the LEFT endpoint.
    let pos_lo = sample_at(&mut d, three, zero_c);
    let pos_hi = sample_at(&mut d, three, one_c);
    let neg_lo = sample_at(&mut d, neg_three, zero_c);
    let neg_hi = sample_at(&mut d, neg_three, one_c);

    let zero_q = ivt_bisect_rat_lit(&mut d, p, 0, 0, false);
    let one_q = ivt_bisect_rat_lit(&mut d, p, 1, 0, false);
    let neg_one_q = ivt_bisect_rat_lit(&mut d, p, 1, 0, true);
    assert!(
        ivt_bisect_rat_eq(&mut d, p, pos_lo, zero_q),
        "at v = 3, ivtPlateau v zero must reduce to 0 -- the root IS the left endpoint"
    );
    assert!(
        ivt_bisect_rat_eq(&mut d, p, pos_hi, one_q),
        "at v = 3, ivtPlateau v one must reduce to 1"
    );
    assert!(
        ivt_bisect_rat_lt(&mut d, p, pos_lo, pos_hi),
        "at v = 3 the right endpoint must be strictly positive, so the root is \
         the left endpoint ALONE"
    );

    // v = -3: the root is the RIGHT endpoint. Same two arguments, mirrored
    // values -- so a transposed branch in the definition fails here even
    // though the v = 3 case above would still pass.
    assert!(
        ivt_bisect_rat_eq(&mut d, p, neg_lo, neg_one_q),
        "at v = -3, ivtPlateau v zero must reduce to -1"
    );
    assert!(
        ivt_bisect_rat_eq(&mut d, p, neg_hi, zero_q),
        "at v = -3, ivtPlateau v one must reduce to 0 -- the root IS the right endpoint"
    );
    assert!(
        ivt_bisect_rat_lt(&mut d, p, neg_lo, neg_hi),
        "at v = -3 the left endpoint must be strictly negative, so the root is \
         the right endpoint ALONE"
    );

    // And the flip itself, stated as the discrimination it is: the left
    // endpoint's value is 0 at v = 3 and NOT 0 at v = -3.
    assert!(
        !ivt_bisect_rat_eq(&mut d, p, neg_lo, zero_q),
        "the endpoint test is vacuous: ivtPlateau's value at zero does not \
         depend on the sign of v"
    );
}

/// **`CReal.ivtPlateau v c` IS the term `ivt_exact_root_decides_sign` states
/// its root hypothesis over.** The theorem is written out as
/// `Equiv (min c (max (add c (neg one)) v)) zero` rather than folded through
/// the definition, so that it is legible without unfolding anything — the same
/// choice `evt_attained_max_decides_sign` makes in writing `mul t v` rather
/// than `evtLinear v t`. This pins the bridge, at closed arguments.
#[test]
fn ivt_plateau_is_the_clamp_the_row_two_theorem_uses() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let one_c = d.kernel().const_(p.one, vec![]);
    let three_nat = d.num(3);
    let three = d.const_app(p.of_nat, &[three_nat]);

    let folded = d.const_app(p.ivt_boundary.ivt_plateau, &[three, one_c]);
    let raw = {
        let neg_one = d.const_app(p.neg, &[one_c]);
        let floor = d.const_app(p.add, &[one_c, neg_one]);
        let lifted = d.const_app(p.max, &[floor, three]);
        d.const_app(p.min, &[one_c, lifted])
    };
    assert!(
        d.kernel().def_eq(folded, raw),
        "`ivtPlateau v x` must be definitionally the clamp \
         `min x (max (add x (neg one)) v)` the row-2 theorem states"
    );
}

/// **The decision principle `ivt_exact_root_decides_sign` derives is ABSENT
/// from the environment**, which is what makes it a boundary rather than a
/// detour.
///
/// A reduction to something the kernel already proves is worth nothing, so
/// this is part of the row-2 claim and not a preliminary to it — the same
/// check `evt_attained_max_decides_sign`'s non-vacuity rests on. The
/// conclusion `∀ v, Or (le v zero) (le zero v)` is analytic LLPO, equivalently
/// the total order `le_total` over `CReal`, and `creal/cotransitivity.rs`'s
/// module documentation states verbatim that no `lt_total` is assumed or
/// provable here.
///
/// The negative is read from `kernel.environment()` and paired with a POSITIVE
/// control of the same declaration kind (`CReal.lt_cotrans`, a `Theorem`,
/// found by the identical lookup) — an empty answer from a query that finds
/// nothing is indistinguishable from a strong negative result. Note the
/// namespace filter is exact: `Rat.le_total` and `Nat.le_total` both exist and
/// a substring match would wrongly report the principle as present.
#[test]
fn ivt_row_two_derives_a_principle_absent_from_the_environment() {
    let (kernel, p) = built();

    let declared: Vec<String> = kernel
        .environment()
        .iter()
        .map(|(name, _)| kernel.display_name(*name).to_string())
        .collect();
    let present = |wanted: &str| declared.iter().any(|shown| shown == wanted);

    // POSITIVE CONTROL, same kind and same lookup: cotransitivity exists, and
    // it exists precisely because the total comparison does not.
    assert!(
        present("CReal.lt_cotrans"),
        "the absence check below is meaningless: this lookup cannot even find \
         a declaration that certainly exists"
    );

    for absent in [
        "CReal.le_total",
        "CReal.lt_total",
        "CReal.leTotal",
        "CReal.ltTotal",
    ] {
        assert!(
            !present(absent),
            "`{absent}` is now in the environment, so \
             `ivt_exact_root_decides_sign` reduces the classical conclusion to \
             something this kernel already proves and is no longer a boundary \
             witness. Do not delete this assertion -- rewrite the row-2 claim."
        );
    }

    // And the theorem itself is a checked `Theorem` resting on nothing.
    let declaration = kernel
        .environment()
        .get(p.ivt_boundary.ivt_exact_root_decides_sign)
        .expect("CReal.ivt_exact_root_decides_sign must be declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "row 2 must be a checked Theorem, not an assertion"
    );
    assert!(
        kernel
            .axiom_footprint(p.ivt_boundary.ivt_exact_root_decides_sign)
            .is_empty(),
        "row 2 must be axiom-free"
    );
}

/// **EVT's own copy of the check above, for `CReal.evt_attained_max_decides_sign`.**
///
/// `docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md`
/// (§"What would have to land", item 3) records that
/// `F:creal-evt-attained-max-decides-sign` had no non-vacuity evidence of its
/// own in the ledger — the environment-absence check above exists only for
/// `ivt_exact_root_decides_sign`, even though its own doc comment says "the
/// same check `evt_attained_max_decides_sign`'s non-vacuity rests on". That
/// was true mathematically (the two theorems render an IDENTICAL conclusion
/// type, `Or (le v zero) (le zero v)`, so one absence-of-`le_total` fact
/// bears on both) but nothing checked `evt_attained_max_decides_sign` itself:
/// a reader auditing this fact alone would find no assertion naming it.
///
/// This closes that gap as its own test rather than a bare citation, so it
/// also re-derives the two per-declaration guards IVT's version carries
/// (`Theorem` kind, empty axiom footprint) for the EVT declaration
/// specifically, not only for its IVT sibling.
///
/// Both directions are checked, same as the IVT version: a POSITIVE control
/// of the same declaration kind (`CReal.lt_cotrans`) proves the lookup can
/// find something that exists, and the four absent-name spellings prove the
/// lookup is not simply finding nothing because of a broken query.
#[test]
fn evt_row_two_derives_a_principle_absent_from_the_environment() {
    let (kernel, p) = built();

    let declared: Vec<String> = kernel
        .environment()
        .iter()
        .map(|(name, _)| kernel.display_name(*name).to_string())
        .collect();
    let present = |wanted: &str| declared.iter().any(|shown| shown == wanted);

    // POSITIVE CONTROL, same kind and same lookup: cotransitivity exists, and
    // it exists precisely because the total comparison does not.
    assert!(
        present("CReal.lt_cotrans"),
        "the absence check below is meaningless: this lookup cannot even find \
         a declaration that certainly exists"
    );

    for absent in [
        "CReal.le_total",
        "CReal.lt_total",
        "CReal.leTotal",
        "CReal.ltTotal",
    ] {
        assert!(
            !present(absent),
            "`{absent}` is now in the environment, so \
             `evt_attained_max_decides_sign` reduces the classical conclusion \
             to something this kernel already proves and is no longer a \
             boundary witness. Do not delete this assertion -- rewrite the \
             row-2 claim."
        );
    }

    // And the theorem itself is a checked `Theorem` resting on nothing.
    let declaration = kernel
        .environment()
        .get(p.extreme_value.evt_attained_max_decides_sign)
        .expect("CReal.evt_attained_max_decides_sign must be declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "row 2 must be a checked Theorem, not an assertion"
    );
    assert!(
        kernel
            .axiom_footprint(p.extreme_value.evt_attained_max_decides_sign)
            .is_empty(),
        "row 2 must be axiom-free"
    );
}
