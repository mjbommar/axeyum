//! Process-wide reuse of built prelude kernels (ADR-0464).
//!
//! # What this is
//!
//! Every prelude builder is a *deterministic function of the empty kernel*: the
//! interners assign dense ids in insertion order, so an identical construction
//! sequence produces an identical [`Kernel`] (the determinism rule, stated on
//! `Kernel` itself). This module exploits exactly that and nothing more. The
//! first caller to ask for a prelude on a **pristine** kernel builds it through
//! the ordinary trusted gate, and the finished kernel is retained as a
//! *template*. Every later caller with a pristine kernel receives a full clone
//! of that template.
//!
//! # Why this is not a weakening of the trusted surface
//!
//! The value handed back is a **bit-exact copy of a kernel state the caller
//! could have reached themselves** — namely the state immediately after running
//! the same builder on a fresh [`Kernel`]. Nothing is reconstructed, nothing is
//! deserialised, and no declaration enters an environment by any route other
//! than [`Kernel::add_declaration`], which ran once, on the template, under the
//! full type checker. There is deliberately no serialisation format here: a
//! deserialiser would put a parser on the trusted path, whereas a clone cannot
//! manufacture a declaration that the checker did not already admit.
//!
//! The whole soundness argument therefore reduces to one testable claim:
//!
//! > prelude construction is deterministic, so the template equals what a fresh
//! > build would have produced.
//!
//! That claim is a test, not an assertion — see `prelude_cache_tests`, which
//! builds each prelude both ways in one process and compares the complete
//! observable state (declaration count and order, every declaration's rendered
//! type, the axiom footprint, and the exported module bytes).
//!
//! # The pristine precondition
//!
//! Restoration overwrites the caller's kernel wholesale, so it is offered only
//! when that kernel is observably identical to [`Kernel::default`] — no interned
//! names, levels or expressions, no declarations, no registered packages, not
//! finalized for export. A kernel carrying any prior content keeps the ordinary
//! build path. This is why the check happens *before* the dependency build (a
//! `AxReal` build interns `Logic` first, which would itself make the kernel
//! non-pristine).
//!
//! `CReal` — the constructed reals — is the slot this mechanism exists for
//! rather than an afterthought: measured 2026-08-18 on a debug build, one
//! `build_creal_prelude` costs **44 s** against `AxReal`'s 5.6 ms and `Logic`'s
//! 0.2 ms, and every consumer of the constructed carrier builds its own. It is
//! also the largest template, so the reuse cost is a `Kernel` clone rather than
//! the near-free clone the small preludes get; both numbers are reported by the
//! `prelude_build_timing` example.
//!
//! `String` preludes deliberately have no template: they require a caller-held
//! [`LogicPrelude`](crate::LogicPrelude) and therefore never start from a
//! pristine kernel, and their marginal cost over `Logic` was measured at ~0.5 ms
//! against `Logic`'s 13.4 ms. The `Logic` template already collects that win.
//!
//! # Disabling
//!
//! Setting `AXEYUM_PRELUDE_CACHE=0` in the environment forces every caller onto
//! the ordinary build path. It is read once. The only supported use is
//! differential testing: a run with the cache off must produce byte-identical
//! output to a run with it on, which is what
//! `scripts/check-prelude-reuse-equivalence.sh` checks across the inventory
//! examples. Because "the flag was ignored" and "the flag changed nothing" look
//! identical from the outside, [`stats`] reports hit/miss/template counters so a
//! gate can prove the cache was actually exercised (or actually bypassed).

use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::{Kernel, PreludeKey, PreludeValue};

static HITS: AtomicU64 = AtomicU64::new(0);
static MISSES: AtomicU64 = AtomicU64::new(0);
static TEMPLATES_BUILT: AtomicU64 = AtomicU64::new(0);

/// Counters describing how the process-wide prelude template store was used.
///
/// Reported so a gate can distinguish "reuse changed nothing" from "reuse never
/// ran" — the two are indistinguishable from output alone, and this repository
/// has shipped several gates that passed over zero work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PreludeCacheStats {
    /// Restorations served from a template.
    pub hits: u64,
    /// Calls that took the ordinary build path (cache off, kernel not pristine,
    /// or no template available).
    pub misses: u64,
    /// Templates constructed, at most one per `PreludeKey` per process.
    pub templates_built: u64,
}

/// Returns the process-wide prelude reuse counters.
#[must_use]
pub fn stats() -> PreludeCacheStats {
    PreludeCacheStats {
        hits: HITS.load(Ordering::Relaxed),
        misses: MISSES.load(Ordering::Relaxed),
        templates_built: TEMPLATES_BUILT.load(Ordering::Relaxed),
    }
}

/// Whether process-wide prelude reuse is enabled (`AXEYUM_PRELUDE_CACHE=0`
/// disables it). Read once per process.
#[must_use]
pub fn enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("AXEYUM_PRELUDE_CACHE").as_deref() != Ok("0"))
}

/// A template slot. `None` records that the ordinary build failed, so callers
/// fall through and observe the same error the template build saw.
type Slot = OnceLock<Option<Kernel>>;

static LOGIC: Slot = OnceLock::new();
static NAT: Slot = OnceLock::new();
static INT: Slot = OnceLock::new();
static REAL: Slot = OnceLock::new();
static CREAL: Slot = OnceLock::new();

fn slot(key: PreludeKey) -> Option<&'static Slot> {
    match key {
        PreludeKey::Logic => Some(&LOGIC),
        PreludeKey::Nat => Some(&NAT),
        PreludeKey::Int => Some(&INT),
        PreludeKey::Real => Some(&REAL),
        PreludeKey::CReal => Some(&CREAL),
        // `List` has no template yet (new, marginal cost over `Logic` not
        // measured) and `String` requires a caller-held `LogicPrelude` (so
        // never starts pristine) -- both fall through to the ordinary build
        // path every time.
        PreludeKey::List | PreludeKey::String(_) => None,
    }
}

/// Builds `key`'s template through the ordinary trusted gate, once per process.
fn template(key: PreludeKey) -> Option<&'static Kernel> {
    let slot = slot(key)?;
    slot.get_or_init(|| {
        TEMPLATES_BUILT.fetch_add(1, Ordering::Relaxed);
        let mut kernel = Kernel::new();
        let built = match key {
            PreludeKey::Logic => crate::prelude::build_logic_prelude_uncached(&mut kernel).is_ok(),
            PreludeKey::Nat => crate::nat_prelude::build_nat_prelude_uncached(&mut kernel).is_ok(),
            PreludeKey::Int => crate::int_prelude::build_int_prelude_uncached(&mut kernel).is_ok(),
            PreludeKey::Real => {
                crate::arith_prelude::build_arith_prelude_uncached(&mut kernel).is_ok()
            }
            PreludeKey::CReal => crate::creal::build_creal_prelude_uncached(&mut kernel).is_ok(),
            PreludeKey::List | PreludeKey::String(_) => false,
        };
        built.then_some(kernel)
    })
    .as_ref()
}

/// Restores `key`'s prelude into `kernel` from the process-wide template.
///
/// Returns `None` — leaving `kernel` untouched — when reuse is disabled, when
/// `kernel` is not pristine, when `key` has no template, or when the template
/// build failed. In every such case the caller must take its ordinary build
/// path, which reproduces the same result (including the same error).
pub(crate) fn try_restore(kernel: &mut Kernel, key: PreludeKey) -> Option<PreludeValue> {
    // A template is a whole-kernel snapshot, so assigning one over `kernel`
    // would reset every field — including the caller's rendering preference,
    // which is not kernel content and which a cache hit must not change. Carry
    // it across explicitly; a silently-cleared flag would make a measurement
    // run render the default bytes while believing it rendered the other.
    let render_proofs_as_def = kernel.render_proofs_as_def();
    let restored = try_restore_inner(kernel, key);
    kernel.set_render_proofs_as_def(render_proofs_as_def);
    restored
}

fn try_restore_inner(kernel: &mut Kernel, key: PreludeKey) -> Option<PreludeValue> {
    if !enabled() || !kernel.is_pristine() {
        MISSES.fetch_add(1, Ordering::Relaxed);
        return None;
    }
    let Some(template) = template(key) else {
        MISSES.fetch_add(1, Ordering::Relaxed);
        return None;
    };
    *kernel = template.clone();
    // Re-validates the package against the restored environment. A clone cannot
    // fail this, which is the point: it is a cheap standing check that the
    // restored state is self-consistent rather than an assumption that it is.
    if let Ok(Some(value)) = kernel.cached_prelude(key) {
        HITS.fetch_add(1, Ordering::Relaxed);
        return Some(value);
    }
    // Unreachable for a clone of a template that registered `key`. Restore the
    // caller's pristine kernel and take the slow path.
    *kernel = Kernel::new();
    MISSES.fetch_add(1, Ordering::Relaxed);
    None
}

#[cfg(test)]
mod prelude_cache_tests;
