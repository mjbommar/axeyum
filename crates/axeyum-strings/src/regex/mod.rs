//! Symbolic-derivative regex engine (Phase C, ADR-0054).
//!
//! A from-scratch, pure-Rust implementation of regex membership via **symbolic
//! Boolean derivatives + transition regexes** (Stanford/Veanes/Bjørner,
//! PLDI 2021; Brzozowski 1964), over the Unicode code-point alphabet as
//! interval-set predicates (ADR-0051 `BitVec(18)` order). It handles
//! intersection and complement **directly via derivatives** — no
//! determinization — and treats bounded loops `R{n,m}` as a **native
//! construct**, never pre-unrolled (Veanes, LPAR 2024).
//!
//! ## Module map
//!
//! * [`predicate`] (T-C.1) — [`CharPred`], the canonical interval-set character
//!   predicate algebra (`∧`/`∨`/`¬`, emptiness, witness, mintermization).
//! * [`ast`] (T-C.2) — the [`Regex`] AST over [`CharPred`] leaves with native
//!   [`Loop`](Regex::Loop).
//! * [`derivative`](mod@derivative) (T-C.2) — [`nullable`], the transition-regex
//!   [`derivative`](derivative::derivative), similarity
//!   [`canon`]icalization, and the
//!   [`derivative_closure`].
//! * [`matcher`] (T-C.2) — the **independent** reference [`matches()`],
//!   the replay trust anchor that shares no code with the derivative engine
//!   (ADR-0054).
//!
//! The two engines are pitted against each other by the fundamental-derivative
//! -theorem property test: for every regex `R` and string `s`, `matches(R, s)`
//! equals `nullable(∂_{s₁}…∂_{sₙ}(R))`.

pub mod ast;
pub mod derivative;
pub mod matcher;
pub mod membership;
pub mod predicate;

pub use ast::Regex;
pub use derivative::{Closure, TransitionRegex, canon, derivative, derivative_closure, nullable};
pub use matcher::matches;
pub use membership::{Membership, MembershipOutcome, recheck_empty};
pub use predicate::{ALPHABET_MAX, CharPred};
