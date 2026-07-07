//! T-C.2 tests for the symbolic-derivative engine.
//!
//! The centerpiece is the **fundamental derivative theorem** (the trust
//! anchor): for random regexes and strings, the independent reference matcher
//! agrees with stepping the transition-regex derivative and checking
//! `nullable`. We also cover loop-specific vectors (native `R{n,m}`, no
//! blowup), complement/intersection without determinization, and
//! derivative-closure finiteness.

use axeyum_strings::regex::ast::Regex;
use axeyum_strings::regex::derivative::{Closure, canon, derivative, derivative_closure, nullable};
use axeyum_strings::regex::matcher::matches;
use axeyum_strings::regex::predicate::CharPred;

/// Deterministic linear-congruential generator (the repo's house constant).
struct Lcg(u64);

impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u32) -> u32 {
        u32::try_from((self.next_u64() >> 33) % u64::from(n.max(1))).expect("fits u32")
    }
    fn coin(&mut self) -> bool {
        self.next_u64() & (1 << 40) != 0
    }
}

// The alphabet slice used by the property test: 'a'..='f' plus 'g' (0x67) as an
// out-of-range probe char for the strings.
const A: u32 = 0x61;
const F: u32 = 0x66;

/// Step the transition-regex derivative across `cs`, returning `true` iff the
/// residual after the last character is nullable — the derivative engine's
/// membership verdict.
fn derivative_matches(r: &Regex, cs: &[u32]) -> bool {
    let mut cur = r.clone();
    for &c in cs {
        cur = derivative(&cur).step(c).clone();
    }
    nullable(&cur)
}

/// A random character predicate over the `a..=f` slice.
fn random_slice_pred(rng: &mut Lcg) -> CharPred {
    match rng.below(6) {
        0 => CharPred::all(),
        1 => CharPred::none(),
        2 => {
            let c = A + rng.below(F - A + 1);
            CharPred::singleton(c)
        }
        _ => {
            let a = A + rng.below(F - A + 1);
            let b = A + rng.below(F - A + 1);
            CharPred::range(a.min(b), a.max(b))
        }
    }
}

/// A random regex of bounded depth over the slice alphabet.
fn random_regex(rng: &mut Lcg, depth: u32) -> Regex {
    if depth == 0 || rng.below(3) == 0 {
        return match rng.below(8) {
            0 => Regex::Empty,
            1 => Regex::None,
            _ => Regex::pred(random_slice_pred(rng)),
        };
    }
    match rng.below(9) {
        0 => Regex::concat(random_regex(rng, depth - 1), random_regex(rng, depth - 1)),
        1 => Regex::union(random_regex(rng, depth - 1), random_regex(rng, depth - 1)),
        2 => Regex::inter(random_regex(rng, depth - 1), random_regex(rng, depth - 1)),
        3 => Regex::comp(random_regex(rng, depth - 1)),
        4 => Regex::star(random_regex(rng, depth - 1)),
        5 => Regex::plus(random_regex(rng, depth - 1)),
        6 => Regex::opt(random_regex(rng, depth - 1)),
        _ => {
            let lo = rng.below(3);
            let hi = if rng.coin() {
                None
            } else {
                Some(lo + rng.below(3))
            };
            Regex::repeat(random_regex(rng, depth - 1), lo, hi)
        }
    }
}

/// A random string of length ≤ 6 over `a..=g` (`g` probes non-matching guards).
fn random_string(rng: &mut Lcg) -> Vec<u32> {
    let len = rng.below(7);
    (0..len).map(|_| A + rng.below(F - A + 2)).collect()
}

/// THE trust anchor: derivative engine vs the independent matcher.
#[test]
fn fundamental_derivative_theorem() {
    let mut rng = Lcg(0xDE21_0A71_5EED_C0DE);
    let cases = 20_000;
    let mut checked = 0u32;
    for _ in 0..cases {
        let r = random_regex(&mut rng, 5);
        let cs = random_string(&mut rng);
        let reference = matches(&r, &cs);
        let engine = derivative_matches(&r, &cs);
        assert_eq!(
            reference, engine,
            "derivative disagreed with matcher on regex {r:?} string {cs:?}"
        );
        checked += 1;
    }
    assert!(checked >= 5_000, "fundamental theorem case count floor");
}

/// Canonicalization is language-preserving: `matches(R, s) == matches(canon(R), s)`.
#[test]
fn canon_preserves_language() {
    let mut rng = Lcg(0xCA20_0FEE_1234_ABCD);
    for _ in 0..10_000 {
        let r = random_regex(&mut rng, 5);
        let cs = random_string(&mut rng);
        assert_eq!(matches(&r, &cs), matches(&canon(&r), &cs));
    }
}

/// Native bounded loop `R{2,3}` on strings of matched-count 1/2/3/4.
#[test]
fn loop_bounded_vectors() {
    let r = Regex::repeat(Regex::character(A), 2, Some(3));
    let a1 = vec![A];
    let a2 = vec![A, A];
    let a3 = vec![A, A, A];
    let a4 = vec![A, A, A, A];
    for (cs, want) in [(&a1, false), (&a2, true), (&a3, true), (&a4, false)] {
        assert_eq!(matches(&r, cs), want, "matcher R{{2,3}} on {cs:?}");
        assert_eq!(derivative_matches(&r, cs), want, "deriv R{{2,3}} on {cs:?}");
    }
}

/// `R{0,0}` is ε.
#[test]
fn loop_zero_is_epsilon() {
    let r = Regex::repeat(Regex::character(A), 0, Some(0));
    assert_eq!(canon(&r), Regex::Empty);
    assert!(matches(&r, &[]));
    assert!(derivative_matches(&r, &[]));
    assert!(!matches(&r, &[A]));
    assert!(!derivative_matches(&r, &[A]));
}

/// `R{n,}` (hi = None) behaves as `R{n} · R*`.
#[test]
fn loop_unbounded_vectors() {
    let r = Regex::repeat(Regex::character(A), 2, None);
    for count in 0u32..8 {
        let cs = vec![A; count as usize];
        let want = count >= 2;
        assert_eq!(matches(&r, &cs), want, "matcher a{{2,}} count {count}");
        assert_eq!(
            derivative_matches(&r, &cs),
            want,
            "deriv a{{2,}} count {count}"
        );
    }
}

/// No blowup for `R{100,200}`: the derivative closure stays small and complete,
/// and stepping a 200-character string agrees with the matcher.
#[test]
fn loop_large_bounds_no_blowup() {
    let r = Regex::repeat(Regex::character(A), 100, Some(200));

    // Each derivative step is O(1): the residual is another *native* shrinking
    // loop, never an unrolled union. The closure is therefore LINEAR in the
    // bound (measured 202 = the shrinking `a{k,k+100}` residuals plus ε/∅),
    // not the exponential union pre-unrolling would produce. Documented bound
    // 256 (linear, ~2·(hi−lo)); asserting ≤ 256 catches any accidental unroll.
    match derivative_closure(&r, 256) {
        Closure::Complete(states) => {
            assert!(
                states.len() <= 256,
                "R{{100,200}} closure size {} exceeded linear bound",
                states.len()
            );
        }
        Closure::Budget => panic!("R{{100,200}} closure must be finite and linear"),
    }

    for count in [99u32, 100, 150, 200, 201] {
        let cs = vec![A; count as usize];
        let want = (100..=200).contains(&count);
        assert_eq!(matches(&r, &cs), want, "matcher a{{100,200}} count {count}");
        assert_eq!(
            derivative_matches(&r, &cs),
            want,
            "deriv a{{100,200}} count {count}"
        );
    }
}

/// Complement and intersection without determinization: `∁(a·b*) ∩ (a·c)`.
#[test]
fn complement_intersection_vectors() {
    let b = 0x62;
    let c = 0x63;
    let a_bstar = Regex::concat(Regex::character(A), Regex::star(Regex::character(b)));
    let a_c = Regex::concat(Regex::character(A), Regex::character(c));
    let r = Regex::inter(Regex::comp(a_bstar.clone()), a_c);

    let cases: &[(&[u32], bool)] = &[
        (&[A, c], true),  // in a·c and not in a·b*
        (&[A, b], false), // in a·b* and not in a·c
        (&[A], false),    // not in a·c
        (&[A, c, c], false),
    ];
    for (cs, want) in cases {
        assert_eq!(matches(&r, cs), *want, "matcher on {cs:?}");
        assert_eq!(derivative_matches(&r, cs), *want, "deriv on {cs:?}");
    }

    // Complement flips membership everywhere.
    let comp = Regex::comp(a_bstar.clone());
    for cs in [vec![A], vec![A, b], vec![A, b, b], vec![A, c], vec![]] {
        assert_eq!(matches(&comp, &cs), !matches(&a_bstar, &cs));
        assert_eq!(derivative_matches(&comp, &cs), !matches(&a_bstar, &cs));
    }
}

/// A battery of similarity-requiring regexes whose derivative closure must be
/// finite and small (the Brzozowski finiteness the canonicalizer secures).
#[test]
fn derivative_closure_finiteness() {
    let a = Regex::character(A);
    let b = Regex::character(0x62);
    let ab = Regex::union(a.clone(), b.clone());

    // (regex, documented closure upper bound)
    let battery: Vec<(Regex, usize)> = vec![
        (Regex::star(ab.clone()), 4),
        (Regex::comp(Regex::star(a.clone())), 6),
        (
            Regex::inter(Regex::star(a.clone()), Regex::star(ab.clone())),
            8,
        ),
        (
            Regex::concat(Regex::star(a.clone()), Regex::star(b.clone())),
            8,
        ),
        (Regex::plus(ab.clone()), 6),
        (
            Regex::union(Regex::star(a.clone()), Regex::comp(Regex::star(b.clone()))),
            16,
        ),
        (
            Regex::inter(
                Regex::comp(Regex::concat(a.clone(), Regex::star(b.clone()))),
                Regex::concat(a.clone(), Regex::character(0x63)),
            ),
            32,
        ),
    ];

    for (r, bound) in battery {
        match derivative_closure(&r, 1024) {
            Closure::Complete(states) => assert!(
                states.len() <= bound,
                "closure of {r:?} was {} states (> documented {bound})",
                states.len()
            ),
            Closure::Budget => panic!("closure of {r:?} must be finite"),
        }
    }
}

/// The transition-regex guards partition the alphabet: for any regex and any
/// probe character, exactly one branch's guard contains it.
#[test]
fn transition_guards_partition_alphabet() {
    let mut rng = Lcg(0x9A17_0F0F_2222_3333);
    for _ in 0..2_000 {
        let r = random_regex(&mut rng, 4);
        let tr = derivative(&r);
        for c in [0u32, A, F, 0x67, 0x100, 0x2_FFFF] {
            let hits = tr.branches().iter().filter(|(g, _)| g.contains(c)).count();
            assert_eq!(hits, 1, "exactly one guard must contain {c} for {r:?}");
        }
    }
}

// ---------------------------------------------------------------------------
// Deadline-poll (task #54): the derivative frontier must be interruptible.
// ---------------------------------------------------------------------------

/// `derivative_within` with a **never-tripping** poll is result-identical to the
/// plain `derivative` — the drift guard that keeps the bounded frontier faithful
/// to the anchored derivative (the only path that matters for soundness; an
/// aborted poll only ever yields a decline).
#[test]
fn derivative_within_matches_derivative_when_poll_never_trips() {
    use axeyum_strings::regex::derivative::derivative_within;
    let mut rng = Lcg(0x5454_5454_D00D_F00D);
    for _ in 0..5_000 {
        let r = random_regex(&mut rng, 5);
        let got = derivative_within(&r, &mut || false).expect("never-tripping poll cannot abort");
        assert_eq!(got, derivative(&r), "bounded derivative diverged for {r:?}");
    }
}

/// A poll that trips after a fixed number of frontier steps aborts the
/// derivative (⇒ `None`), so a single expensive `∂R` is interruptible mid-flight
/// rather than a deadline-uninterruptible grind. The subject is a deeply-nested
/// `Σ*`-enlarged intersection — exactly the membership-over-concat shape whose
/// `product` cascade is the pathological frontier.
#[test]
fn derivative_within_aborts_when_poll_trips() {
    use axeyum_strings::regex::derivative::derivative_within;

    // `contains([lo,hi]) = Σ* [lo,hi] Σ*`, intersected across overlapping ranges
    // so the derivative's `product` frontier does real (non-collapsing) work.
    let contains = |lo: u32, hi: u32| {
        Regex::concat(
            Regex::star(Regex::any_char()),
            Regex::concat(Regex::char_range(lo, hi), Regex::star(Regex::any_char())),
        )
    };
    let mut r = contains(A, A + 40);
    for i in 1..16u32 {
        r = Regex::inter(r, contains(A + i, A + i + 40));
    }
    let r = Regex::inter(r, Regex::star(Regex::any_char()));

    // Poll trips after 8 frontier steps: far fewer than this intersection's
    // derivative needs, so it must abort to `None`.
    let mut ticks = 0u32;
    let out = derivative_within(&r, &mut || {
        ticks += 1;
        ticks > 8
    });
    assert!(
        out.is_none(),
        "expected an aborted (None) derivative under a tight poll"
    );
}
