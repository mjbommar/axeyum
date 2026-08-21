//! AC-Bridge workstream B (wild Hast--Matei): the characteristic-two failure of
//! Hast--Matei's Lemma 2.6, measured exactly.
//!
//! Hast--Matei (arXiv:1604.02067, IMRN 2019) prove their moment bound
//! (Theorem 1.4) for `m > 2` only under `p > n`.  Their Remark 4.1 states the
//! restriction is "due solely to the failure of Lemma 2.6 in low
//! characteristic".  Lemma 2.6 says, for `s, t <= n` and any `c in k^t`, that
//!
//! ```text
//! Z = { w in A^n : #{w_1,...,w_n} <= s,  e_j(w) = c_j  (1 <= j <= t) }
//! ```
//!
//! has `dim Z = max{s - t, 0}` when `char k > n`.  Theorem 2.7 uses it only at
//! `(s, t) = (n-h-2, n-h-1)`, i.e. `dim Z = 0`, to bound the singular locus of
//! `X_(m,n,h)` and hence to place the Ghorpade--Lachaud vanishing range.
//!
//! In `char 2` the statement is FALSE.  Every `f` factors canonically as
//! `f = C_0 C_1^2 C_2^4 ...` with `C_j` monic of degree `d_j`, and perturbing
//! the `j`-th layer moves `f` by `(f / C_j^(2^j)) u^(2^j)`, a change of degree
//! `n - 2^j (d_j - deg u)`.  So the whole layer-`j` perturbation space of
//! dimension `d_j - floor(t / 2^j)` stays inside ONE interval.  This file
//! computes the resulting excess exactly, and verifies it by exhaustive
//! enumeration over `F_2` (and, as a tame control, over `F_p`, `p` odd, where
//! the excess must vanish).
//!
//! Read-only diagnostic; exact integers only.  Finite computation is evidence,
//! never a theorem.
//!
//! Usage:
//!   `acb_whm_strata optimize <ell-lo> <ell-hi>`  -- predicted wild excess
//!   `acb_whm_strata count <p> <n> <h>`           -- exhaustive interval census
//!   `acb_whm_strata sweep <ell-lo> <ell-hi>`     -- census vs prediction, F_2
//!   `acb_whm_strata witness <ell>`               -- explicit refuting family

// ---------------------------------------------------------------------------
// Part 1: polynomials over F_p, p prime, dense little-endian coefficients.
// ---------------------------------------------------------------------------

/// Monic-or-zero dense polynomial over `F_p`; `c[i]` is the coefficient of
/// `x^i` and the leading coefficient is nonzero (the zero polynomial is `[]`).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Poly {
    p: u32,
    c: Vec<u32>,
}

impl Poly {
    fn zero(p: u32) -> Self {
        Self { p, c: Vec::new() }
    }

    fn one(p: u32) -> Self {
        Self { p, c: vec![1] }
    }

    fn from_vec(p: u32, mut c: Vec<u32>) -> Self {
        for v in &mut c {
            *v %= p;
        }
        while c.last() == Some(&0) {
            c.pop();
        }
        Self { p, c }
    }

    fn is_zero(&self) -> bool {
        self.c.is_empty()
    }

    /// Degree; `usize::MAX` for the zero polynomial (never used as a number).
    fn deg(&self) -> usize {
        self.c.len().saturating_sub(1)
    }

    fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero(self.p);
        }
        let mut out = vec![0_u32; self.c.len() + other.c.len() - 1];
        for (i, a) in self.c.iter().enumerate() {
            if *a == 0 {
                continue;
            }
            for (j, b) in other.c.iter().enumerate() {
                out[i + j] = (out[i + j] + a * b) % self.p;
            }
        }
        Self::from_vec(self.p, out)
    }

    fn derivative(&self) -> Self {
        let mut out = Vec::new();
        for (i, a) in self.c.iter().enumerate().skip(1) {
            let k = u32::try_from(i % self.p as usize).expect("index fits u32");
            out.push((a * k) % self.p);
        }
        Self::from_vec(self.p, out)
    }

    /// `(quotient, remainder)` of `self` by `other`; `other` must be nonzero.
    fn div_rem(&self, other: &Self) -> (Self, Self) {
        assert!(!other.is_zero(), "division by zero polynomial");
        if self.is_zero() || self.c.len() < other.c.len() {
            return (Self::zero(self.p), self.clone());
        }
        let p = self.p;
        let inv_lead = mod_inverse(*other.c.last().expect("nonzero"), p);
        let mut rem = self.c.clone();
        let mut quo = vec![0_u32; self.c.len() - other.c.len() + 1];
        for shift in (0..quo.len()).rev() {
            let top = rem[shift + other.c.len() - 1];
            if top == 0 {
                continue;
            }
            let factor = (top * inv_lead) % p;
            quo[shift] = factor;
            for (j, b) in other.c.iter().enumerate() {
                let sub = (factor * b) % p;
                rem[shift + j] = (rem[shift + j] + p - sub) % p;
            }
        }
        (Self::from_vec(p, quo), Self::from_vec(p, rem))
    }

    fn gcd(&self, other: &Self) -> Self {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let (_, r) = a.div_rem(&b);
            a = b;
            b = r;
        }
        if a.is_zero() {
            return a;
        }
        // Normalize monic.
        let inv = mod_inverse(*a.c.last().expect("nonzero"), a.p);
        let c = a.c.iter().map(|v| (v * inv) % a.p).collect();
        Self::from_vec(a.p, c)
    }

    /// `p`-th root of a polynomial whose derivative vanishes.  Over `F_p` the
    /// Frobenius is the identity on coefficients, so this is just decimation.
    fn pth_root(&self) -> Self {
        let step = self.p as usize;
        let mut out = Vec::new();
        let mut i = 0;
        while i < self.c.len() {
            out.push(self.c[i]);
            i += step;
        }
        Self::from_vec(self.p, out)
    }

    /// The radical: the product of the distinct irreducible factors.  Its
    /// degree is the number of distinct roots in an algebraic closure.
    fn radical(&self) -> Self {
        if self.is_zero() || self.c.len() <= 1 {
            return Self::one(self.p);
        }
        let d = self.derivative();
        if d.is_zero() {
            return self.pth_root().radical();
        }
        let g = self.gcd(&d);
        let (w, r0) = self.div_rem(&g);
        assert!(r0.is_zero(), "gcd must divide");
        let r = g.radical();
        let common = w.gcd(&r);
        let (reduced, r1) = r.div_rem(&common);
        assert!(r1.is_zero(), "gcd must divide");
        w.mul(&reduced)
    }
}

fn mod_inverse(a: u32, p: u32) -> u32 {
    let mut result = 1_u32;
    let mut base = a % p;
    let mut e = p - 2;
    while e > 0 {
        if e & 1 == 1 {
            result = (result * base) % p;
        }
        base = (base * base) % p;
        e >>= 1;
    }
    result
}

// ---------------------------------------------------------------------------
// Part 2: fast F_2 path (bitmask polynomials) for the large-`n` census.
// ---------------------------------------------------------------------------

fn f2_deg(f: u64) -> usize {
    debug_assert!(f != 0);
    63 - f.leading_zeros() as usize
}

fn f2_mul(mut a: u64, b: u64) -> u64 {
    let mut out = 0_u64;
    while a != 0 {
        let k = a.trailing_zeros();
        a &= a - 1;
        out ^= b << k;
    }
    out
}

fn f2_div_rem(a: u64, b: u64) -> (u64, u64) {
    assert!(b != 0, "division by zero polynomial");
    if a == 0 || f2_deg(a) < f2_deg(b) {
        return (0, a);
    }
    let db = f2_deg(b);
    let mut rem = a;
    let mut quo = 0_u64;
    while rem != 0 && f2_deg(rem) >= db {
        let shift = f2_deg(rem) - db;
        quo ^= 1_u64 << shift;
        rem ^= b << shift;
    }
    (quo, rem)
}

fn f2_gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let (_, r) = f2_div_rem(a, b);
        a = b;
        b = r;
    }
    a
}

const F2_ODD: u64 = 0xAAAA_AAAA_AAAA_AAAA;

fn f2_derivative(f: u64) -> u64 {
    (f & F2_ODD) >> 1
}

fn f2_sqrt(f: u64) -> u64 {
    let mut out = 0_u64;
    let mut i = 0;
    while (1_u64 << i) <= f {
        if f >> i & 1 == 1 {
            debug_assert!(i % 2 == 0, "not a square");
            out |= 1_u64 << (i / 2);
        }
        i += 1;
    }
    out
}

fn f2_radical(f: u64) -> u64 {
    if f <= 1 {
        return 1;
    }
    let d = f2_derivative(f);
    if d == 0 {
        return f2_radical(f2_sqrt(f));
    }
    let g = f2_gcd(f, d);
    let (w, r0) = f2_div_rem(f, g);
    debug_assert_eq!(r0, 0);
    let r = f2_radical(g);
    let (reduced, r1) = f2_div_rem(r, f2_gcd(w, r));
    debug_assert_eq!(r1, 0);
    f2_mul(w, reduced)
}

/// The canonical characteristic-two layer profile: `f = prod_j C_j^(2^j)`
/// with `C_j` the product of the irreducible factors whose multiplicity has
/// bit `j` set.  Returns `(d_0, d_1, ...)`.
fn f2_layers(mut f: u64) -> Vec<usize> {
    let mut out = Vec::new();
    while f > 1 {
        let d = f2_derivative(f);
        let odd = if d == 0 {
            1
        } else {
            f2_div_rem(f, f2_gcd(f, d)).0
        };
        out.push(f2_deg(odd));
        let (rest, r) = f2_div_rem(f, odd);
        debug_assert_eq!(r, 0);
        f = f2_sqrt(rest);
    }
    out
}

// ---------------------------------------------------------------------------
// Part 3: the predicted excess, by exhaustive search over layer profiles.
// ---------------------------------------------------------------------------

/// One layer profile and the two numbers Hast--Matei's Lemma 2.6 controls.
#[derive(Clone, Debug)]
struct Profile {
    d: Vec<usize>,
    /// Generic number of distinct roots `sum_j d_j` (must be `<= s`).
    k: usize,
    /// Fibre dimension of the interval map on this stratum.
    delta: usize,
}

/// `delta = sum_(j>=1) max(0, d_j - floor(t / p^j))`, `t = n-h-1`.  A layer of
/// degree `d_j > s` is discarded by the caller: perturbing it produces a
/// generic member with `d_j` distinct roots, outside `T_s`.
fn layer_delta(d: &[usize], t: usize, p: usize) -> usize {
    let mut power = 1_usize;
    let mut out = 0_usize;
    for (j, dj) in d.iter().enumerate() {
        power = if j == 0 { 1 } else { power * p };
        if j == 0 {
            continue;
        }
        out += dj.saturating_sub(t / power);
    }
    out
}

/// All profiles with `sum_j 2^j d_j = n` and `sum_j d_j <= s`, maximizing
/// `k + delta`.  The tame value of that maximum is exactly `s`.
fn best_profiles_p(n: usize, h: usize, p: usize) -> (usize, Vec<Profile>) {
    let s = n - h - 2;
    let t = n - h - 1;
    let mut layers = 1_usize;
    while p.pow(u32::try_from(layers).expect("fits")) <= n {
        layers += 1;
    }
    let mut best = 0_usize;
    let mut winners: Vec<Profile> = Vec::new();
    let mut d = vec![0_usize; layers];
    fn walk(
        j: usize,
        remaining: usize,
        used: usize,
        d: &mut Vec<usize>,
        s: usize,
        t: usize,
        p: usize,
        best: &mut usize,
        winners: &mut Vec<Profile>,
    ) {
        if j == d.len() {
            if remaining == 0 {
                // `used` is the number of NONZERO layers: every layer needs at
                // least one distinct root, and a layer of degree `c_j` may
                // contribute anywhere from 1 to `c_j` distinct roots (it is an
                // arbitrary monic polynomial, e.g. a power of one irreducible).
                // The stratum dimension is therefore
                // `k = min(s, sum_j c_j)`, feasible iff `used <= s`.
                let _ = used;
                // Layers we perturb: their generic member has `c_j` distinct
                // roots.  Layers we hold fixed may be a power of a single
                // irreducible and so contribute as little as one distinct root.
                let mut power = 1_usize;
                let mut moving = 0_usize;
                let mut frozen = 0_usize;
                for (j, dj) in d.iter().enumerate() {
                    if j > 0 {
                        power *= p;
                    }
                    if *dj == 0 {
                        continue;
                    }
                    if j > 0 && *dj > t / power {
                        moving += *dj;
                    } else {
                        frozen += 1;
                    }
                }
                if moving + frozen > s {
                    return;
                }
                let k = s.min(d.iter().sum::<usize>());
                let delta = layer_delta(d, t, p);
                let score = k + delta;
                if score > *best {
                    *best = score;
                    winners.clear();
                }
                if score == *best {
                    winners.push(Profile {
                        d: d.clone(),
                        k,
                        delta,
                    });
                }
            }
            return;
        }
        let weight = p.pow(u32::try_from(j).expect("fits"));
        let cap = remaining / weight;
        for dj in 0..=cap {
            d[j] = dj;
            walk(
                j + 1,
                remaining - dj * weight,
                used + usize::from(dj > 0),
                d,
                s,
                t,
                p,
                best,
                winners,
            );
        }
        d[j] = 0;
    }
    walk(0, n, 0, &mut d, s, t, p, &mut best, &mut winners);
    (best, winners)
}

/// Characteristic-two specialization used everywhere else in this file.
fn best_profiles(n: usize, h: usize) -> (usize, Vec<Profile>) {
    best_profiles_p(n, h, 2)
}

// ---------------------------------------------------------------------------
// Part 4: exhaustive interval census.
// ---------------------------------------------------------------------------

/// Census over `F_2` of the locus `#{distinct roots} <= s`, bucketed by the
/// short interval (the top `t = n-h-1` coefficients).  Returns
/// `(total, max_bucket, argmax_label, profile histogram of the max bucket)`.
fn census_f2(n: usize, h: usize) -> (u64, u64, u64, Vec<(Vec<usize>, u64)>) {
    let s = n - h - 2;
    let t = n - h - 1;
    let buckets = 1_usize << t;
    let mut counts = vec![0_u64; buckets];
    let mut total = 0_u64;
    let lead = 1_u64 << n;
    for tail in 0..(1_u64 << n) {
        let f = lead | tail;
        if f2_deg(f2_radical(f)) > s {
            continue;
        }
        total += 1;
        // interval label: coefficients of x^(n-1) .. x^(n-t)
        let label = ((f >> (n - t)) & ((1_u64 << t) - 1)) as usize;
        counts[label] += 1;
    }
    let (arg, max) = counts
        .iter()
        .enumerate()
        .max_by_key(|(i, v)| (**v, std::cmp::Reverse(*i)))
        .map(|(i, v)| (i, *v))
        .expect("nonempty");
    let mut histogram: Vec<(Vec<usize>, u64)> = Vec::new();
    for tail in 0..(1_u64 << n) {
        let f = lead | tail;
        let label = ((f >> (n - t)) & ((1_u64 << t) - 1)) as usize;
        if label != arg || f2_deg(f2_radical(f)) > s {
            continue;
        }
        let prof = f2_layers(f);
        match histogram.iter_mut().find(|(p, _)| *p == prof) {
            Some((_, c)) => *c += 1,
            None => histogram.push((prof, 1)),
        }
    }
    histogram.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    (total, max, arg as u64, histogram)
}

/// Same census over `F_p`, `p` odd (the tame control).  Only the totals are
/// needed, so no profile histogram.
fn census_fp(p: u32, n: usize, h: usize) -> (u64, u64) {
    let s = n - h - 2;
    let t = n - h - 1;
    let buckets = (p as u64).pow(u32::try_from(t).expect("t fits u32")) as usize;
    let mut counts = vec![0_u64; buckets];
    let mut total = 0_u64;
    let space = (p as u64).pow(u32::try_from(n).expect("n fits u32"));
    for code in 0..space {
        let mut c = vec![0_u32; n + 1];
        let mut rest = code;
        for slot in c.iter_mut().take(n) {
            *slot = u32::try_from(rest % u64::from(p)).expect("digit fits u32");
            rest /= u64::from(p);
        }
        c[n] = 1;
        let f = Poly::from_vec(p, c.clone());
        if f.radical().deg() > s {
            continue;
        }
        total += 1;
        let mut label = 0_usize;
        for j in 0..t {
            label = label * p as usize + c[n - 1 - j] as usize;
        }
        counts[label] += 1;
    }
    let max = counts.iter().copied().max().unwrap_or(0);
    (total, max)
}

// ---------------------------------------------------------------------------
// Part 5: the explicit refuting family.
// ---------------------------------------------------------------------------

/// Build the predicted witness for the odd endpoint and check every claim
/// about it by direct computation over `F_2`: same interval, root count in
/// range, and family size `2^delta`.
fn witness(ell: usize) -> Result<(), String> {
    let n = 2 * ell + 1;
    let h = n - ell - 1;
    let s = n - h - 2;
    let t = n - h - 1;
    let (score, winners) = best_profiles(n, h);
    let profile = winners.first().ok_or("no profile")?.clone();
    let excess = score.saturating_sub(s);
    if excess == 0 {
        println!(
            "ACB_WHM|witness|ell={ell}|n={n}|h={h}|s={s}|t={t}|profile={:?}|excess=0|no_wild_family_predicted",
            profile.d
        );
        return Ok(());
    }
    // Frozen layers are powers of one linear polynomial (one distinct root
    // each); moving layers are pseudorandom monic polynomials of the right
    // degree.  Every claim about the resulting family is then CHECKED, so the
    // construction only has to be concrete, not clever.
    let mut moving: Vec<usize> = Vec::new();
    let mut cs: Vec<u64> = vec![1; profile.d.len()];
    let mut frozen_seen = 0_u64;
    for (j, dj) in profile.d.iter().enumerate() {
        if *dj == 0 {
            continue;
        }
        let width = if j == 0 { 0 } else { dj.saturating_sub(t >> j) };
        if width > 0 {
            moving.push(j);
            // deterministic monic of degree dj
            let mut f = 1_u64 << dj;
            let mut x = 0x9E37_79B9_7F4A_7C15_u64 ^ (j as u64);
            for bit in 0..*dj {
                x = x.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                if x >> 33 & 1 == 1 {
                    f |= 1_u64 << bit;
                }
            }
            cs[j] = f;
        } else {
            // (x + a)^{dj}, a = 0 or 1, distinct per frozen layer
            let a = frozen_seen & 1;
            frozen_seen += 1;
            let lin = 0b10_u64 | a;
            let mut f = 1_u64;
            for _ in 0..*dj {
                f = f2_mul(f, lin);
            }
            cs[j] = f;
        }
    }
    let assemble = |cs: &[u64]| -> u64 {
        let mut prod = 1_u64;
        for (j, c) in cs.iter().enumerate() {
            let mut power = *c;
            for _ in 0..j {
                power = f2_mul(power, power);
            }
            prod = f2_mul(prod, power);
        }
        prod
    };
    let base = assemble(&cs);
    if f2_deg(base) != n {
        return Err(format!("witness degree {} != {n}", f2_deg(base)));
    }
    let label = (base >> (n - t)) & ((1_u64 << t) - 1);
    let widths: Vec<usize> = moving
        .iter()
        .map(|j| profile.d[*j].saturating_sub(t >> *j))
        .collect();
    let total: usize = widths.iter().sum();
    let mut members = 0_u64;
    let mut bad_interval = 0_u64;
    let mut bad_roots = 0_u64;
    let mut root_max = 0_usize;
    let mut distinct = std::collections::BTreeSet::new();
    for code in 0..(1_u64 << total) {
        let mut cs2 = cs.clone();
        let mut rest = code;
        for (idx, j) in moving.iter().enumerate() {
            let w = widths[idx];
            let u = rest & ((1_u64 << w) - 1);
            rest >>= w;
            cs2[*j] ^= u;
        }
        let f = assemble(&cs2);
        members += 1;
        distinct.insert(f);
        if f2_deg(f) != n || (f >> (n - t)) & ((1_u64 << t) - 1) != label {
            bad_interval += 1;
        }
        let r = f2_deg(f2_radical(f));
        root_max = root_max.max(r);
        if r > s {
            bad_roots += 1;
        }
    }
    println!(
        "ACB_WHM|witness|ell={ell}|n={n}|h={h}|s={s}|t={t}|profile={:?}|k={}|delta={}|score={score}|tame_score={s}|excess={excess}",
        profile.d, profile.k, profile.delta
    );
    println!(
        "ACB_WHM|witness_family|ell={ell}|moving_layers={moving:?}|widths={widths:?}|dim={total}|members={members}|distinct={}|left_interval={bad_interval}|max_distinct_roots={root_max}|root_budget={s}|over_root_budget={bad_roots}",
        distinct.len()
    );
    println!(
        "ACB_WHM|witness_verdict|ell={ell}|hm_lemma_2_6_says_dim=0|observed_family_size={}|refuted={}",
        distinct.len(),
        bad_interval == 0 && bad_roots == 0 && distinct.len() == 1_usize << total && total > 0
    );
    Ok(())
}

// ---------------------------------------------------------------------------

fn endpoints(ell: usize) -> [(usize, usize); 2] {
    let odd = 2 * ell + 1;
    let even = 2 * ell + 2;
    [(odd, odd - ell - 1), (even, even - ell - 1)]
}

fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        return Err("usage: acb_whm_strata <optimize|count|sweep|witness> ...".to_owned());
    }
    match args[0].as_str() {
        "optimize" => {
            if args.len() != 3 {
                return Err("usage: acb_whm_strata optimize <ell-lo> <ell-hi>".to_owned());
            }
            let lo: usize = args[1].parse().map_err(|_| "bad ell-lo".to_owned())?;
            let hi: usize = args[2].parse().map_err(|_| "bad ell-hi".to_owned())?;
            for ell in lo..=hi {
                for (n, h) in endpoints(ell) {
                    if h < 1 || h > n - 3 {
                        continue;
                    }
                    let s = n - h - 2;
                    let (score, winners) = best_profiles(n, h);
                    let excess = score.saturating_sub(s);
                    let (prof, k, delta) = match winners.first() {
                        Some(top) => (format!("{:?}", top.d), top.k, top.delta),
                        None => ("none".to_owned(), 0, 0),
                    };
                    println!(
                        "ACB_WHM|optimize|ell={ell}|n={n}|h={h}|s={s}|tame_codim_sing={}|excess_lower_bound={excess}|wild_codim_sing_upper={}|profile={prof}|k={k}|delta={delta}|ties={}",
                        2 * h + 3,
                        2 * h + 3 - excess,
                        winners.len()
                    );
                }
            }
        }
        "count" => {
            if args.len() != 4 {
                return Err("usage: acb_whm_strata count <p> <n> <h>".to_owned());
            }
            let p: u32 = args[1].parse().map_err(|_| "bad p".to_owned())?;
            let n: usize = args[2].parse().map_err(|_| "bad n".to_owned())?;
            let h: usize = args[3].parse().map_err(|_| "bad h".to_owned())?;
            if h < 1 || h + 3 > n {
                return Err("need 1 <= h <= n-3".to_owned());
            }
            if p == 2 {
                let (total, max, arg, histogram) = census_f2(n, h);
                println!(
                    "ACB_WHM|count|p=2|n={n}|h={h}|s={}|t={}|locus_points={total}|max_bucket={max}|argmax_label={arg}",
                    n - h - 2,
                    n - h - 1
                );
                for (prof, c) in histogram.iter().take(12) {
                    println!("ACB_WHM|count_stratum|p=2|n={n}|h={h}|profile={prof:?}|members={c}");
                }
            } else {
                let (total, max) = census_fp(p, n, h);
                println!(
                    "ACB_WHM|count|p={p}|n={n}|h={h}|s={}|t={}|locus_points={total}|max_bucket={max}",
                    n - h - 2,
                    n - h - 1
                );
            }
        }
        "sweep" => {
            if args.len() != 3 {
                return Err("usage: acb_whm_strata sweep <ell-lo> <ell-hi>".to_owned());
            }
            let lo: usize = args[1].parse().map_err(|_| "bad ell-lo".to_owned())?;
            let hi: usize = args[2].parse().map_err(|_| "bad ell-hi".to_owned())?;
            for ell in lo..=hi {
                for (n, h) in endpoints(ell) {
                    if h < 1 || h + 3 > n || n > 26 {
                        continue;
                    }
                    let s = n - h - 2;
                    let (score, winners) = best_profiles(n, h);
                    let (total, max, arg, histogram) = census_f2(n, h);
                    let top = histogram
                        .first()
                        .map(|(p, _)| p.clone())
                        .unwrap_or_default();
                    println!(
                        "ACB_WHM|sweep|ell={ell}|n={n}|h={h}|s={s}|predicted_excess={}|predicted_delta={}|locus_points={total}|max_bucket={max}|log2_max_bucket={:.3}|argmax_label={arg}|max_bucket_top_profile={top:?}",
                        score.saturating_sub(s),
                        winners.first().map(|p| p.delta).unwrap_or(0),
                        (max as f64).log2()
                    );
                }
            }
        }
        "witness" => {
            if args.len() != 2 {
                return Err("usage: acb_whm_strata witness <ell>".to_owned());
            }
            let ell: usize = args[1].parse().map_err(|_| "bad ell".to_owned())?;
            witness(ell)?;
        }
        "predict" => {
            if args.len() != 4 {
                return Err("usage: acb_whm_strata predict <p> <n> <h>".to_owned());
            }
            let p: usize = args[1].parse().map_err(|_| "bad p".to_owned())?;
            let n: usize = args[2].parse().map_err(|_| "bad n".to_owned())?;
            let h: usize = args[3].parse().map_err(|_| "bad h".to_owned())?;
            let s = n - h - 2;
            let (score, winners) = best_profiles_p(n, h, p);
            let excess = score.saturating_sub(s);
            let (prof, k, delta) = match winners.first() {
                Some(top) => (format!("{:?}", top.d), top.k, top.delta),
                None => ("none".to_owned(), 0, 0),
            };
            println!(
                "ACB_WHM|predict|p={p}|n={n}|h={h}|s={s}|tame={}|excess_lower_bound={excess}|predicted_max_bucket=p^{delta}|profile={prof}|k={k}|delta={delta}|ties={}",
                p > n,
                winners.len()
            );
        }
        other => return Err(format!("unknown mode {other}")),
    }
    Ok(())
}
