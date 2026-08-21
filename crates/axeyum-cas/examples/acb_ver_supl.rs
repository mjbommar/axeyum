//! AC-Bridge phase 3 (workstream 20, adversarial verification): an INDEPENDENT
//! re-derivation of the conductor-graded machinery that workstreams A and C
//! declared PROVED, plus the a-priori ceiling that decides how much of
//! `(SUP-L)` is actually open.
//!
//! Independence.  This example shares no code path with `gf2_hayes.rs`, with
//! `acb_cab_levels.rs` or with `acb_dic_profile.rs`:
//!
//! * the class populations `N_n(e)` come from the group-algebra Dirichlet
//!   series `N(z) = z A'(z) / A(z)` in `Z[E_ell]`, with the CLOSED FORM
//!   `A_d = 1_(V_d)` for `d <= ell` and `A_d = 2^(d-ell) * 1` for `d > ell` --
//!   no polynomial enumeration, no Moebius transform over the class vector,
//!   no Hayes character table;
//! * the conductor components `D_[j]` come from DIRECT subgroup averaging over
//!   the cylinders, not from the sibling recursion `R_(j-1) = R_j + R_j g_j`.
//!
//! Group multiplication is exploited in the only structural way this file
//! needs: for a FIXED `i`, the map `j -> i*j` on the packed coefficient
//! vectors is AFFINE over `F_2` (`c = a + (I + M_a) b`), so each shift is one
//! Gray-code walk with a single XOR per step.
//!
//! What it asserts (fail-closed: any violation exits NONZERO):
//!   sum_e N_n(e) = 2^n ;  sum_e D_e = 0 ;  D = sum_j D_[j] ;
//!   Lemma 4  : <D_[j], D_[k]> = 0 for j != k, and sum_j V_j = M_2 ;
//!   Lemma 6  : V_1 = 0, V_2 = 2^(n-ell+1) exactly, V_j <= 2^(n-ell) 2^(j-1) (j-1)^2 ;
//!   Lemma D2 : C_0 = M_2^2, C_ell = 2^ell M_4, 0 <= q_j <= 1,
//!              and R_0 = prod_j (1 + q_j) as an EXACT rational identity ;
//!   Result C4: q_1 = 0 at the odd endpoint ;
//!   the a-priori ceiling  kappa_j <= 2^((j-1)/2)  (Weil + triangle).
//!
//! What it REPORTS, and this is the point of the file: for every level it
//! prints `kappa_j` together with `kappa_j / 2^((j-1)/2)`.  A level whose
//! ceiling `2^((j-1)/2)` is at most `K` is a level on which `(SUP-L)` at that
//! `K` is a THEOREM and carries no information; `K = 2` is such a level for
//! every `j <= 3`.  The measured global maximum `2.0000` of the `kappa` table
//! sits at `j = 3` and is therefore NOT evidence about the open regime.  The
//! binding open value is `max_(j >= 4) kappa_j`, printed separately.
//!
//! Finite computation is evidence, never a theorem.
//!
//! Usage:
//!   `acb_ver_supl sweep <lo> <hi>`   -- both endpoint parities per `ell`
//!   `acb_ver_supl row <ell> <n>`     -- one row, full level table

#![allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_wrap,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::needless_range_loop,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::doc_markdown,
    clippy::explicit_iter_loop,
    clippy::manual_range_contains,
    clippy::unreadable_literal
)]

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Multiply two packed principal units mod `t^(ell+1)`.
/// bit `i-1` of the word is the coefficient `a_i`.
fn gmul(a: u32, b: u32, ell: usize) -> u32 {
    // c_k = a_k + b_k + sum_{i=1}^{k-1} a_i b_{k-i}
    let mut c: u32 = a ^ b;
    for k in 2..=ell {
        let mut acc = 0u32;
        for i in 1..k {
            acc ^= ((a >> (i - 1)) & 1) & ((b >> (k - i - 1)) & 1);
        }
        c ^= acc << (k - 1);
    }
    c
}

/// Columns of the affine map `j -> i*j`: returns `(offset, cols)` with
/// `i*j = offset ^ XOR_{q : bit q of j set} cols[q]`.
fn affine_shift(i: u32, ell: usize) -> (u32, Vec<u32>) {
    let offset = gmul(i, 0, ell); // i * 1
    let cols = (0..ell).map(|q| gmul(i, 1u32 << q, ell) ^ offset).collect();
    (offset, cols)
}

/// `out[i*j] += src[j]` for every `j`, via one Gray-code walk.
fn shift_add(out: &mut [i128], src: &[i128], i: u32, ell: usize) {
    let (offset, cols) = affine_shift(i, ell);
    let n = 1usize << ell;
    let mut c = offset;
    out[c as usize] += src[0];
    let mut prev = 0usize;
    for k in 1..n {
        let g = k ^ (k >> 1);
        let flipped = (g ^ prev).trailing_zeros() as usize;
        c ^= cols[flipped];
        out[c as usize] += src[g];
        prev = g;
    }
}

/// `N_n` as a vector over the class group, from the Dirichlet series.
fn populations(ell: usize, n: usize) -> Vec<i128> {
    let g = 1usize << ell;
    // conv(A_d, b)
    let conv = |d: usize, b: &[i128]| -> Vec<i128> {
        let mut out = vec![0i128; g];
        if d <= ell {
            for i in 0..(1usize << d) {
                shift_add(&mut out, b, i as u32, ell);
            }
        } else {
            let s: i128 = b.iter().sum();
            let f = 1i128 << (d - ell);
            for v in out.iter_mut() {
                *v = f * s;
            }
        }
        out
    };
    let mut bs: Vec<Vec<i128>> = Vec::with_capacity(n + 1);
    let mut b0 = vec![0i128; g];
    b0[0] = 1;
    bs.push(b0);
    for m in 1..=n {
        let mut acc = vec![0i128; g];
        for d in 1..=m {
            let c = conv(d, &bs[m - d]);
            for e in 0..g {
                acc[e] += c[e];
            }
        }
        for v in acc.iter_mut() {
            *v = -*v;
        }
        bs.push(acc);
    }
    let mut nn = vec![0i128; g];
    for d in 1..=n {
        let c = conv(d, &bs[n - d]);
        for e in 0..g {
            nn[e] += (d as i128) * c[e];
        }
    }
    nn
}

struct Row {
    ell: usize,
    n: usize,
    m2: BigInt,
    m4: BigInt,
    /// `V_j`, `sup_j`, `kappa_j` per level `j = 1..ell`
    v: Vec<BigRational>,
    sup: Vec<BigRational>,
    q: Vec<BigRational>,
    r0: BigRational,
}

fn big(x: i128) -> BigInt {
    BigInt::from(x)
}

fn analyze(ell: usize, n: usize) -> Result<Row, String> {
    let g = 1usize << ell;
    let nn = populations(ell, n);
    let total: i128 = nn.iter().sum();
    if total != 1i128 << n {
        return Err(format!("population invariant: sum={total} expected 2^{n}"));
    }
    let mu = 1i128 << (n - ell);
    let d: Vec<i128> = nn.iter().map(|v| v - mu).collect();
    if d.iter().sum::<i128>() != 0 {
        return Err("sum_e D_e != 0".into());
    }
    let m2: BigInt = d.iter().map(|x| big(*x) * big(*x)).sum();
    let m4: BigInt = d.iter().map(|x| big(*x).pow(4)).sum();

    // cylinder sums T_j[b] = sum over the level-j cylinder b  (b = index mod 2^j)
    let mut t: Vec<Vec<BigInt>> = Vec::with_capacity(ell + 1);
    for j in 0..=ell {
        let blocks = 1usize << j;
        let mut s = vec![BigInt::zero(); blocks];
        for (e, dv) in d.iter().enumerate() {
            s[e & (blocks - 1)] += big(*dv);
        }
        t.push(s);
    }
    // D_[j](e) = T_j[e mod 2^j] / 2^(ell-j) - T_(j-1)[e mod 2^(j-1)] / 2^(ell-j+1)
    let mut layers: Vec<Vec<BigRational>> = Vec::with_capacity(ell + 1);
    layers.push(vec![]); // index 0 unused
    for j in 1..=ell {
        let bj = 1usize << j;
        let bp = 1usize << (j - 1);
        let den_j = BigInt::from(2u32).pow((ell - j) as u32);
        let den_p = BigInt::from(2u32).pow((ell - j + 1) as u32);
        let vals: Vec<BigRational> = (0..bj)
            .map(|e| {
                BigRational::new(t[j][e].clone(), den_j.clone())
                    - BigRational::new(t[j - 1][e & (bp - 1)].clone(), den_p.clone())
            })
            .collect();
        layers.push(vals);
    }
    // reconstruction D = sum_j D_[j]  (D_[j] is constant on level-j cylinders)
    for e in 0..g {
        let mut acc = BigRational::zero();
        for j in 1..=ell {
            acc += layers[j][e & ((1usize << j) - 1)].clone();
        }
        if acc != BigRational::from(big(d[e])) {
            return Err(format!("reconstruction failed at class {e}"));
        }
    }
    // Lemma 4: orthogonality, and sum_j V_j = M_2
    let mut v = vec![BigRational::zero(); ell + 1];
    let mut sup = vec![BigRational::zero(); ell + 1];
    for j in 1..=ell {
        let mult = BigInt::from(2u32).pow((ell - j) as u32);
        let mut acc = BigRational::zero();
        let mut mx = BigRational::zero();
        for x in &layers[j] {
            acc += x.clone() * x.clone();
            if x.abs() > mx {
                mx = x.abs();
            }
        }
        v[j] = acc * BigRational::from(mult);
        sup[j] = mx;
    }
    for j in 1..=ell {
        for k in (j + 1)..=ell {
            let mut acc = BigRational::zero();
            for e in 0..g {
                acc += layers[j][e & ((1usize << j) - 1)].clone()
                    * layers[k][e & ((1usize << k) - 1)].clone();
            }
            if !acc.is_zero() {
                return Err(format!("Lemma 4 FAILED: <D_[{j}],D_[{k}]> = {acc}"));
            }
        }
    }
    let vsum: BigRational = v[1..].iter().cloned().sum();
    if vsum != BigRational::from(m2.clone()) {
        return Err(format!("sum_j V_j = {vsum} != M_2 = {m2}"));
    }
    // Lemma 6
    if !v[1].is_zero() {
        return Err(format!("Lemma 6 FAILED: V_1 = {} != 0", v[1]));
    }
    if ell >= 2 {
        let want = BigRational::from(BigInt::from(2u32).pow((n - ell + 1) as u32));
        if v[2] != want {
            return Err(format!("Lemma 6 FAILED: V_2 = {} != 2^(n-ell+1)", v[2]));
        }
    }
    for j in 2..=ell {
        let env = BigInt::from(2u32).pow((n - ell) as u32)
            * BigInt::from(2u32).pow((j - 1) as u32)
            * BigInt::from(((j - 1) * (j - 1)) as u32);
        if v[j] > BigRational::from(env.clone()) {
            return Err(format!(
                "Lemma 6 FAILED: V_{j} = {} exceeds Weil envelope {env}",
                v[j]
            ));
        }
    }
    // Lemma D2 (workstream C): C_j, q_j, and the product identity
    let mut c = Vec::with_capacity(ell + 1);
    for j in 0..=ell {
        let blocks = 1usize << j;
        let mut m = vec![BigInt::zero(); blocks];
        for (e, dv) in d.iter().enumerate() {
            m[e & (blocks - 1)] += big(*dv) * big(*dv);
        }
        let s: BigInt = m.iter().map(|x| x * x).sum();
        c.push(BigInt::from(2u32).pow(j as u32) * s);
    }
    if c[0] != m2.clone() * m2.clone() {
        return Err("Lemma D2 FAILED: C_0 != M_2^2".into());
    }
    if c[ell] != BigInt::from(2u32).pow(ell as u32) * m4.clone() {
        return Err("Lemma D2 FAILED: C_ell != 2^ell M_4".into());
    }
    let mut q = vec![BigRational::zero(); ell + 1];
    let mut prod = BigRational::one();
    for j in 1..=ell {
        let qj = BigRational::new(c[j].clone() - c[j - 1].clone(), c[j - 1].clone());
        if qj < BigRational::zero() || qj > BigRational::one() {
            return Err(format!("Lemma D2 FAILED: q_{j} = {qj} outside [0,1]"));
        }
        prod *= BigRational::one() + qj.clone();
        q[j] = qj;
    }
    let r0 = BigRational::new(
        BigInt::from(2u32).pow(ell as u32) * m4.clone(),
        m2.clone() * m2.clone(),
    );
    if prod != r0 {
        return Err(format!(
            "Lemma D2 FAILED: prod(1+q_j) = {prod} != R_0 = {r0}"
        ));
    }
    // Result C4: q_1 = 0 at the odd endpoint
    if n == 2 * ell + 1 && !q[1].is_zero() {
        return Err(format!("Result C4 FAILED: q_1 = {} at odd endpoint", q[1]));
    }
    Ok(Row {
        ell,
        n,
        m2,
        m4,
        v,
        sup,
        q,
        r0,
    })
}

fn f64_of(r: &BigRational) -> f64 {
    let (num, den) = (r.numer(), r.denom());
    let (nf, df) = (
        num.to_string().parse::<f64>(),
        den.to_string().parse::<f64>(),
    );
    match (nf, df) {
        (Ok(a), Ok(b)) if b != 0.0 && a.is_finite() && b.is_finite() => a / b,
        _ => {
            // fall back through the bit length for very large values
            let bits = num.bits() as i64 - den.bits() as i64;
            (bits as f64).exp2()
        }
    }
}

/// `kappa_j = max_e |D_[j](e)| * 2^ell / ((j-1) 2^((j-1)/2) 2^(n/2))`
fn kappa(row: &Row, j: usize) -> f64 {
    let sup = f64_of(&row.sup[j]);
    let den = ((j - 1) as f64) * (((j - 1) as f64) / 2.0).exp2() * ((row.n as f64) / 2.0).exp2()
        / (row.ell as f64).exp2();
    sup / den
}

fn ceiling(j: usize) -> f64 {
    (((j - 1) as f64) / 2.0).exp2()
}

fn report(row: &Row) -> f64 {
    println!(
        "ACB_VER|row|ell={}|n={}|M_2={}|M_4={}|R_0={:.9}",
        row.ell,
        row.n,
        row.m2,
        row.m4,
        f64_of(&row.r0)
    );
    let mut open_max = 0.0f64;
    let mut open_at = 0usize;
    for j in 2..=row.ell {
        let k = kappa(row, j);
        let c = ceiling(j);
        let trivial = c <= 2.0;
        if !trivial && k > open_max {
            open_max = k;
            open_at = j;
        }
        println!(
            "ACB_VER|level|ell={}|n={}|j={j}|V_j={}|sup={}|kappa={k:.4}|ceiling={c:.4}|\
             fill={:.4}|K2_is_theorem={trivial}|q_j={:.6e}",
            row.ell,
            row.n,
            row.v[j],
            row.sup[j],
            k / c,
            f64_of(&row.q[j])
        );
    }
    println!(
        "ACB_VER|summary|ell={}|n={}|max_kappa_all={:.4}|max_kappa_open(j>=4)={open_max:.4}@j={open_at}",
        row.ell,
        row.n,
        (2..=row.ell).map(|j| kappa(row, j)).fold(0.0f64, f64::max)
    );
    open_max
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: acb_ver_supl sweep <lo> <hi> | acb_ver_supl row <ell> <n>";
    if args.len() < 4 {
        eprintln!("{usage}");
        std::process::exit(2);
    }
    let a: usize = args[2].parse().expect("numeric");
    let b: usize = args[3].parse().expect("numeric");
    let rows: Vec<(usize, usize)> = match args[1].as_str() {
        "sweep" => (a..=b)
            .flat_map(|e| [(e, 2 * e + 1), (e, 2 * e + 2)])
            .collect(),
        "row" => vec![(a, b)],
        _ => {
            eprintln!("{usage}");
            std::process::exit(2);
        }
    };
    let mut worst_open = 0.0f64;
    let mut worst_all = 0.0f64;
    let mut failures = 0usize;
    for (ell, n) in rows {
        if ell < 2 || ell > 16 {
            eprintln!("ACB_VER|refused|ell={ell}|reason=outside the 2..16 budget window");
            failures += 1;
            continue;
        }
        match analyze(ell, n) {
            Ok(row) => {
                let o = report(&row);
                worst_open = worst_open.max(o);
                worst_all =
                    worst_all.max((2..=row.ell).map(|j| kappa(&row, j)).fold(0.0, f64::max));
            }
            Err(e) => {
                eprintln!("ACB_VER|FAIL|ell={ell}|n={n}|{e}");
                failures += 1;
            }
        }
    }
    println!(
        "ACB_VER|verdict|failures={failures}|global_max_kappa={worst_all:.4}|\
         global_max_kappa_open_levels={worst_open:.4}"
    );
    // Fail-closed: a violated assertion, or a kappa above the K = 2 the
    // reduction chain of diary 11 is calibrated on, is a NONZERO exit.
    if failures > 0 {
        eprintln!("ACB_VER|EXIT|assertion failures");
        std::process::exit(1);
    }
    if worst_all > 2.0 {
        eprintln!("ACB_VER|EXIT|(SUP-L) at K=2 REFUTED on a measured row: kappa={worst_all}");
        std::process::exit(3);
    }
}
