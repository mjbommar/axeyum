"""Plancherel forcing test on the cylinder twists `A_psi` (Sawin arXiv:2209.02170 template).

The template being applied (note 15 sec. 2.3): Plancherel fixes the TOTAL second
moment of a character family exactly; if the family vanishes off a sparse locus,
the surviving values are forced to be large; if the forced maximum exceeds the
target threshold, the square-root-cancellation statement is FALSE.  This is a
disproof template.  Here it is aimed at

    A_psi = sum_{F monic, deg F = n, <F>_{a-1} = 1} Lambda(F) psi(<F>_ell)
          = sum_{g in K} N_ell(g) psi(g),      K = ker(E_ell -> E_{a-1}),

whose square-root statement is `(CYL)`: `|A_psi| < 2^{ell-1}` for every psi != 1.

Exact integer arithmetic throughout (Python ints for every quantity that enters a
control).  Hard controls, any of which aborts the run with a nonzero exit status:

    CHECK_K_ELEMENTARY          K is elementary abelian (needs a > ell/2)
    CHECK_DIRECT_VS_WHT         direct character summation == Walsh transform
    CHECK_PARSEVAL              sum_psi A_psi^2 == |K| sum_{g in K} N(g)^2
    CHECK_NTM_VS_SSD            sum_{psi != 1} A_psi^2 == |K| * SSD_id
    CHECK_PARITY                A_psi == A_1 (mod 2) for every psi
    CHECK_TRIVIAL_CHARACTER     A_1 == sum_{g in K} N(g) == N_{a-1}(1)
    CHECK_FORCING_SOUND         the forcing lower bound never exceeds the truth
    CHECK_TOTAL_MANGOLDT        sum over all classes of N_ell == 2^n
    CHECK_LAYER_PLANCHEREL      sum_{g0} T_{j,s}(g0)^2 == 2^j sum_{chi in X} |S|^2
    CHECK_CONDUCTOR_PLANCHEREL  sum_{g0} A_j(g0)^2 == 2^j sum_{cond = j} |S|^2
    CHECK_LAYER_IDENTITY        T_{j,s}(1) == the four-population layer sum
    CHECK_REACH_BRACKET         8 ell^1.5 2^-ell/2 <= model reach <= 32 ell^1.5 2^-ell/2

`--mutation-controls` runs the pipeline seven times with one deliberate fault
each and requires that each fault trips exactly one NAMED check (and that the
clean run trips none).  Note that `CHECK_PARSEVAL` is only a control because its
two sides are computed by INDEPENDENT routes (the kernel built from generators
versus the kernel selected out of all `2^ell` classes by projection): Parseval is
an identity for whatever vector it is handed, so a single-route form of it
survives a corrupted population, which the `perturb_population` control pins.

Usage:
    lemire_cylinder_plancherel.py --dumps <dump>...  [--out-dir DIR]
                                 [--layers] [--layer-max-ell N]
    lemire_cylinder_plancherel.py --model-extrapolation [<ell>...] [--out-dir DIR]
    lemire_cylinder_plancherel.py --mutation-controls --dumps <one small dump>
"""

from __future__ import annotations

import argparse
import math
import os
import sys

import numpy as np

from lemire_layers import ek, level_populations, load_dump
from lemire_layers import h as subgroup_index


class CheckFailure(AssertionError):
    def __init__(self, name: str, detail: str = "") -> None:
        super().__init__(f"{name}: {detail}")
        self.name = name


def check(name: str, condition: bool, detail: str = "") -> None:
    if not condition:
        raise CheckFailure(name, detail)


# --------------------------------------------------------------------------
# the cylinder K and its dual
# --------------------------------------------------------------------------


def kernel_layout(ell: int, a: int):
    """Flat class indices of `K = ker(E_ell -> E_{a-1})` in K-bit order.

    Returns `(flat, kdims, weights)`: `flat[u]` is the mixed-radix index of the
    class of `K` whose K-bit pattern is `u`; `kdims[b]` is the odd Big-Witt
    degree carrying bit `b`; `weights[b] = k * 2^{e_k(ell) - 1}` is the Swan
    conductor that bit contributes (note 01 sec. 2.1), so the conductor of the
    character `psi_u` is `max_{b in u} weights[b]`.
    """
    increments, kdims, weights = kernel_bits(ell, a)
    flat = np.zeros(1, dtype=np.int64)
    for increment in increments:
        flat = np.concatenate([flat, flat + increment])
    return flat, kdims, weights


def kernel_bits(ell: int, a: int):
    """`(increments, kdims, weights)` for the K-bits, in pure Python integers.

    Split out of `kernel_layout` so that the conductor multiset of `K^dual` --
    which is all `model_reach` needs -- can be computed at any `ell`, including
    sizes where the mixed-radix strides overflow a machine word.
    """
    factors = [(k, 1 << ek(ell, k)) for k in range(1, ell + 1, 2)]
    increments: list[int] = []
    kdims: list[int] = []
    weights: list[int] = []
    stride = 1
    for k, order in factors:
        low = (1 << ek(a - 1, k)) if k <= a - 1 else 1
        quotient = order // low
        if quotient > 1:
            check(
                "CHECK_K_ELEMENTARY",
                quotient == 2,
                f"ell={ell} a={a} factor k={k}: quotient {quotient} != 2",
            )
            increments.append(stride * low)
            kdims.append(k)
            weights.append(k * (order >> 1))
        stride *= order
    return increments, kdims, weights


def projection_route_moments(ell: int, a: int, counts: np.ndarray):
    """`(|K|, sum_{g in K} N(g), sum_{g in K} N(g)^2)` by SELECTING classes.

    `kernel_layout` CONSTRUCTS the kernel from generators; this route instead
    projects every one of the `2^ell` classes to `E_{a-1}` and keeps those over
    the identity.  The two are independent computations, which is what makes the
    Parseval control able to fail: Parseval itself is an identity for whatever
    vector is handed to it, so it detects nothing unless its two sides come from
    different routes.
    """
    factors = [(k, 1 << ek(ell, k)) for k in range(1, ell + 1, 2)]
    indices = np.arange(len(counts), dtype=np.int64)
    keep = np.ones(len(counts), dtype=bool)
    stride = 1
    for k, order in factors:
        low = (1 << ek(a - 1, k)) if k <= a - 1 else 1
        if low > 1:
            keep &= (((indices // stride) % order) % low) == 0
        stride *= order
    selected = counts[keep]
    squares = sum(int(v) * int(v) for v in selected)
    return int(selected.size), int(selected.sum()), squares


def characters_direct(values: list[int]) -> list[int]:
    """`A_u = sum_g (-1)^{popcount(u & g)} N(g)` by direct summation over K x K^."""
    size = len(values)
    out = []
    for u in range(size):
        total = 0
        for g, value in enumerate(values):
            total += value if bin(u & g).count("1") % 2 == 0 else -value
        out.append(total)
    return out


def characters_walsh(values: list[int]) -> list[int]:
    """The same transform by the fast Walsh--Hadamard butterfly (exact Python ints)."""
    out = list(values)
    step = 1
    while step < len(out):
        for start in range(0, len(out), 2 * step):
            for i in range(start, start + step):
                x, y = out[i], out[i + step]
                out[i], out[i + step] = x + y, x - y
        step *= 2
    return out


def conductor_of(u: int, weights: list[int]) -> int:
    """Swan conductor in `E_ell` of the character `psi_u` of `K` (0 for u = 0)."""
    best = 0
    for bit, weight in enumerate(weights):
        if (u >> bit) & 1:
            best = max(best, weight)
    return best


# --------------------------------------------------------------------------
# part A/B: the identity-cylinder statistic
# --------------------------------------------------------------------------


def is_linear_coset(elements) -> bool:
    """Is the set a coset of a subspace of `F_2^r`? (Any 2-element set is.)"""
    elements = set(elements)
    if not elements:
        return False
    base = next(iter(elements))
    return is_linear_subspace({x ^ base for x in elements})


def is_linear_subspace(elements: set[int]) -> bool:
    if 0 not in elements:
        return False
    for x in elements:
        for y in elements:
            if x ^ y not in elements:
                return False
    return True


def cylinder_statistic(ell: int, degree: int, counts: np.ndarray, faults: set[str] | None = None):
    faults = faults or set()
    n = degree
    c = math.ceil(math.log2(ell))
    a = ell - c - 1
    flat, kdims, weights = kernel_layout(ell, a)
    size = len(flat)
    populations = [int(v) for v in counts[flat]]
    if "perturb_population" in faults:
        populations[3] += 1

    check(
        "CHECK_TOTAL_MANGOLDT",
        int(counts.sum()) == 1 << n,
        f"ell={ell} n={n}: sum of populations {int(counts.sum())} != 2^{n}",
    )

    direct = characters_direct(populations)
    walsh = characters_walsh(populations)
    if "flip_direct_sign" in faults:
        direct[1] = -direct[1]
    check(
        "CHECK_DIRECT_VS_WHT",
        direct == walsh,
        f"ell={ell} n={n}: direct character summation disagrees with the Walsh transform",
    )
    amplitudes = walsh
    if "perturb_amplitude" in faults:
        amplitudes = list(amplitudes)
        amplitudes[2] += 1

    trivial = amplitudes[0]
    check(
        "CHECK_TRIVIAL_CHARACTER",
        trivial == sum(populations),
        f"ell={ell} n={n}: A_1 {trivial} != cylinder mass {sum(populations)}",
    )
    check(
        "CHECK_PARITY",
        all((value - trivial) % 2 == 0 for value in amplitudes),
        f"ell={ell} n={n}: some A_psi has the wrong parity against A_1={trivial}",
    )

    total_mass = sum(value * value for value in amplitudes)
    selected_size, selected_sum, selected_squares = projection_route_moments(ell, a, counts)
    check(
        "CHECK_PARSEVAL",
        selected_size == size and total_mass == size * selected_squares,
        f"ell={ell} n={n}: sum_psi A_psi^2 = {total_mass} != |K| sum N^2 = "
        f"{size * selected_squares} (|K| by construction {size}, by selection {selected_size})",
    )

    # SSD_id computed the other way round: |K| * sum (N - mean)^2, kept integral.
    ssd_numerator = size * sum(v * v for v in populations) - trivial * trivial
    nontrivial_mass = total_mass - trivial * trivial
    if "drop_trivial_character" in faults:
        nontrivial_mass = total_mass
    check(
        "CHECK_NTM_VS_SSD",
        nontrivial_mass == ssd_numerator,
        f"ell={ell} n={n}: sum_{{psi!=1}} A^2 = {nontrivial_mass} != |K| SSD_id = {ssd_numerator}",
    )

    threshold = 1 << (ell - 1)
    threshold_square = threshold * threshold
    tail = amplitudes[1:]
    absolutes = sorted(abs(v) for v in tail)
    maximum = absolutes[-1]
    zeros = sum(1 for v in absolutes if v == 0)
    zero_set = {u for u, v in enumerate(amplitudes) if u and v == 0}

    denominator = size - 1 - zeros
    if "shrink_forcing_denominator" in faults:
        denominator = max(1, denominator // 8)
    forced_zero = _sqrt_ceiling(nontrivial_mass, denominator)
    check(
        "CHECK_FORCING_SOUND",
        forced_zero <= maximum * maximum,
        f"ell={ell} n={n}: forcing bound {forced_zero} exceeds the true max^2 {maximum * maximum}",
    )

    # strongest forcing available from the empirical small-value distribution:
    # for every observed cut tau, Z_tau = #{psi != 1 : |A_psi| <= tau}.
    best_forced = 0
    best_tau = 0
    best_count = 0
    for position, tau in enumerate(absolutes[:-1]):
        count = position + 1
        while count < len(absolutes) - 1 and absolutes[count] == tau:
            count += 1
        remaining = nontrivial_mass - count * tau * tau
        bound = _sqrt_ceiling(remaining, len(absolutes) - count)
        if bound > best_forced:
            best_forced, best_tau, best_count = bound, tau, count
    check(
        "CHECK_FORCING_SOUND",
        best_forced <= maximum * maximum,
        f"ell={ell} n={n}: empirical forcing {best_forced} exceeds max^2 {maximum * maximum}",
    )

    model = (1 << (n - a + 1)) * sum(conductor_of(u, weights) - 1 for u in range(1, size))

    # Structure probe on the SMALLEST values: if the near-vanishing psi were the
    # annihilator of a sub-cylinder they would form a coset.  m = 2 is trivially
    # a coset and is reported only to keep the reader honest about that.
    order = sorted((u for u in range(1, size)), key=lambda u: abs(amplitudes[u]))
    smallest_coset = {m: is_linear_coset(order[:m]) for m in (2, 4, 8, 16)}

    refutable = nontrivial_mass >= threshold_square
    zeros_needed = max(0, size - 1 - nontrivial_mass // threshold_square) if refutable else None

    return dict(
        ell=ell,
        n=n,
        a=a,
        c=c,
        K=size,
        kdims=kdims,
        weights=weights,
        populations=populations,
        amplitudes=amplitudes,
        conductors=[conductor_of(u, weights) for u in range(size)],
        trivial=trivial,
        mean_model=1 << (n - a + 1),
        total_mass=total_mass,
        nontrivial_mass=nontrivial_mass,
        model_mass=model,
        threshold=threshold,
        threshold_square=threshold_square,
        maximum=maximum,
        zeros=zeros,
        zero_set=zero_set,
        forced_zero=forced_zero,
        best_forced=best_forced,
        best_tau=best_tau,
        best_count=best_count,
        ceiling=nontrivial_mass,
        refutable=refutable,
        zeros_needed=zeros_needed,
        smallest_coset=smallest_coset,
        sorted_absolutes=absolutes,
    )


def _sqrt_ceiling(mass: int, denominator: int) -> int:
    """The forced `max^2` lower bound `mass / denominator`, kept as an integer floor."""
    if denominator <= 0:
        return 0
    return mass // denominator


# --------------------------------------------------------------------------
# part D: the twisted layer family and the twisted conductor family
# --------------------------------------------------------------------------


def exact_sum_of_squares(values: np.ndarray) -> int:
    total = 0
    for start in range(0, values.size, 1 << 16):
        chunk = values[start : start + (1 << 16)].astype(object)
        total += int((chunk * chunk).sum())
    return total


def coset_labels(indices: np.ndarray, factors, s: int):
    """Label of each index modulo the power subgroup `2^s E_j`, plus the label count."""
    labels = np.zeros(len(indices), dtype=np.int64)
    stride = 1
    label_stride = 1
    for _, order in factors:
        modulus = min(order, 1 << s)
        digit = (indices // stride) % order
        labels += (digit % modulus) * label_stride
        label_stride *= modulus
        stride *= order
    return labels, label_stride


def project_indices(indices: np.ndarray, factors_from, factors_to):
    out = np.zeros(len(indices), dtype=np.int64)
    stride = 1
    target_stride = 1
    targets = dict(factors_to)
    for k, order in factors_from:
        digit = (indices // stride) % order
        if k in targets:
            out += (digit % targets[k]) * target_stride
            target_stride *= targets[k]
        stride *= order
    return out


def coset_sums(populations: np.ndarray, labels: np.ndarray, count: int) -> np.ndarray:
    sums = np.zeros(count, dtype=object)
    accumulator = np.zeros(count, dtype=np.int64)
    np.add.at(accumulator, labels, populations)
    sums[:] = [int(v) for v in accumulator]
    return sums


def partner_indices(indices: np.ndarray, factors, j: int) -> np.ndarray:
    """Multiplication by `1 + x^j`: adds `2^{v_2(j)}` in the Big-Witt factor `odd(j)`."""
    odd, valuation = j, 0
    while odd % 2 == 0:
        odd //= 2
        valuation += 1
    position = next(i for i, (k, _) in enumerate(factors) if k == odd)
    stride = 1
    for _, order in factors[:position]:
        stride *= order
    order = factors[position][1]
    digit = (indices // stride) % order
    step = (1 << valuation) * stride
    return indices + np.where(digit + (1 << valuation) < order, step, -step)


def layer_statistic(ell: int, degree: int, counts: np.ndarray, faults: set[str] | None = None):
    """Twisted layer sums `T_{j,s}(g0)` and twisted conductor sums `A_j(g0)`."""
    faults = faults or set()
    n = degree
    c = math.ceil(math.log2(ell))
    a = ell - c - 1
    rows = []
    cache: dict[int, tuple] = {}

    def level(j: int):
        if j not in cache:
            cache[j] = level_populations(ell, counts, j)
        return cache[j]

    for j in range(max(a, 2), ell + 1):
        factors_j, populations_j = level(j)
        factors_prev, populations_prev = level(j - 1)
        indices = np.arange(1 << j, dtype=np.int64)
        projected = project_indices(indices, factors_j, factors_prev)

        # --- conductor family A_j(g0) = 2^{j-1} H_j(g0) ---
        partners = partner_indices(indices, factors_j, j)
        imbalance = populations_j[indices] - populations_j[partners]
        left = (1 << (2 * j - 2)) * exact_sum_of_squares(imbalance)
        square_j = exact_sum_of_squares(populations_j)
        square_prev = exact_sum_of_squares(populations_prev)
        if "perturb_conductor_mass" in faults and j == max(a, 2):
            square_j += 1
        right = (1 << j) * ((1 << j) * square_j - (1 << (j - 1)) * square_prev)
        check(
            "CHECK_CONDUCTOR_PLANCHEREL",
            left == right,
            f"ell={ell} n={n} j={j}: {left} != {right}",
        )
        conductor_values = [abs(int(v)) * (1 << (j - 1)) for v in imbalance]
        conductor_max = max(conductor_values)
        conductor_identity = conductor_values[0]
        conductor_zeros = sum(1 for v in conductor_values if v == 0)
        conductor_rank = sum(1 for v in conductor_values if v > conductor_identity) + 1
        conductor_mass = left
        conductor_points = 1 << j
        conductor_forced = _sqrt_ceiling(conductor_mass, conductor_points - conductor_zeros)
        check(
            "CHECK_FORCING_SOUND",
            conductor_forced <= conductor_max * conductor_max,
            f"ell={ell} n={n} j={j}: conductor forcing exceeds the truth",
        )
        conductor_threshold = ((1 << (j - 1)) * (j - 1) * (1 << math.ceil(n / 2))) // (4 * ell)

        smax = ek(j, 1)
        subgroup_cache: dict[int, tuple] = {}

        def cosets(level_factors, level_populations_array, s: int, key):
            if (key, s) not in subgroup_cache:
                labels, count = coset_labels(
                    np.arange(len(level_populations_array), dtype=np.int64), level_factors, s
                )
                subgroup_cache[(key, s)] = (
                    labels,
                    count,
                    coset_sums(level_populations_array, labels, count),
                )
            return subgroup_cache[(key, s)]

        for s in range(1, smax + 1):
            width = (subgroup_index(j, s) - subgroup_index(j, s - 1)) - (
                subgroup_index(j - 1, s) - subgroup_index(j - 1, s - 1)
            )
            if width <= 0:
                continue
            labels_s, count_s, sums_s = cosets(factors_j, populations_j, s, "j")
            labels_p, count_p, sums_p = cosets(factors_j, populations_j, s - 1, "j")
            prev_labels_s, prev_count_s, prev_sums_s = cosets(
                factors_prev, populations_prev, s, "j-1"
            )
            prev_labels_p, prev_count_p, prev_sums_p = cosets(
                factors_prev, populations_prev, s - 1, "j-1"
            )

            twisted = (
                subgroup_index(j, s) * sums_s[labels_s]
                - subgroup_index(j, s - 1) * sums_p[labels_p]
                - subgroup_index(j - 1, s) * prev_sums_s[prev_labels_s[projected]]
                + subgroup_index(j - 1, s - 1) * prev_sums_p[prev_labels_p[projected]]
            )
            left = int(sum(int(v) * int(v) for v in twisted))
            spectral = (
                subgroup_index(j, s) * int(sum(int(v) * int(v) for v in sums_s))
                - subgroup_index(j, s - 1) * int(sum(int(v) * int(v) for v in sums_p))
                - subgroup_index(j - 1, s) * int(sum(int(v) * int(v) for v in prev_sums_s))
                + subgroup_index(j - 1, s - 1)
                * int(sum(int(v) * int(v) for v in prev_sums_p))
            )
            if "perturb_layer_spectrum" in faults and s == 1:
                spectral += 1
            check(
                "CHECK_LAYER_PLANCHEREL",
                left == (1 << j) * spectral,
                f"ell={ell} n={n} j={j} s={s}: {left} != 2^{j} * {spectral}",
            )

            identity = int(twisted[0])
            expected = subgroup_index(j - 1, s) * (
                2 * int(sums_s[labels_s[0]]) - int(prev_sums_s[prev_labels_s[0]])
            ) - (
                0
                if j % (1 << (s - 1)) == 0
                else subgroup_index(j - 1, s - 1)
                * (2 * int(sums_p[labels_p[0]]) - int(prev_sums_p[prev_labels_p[0]]))
            )
            check(
                "CHECK_LAYER_IDENTITY",
                identity == expected,
                f"ell={ell} n={n} j={j} s={s}: T(1)={identity} != four-population {expected}",
            )

            absolutes = [abs(int(v)) for v in twisted]
            maximum = max(absolutes)
            zeros = sum(1 for v in absolutes if v == 0)
            rank = sum(1 for v in absolutes if v > abs(identity)) + 1
            points = len(absolutes)
            allowance = width * (j - 1) * (1 << math.ceil(n / 2))
            hwo_threshold = allowance // (4 * ell)
            forced = _sqrt_ceiling(left, points - zeros) if points - zeros else 0
            check(
                "CHECK_FORCING_SOUND",
                forced <= maximum * maximum,
                f"ell={ell} n={n} j={j} s={s}: layer forcing exceeds the truth",
            )
            rows.append(
                dict(
                    kind="layer",
                    j=j,
                    s=s,
                    width=width,
                    points=points,
                    identity=identity,
                    maximum=maximum,
                    zeros=zeros,
                    rank=rank,
                    total_mass=left,
                    forced=forced,
                    hwo_threshold=hwo_threshold,
                )
            )
        rows.append(
            dict(
                kind="conductor",
                j=j,
                s=None,
                width=1 << (j - 1),
                points=conductor_points,
                identity=conductor_identity,
                maximum=conductor_max,
                zeros=conductor_zeros,
                rank=conductor_rank,
                total_mass=conductor_mass,
                forced=conductor_forced,
                hwo_threshold=conductor_threshold,
            )
        )
    return rows


# --------------------------------------------------------------------------
# reporting
# --------------------------------------------------------------------------


def format_cylinder_row(r: dict) -> str:
    thr = r["threshold"]
    ratio = math.sqrt(r["nontrivial_mass"]) / thr
    return (
        f"ell={r['ell']:2d} n={r['n']:2d} a={r['a']:2d} |K|={r['K']:4d} "
        f"A_1={r['trivial']:16d} mean_2^(n-a+1)={r['mean_model']:16d} | "
        f"NTM={r['nontrivial_mass']:24d} model={r['model_mass']:24d} "
        f"NTM/model={r['nontrivial_mass'] / r['model_mass']:.4f} | "
        f"zeros={r['zeros']:3d}/{r['K'] - 1:3d} max={r['maximum']:12d} "
        f"max/thr={r['maximum'] / thr:.4f} | "
        f"forced={int(math.isqrt(r['forced_zero'])):12d} "
        f"forced/thr={math.sqrt(r['forced_zero']) / thr:.4f} "
        f"ceiling/thr={ratio:.4f} thr=2^(ell-1)={thr} "
        f"REFUTABLE={'YES' if r['refutable'] else 'NO'}"
    )


def run(paths, out_dir, do_layers, layer_max_ell):
    results = []
    for path in paths:
        ell, degree, factors, counts = load_dump(path)
        r = cylinder_statistic(ell, degree, counts)
        results.append(r)
        print(format_cylinder_row(r))
        sys.stdout.flush()
    if out_dir:
        _write_cylinder_files(results, out_dir)
    layer_rows = []
    if do_layers:
        for path in paths:
            ell, degree, factors, counts = load_dump(path)
            if ell > layer_max_ell:
                continue
            for row in layer_statistic(ell, degree, counts):
                row["ell"], row["n"] = ell, degree
                layer_rows.append(row)
                print(_format_layer_row(row))
                sys.stdout.flush()
        if out_dir:
            _write_layer_file(layer_rows, out_dir)
    return results, layer_rows


def _format_layer_row(row: dict) -> str:
    label = f"{row['kind']:9s} j={row['j']:2d} s={'-' if row['s'] is None else row['s']}"
    thr = row["hwo_threshold"]
    maximum = row["maximum"]
    return (
        f"ell={row['ell']:2d} n={row['n']:2d} {label} points={row['points']:9d} "
        f"zeros={row['zeros']:9d} |identity|={abs(row['identity']):18d} "
        f"max={maximum:18d} rank={row['rank']:9d} "
        f"forced={int(math.isqrt(row['forced'])):18d} "
        f"hwo_thr={thr:18d} mass={row['total_mass']} "
        f"need_surviving={(row['total_mass'] / (thr * thr) / row['points'] if thr else float('inf')):.4e} "
        f"surviving={(row['points'] - row['zeros']) / row['points']:.6f} "
        f"max/thr={(maximum / thr if thr else float('nan')):.4f} "
        f"forced/thr={(math.sqrt(row['forced']) / thr if thr else float('nan')):.4f}"
    )


def _open_output(out_dir: str, name: str):
    if not name.startswith("plancherel-"):
        raise SystemExit(f"refusing to write {name}: data files must be prefixed plancherel-")
    os.makedirs(out_dir, exist_ok=True)
    return open(os.path.join(out_dir, name), "w")


def _write_cylinder_files(results, out_dir):
    with _open_output(out_dir, "plancherel-cylinder-ell12-24.txt") as fh:
        fh.write(
            "# Plancherel forcing on the identity-cylinder twists A_psi.\n"
            "# NTM = sum_{psi != 1} A_psi^2 = |K| * SSD_id (exact).\n"
            "# model = 2^{n-a+1} sum_{psi != 1} (cond(psi) - 1)  (Sato-Tate / Keating-Rudnick).\n"
            "# forced = sqrt(NTM / (|K| - 1 - Z)) with Z the exact-zero count.\n"
            "# ceiling = sqrt(NTM): the forcing lemma's absolute maximum (all mass on one psi).\n"
            "# REFUTABLE=YES iff NTM >= 2^{2ell-2}, i.e. iff SOME vanishing pattern could\n"
            "# force max |A_psi| >= 2^{ell-1} and refute (CYL).\n"
        )
        for r in results:
            fh.write(format_cylinder_row(r) + "\n")
    with _open_output(out_dir, "plancherel-cylinder-spectra.txt") as fh:
        fh.write(
            "# The exact multiset {A_psi}. Columns: ell n psi cond(psi) A_psi |A|/2^(ell-1)\n"
        )
        for r in results:
            for u, value in enumerate(r["amplitudes"]):
                fh.write(
                    f"ell={r['ell']:2d} n={r['n']:2d} psi={u:4d} cond={r['conductors'][u]:3d} "
                    f"A={value:16d} rel={abs(value) / r['threshold']:.6f}\n"
                )
    with _open_output(out_dir, "plancherel-cylinder-forcing.txt") as fh:
        fh.write(
            "# Forcing detail. small(t) = #{psi != 1 : |A_psi| <= t * 2^(ell-1)}.\n"
            "# best_forced = max over observed cuts tau of sqrt((NTM - Z_tau tau^2)/(|K|-1-Z_tau)).\n"
            "# smallest_m_is_coset: do the m psi with the smallest |A_psi| form a coset of a\n"
            "# subspace of K^dual (which is what an annihilator of a sub-cylinder would be)?\n"
            "# m=2 is a coset for trivial reasons; the chance rate at m=4, |K|=128 is 0.8%.\n"
            "# Z_needed = the exact-zero count that would refute (CYL); - means impossible\n"
            "# (no vanishing pattern whatever can force max |A_psi| >= 2^(ell-1)).\n"
        )
        for r in results:
            thr = r["threshold"]
            cuts = [0.0, 0.001, 0.01, 0.05, 0.1, 0.25, 0.5]
            counts = [
                sum(1 for v in r["sorted_absolutes"] if v <= t * thr) for t in cuts
            ]
            rms = math.sqrt(r["nontrivial_mass"] / (r["K"] - 1))
            smallest = r["sorted_absolutes"][0]
            valuations = sorted(
                (v & -v).bit_length() - 1 for v in r["sorted_absolutes"] if v
            )
            fh.write(
                f"ell={r['ell']:2d} n={r['n']:2d} |K|-1={r['K'] - 1:3d} "
                + " ".join(f"small({t})={c}" for t, c in zip(cuts, counts))
                + f" | min|A|={smallest} min/rms={smallest / rms:.4f} rms/thr={rms / thr:.4f}"
                f" v2(A_1)={((r['trivial'] & -r['trivial']).bit_length() - 1)}"
                f" v2min={valuations[0]} v2max={valuations[-1]}"
                + f" | best_forced/thr={math.sqrt(r['best_forced']) / thr:.4f}"
                f" at tau/thr={r['best_tau'] / thr:.6f} Z_tau={r['best_count']}"
                f" | ceiling/thr={math.sqrt(r['ceiling']) / thr:.4f}"
                f" Z_needed={r['zeros_needed'] if r['refutable'] else '-'}"
                f" | zero_set_is_subgroup="
                f"{is_linear_subspace(r['zero_set'] | {0}) if r['zero_set'] else 'n/a'}"
                + " smallest_m_is_coset="
                + ",".join(f"{m}:{int(v)}" for m, v in r["smallest_coset"].items())
                + "\n"
            )


def _write_layer_file(rows, out_dir):
    with _open_output(out_dir, "plancherel-layers-ell12-22.txt") as fh:
        fh.write(
            "# Plancherel forcing on the TWISTED layer family T_{j,s}(g0) and the twisted\n"
            "# conductor family A_j(g0) = 2^{j-1} H_j(g0), g0 in E_j.\n"
            "# Identity: sum_{g0} T_{j,s}(g0)^2 = 2^j sum_{chi in X_{j,s}} |S_n(chi)|^2 (exact).\n"
            "# hwo_thr = #X (j-1) 2^{ceil(n/2)} / (4 ell): the (HWO) allowance at g0 = 1.\n"
            "# need_surviving = mass / (hwo_thr^2 * points): the fraction of E_j on which the\n"
            "# family may survive if the forcing is to reach the (HWO) allowance at all.\n"
            "# surviving = the measured fraction. Refutation needs surviving <= need_surviving.\n"
            "# NOTE the quantifier: forcing produces SOME g0, while (HWO) is the claim at g0 = 1.\n"
        )
        for row in rows:
            fh.write(_format_layer_row(row) + "\n")


# --------------------------------------------------------------------------
# mutation controls
# --------------------------------------------------------------------------


MUTATIONS = [
    ("perturb_population", "CHECK_PARSEVAL", False),
    ("flip_direct_sign", "CHECK_DIRECT_VS_WHT", False),
    ("perturb_amplitude", "CHECK_PARITY", False),
    ("drop_trivial_character", "CHECK_NTM_VS_SSD", False),
    ("shrink_forcing_denominator", "CHECK_FORCING_SOUND", False),
    ("perturb_layer_spectrum", "CHECK_LAYER_PLANCHEREL", True),
    ("perturb_conductor_mass", "CHECK_CONDUCTOR_PLANCHEREL", True),
]


def mutation_controls(path: str) -> int:
    ell, degree, factors, counts = load_dump(path)
    failures = []
    try:
        cylinder_statistic(ell, degree, counts)
        layer_statistic(ell, degree, counts)
    except CheckFailure as exc:
        print(f"CONTROL|clean|UNEXPECTED_FAILURE|{exc}")
        return 1
    print("CONTROL|clean|no check tripped|OK")
    for fault, expected, is_layer in MUTATIONS:
        try:
            if is_layer:
                layer_statistic(ell, degree, counts, faults={fault})
            else:
                cylinder_statistic(ell, degree, counts, faults={fault})
        except CheckFailure as exc:
            status = "OK" if exc.name == expected else "WRONG_CHECK"
            print(f"CONTROL|{fault}|tripped {exc.name}|expected {expected}|{status}")
            if status != "OK":
                failures.append(fault)
        else:
            print(f"CONTROL|{fault}|SURVIVED|expected {expected}|FAIL")
            failures.append(fault)
    if failures:
        print(f"MUTATION CONTROLS FAILED: {failures}")
        return 1
    print(f"MUTATION CONTROLS PASSED: {len(MUTATIONS)}/{len(MUTATIONS)}")
    return 0


def model_reach(ell: int, n: int):
    """The template's reach `sqrt(NTM_model) / 2^{ell-1}` at (ell, n), exactly.

    `NTM_model = 2^{n-a+1} * Sigma`, `Sigma = sum_{psi != 1} (cond(psi) - 1)`
    (P4).  `Sigma` depends on `ell` alone -- it is a property of the conductor
    multiset of `K^dual` -- so this needs no population data and extrapolates to
    any `ell`, including the first row where `(HWO)`/`(CYL)` is claimed.
    """
    c = math.ceil(math.log2(ell))
    a = ell - c - 1
    _, _, weights = kernel_bits(ell, a)
    size = 1 << len(weights)
    sigma = sum(conductor_of(u, weights) - 1 for u in range(1, size))
    mass = (1 << (n - a + 1)) * sigma
    # log2 first: at ell = 1024 the mass has ~2100 bits and does not fit a float.
    log_reach = 0.5 * math.log2(mass) - (ell - 1)
    reach = 2.0**log_reach if log_reach > -1000 else 0.0
    return dict(ell=ell, n=n, a=a, c=c, K=size, sigma=sigma, mass=mass,
                reach=reach, log_reach=log_reach)


def print_model_extrapolation(ells, out_dir=None):
    lines = [
        "# The Plancherel template's reach sqrt(NTM_model)/2^(ell-1), model (P4), exact.",
        "# Sigma = sum_{psi != 1} (cond(psi) - 1) depends on ell alone; no dump needed.",
        "# reach >= 1 is the ONLY regime in which any vanishing pattern could refute (CYL).",
        "# bracket = 8 ell^1.5 2^(-ell/2) .. 32 ell^1.5 2^(-ell/2)  (Proposition 5);",
        "# the run ASSERTS the reach lies inside it at every ell printed.",
    ]
    for ell in ells:
        for n in (2 * ell + 1, 2 * ell + 2):
            r = model_reach(ell, n)
            low = 8 * ell**1.5 * 2 ** (-ell / 2)
            high = 32 * ell**1.5 * 2 ** (-ell / 2)
            check(
                "CHECK_REACH_BRACKET",
                low <= r["reach"] <= high,
                f"ell={ell} n={n}: reach {r['reach']:.4e} outside [{low:.4e},{high:.4e}]",
            )
            lines.append(
                f"ell={ell:5d} n={n:5d} c={r['c']:2d} |K|={r['K']:6d} Sigma={r['sigma']:10d} "
                f"reach=2^{r['log_reach']:+.2f}={r['reach']:.4e} bracket=[{low:.3e},{high:.3e}] "
                f"{'CAN REFUTE' if r['reach'] >= 1 else 'cannot refute'}"
            )
    text = "\n".join(lines)
    print(text)
    if out_dir:
        with _open_output(out_dir, "plancherel-model-reach.txt") as fh:
            fh.write(text + "\n")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dumps", nargs="*", default=[])
    parser.add_argument("--model-extrapolation", nargs="*", type=int, default=None)
    parser.add_argument("--out-dir", default=None)
    parser.add_argument("--layers", action="store_true")
    parser.add_argument("--layer-max-ell", type=int, default=22)
    parser.add_argument("--mutation-controls", action="store_true")
    args = parser.parse_args(argv)
    if args.model_extrapolation is not None:
        ells = args.model_extrapolation or [
            *range(12, 25), 32, 33, 48, 64, 65, 100, 128, 129, 200, 512, 1024
        ]
        print_model_extrapolation(ells, args.out_dir)
        if not args.dumps:
            return 0
    if not args.dumps:
        raise SystemExit("--dumps is required unless --model-extrapolation is given")
    if args.mutation_controls:
        return mutation_controls(args.dumps[0])
    run(args.dumps, args.out_dir, args.layers, args.layer_max_ell)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except CheckFailure as exc:
        print(f"CHECK FAILED: {exc}", file=sys.stderr)
        sys.exit(2)
