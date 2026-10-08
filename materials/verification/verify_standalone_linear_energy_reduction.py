"""Independent finite algebra checks for the reconstructed coarse reduction.

Finite tests cannot establish asymptotic constants, global classification, or
the uniform permanent theorem used as an explicit input in the research note.
"""
from fractions import Fraction as F
from itertools import combinations
import json
from math import factorial, lgamma, log, prod
from random import Random

import numpy as np

from centered_permanent_coefficients import carousel
from diagnose_score_adaptive_error import potentials
from verify_carousel_repair_audit import all_tournaments
from verify_extreme_local_max import count_paths
from verify_local_two_permanent_formula import subset_permanent
from verify_word_minor_and_cube import determinant_integer
from verify_preconditioned_nonprincipal_scaling import exact_checks as nonprincipal_checks
from verify_extreme_cross_decomposition import audit, paired_bound_checks


def rows_of(s):
    return tuple(sum(1 << j for j, v in enumerate(row) if v == 1) for row in s)


def restriction(s, ids):
    return [[s[i][j] for j in ids] for i in ids]


def rank_cap(s, ambient):
    """Exact comparison, using 2(1+1/n)^N rather than the larger 2e."""
    size = len(s)
    assert ambient >= size >= 1
    numerator = determinant_integer([
        [(ambient+1)*int(i == j)+1+s[i][j] for j in range(size)]
        for i in range(size)])
    spectral_num = determinant_integer([
        [size*int(i == j)+s[i][j] for j in range(size)]
        for i in range(size)])
    assert numerator > 0 and spectral_num > 0
    # numerator/ambient^N <= 2(1+1/ambient)^N spectral_num/N^N.
    assert numerator*size**size <= 2*(ambient+1)**size*spectral_num
    return numerator


def scalar_curvature_checks():
    records = []
    running_factorial = 1
    minimum = None
    for k in range(2, 1001):
        running_factorial *= k-1
        # The two ingredients proving a dimension-free curvature constant.
        assert k**(k-1) >= 2**(k-1)*running_factorial
        assert (k+1)**k < 3*k**k
        prev = lgamma(k)/(k-1)
        current = lgamma(k+1)/k
        following = lgamma(k+2)/(k+1)
        scaled = ((current-prev)-(following-current))*k*(k+1)
        assert scaled > 0.25
        minimum = scaled if minimum is None else min(minimum, scaled)
        if k in (2, 3, 5, 10, 100, 1000):
            records.append({"k": k, "scaled_second_difference": scaled})
    # The formal proof uses log(4/3) >= 1/4, not a floating lower bound.
    assert log(F(4, 3)) > 0.25
    print("PASS integer AM-GM/binomial curvature ingredients: 999 cases", flush=True)
    return {"integer_curvature_cases": 999, "minimum_numeric_scaled_curvature": minimum,
            "curvature_diagnostics": records}


def matrix_checks(s, weighted=True):
    n = len(s)
    scores = [sum(row) for row in s]
    variance = F(sum(z*z for z in scores), 4)
    rows = rows_of(s)
    dets, perms, deletion_count, caps = {}, {}, 0, 0
    for mask in range(1 << n):
        ids = [i for i in range(n) if mask >> i & 1]
        sp = restriction(s, ids)
        k = len(ids)
        d = determinant_integer([
            [int(i == j)+int(sp[i][j] == 1) for j in range(k)]
            for i in range(k)]) if k else 1
        assert d > 0
        assert F(d*d) <= F(k+1, 2)**k
        dets[mask] = d
        perms[mask] = subset_permanent(rows_of(sp))
        removed = n-k
        remaining_var = F(sum(sum(row)**2 for row in sp), 4)
        shortfall = variance-F(removed*n*n, 4)-remaining_var
        if shortfall > 0:
            assert shortfall*shortfall <= removed*removed*n*variance
        deletion_count += 1
        if k:
            rank_cap(sp, n)
            caps += 1
    full = (1 << n)-1
    convolution = sum(dets[mask]*perms[full ^ mask] for mask in dets)
    assert convolution == count_paths(rows)
    assert sum(dets[mask]*F(2, n)**mask.bit_count() for mask in dets) == F(
        rank_cap(s, n), n**n)
    weighted_check = 0
    if weighted and all(abs(z) < n-1 for z in scores):
        denominators = [(n-1)**2-z*z for z in scores]
        weights = [F((n-1)**2, d) for d in denominators]
        diagonal_num = determinant_integer([
            [n*denominators[i]*int(i == j)
             +(n-1)**2*(int(i == j)+1+s[i][j]) for j in range(n)]
            for i in range(n)])
        generated = sum(dets[mask]*F(2, n)**mask.bit_count()
                        *prod(weights[i] for i in range(n) if mask >> i & 1)
                        for mask in dets)
        assert generated == F(diagonal_num, n**n*prod(denominators))
        assert generated > 0
        weighted_check = 1
    return deletion_count, caps+1, weighted_check


def exact_global_checks():
    graphs = deletions = caps = weighted = 0
    for n in range(1, 6):
        for s in all_tournaments(n):
            dc, rc, wc = matrix_checks(s, weighted=n >= 3)
            graphs += 1
            deletions += dc
            caps += rc
            weighted += wc
        print("PASS complete labeled matrix/path/subset/rank-cap algebra n =", n, flush=True)
    rng = Random(2026100512)
    for n in (6, 7, 8, 9):
        c = carousel(n) if n % 2 else [[i-j and (1 if i < j else -1)
                                      for j in range(n)] for i in range(n)]
        samples = [c]
        for _ in range(2):
            s = [[0]*n for _ in range(n)]
            for i, j in combinations(range(n), 2):
                s[i][j] = rng.choice((-1, 1))
                s[j][i] = -s[i][j]
            samples.append(s)
        for s in samples:
            dc, rc, wc = matrix_checks(s)
            graphs += 1
            deletions += dc
            caps += rc
            weighted += wc
    print("PASS exact full-subset checks:", graphs, "graphs;", deletions,
          "score deletions;", caps, "rank caps;", weighted, "weighted generators", flush=True)
    return {"exact_graphs": graphs, "exact_score_deletion_checks": deletions,
            "exact_rank_cap_checks": caps, "exact_weighted_generator_checks": weighted}


def degree_interpolation_checks():
    rng = Random(2026100513)
    count, minimum_slack = 0, None
    for n in range(3, 102):
        center = F(n-1, 2)
        lower, upper = int(center), int(center+F(1, 2))
        mean_value = (lgamma(lower+1)/lower+lgamma(upper+1)/upper)/2
        # Odd mean is an integer, so lower == upper.
        for _ in range(10):
            s = [[0]*n for _ in range(n)]
            for i, j in combinations(range(n), 2):
                s[i][j] = rng.choice((-1, 1))
                s[j][i] = -s[i][j]
            degrees = [sum(v == 1 for v in row) for row in s]
            if not min(degrees):
                continue
            variance = sum((d-float(center))**2 for d in degrees)
            observed = sum(lgamma(d+1)/d for d in degrees)
            bound = n*mean_value-(variance-n/4)/(8*n*n)
            slack = bound-observed
            assert slack > -1e-12
            minimum_slack = slack if minimum_slack is None else min(minimum_slack, slack)
            count += 1
    print("PASS odd/even mean curvature diagnostics:", count, "degree sequences", flush=True)
    return {"degree_interpolation_diagnostics": count,
            "minimum_degree_interpolation_slack": minimum_slack}


def moderate_diagnostics():
    records = []
    for n in (33, 65, 129, 257):
        for label in ("single_edge", "sqrt_hub", "moderate_hub"):
            s = np.asarray(carousel(n), float)
            k = 1 if label == "single_edge" else int(n**0.5) if label == "sqrt_hub" else n//3
            for j in range(1, k+1):
                s[0, j] *= -1
                s[j, 0] *= -1
            a = s.sum(axis=1)/(n-1)
            tau = float(a@a)
            assert np.max(abs(a)) < 0.9
            raw = (1-np.eye(n)+s)/(n-1)
            pre = raw/(1+a[:, None])/(1-a[None, :])
            nu = float(pre.sum()-n)
            normalized = n*pre/pre.sum()
            x, y, bmat, residual = potentials(normalized)
            assert residual < 2e-13
            scale = (tau+tau*tau)/n+tau**1.5/n**0.5
            records.append({
                "n": n, "label": label, "tau": tau, "score_energy": float(np.sum(s.sum(axis=1)**2)),
                "mass_error_over_budget": abs(nu)/scale,
                "scaled_frobenius_over_budget": float(np.linalg.norm(bmat-normalized))/(tau/n)**0.5,
                "scaling_residual": float(residual),
                "log_full_score_product": float(np.log1p(-a*a).sum()),
                "negative_tau": -tau,
            })
            assert records[-1]["log_full_score_product"] <= -tau+1e-14
    print("PASS true score-preconditioned full-graph diagnostics:", len(records), flush=True)
    return records


def main():
    record = {"scope": "Exact finite algebra and diagnostics only; no permanent theorem or asymptotic threshold certified."}
    record.update(scalar_curvature_checks())
    record.update(exact_global_checks())
    record.update(degree_interpolation_checks())
    nonprincipal_checks()
    # Repeat the complete four-block permutation classification, independently
    # of Hamilton counting and including f-2s < 0 paired-product cases.
    rng = Random(2026100514)
    blocks = 0
    for n in (5, 6, 7, 8):
        for _ in range(2):
            a = [[0]*n for _ in range(n)]
            for i, j in combinations(range(n), 2):
                a[i][j] = rng.randrange(2)
                a[j][i] = 1-a[i][j]
            for f in (1, 2, 3):
                audit(a, f)
                blocks += 1
    paired_bound_checks()
    record["rerun_four_block_permutation_checks"] = blocks
    record["rerun_nonprincipal_checks"] = "Existing checker exact_checks rerun; see stdout for counted matrix/minor/permanent checks."
    record["moderate_scaling_records"] = moderate_diagnostics()
    print("RECORD "+json.dumps(record), flush=True)


if __name__ == "__main__":
    main()
