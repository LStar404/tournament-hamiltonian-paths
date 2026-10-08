"""Exact checks for separate row/column Gaussian deletion and centering.

Finite checks do not prove asymptotic constants or finite global P(n).
The permanent examples have exact integer counts and rational error intervals;
their scaled errors are observations, not a uniform remainder certificate.
"""
from fractions import Fraction as F
from itertools import permutations
from math import factorial, isqrt
from pathlib import Path
from random import Random
import hashlib
import json
import time


def transpose(a):
    return [list(row) for row in zip(*a)]


def multiply(a, b):
    bt = transpose(b)
    return [[sum(x*y for x, y in zip(row, col)) for col in bt] for row in a]


def determinant(a):
    a = [[F(x) for x in row] for row in a]
    result = F(1)
    for i in range(len(a)):
        j = next((j for j in range(i, len(a)) if a[j][i]), None)
        if j is None:
            return F(0)
        if j != i:
            a[i], a[j] = a[j], a[i]
            result = -result
        pivot = a[i][i]
        result *= pivot
        for j in range(i+1, len(a)):
            coefficient = a[j][i]/pivot
            for k in range(i+1, len(a)):
                a[j][k] -= coefficient*a[i][k]
            a[j][i] = F(0)
    return result


def gaussian_denominator(a):
    gram = multiply(transpose(a), a)
    value = determinant([[int(i == j)-gram[i][j]
                          for j in range(len(a))] for i in range(len(a))])
    assert value > 0
    return value


def center(a):
    n = len(a)
    rows = list(map(sum, a))
    cols = list(map(sum, transpose(a)))
    mass = sum(rows)
    return [[a[i][j]-rows[i]/n-cols[j]/n+mass/(n*n)
             for j in range(n)] for i in range(n)]


def minor(a, removed_rows, removed_cols):
    n = len(a)
    return [[a[i][j] for j in range(n) if j not in removed_cols]
            for i in range(n) if i not in removed_rows]


def log_interval(value, terms):
    """Exact enclosure of log(value) for a rational value >= 1."""
    assert value >= 1
    if value == 1:
        return F(0), F(0)
    h = (value-1)/(value+1)
    h2 = h*h
    term, total = h, F(0)
    for k in range(terms):
        total += 2*term/(2*k+1)
        term *= h2
    return total, total+2*term/((2*terms+1)*(1-h2))


def verify_log_bound(ratio, budget):
    assert ratio >= 1 and budget >= 0
    if ratio == 1:
        return 0
    for terms in (4, 8, 16, 32, 64):
        lo, hi = log_interval(ratio, terms)
        if hi <= budget:
            return terms
        assert lo <= budget, (ratio, lo, budget)
    raise AssertionError("Insufficient rational log enclosure")


def deletion_pairs(n):
    pairs = [((), ()), ((0,), (0,)), ((0,), (1,)),
             ((n-1,), (0,)), ((0, 1), (0, 1)),
             ((0, 1), (1, 2)), ((0, 1), (n-2, n-1))]
    return list(dict.fromkeys(pairs))


def check_gaussian_deletion(a, q_squared, pairs):
    """Check exact PSD-order determinant direction and integral trace bound."""
    assert 0 <= q_squared < 1
    n = len(a)
    full_den = gaussian_denominator(a)
    row_sq = [sum(x*x for x in row) for row in a]
    col_sq = [sum(x*x for x in col) for col in transpose(a)]
    count = nonprincipal = centered_checks = max_terms = 0
    for removed_rows, removed_cols in pairs:
        z = minor(a, removed_rows, removed_cols)
        den = gaussian_denominator(z)
        assert full_den <= den
        budget = (sum(row_sq[i] for i in removed_rows)
                  + sum(col_sq[j] for j in removed_cols))/(1-q_squared)
        max_terms = max(max_terms, verify_log_bound(den/full_den, budget))
        centered = center(z)
        cent_den = gaussian_denominator(centered)
        assert den <= cent_den
        r = len(z)
        row_sums = list(map(sum, z))
        col_sums = list(map(sum, transpose(z)))
        cent_budget = (sum(x*x for x in row_sums)
                       + sum(x*x for x in col_sums))/(r*(1-q_squared))
        max_terms = max(max_terms, verify_log_bound(cent_den/den, cent_budget))
        count += 1
        nonprincipal += removed_rows != removed_cols
        centered_checks += 1
    return count, nonprincipal, centered_checks, max_terms


def generic_checks():
    rng = Random(20261008153)
    matrices = deletions = different = centering = maximum_terms = nonnormal = 0
    for n in range(3, 10):
        for _ in range(3):
            a = [[F(rng.randrange(-2, 3), 4*n) for _ in range(n)] for _ in range(n)]
            norm_sq = sum(x*x for row in a for x in row)
            assert norm_sq <= F(1, 4)
            q_sq = F(1, 4)  # Frobenius norm is a rigorous operator-norm cap.
            nonnormal += multiply(a, transpose(a)) != multiply(transpose(a), a)
            pairs = deletion_pairs(n)
            if n <= 5:
                pairs = list(dict.fromkeys(pairs+[
                    ((i,), (j,)) for i in range(n) for j in range(n)]))
            c, d, e, k = check_gaussian_deletion(a, q_sq, pairs)
            matrices += 1
            deletions += c
            different += d
            centering += e
            maximum_terms = max(maximum_terms, k)
    assert nonnormal > 0 and different > 0
    return dict(matrices=matrices, nonnormal_matrices=nonnormal,
                deletion_checks=deletions, nonprincipal_checks=different,
                centering_checks=centering, maximum_log_series_terms=maximum_terms)


def tournament(n, code):
    s = [[0]*n for _ in range(n)]
    k = 0
    for i in range(n):
        for j in range(i+1, n):
            s[i][j] = 1 if (code >> k) & 1 else -1
            s[j][i] = -s[i][j]
            k += 1
    return s


def carousel(n):
    assert n % 2
    return [[0 if i == j else 1 if 0 < (j-i) % n <= n//2 else -1
             for j in range(n)] for i in range(n)]


def near_regular_witness(n):
    if n % 2:
        return carousel(n)
    return minor(carousel(n+1), (0,), (0,))


def tournament_checks():
    rng = Random(20261008154)
    matrices = comparisons = different = scalar_scales = 0
    for n in range(4, 10):
        codes = range(1 << 6) if n == 4 else [
            0, (1 << (n*(n-1)//2))-1,
            *[rng.getrandbits(n*(n-1)//2) for _ in range(5)]]
        for code in codes:
            s = tournament(n, code)
            scores = list(map(sum, s))
            tau = F(sum(x*x for x in scores), (n-1)**2)
            y = [[F(s[i][j]-int(i == j), n-1) for j in range(n)] for i in range(n)]
            q_sq = F(n*(n-1)//2+1, (n-1)**2)
            assert q_sq < 1
            full_den = gaussian_denominator(y)
            target_den = gaussian_denominator([[F(x, n) for x in row] for row in s])
            gram_trace_difference = F(2*n-1, n*(n-1))+F(n, (n-1)**2)
            assert full_den <= target_den
            verify_log_bound(target_den/full_den, gram_trace_difference/(1-q_sq))
            for rows, cols in deletion_pairs(n):
                t, m = len(rows), n-len(rows)
                ym = minor(y, rows, cols)
                z = center(ym)
                cent_den = gaussian_denominator(z)
                assert cent_den >= full_den
                # Twice the log-Gaussian loss budget.
                loss = (F(2*t*n, (n-1)**2)
                        + 4*(tau+F(n*(1+t*t), (n-1)**2))/m)/(1-q_sq)
                verify_log_bound(cent_den/full_den, loss)
                # Norm of the *remaining* normalized-ones directions.
                actual_center_loss = (sum(x*x for x in map(sum, ym))
                                      + sum(x*x for x in map(sum, transpose(ym))))/m
                assert actual_center_loss <= 4*(tau+F(n*(1+t*t), (n-1)**2))/m
                if q_sq <= F(7, 9) and m >= F(n, 2):
                    # Log loss <= (24t + 18tau + 8)/n.
                    assert loss/2 <= F(24*t+8, n)+18*tau/n
                    # Full Gram correction <= 43/(4n).
                    assert gram_trace_difference/(2*(1-q_sq)) <= F(43, 4*n)
                # Separate scalar restoration: rigorous Frobenius gap cap.
                d = F(1001, 1000)
                z_norm_sq = sum(x*x for row in z for x in row)
                if d*d*z_norm_sq < 1:
                    scaled_den = gaussian_denominator([[d*x for x in row] for row in z])
                    assert scaled_den <= cent_den
                    budget = (d*d-1)*z_norm_sq/(1-d*d*z_norm_sq)
                    verify_log_bound(cent_den/scaled_den, budget)
                    scalar_scales += 1
                comparisons += 1
                different += rows != cols
            matrices += 1
    return dict(matrices=matrices, all_labeled_n4=64,
                gaussian_comparisons=comparisons, nonprincipal_checks=different,
                scalar_restoration_checks=scalar_scales)


def permanent01(a):
    """Exact integer subset recurrence; no generic weighted-matrix shortcut."""
    n = len(a)
    masks = [sum(1 << j for j, x in enumerate(row) if x) for row in a]
    dp = [0]*(1 << n)
    dp[0] = 1
    for mask in range((1 << n)-1):
        if not dp[mask]:
            continue
        available = masks[mask.bit_count()] & ~mask
        while available:
            bit = available & -available
            available -= bit
            dp[mask | bit] += dp[mask]
    return dp[-1]


def hamilton01(a):
    n = len(a)
    outgoing = [sum(1 << j for j, x in enumerate(row) if x) for row in a]
    full = (1 << n)-1
    dp = [[0]*n for _ in range(1 << n)]
    for i in range(n):
        dp[1 << i][i] = 1
    for mask in range(1, 1 << n):
        occupied = mask
        while occupied:
            end_bit = occupied & -occupied
            occupied -= end_bit
            end = end_bit.bit_length()-1
            value = dp[mask][end]
            if not value:
                continue
            available = outgoing[end] & (full ^ mask)
            while available:
                next_bit = available & -available
                available -= next_bit
                nxt = next_bit.bit_length()-1
                dp[mask | next_bit][nxt] += value
    return sum(dp[-1])


def transitive_rho(n):
    numerator = (n+1)**n+(n-1)**n
    real_power = sum((-1)**j*factorial(n)//(factorial(2*j)*factorial(n-2*j))
                     * n**(n-2*j) for j in range(n//2+1))
    assert real_power > 0
    return F(numerator, 2*real_power)


def sqrt_interval(value, bits=80):
    assert value >= 0
    scale = 1 << bits
    lo_int = isqrt(value.numerator*scale*scale//value.denominator)
    lo, hi = F(lo_int, scale), F(lo_int+1, scale)
    assert lo*lo <= value <= hi*hi
    return lo, hi


def exp_one_interval(terms=30):
    lo = sum((F(1, factorial(k)) for k in range(terms+1)), F(0))
    hi = lo+F(1, factorial(terms+1))/(1-F(1, terms+2))
    return lo, hi


def permanent_examples():
    e_lo, e_hi = exp_one_interval()
    records = []
    independent_permutation_checks = 0
    for n in range(4, 18):
        s = near_regular_witness(n)
        a = [[int(x == 1) for x in row] for row in s]
        d = max(map(abs, map(sum, s)))
        g2 = 1/gaussian_denominator([[F(x, n) for x in row] for row in s])
        d_lo, d_hi = sqrt_interval(g2)
        for rows, cols in [((), ()), ((0,), (0,)), ((0,), (1,)),
                           ((0, 1), (2, 3))]:
            m, t = n-len(rows), len(rows)
            am = minor(a, rows, cols)
            p = permanent01(am)
            if m <= 6:
                direct = sum(all(am[i][perm[i]] for i in range(m))
                             for perm in permutations(range(m)))
                assert p == direct
                independent_permutation_checks += 1
            coefficient = F(p*(1 << m), factorial(m))
            ratio_lo, ratio_hi = e_lo*coefficient/d_hi, e_hi*coefficient/d_lo
            error = max(abs(ratio_lo-1), abs(ratio_hi-1))
            scaled_upper = error*n/(d+t+1)**2
            records.append(dict(n=n, max_absolute_score=d, t=t,
                                removed_rows=rows, removed_cols=cols,
                                permanent=str(p),
                                relative_error_upper_rational=str(error),
                                scaled_error_upper_rational=str(scaled_upper),
                                scaled_error_upper_diagnostic=float(scaled_upper)))
    return dict(scope="Finite exact examples, not an asymptotic constant certificate.",
                independent_permutation_checks=independent_permutation_checks,
                records=records,
                max_scaled_error_upper_diagnostic=max(
                    r["scaled_error_upper_diagnostic"] for r in records))


def path_examples():
    records = []
    independent_permutation_checks = 0
    for n in range(4, 18):
        s = near_regular_witness(n)
        d = max(map(abs, map(sum, s)))
        a = [[int(x == 1) for x in row] for row in s]
        h = hamilton01(a)
        if n <= 6:
            direct = sum(all(a[perm[i]][perm[i+1]] for i in range(n-1))
                         for perm in permutations(range(n)))
            assert direct == h
            independent_permutation_checks += 1
        plus_det = determinant([[int(i == j)+F(s[i][j], n)
                                 for j in range(n)] for i in range(n)])
        gram_det = gaussian_denominator([[F(x, n) for x in row] for row in s])
        rho = transitive_rho(n)
        assert plus_det > 0 and plus_det*plus_det/gram_det == rho*rho
        normalized = F(h*(1 << (n-1)), factorial(n))
        error = abs(normalized-rho)
        records.append(dict(n=n, max_absolute_score=d, hamilton_paths=str(h),
                            normalized_path_count=str(normalized), rho=str(rho),
                            absolute_error=str(error),
                            scaled_error=str(n*error/(d+1)**2)))
    return dict(scope="Exact witness counts and spectra, not a uniform error certificate.",
                independent_permutation_checks=independent_permutation_checks,
                records=records)


def main():
    start = time.perf_counter()
    record = dict(date="2026-10-08",
                  version="separate_row_column_psd_gaussian_deletion_v1",
                  scope="Exact finite identities/inequalities; no global P(n) certification.",
                  generic=generic_checks(),
                  tournaments=tournament_checks(),
                  near_regular_nonprincipal_permanent_examples=permanent_examples(),
                  near_regular_path_examples=path_examples())
    record["seconds"] = time.perf_counter()-start
    record["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print("RECORD "+json.dumps(record, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    main()
