"""Exact checks accompanying an explicit zeroth-order permanent error budget.

Exact rank-two, nonnormal block families are checked through n=384. Finite
families do not establish the general theorem; its proof is in the audit note.
"""
from fractions import Fraction as F
from itertools import permutations
import json
from math import factorial, isqrt, exp, log
from time import perf_counter

from verify_kernel_activity_window import kernel_weight


KERNEL = ((1, -1, 0), (1, 0, -1), (-2, 1, 1))


def block_permanent_normalized(group_size, sign):
    """Coefficient DP by column-group occupancies, using integer weights."""
    size = 3 * group_size
    width = group_size + 1
    dp = [0] * (width * width)
    dp[0] = 1
    for row in range(size):
        weights = [4 + sign * value for value in KERNEL[row // group_size]]
        following = [0] * len(dp)
        for left in range(max(0, row - 2 * group_size), min(group_size, row) + 1):
            low = max(0, row - left - group_size)
            high = min(group_size, row - left)
            for right in range(low, high + 1):
                index = left * width + right
                value = dp[index]
                if not value:
                    continue
                third = row - left - right
                if left < group_size:
                    following[index + width] += value * weights[0]
                if right < group_size:
                    following[index + 1] += value * weights[1]
                if third < group_size:
                    following[index] += value * weights[2]
        dp = following
    numerator = dp[-1] * factorial(group_size)**3
    return F(numerator, factorial(size) * 4**size)


def independent_small_block_check(group_size, sign, observed):
    size = 3 * group_size
    exact = 0
    for permutation in permutations(range(size)):
        weight = 1
        for row, column in enumerate(permutation):
            weight *= 4 + sign * KERNEL[row // group_size][column // group_size]
        exact += weight
    assert observed == F(exact, factorial(size) * 4**size)


def algebra_checks():
    bound_e = F(87, 32)
    assert sum((F(1, factorial(k)) for k in range(7)), F(0)) \
        + F(8, 7 * factorial(7)) < bound_e
    assert 96 * bound_e**2 < 710
    assert kernel_weight(1, 1) == F(3, 2)
    assert kernel_weight(1, 2) == F(10, 3)
    activity_checks = 0
    for weight in (F(1), F(3, 2), F(2), F(4)):
        for deficit in range(1, 25):
            finite_sum = sum(
                (4 * deficit * weight)**b / factorial(b)
                for b in range(0, 2 * deficit + 1)
            )
            assert finite_sum <= (2 * bound_e * weight)**(2 * deficit)
            activity = sum(
                kernel_weight(deficit, b) * weight**(b + deficit)
                for b in range(1, 2 * deficit + 1)
            )
            assert activity <= (710 * weight**3 * deficit)**deficit
            activity_checks += 1
    recovery_checks = 0
    for size in range(4, 257):
        ratio = F(1)
        for degree in range(size // 4 + 1):
            if degree:
                ratio *= F(size, size - degree + 1)
            assert 0 <= ratio - 1 <= F(2 * degree * (degree - 1), 3 * size) * ratio
            recovery_checks += 1
    return {"exact_activity_checks": activity_checks,
            "exact_factorial_recovery_checks": recovery_checks,
            "new_core_constant": "710*W^3",
            "prior_core_constant": "1152*W^3",
            "exact_first_core_activity": "(3/2)*W^2+(10/3)*W^3"}


def block_family_checks():
    assert all(sum(row) == 0 for row in KERNEL)
    assert all(sum(KERNEL[i][j] for i in range(3)) == 0 for j in range(3))
    gram_left = [[sum(KERNEL[i][k] * KERNEL[j][k] for k in range(3))
                  for j in range(3)] for i in range(3)]
    gram_right = [[sum(KERNEL[k][i] * KERNEL[k][j] for k in range(3))
                   for j in range(3)] for i in range(3)]
    assert gram_left != gram_right
    assert sum(gram_left[i][i] for i in range(3)) == 10
    assert sum(value**2 for row in gram_left for value in row) == 82
    # Nonzero eigenvalues of KERNEL*KERNEL^T are 1 and 9.
    # B=E/n has singular values 1/12 and 1/4 for every group size.
    gaussian_squared = F(2304, 2145)
    precision = 2**96
    root = isqrt(gaussian_squared.numerator * precision**2 //
                 gaussian_squared.denominator)
    lower, upper = F(root, precision), F(root + 1, precision)
    assert lower**2 <= gaussian_squared < upper**2
    records = []
    for group_size in (1, 2, 4, 8, 16, 32, 64, 128):
        size = 3 * group_size
        pair = {}
        for sign in (1, -1):
            observed = block_permanent_normalized(group_size, sign)
            if group_size <= 2:
                independent_small_block_check(group_size, sign, observed)
            scaled_lower = size * (observed - upper)
            scaled_upper = size * (observed - lower)
            # A finite-family observation, not a claimed universal error bound.
            assert abs(scaled_lower) < 1 and abs(scaled_upper) < 1
            pair[sign] = observed
            records.append({
                "n": size, "sign": sign, "normalized_permanent_exact": str(observed),
                "gaussian_squared": str(gaussian_squared),
                "n_times_error_interval": [str(scaled_lower), str(scaled_upper)],
                "n_times_error_decimal_diagnostic": float((scaled_lower + scaled_upper) / 2),
                "not_a_uniform_all_matrix_certificate": True,
            })
        assert pair[1] != pair[-1]
        print("PASS exact nonnormal rank-two +/- family", size, flush=True)
    return {"nonnormal_rank_two_records": records,
            "gaussian_target_squared": str(gaussian_squared),
            "spectral_gap_bound": "1/4", "entry_bound": "1/2"}


def illustrative_budgets():
    records = []
    for entry_bound, gap in ((F(1), F(3, 4)), (F(1, 2), F(1, 4))):
        radius = (3 + gap) / (2 * (1 + gap))
        recovery_radius = (1 + radius) / 2
        c, q, r, sigma = map(float, (entry_bound, gap, radius, recovery_radius))
        activity = max(1.0, c * r + c*c * r*r / (1 - r*q))
        constant = 710 * activity**3
        alpha = min(0.25, 1 / (16 * constant), log(sigma) / 2)
        ar = exp(c*c*r*r / (2 * (1 - r*r*q*q)))
        ass = exp(c*c*sigma*sigma / (2 * (1 - sigma*sigma*q*q)))
        h1 = sigma*sigma*c*c / (1 - sigma*sigma*q*q)
        h2minus = sigma*sigma*c*c*(1 + sigma*sigma*q*q) / (1 - sigma*sigma*q*q)**2
        kg = ass * (h1*h1 + h2minus) / (2 * (1 - alpha))
        first_core = 1.5 * activity**2 + F(10, 3) * activity**3
        records.append({"C": str(entry_bound), "q": str(gap), "R": str(radius),
                        "sigma": str(recovery_radius), "alpha_diagnostic": alpha,
                        "new_leading_error_constant_diagnostic": ar * first_core + kg,
                        "prior_coarse_core_leading_constant_diagnostic": ar * 2 * 1152 * activity**3,
                        "not_outward_rounded_finite_error_certificates": True})
    return records


def main():
    start = perf_counter()
    record = {"date": "2026-10-08",
              "scope": "Zeroth-order uniform permanent proof audit and finite exact checks; not full Hamilton extremal closure.",
              "all_matrix_proof_requires_note_not_finite_family_tests": True}
    record.update(algebra_checks())
    record.update(block_family_checks())
    record["illustrative_budget_diagnostics"] = illustrative_budgets()
    record["seconds"] = round(perf_counter() - start, 3)
    print("RECORD " + json.dumps(record), flush=True)


if __name__ == "__main__":
    main()
