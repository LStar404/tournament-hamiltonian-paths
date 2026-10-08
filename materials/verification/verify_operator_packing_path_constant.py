"""Exact finite checks for the operator-cap Gaussian packing constant.

The global Hamilton conclusion uses the separate analytic proof; finite
spectral tests neither prove that asymptotic conclusion nor its threshold.
"""
from fractions import Fraction as F
from functools import cmp_to_key
from math import factorial, prod
from pathlib import Path
from random import Random
import hashlib
import json
import time

from verify_carousel_repair_audit import all_tournaments
from verify_word_minor_and_cube import determinant_integer


def arctan_interval(x, terms=20):
    value = sum(((-1)**k*x**(2*k+1)/(2*k+1) for k in range(terms)), F(0))
    next_term = x**(2*terms+1)/(2*terms+1)
    return (value, value+next_term) if terms % 2 == 0 else (value-next_term, value)


def decimal_interval(lo, hi, places=15):
    scale = 10**places
    lower = lo.numerator*scale//lo.denominator
    upper = (hi.numerator*scale+hi.denominator-1)//hi.denominator
    def format_integer(value):
        return str(value//scale)+"."+str(value % scale).zfill(places)
    return format_integer(lower), format_integer(upper)


def packing_cap(a, total):
    k = total//a
    remaining = total-k*a
    return ((1+a)/(1-a))**k*(1+remaining)/(1-remaining)


def constant_certificate():
    l5, u5 = arctan_interval(F(1, 5))
    l239, u239 = arctan_interval(F(1, 239))
    pi_lo, pi_hi = 16*l5-4*u239, 16*u5-4*l239
    assert F(3141592653589793, 10**15) < pi_lo < pi_hi < F(3141592653589794, 10**15)
    a_lo, a_hi = 4/(pi_hi*pi_hi), 4/(pi_lo*pi_lo)
    assert F(1, 4) < a_lo < a_hi < F(1, 2)
    assert a_hi < F(405285, 10**6)
    c_lo, c_hi = packing_cap(a_lo, F(1, 2)), packing_cap(a_hi, F(1, 2))
    c_decimal = decimal_interval(c_lo, c_hi)
    rational_upper = F(c_decimal[1])
    assert rational_upper > c_hi
    cosh_lo = sum((F(1, factorial(2*k)) for k in range(15)), F(0))
    cosh_hi = cosh_lo+F(1, factorial(30))/(1-F(1, 31*32))
    cos_lo = sum((F((-1)**k, factorial(2*k)) for k in range(16)), F(0))
    cos_hi = cos_lo+F(1, factorial(32))
    assert cos_lo > 0
    l_lo, l_hi = cosh_lo/cos_hi, cosh_hi/cos_lo
    gap_lo, gap_hi = c_lo/l_hi-1, c_hi/l_lo-1
    assert 0 < gap_lo < gap_hi < F(51, 100000)
    return dict(pi_interval=[str(pi_lo), str(pi_hi)],
                operator_cap_interval=[str(a_lo), str(a_hi)],
                C_interval_decimal=c_decimal, C_rational_upper=str(rational_upper),
                relative_gap_interval_decimal=decimal_interval(gap_lo, gap_hi),
                lower_constant_interval_decimal=decimal_interval(l_lo, l_hi)), rational_upper


def composition_lists(length, remaining, cap):
    if length == 0:
        yield ()
        return
    for x in range(min(remaining, cap)+1):
        for tail in composition_lists(length-1, remaining-x, cap):
            yield (x,)+tail


def packing_checks():
    count = 0
    for cap_int in (6, 8):
        a = F(cap_int, 20)
        for length in range(1, 7):
            for entries in composition_lists(length, 10, cap_int):
                values = [F(x, 20) for x in entries]
                total = sum(values)
                observed = prod((1+x)/(1-x) for x in values)
                assert observed <= packing_cap(a, total)
                assert packing_cap(a, total) <= packing_cap(a, F(1, 2))
                count += 1
    return count


def angle_order(a, b):
    cross = a[0]*b[1]-a[1]*b[0]
    return -1 if cross > 0 else 1 if cross < 0 else 0


def phase_checks():
    rng = Random(20261008159)
    count = 0
    rational_a = F(405285, 10**6)
    for n in range(2, 25):
        for _ in range(12):
            points = [(rng.randrange(-5, 6), rng.randrange(-5, 6)) for _ in range(n)]
            folded = [(a, b) if b > 0 or (b == 0 and a >= 0) else (-a, -b)
                      for a, b in points]
            ordered = sorted([p for p in folded if p != (0, 0)],
                             key=cmp_to_key(angle_order))
            active = len(ordered)
            cross_sum = sum(ordered[i][0]*ordered[j][1]-ordered[i][1]*ordered[j][0]
                            for i in range(active) for j in range(i+1, active))
            assert cross_sum >= 0
            norm_squared = sum(a*a+b*b for a, b in points)
            assert 4*cross_sum*cross_sum <= rational_a*n*n*norm_squared*norm_squared
            count += 1
    return count


def spectral_checks(c_upper):
    a_num, a_den = 405285, 10**6
    total = psd = large = 0
    c_sq = c_upper*c_upper
    for n in range(1, 7):
        for s in all_tournaments(n):
            square = [[sum(s[i][k]*s[k][j] for k in range(n))
                       for j in range(n)] for i in range(n)]
            numerator = determinant_integer([[n*int(i == j)+s[i][j]
                                              for j in range(n)] for i in range(n)])
            denominator = determinant_integer([[n*n*int(i == j)+square[i][j]
                                                for j in range(n)] for i in range(n)])
            assert numerator > 0 and denominator > 0
            assert numerator*numerator*c_sq.denominator <= c_sq.numerator*denominator
            if n <= 5:
                # Sylvester's criterion: exact rigorous cap on all singular values.
                capped = [[a_num*n*n*int(i == j)+a_den*square[i][j]
                           for j in range(n)] for i in range(n)]
                for k in range(1, n+1):
                    assert determinant_integer([row[:k] for row in capped[:k]]) > 0
                psd += 1
            total += 1
    rng = Random(20261008160)
    for n in range(7, 14):
        for _ in range(6):
            s = [[0]*n for _ in range(n)]
            for i in range(n):
                for j in range(i+1, n):
                    s[i][j] = rng.choice((-1, 1))
                    s[j][i] = -s[i][j]
            square = [[sum(s[i][k]*s[k][j] for k in range(n))
                       for j in range(n)] for i in range(n)]
            numerator = determinant_integer([[n*int(i == j)+s[i][j]
                                              for j in range(n)] for i in range(n)])
            denominator = determinant_integer([[n*n*int(i == j)+square[i][j]
                                                for j in range(n)] for i in range(n)])
            assert numerator > 0 and denominator > 0
            assert numerator*numerator*c_sq.denominator <= c_sq.numerator*denominator
            large += 1
    return dict(complete_labeled_orders=list(range(1, 7)),
                complete_spectral_ratio_checks=total,
                complete_psd_operator_cap_checks_through_5=psd,
                sampled_orders_7_through_13=large)


def main():
    start = time.perf_counter()
    constants, cap = constant_certificate()
    record = dict(date="2026-10-08", version="operator_norm_and_convex_packing_v1",
                  scope="Exact constant enclosures and finite spectral checks, not a global asymptotic certification.",
                  constants=constants, convex_packing_checks=packing_checks(),
                  phase_order_checks=phase_checks(), spectral=spectral_checks(cap))
    record["seconds"] = time.perf_counter()-start
    record["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print("RECORD "+json.dumps(record), flush=True)


if __name__ == "__main__":
    main()
