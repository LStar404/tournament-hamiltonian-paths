"""Exact finite checks for the sixth-to-fourth moment stability bridge.

These validate identities and inequalities, not the compactness argument.
"""
from itertools import combinations
from random import Random

from check_higher_coefficient_envelope import multiply
from centered_permanent_coefficients import carousel, triangle_flip
from verify_inverse_n_spectral_bounds import random_skew


def majorization_matrix(n):
    return [[1 if i+j+2 <= n else 0 if i+j+2 == n+1
             else (-1)**(i+j-n) for j in range(n)] for i in range(n)]


def transitive(n):
    return [[0 if i == j else 1 if i < j else -1 for j in range(n)] for i in range(n)]


def weakly_majorized(a, b):
    assert a == sorted(a, reverse=True) and b == sorted(b, reverse=True)
    aa = bb = 0
    for x, y in zip(a, b):
        aa += x
        bb += y
        if aa > bb:
            return False
    return True


def matvec(a, x):
    return [sum(v*w for v, w in zip(row, x)) for row in a]


def norm2(x):
    return sum(t*t for t in x)


def check(s):
    n = len(s)
    t = transitive(n)
    c = majorization_matrix(n)
    s2, t2, c2 = multiply(s, s), multiply(t, t), multiply(c, c)
    s3, t3 = multiply(s2, s), multiply(t2, t)
    b = [c2[i][0] for i in range(n)]
    cb = matvec(c, b)
    gap4 = sum(norm2(row) for row in t2)-sum(norm2(row) for row in s2)
    gap6 = sum(norm2(row) for row in t3)-sum(norm2(row) for row in s3)
    column4 = column6_lower = squared_distance = 0
    for j in range(n):
        a = sorted((abs(s2[i][j]) for i in range(n)), reverse=True)
        ca = matvec(c, a)
        assert weakly_majorized(a, b)
        assert weakly_majorized(ca, cb)
        assert weakly_majorized(sorted((abs(s3[i][j]) for i in range(n)), reverse=True), ca)
        f = norm2(cb)-norm2(ca)
        dist = norm2([x-y for x, y in zip(cb, ca)])
        assert f >= dist >= 0
        column4 += norm2(b)-norm2(a)
        column6_lower += f
        squared_distance += dist
    assert gap4 == column4
    assert gap6 >= column6_lower >= squared_distance
    forbidden = 0
    for subset in combinations(range(n), 4):
        score = sorted(sum(s[i][j] == 1 for j in subset) for i in subset)
        bad = score in ([0, 2, 2, 2], [1, 1, 1, 3])
        i, j, k, l = subset
        pf = s[i][j]*s[k][l]-s[i][k]*s[j][l]+s[i][l]*s[j][k]
        assert pf*pf == (9 if bad else 1)
        forbidden += bad
    assert gap4 == 32*forbidden, (n, gap4, forbidden)
    return gap4/n**4, gap6/n**6, forbidden


if __name__ == "__main__":
    rng = Random(2026092713)
    for bits in range(64):
        s = [[0]*4 for _ in range(4)]
        for bit, (i, j) in enumerate(combinations(range(4), 2)):
            s[i][j] = 1 if bits >> bit & 1 else -1
            s[j][i] = -s[i][j]
        check(s)
    checked = 64
    for n in range(3, 18):
        for _ in range(4):
            check(random_skew(n, rng))
            checked += 1
    print("Exact majorization, norm-gap, and forbidden-four identities passed:", checked, "matrices")
    for n in (9, 17, 33, 65):
        s = carousel(n)
        triangle_flip(s, rng)
        g4, g6, bad = check(s)
        print("DIAGNOSTIC one cyclic-triangle flip", n, "gap4", g4,
              "gap6", g6, "forbidden fours", bad, flush=True)
