"""Exact coefficients of per(J+tS)/n! for skew tournament sign matrices."""

from fractions import Fraction
from math import factorial
from random import Random


def carousel(n):
    assert n % 2 == 1
    return [[0 if i == j else (1 if (j-i) % n <= n//2 else -1)
             for j in range(n)] for i in range(n)]


def triangle_flip(s, rng):
    n = len(s)
    for _ in range(1000):
        i, j, k = rng.sample(range(n), 3)
        if s[i][j] == s[j][k] == s[k][i] == 1:
            for u, v in [(i,j), (j,k), (k,i)]:
                s[u][v] = -1
                s[v][u] = 1
            return
    raise RuntimeError("no cyclic triangle")


def coefficients(s, max_degree=6):
    n = len(s)
    d = min(n, max_degree)
    dp = [None] * (1 << n)
    dp[0] = [1]
    for mask in range((1 << n)-1):
        old = dp[mask]
        if old is None:
            continue
        i = mask.bit_count()
        free = ((1 << n)-1) ^ mask
        while free:
            b = free & -free
            j = b.bit_length()-1
            new_mask = mask | b
            out = dp[new_mask]
            if out is None:
                out = dp[new_mask] = [0] * (d+1)
            z = s[i][j]
            for k, x in enumerate(old):
                out[k] += x
                if k < d:
                    out[k+1] += z*x
            free -= b
    return [Fraction(x, factorial(n)) for x in dp[-1]]


def trace_four(s):
    n = len(s)
    sq = [[sum(s[i][k]*s[k][j] for k in range(n))
           for j in range(n)] for i in range(n)]
    return sum(x*x for row in sq for x in row)


def c4_formula(s):
    n = len(s)
    return Fraction(n*(n-1)*(n*n-13*n+24)+2*trace_four(s),
                    8*n*(n-1)*(n-2)*(n-3))


def c6_formula(s):
    n=len(s)
    c=[[sum(s[i][k]*s[j][k] for k in range(n))
        for j in range(n)] for i in range(n)]
    t4=sum(c[i][j]**2 for i in range(n) for j in range(n))
    t6=sum(c[i][j]*c[j][k]*c[k][i]
           for i in range(n) for j in range(n) for k in range(n))
    h3=sum(c[i][j]**3 for i in range(n) for j in range(n))
    a=(15*n**6-585*n**5+9045*n**4-44835*n**3
       +82080*n**2-45720*n)
    q6=a+90*(n*n-25*n+72)*t4+120*t6-480*h3
    return Fraction(q6, factorial(6)*factorial(n)//factorial(n-6))


if __name__ == "__main__":
    rng = Random(61072)
    for n in (5, 7, 9, 11, 13, 15):
        s = carousel(n)
        samples = []
        for k in range(12 if n <= 11 else 4):
            if k:
                triangle_flip(s, rng)
            a = coefficients(s, 6)
            assert a[2] == Fraction(1, 2)
            assert a[4] == c4_formula(s)
            if n>=7:
                assert a[6] == c6_formula(s)
            samples.append((a[4], a[6] if n >= 6 else Fraction(0)))
        print(n, "carousel", samples[0], "c6_range",
              min(x[1] for x in samples), max(x[1] for x in samples),
              "sec6", Fraction(61,720))
