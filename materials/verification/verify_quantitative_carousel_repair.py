"""Exact checks of quantitative spectral and switching/round repair steps."""
from fractions import Fraction as F
from itertools import combinations
from random import Random

from verify_spectral_stability_bridge import check, transitive
from verify_inverse_n_spectral_bounds import random_skew
from check_higher_coefficient_envelope import multiply


def triangle_count(s, vertices):
    return sum(s[i][j] == s[j][k] == s[k][i]
               for i, j, k in combinations(vertices, 3))


def forbidden_sets(s):
    result = []
    for vertices in combinations(range(len(s)), 4):
        i, j, k, l = vertices
        pf = s[i][j]*s[k][l]-s[i][k]*s[j][l]+s[i][l]*s[j][k]
        if pf*pf == 9:
            result.append(vertices)
    return result


def optimal_order(s, vertices):
    m = len(vertices)
    out = [sum(1 << j for j, v in enumerate(vertices) if s[u][v] == 1) for u in vertices]
    dp, last = [0]*(1 << m), [0]*(1 << m)
    for mask in range(1, 1 << m):
        best = m*m
        for v in range(m):
            if mask >> v & 1:
                rest = mask ^ (1 << v)
                cost = dp[rest]+(out[v] & rest).bit_count()
                if cost < best:
                    best, last[mask] = cost, v
        dp[mask] = best
    mask, reverse = (1 << m)-1, []
    while mask:
        v = last[mask]
        reverse.append(vertices[v])
        mask ^= 1 << v
    return list(reversed(reverse)), dp[-1]


def repair_check(s):
    n = len(s)
    bad = forbidden_sets(s)
    pivot_counts = [sum(i in subset for subset in bad) for i in range(n)]
    assert sum(pivot_counts) == 4*len(bad)
    pivot = min(range(n), key=pivot_counts.__getitem__)
    for v in range(n):
        signs = [1 if i == v else s[v][i] for i in range(n)]
        switched = [[signs[i]*s[i][j]*signs[j] for j in range(n)] for i in range(n)]
        assert triangle_count(switched, [i for i in range(n) if i != v]) == pivot_counts[v]
    signs = [1 if i == pivot else s[pivot][i] for i in range(n)]
    switched = [[signs[i]*s[i][j]*signs[j] for j in range(n)] for i in range(n)]
    order, edits = optimal_order(switched, [i for i in range(n) if i != pivot])
    order = [pivot]+order
    pos = {v: i for i, v in enumerate(order)}
    local = [[0 if i == j else signs[i]*signs[j]*(1 if pos[i] < pos[j] else -1)
              for j in range(n)] for i in range(n)]
    assert sum(s[i][j] != local[i][j] for i in range(n) for j in range(i+1, n)) == edits
    assert not forbidden_sets(local)
    assert edits*edits <= 729*(n-1)*pivot_counts[pivot]
    circular = [v for v in order if signs[v] == 1]+[v for v in order if signs[v] == -1]
    reference = [[0]*n for _ in range(n)]
    mismatch_rows = 0
    for i, v in enumerate(circular):
        degree = sum(x == 1 for x in local[v])
        assert all(local[v][circular[(i+j) % n]] == (1 if j <= degree else -1)
                   for j in range(1, n))
        target = n//2 if n % 2 or i < n//2 else n//2-1
        mismatch_rows += abs(degree-target)
        for j in range(1, n):
            reference[v][circular[(i+j) % n]] = 1 if j <= target else -1
    assert all(reference[i][j] == -reference[j][i] for i in range(n) for j in range(n))
    local_distance = sum(reference[i][j] != local[i][j] for i in range(n) for j in range(i+1, n))
    assert mismatch_rows == 2*local_distance
    distance = sum(reference[i][j] != s[i][j] for i in range(n) for j in range(i+1, n))
    score_l1 = sum(abs(sum(row)) for row in s)
    assert 4*distance <= 8*edits+score_l1+(n if n % 2 == 0 else 0)
    return edits, distance


def quantitative_gap(s):
    n = len(s)
    t = transitive(n)
    s2, t2 = multiply(s, s), multiply(t, t)
    s3, t3 = multiply(s2, s), multiply(t2, t)
    norm2 = lambda a: sum(x*x for row in a for x in row)
    gap4 = F(norm2(t2)-norm2(s2), n**4)
    gap6 = F(norm2(t3)-norm2(s3), n**6)
    excess = max(F(0), gap4-F(6, n))
    assert excess*excess <= 4*gap6
    return gap4, gap6


if __name__ == "__main__":
    rng = Random(2026092715)
    count = 0
    for n in range(3, 13):
        for _ in range(8):
            s = random_skew(n, rng)
            repair_check(s)
            quantitative_gap(s)
            count += 1
    print("Exact pivot identities, optimal repair, round order and distance bounds:", count, "passed")
    for n in (24, 48, 72, 96):
        for _ in range(3):
            g4, g6 = quantitative_gap(random_skew(n, rng))
        print("Exact squared quantitative gap inequality passed", n,
              "last gap4", float(g4), "last gap6", float(g6), flush=True)
