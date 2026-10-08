"""Independently verify exact finite-order lower-bound certificates.

Every row integer is an outgoing-neighbor bitmask, using vertices 0,...,n-1.
No optimality over all tournaments is asserted.
"""
from fractions import Fraction
from math import factorial
from random import Random
from verify_extreme_local_max import count_paths

WITNESSES = {
    12: (531205, (1656,1069,1921,468,3142,2844,934,1331,2579,3226,2408,207)),
    13: (3719893, (3730,3428,1241,6243,938,5317,5905,2890,2605,5166,6552,4724,407)),
    14: (24855901, (10442,9700,6937,11490,6219,4885,9636,10036,6681,6235,4917,9442,10443,1844)),
    15: (198464295, (254,508,1016,2032,4064,8128,16256,32512,32257,31747,30727,28687,24607,16447,127)),
    16: (1522320909, (510,508,2032,2036,4064,16320,32640,32512,65024,63491,64003,61455,57375,49183,32831,255)),
}


def check_tournament(rows):
    n = len(rows)
    for i, row in enumerate(rows):
        assert 0 <= row < (1 << n)
        assert not (row >> i) & 1
        for j in range(i):
            assert ((row >> j) & 1) + ((rows[j] >> i) & 1) == 1


def walk_inclusion_exclusion(rows):
    """Different count: all length-(n-1) walks, excluding omitted vertices."""
    n = len(rows)
    total = 0
    for mask in range(1, 1 << n):
        vs = [v for v in range(n) if mask >> v & 1]
        neighbors = {v: [u for u in vs if rows[v] >> u & 1] for v in vs}
        walks = {v: 1 for v in vs}
        for _ in range(n - 1):
            walks = {v: sum(walks[u] for u in neighbors[v]) for v in vs}
        value = sum(walks.values())
        total += value if (n-len(vs)) % 2 == 0 else -value
    return total


def circulant(n, code):
    steps = [d if code >> (d-1) & 1 else n-d for d in range(1, n//2+1)]
    return tuple(sum(1 << ((v+d) % n) for d in steps) for v in range(n))


def paley_rows(n):
    squares = {x*x % n for x in range(1, n)}
    return tuple(sum(1 << j for j in range(n) if (j-i) % n in squares)
                 for i in range(n))


def extend(rows, mask):
    n = len(rows)
    return tuple(row | (0 if mask >> i & 1 else 1 << n)
                 for i, row in enumerate(rows)) + (mask,)


def paley_checks():
    rng = Random(20260926)
    for n, h, alpha in ((7, 189, 39), (11, 95095, 14421)):
        rows = paley_rows(n)
        assert count_paths(rows) == h
        masks = (range(1 << n) if n == 7 else
                 sorted({(1 << k)-1 for k in range(n+1)}
                        | {rng.randrange(1 << n) for _ in range(64)}))
        for mask in masks:
            extension = extend(rows, mask)
            check_tournament(extension)
            k = mask.bit_count()
            assert count_paths(extension) == h + alpha*k*(n-k)
        print("Paley extension polynomial", n, "H =", h,
              "+", alpha, "* k*(n-k); direct masks", len(masks), flush=True)


def fixed_vertex_balancing_counterexample():
    rows = (6,28,0,37,45,7)
    check_tournament(rows)
    maxima = [0]*7
    for mask in range(64):
        k = mask.bit_count()
        maxima[k] = max(maxima[k], count_paths(extend(rows, mask)))
    assert maxima == [11,65,95,111,121,111,11]
    assert count_paths((70,28,64,37,45,7,58)) == 121
    print("fixed-vertex balancing counterexample, maxima by degree:", maxima, flush=True)


def main():
    for n, (expected, rows) in WITNESSES.items():
        check_tournament(rows)
        actual = count_paths(rows)
        assert actual == expected, (n, actual, expected)
        ratio = Fraction(actual * 2**(n-1), factorial(n))
        print("certificate", n, actual, "ratio", float(ratio),
              "degrees", sorted(row.bit_count() for row in rows), flush=True)
    n = 13
    independent = walk_inclusion_exclusion(WITNESSES[n][1])
    assert independent == WITNESSES[n][0]
    print("independent walk inclusion-exclusion, n=13:", independent, flush=True)
    independent14 = walk_inclusion_exclusion(WITNESSES[14][1])
    assert independent14 == WITNESSES[14][0]
    print("independent walk inclusion-exclusion, n=14:", independent14, flush=True)
    maximum = 0
    for code in range(1 << (n//2)):
        rows = circulant(n, code)
        check_tournament(rows)
        maximum = max(maximum, count_paths(rows))
    assert maximum == 3711175 < independent
    print("all 64 circulant tournaments of order 13:", maximum, flush=True)
    paley_checks()
    fixed_vertex_balancing_counterexample()


if __name__ == "__main__":
    main()
