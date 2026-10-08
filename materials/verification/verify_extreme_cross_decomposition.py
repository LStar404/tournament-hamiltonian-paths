"""Exact permutation block decomposition across an arbitrary exceptional set."""
from functools import lru_cache
from fractions import Fraction as F
from itertools import combinations, permutations
from math import factorial, prod
from random import Random


def audit(a, f):
    n = len(a)
    exceptional, core = tuple(range(f)), tuple(range(f, n))

    @lru_cache(None)
    def minor(rows, cols):
        assert len(rows) == len(cols)
        return sum(prod(a[i][j] for i, j in zip(rows, order)) for order in permutations(cols))

    direct = minor(tuple(range(n)), tuple(range(n)))
    decomposition = 0
    for s in range(f+1):
        t = f-s
        if t > len(core):
            continue
        for rows_f in combinations(exceptional, s):
            outgoing = tuple(i for i in exceptional if i not in rows_f)
            for cols_f in combinations(exceptional, s):
                incoming = tuple(j for j in exceptional if j not in cols_f)
                inside = minor(rows_f, cols_f)
                for rows_core in combinations(core, t):
                    keep_rows = tuple(i for i in core if i not in rows_core)
                    for cols_core in combinations(core, t):
                        keep_cols = tuple(j for j in core if j not in cols_core)
                        decomposition += (inside*minor(outgoing, cols_core)*minor(rows_core, incoming)
                                          *minor(keep_rows, keep_cols))
    assert decomposition == direct


def paired_bound_checks():
    rng = Random(20261004091)
    tests = 0
    for f in range(7):
        for _ in range(4):
            u = [F(rng.randint(0, 10), 5) for _ in range(f)]
            v = [F(rng.randint(0, 10), 5) for _ in range(f)]
            cap = max([F(1, 3)]+[u[i]*v[i] for i in range(f)])
            largest = max([F(1)]+u+v)
            for s in range(f+1):
                total = 0
                for rows in combinations(range(f), s):
                    for cols in combinations(range(f), s):
                        value = prod(u[i] for i in range(f) if i not in rows)*prod(
                            v[j] for j in range(f) if j not in cols)
                        assert value <= cap**(f-2*s)*largest**(2*s)
                        total += value
                assert factorial(s)*total <= cap**(f-2*s)*largest**(2*s)*F(f**(2*s), factorial(s))
                tests += 1
    print("PASS exact paired-product exceptional-set bound:", tests, "cases", flush=True)


if __name__ == "__main__":
    rng = Random(20261004089)
    count = 0
    for n in (5, 6, 7, 8):
        for _ in range(2):
            a = [[0]*n for _ in range(n)]
            for i in range(n):
                for j in range(i+1, n):
                    a[i][j] = rng.randrange(2)
                    a[j][i] = 1-a[i][j]
            for f in (1, 2, 3):
                audit(a, f)
                count += 1
    print("PASS full permutation versus nonprincipal four-block decomposition:", count, "cases", flush=True)
    paired_bound_checks()

