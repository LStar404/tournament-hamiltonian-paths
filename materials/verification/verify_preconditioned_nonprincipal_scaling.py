"""Nonprincipal score-preconditioned minors: exact identities and diagnostics."""
from fractions import Fraction as F
from itertools import permutations
from math import prod
from random import Random

import numpy as np

from centered_permanent_coefficients import carousel, triangle_flip
from diagnose_score_adaptive_error import potentials


def centered(rows):
    n = len(rows)
    rs = list(map(sum, rows))
    cs = [sum(rows[i][j] for i in range(n)) for j in range(n)]
    mass = sum(rs)
    return [[rows[i][j]-rs[i]/n-cs[j]/n+mass/(n*n)
             for j in range(n)] for i in range(n)]


def permanent(rows):
    n = len(rows)
    return sum(prod(rows[i][p[i]] for i in range(n)) for p in permutations(range(n)))


def deletion_pairs(n):
    return [((), ()), ((0,), (0,)), ((0,), (1,)),
            ((0, 1), (0, 1)), ((0, 1), (1, 2)), ((0, 1), (n-2, n-1))]


def exact_audit(s):
    n = len(s)
    a = [F(sum(row), n-1) for row in s]
    if max(map(abs, a)) > F(9, 10):
        return 0, 0
    c = [[F(1-int(i == j)+s[i][j], n-1) for j in range(n)] for i in range(n)]
    left, right = [1/(1+x) for x in a], [1/(1-x) for x in a]
    pre = [[left[i]*c[i][j]*right[j] for j in range(n)] for i in range(n)]
    mass = sum(map(sum, pre))
    hat = [[n*z/mass for z in row] for row in pre]
    er = [sum(row)-1 for row in hat]
    ec = [sum(hat[i][j] for i in range(n))-1 for j in range(n)]
    assert sum(er) == sum(ec) == 0
    difference = [[pre[i][j]-c[i][j] for j in range(n)] for i in range(n)]
    gamma = prod(1-x*x for x in a)
    minors = per_checks = 0
    for removed_rows, removed_cols in deletion_pairs(n):
        t, r = len(removed_rows), n-len(removed_rows)
        ir = [i for i in range(n) if i not in removed_rows]
        jc = [j for j in range(n) if j not in removed_cols]
        x = [[F(n, r)*hat[i][j] for j in jc] for i in ir]
        mx = sum(map(sum, x))
        intersection = sum(hat[i][j] for i in removed_rows for j in removed_cols)
        assert mx-r == F(n, r)*(-sum(er[i] for i in removed_rows)
                                -sum(ec[j] for j in removed_cols)+intersection-F(t*t, n))
        for ii, i in enumerate(ir):
            assert sum(x[ii])-1 == F(n, r)*(er[i]+F(t, n)-sum(hat[i][j] for j in removed_cols))
        for jj, j in enumerate(jc):
            assert sum(x[ii][jj] for ii in range(r))-1 == F(n, r)*(
                ec[j]+F(t, n)-sum(hat[i][j] for i in removed_rows))
        assert mx > 0
        normalized = [[r*z/mx for z in row] for row in x]
        e = centered(normalized)
        assert sum(map(sum, normalized)) == r
        assert all(sum(row) == 0 for row in e)
        assert all(sum(e[ii][jj] for ii in range(r)) == 0 for jj in range(r))
        multiplier = F(n*n)/(mass*mx)
        skew_minus_partial_identity = [[F(s[i][j]-int(i == j)) for j in jc] for i in ir]
        centered_base = centered(skew_minus_partial_identity)
        centered_difference = centered([[difference[i][j] for j in jc] for i in ir])
        expected = [[multiplier*(centered_base[ii][jj]/(n-1)+centered_difference[ii][jj])
                     for jj in range(r)] for ii in range(r)]
        assert e == expected
        rowcol_factor = prod(1+a[i] for i in ir)*prod(1-a[j] for j in jc)
        assert rowcol_factor == gamma*prod(left[i] for i in removed_rows)*prod(right[j] for j in removed_cols)
        if r <= 6:
            minor_a = [[(1-int(i == j)+s[i][j])//2 for j in jc] for i in ir]
            assert permanent(minor_a) == (F(n-1)/(2*multiplier))**r*rowcol_factor*permanent(normalized)
            per_checks += 1
        minors += 1
    return minors, per_checks


def exact_checks():
    rng = Random(20261004083)
    matrices = minors = perms = 0
    for n in (5, 7, 9, 11, 13):
        base = carousel(n)
        for _ in range(n):
            triangle_flip(base, rng)
        samples = [base]
        single = [row[:] for row in base]
        single[0][1] *= -1
        single[1][0] *= -1
        samples.append(single)
        hub = carousel(n)
        for j in range(1, 1+n//3):
            hub[0][j] *= -1
            hub[j][0] *= -1
        samples.append(hub)
        for _ in range(2):
            s = [[0]*n for _ in range(n)]
            for i in range(n):
                for j in range(i+1, n):
                    s[i][j] = rng.choice((-1, 1))
                    s[j][i] = -s[i][j]
            samples.append(s)
        for s in samples:
            m, p = exact_audit(s)
            if m:
                matrices += 1
                minors += m
                perms += p
    print("PASS exact nonprincipal mass/margins, centered compression, retained product:",
          matrices, "matrices;", minors, "minors;", perms, "independent permanent identities", flush=True)


def diagnostics():
    count = 0
    for n in (17, 33, 65, 129):
        for kind in ("regular", "disjoint", "hub"):
            s = np.array(carousel(n), float)
            edges = ([] if kind == "regular" else [(i, i+1) for i in range(0, n-1, 2)]
                     if kind == "disjoint" else [(0, j) for j in range(1, 1+n//3)])
            for i, j in edges:
                s[i, j] *= -1
                s[j, i] *= -1
            a = s.sum(axis=1)/(n-1)
            tau = float(a@a)
            c = (1-np.eye(n)+s)/(n-1)
            pre = c/(1+a[:, None])/(1-a[None, :])
            hat = n*pre/pre.sum()
            for removed_rows, removed_cols in deletion_pairs(n):
                ir = [i for i in range(n) if i not in removed_rows]
                jc = [j for j in range(n) if j not in removed_cols]
                t, r = len(removed_rows), n-len(removed_rows)
                raw = hat[np.ix_(ir, jc)]*n/r
                raw *= r/raw.sum()
                eps = max(np.max(abs(raw.sum(axis=0)-1)), np.max(abs(raw.sum(axis=1)-1)))
                p = np.eye(r)-np.ones((r, r))/r
                e = p@raw@p
                x, y, b, error = potentials(raw)
                assert error < 2e-13
                scale = np.sqrt(tau/n)+t/n
                shift_ratio = np.linalg.norm(b-raw)/(scale if scale else 1/n)
                potential_ratio = max(np.max(abs(x)), np.max(abs(y)))/(eps if eps else 1/n)
                print("DIAGNOSTIC n", n, kind, "remove", (removed_rows, removed_cols),
                      "tau", tau, "center norm", np.linalg.norm(e, 2),
                      "epsilon", eps, "potential/epsilon", potential_ratio,
                      "Frobenius/budget", shift_ratio, flush=True)
                count += 1
    print("Diagnostics:", count, "; no finite-domain or asymptotic certification.", flush=True)


if __name__ == "__main__":
    exact_checks()
    diagnostics()

