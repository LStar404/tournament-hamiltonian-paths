"""Floating-point diagnostics for paired potentials; exact resolvent checks.

No finite diagnostics certify the asymptotic constants in the proof note.
"""
from fractions import Fraction as F
from math import exp, log, sqrt

from centered_permanent_coefficients import carousel
from check_higher_coefficient_envelope import multiply
from verify_first_kernel_correction import inverse


def scaling(s):
    n = len(s)
    c = [[2/(n-1) if x == 1 else 0.0 for x in row] for row in s]
    x, y = [0.0]*n, [0.0]*n
    for step in range(20000):
        ey = [exp(t) for t in y]
        x = [-log(sum(c[i][j]*ey[j] for j in range(n))) for i in range(n)]
        ex = [exp(t) for t in x]
        y = [-log(sum(c[i][j]*ex[i] for i in range(n))) for j in range(n)]
        if step % 5 == 0:
            error = max(abs(sum(c[i][j]*exp(x[i]+y[j]) for j in range(n))-1)
                        for i in range(n))
            if error < 2e-13:
                break
    else:
        raise RuntimeError("Scaling did not converge; do not report unchecked potentials")
    gauge = (sum(y)-sum(x))/(2*n)
    x, y = [t+gauge for t in x], [t-gauge for t in y]
    p, t = [a+b for a, b in zip(x, y)], [a-b for a, b in zip(x, y)]
    a = [sum(row)-1 for row in c]
    e = [sum(c[i][j]*(exp(x[i]+y[j])-1-x[i]-y[j]) for j in range(n)) for i in range(n)]
    f = [sum(c[j][i]*(exp(x[j]+y[i])-1-x[j]-y[i]) for j in range(n)) for i in range(n)]
    residual = max(abs(p[i]+(sum(p)-p[i])/(n-1)-
                       (sum(s[i][j]*t[j] for j in range(n))/(n-1)-a[i]*t[i]-e[i]-f[i]))
                   for i in range(n))
    assert residual < 1e-11, residual
    return n*max(map(abs, p)), sqrt(n)*max(map(abs, x+y)), residual


def resolvent(s):
    n = len(s)
    k = [[F(x, n) for x in row] for row in s]
    k2 = multiply(k, k)
    return k, inverse([[F(i == j)+k2[i][j] for j in range(n)] for i in range(n)])


def edit_diagnostic(s, reference):
    n = len(s)
    k, r = resolvent(s)
    k0, r0 = resolvent(reference)
    delta = [[x-y for x, y in zip(row, row0)] for row, row0 in zip(k, k0)]
    first = multiply(multiply(multiply(r, delta), k), r0)
    second = multiply(multiply(multiply(r, k0), delta), r0)
    assert all(r[i][j]-r0[i][j] == -first[i][j]-second[i][j]
               for i in range(n) for j in range(n))
    edits = sum(s[i][j] != reference[i][j] for i in range(n) for j in range(i+1, n))
    eta = F(edits, n*n)
    diagonal = sum(abs(r[i][i]-r0[i][i]) for i in range(n))
    entries = sum(abs(r[i][j]-r0[i][j]) for i in range(n) for j in range(n))
    return float(diagonal/eta), float(entries/(eta*n))


if __name__ == "__main__":
    for n in (9, 17, 33, 65):
        reference = carousel(n)
        for kind in ("disjoint", "hub"):
            s = [row[:] for row in reference]
            edges = ([(i, i+1) for i in range(0, n-1, 2)] if kind == "disjoint"
                     else [(0, j) for j in range(1, min(int(sqrt(n)), n//2)+1)])
            for i, j in edges:
                s[i][j] *= -1
                s[j][i] *= -1
            forced = next((i for i, row in enumerate(s) if sum(x == 1 for x in row) == 1), None)
            if forced is not None:
                column = next(j for j, x in enumerate(s[forced]) if x == 1)
                assert any(s[i][column] == 1 for i in range(n) if i != forced)
                # A doubly stochastic row forces this entry to 1; another
                # positive entry in the same column is then impossible.
                print("EXACT small-order obstruction: no finite positive scaling",
                      n, kind, "forced row/column", forced, column, flush=True)
                continue
            pair, separate, error = scaling(s)
            print("DIAGNOSTIC", n, kind, "n*paired_max", pair,
                  "sqrt(n)*separate_max", separate, "identity residual", error, flush=True)
            if n <= 33:
                diagonal, entries = edit_diagnostic(s, reference)
                print("Exact resolvent identity passed; DIAGNOSTIC ratios diag/eta",
                      diagonal, "entry_l1/(n*eta)", entries, flush=True)
