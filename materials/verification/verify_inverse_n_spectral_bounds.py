"""Audit new identities; numerical checks are diagnostics, not proofs."""
from fractions import Fraction as F
from math import exp, log, sqrt
from random import Random

from centered_permanent_coefficients import carousel
from verify_first_kernel_correction import inverse
from verify_polar_permanent_tail import determinant


def transpose(a):
    return list(map(list, zip(*a)))


def multiply(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def norm(a):
    return sqrt(sum(float(x)**2 for row in a for x in row))


def random_skew(n, rng):
    s = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            s[i][j] = rng.choice((-1, 1))
            s[j][i] = -s[i][j]
    return s


def exact_gram_identity(s):
    n = len(s)
    p = [[F(1, n)]*n for _ in range(n)]
    y = [[(F(s[i][j])-int(i == j)+p[i][j])/(n-1)
          for j in range(n)] for i in range(n)]
    lhs = multiply(transpose(y), y)
    q = multiply(transpose(s), s)
    ps, sp = multiply(p, s), multiply(s, p)
    for i in range(n):
        for j in range(n):
            rhs = (q[i][j]*F(1, (n-1)**2)
                   +(ps[i][j]-sp[i][j]+int(i == j)-p[i][j])/(n-1)**2)
            assert lhs[i][j] == rhs


def spectral_logs(s, scale):
    n = len(s)
    z = [[F(x, scale) for x in row] for row in s]
    q = multiply(transpose(z), z)
    d_squared_inverse = determinant([[int(i == j)-q[i][j]
                                      for j in range(n)] for i in range(n)])
    numerator = determinant([[int(i == j)+z[i][j]
                              for j in range(n)] for i in range(n)])
    assert d_squared_inverse > 0 and numerator > 0
    return -log(float(d_squared_inverse))/2, log(float(numerator))


def schur_identity(s, k):
    n = len(s)
    z = [[F(x, n) for x in row] for row in s]
    vv = [[int(i == j)+z[i][j] for j in range(k, n)]
          for i in range(k, n)]
    uu = [[int(i == j)+z[i][j] for j in range(k)] for i in range(k)]
    cross = [row[k:] for row in z[:k]]
    correction = multiply(multiply(cross, inverse(vv)), transpose(cross))
    schur = [[uu[i][j]+correction[i][j] for j in range(k)] for i in range(k)]
    full = [[int(i == j)+z[i][j] for j in range(n)] for i in range(n)]
    assert determinant(full) == determinant(vv)*determinant(schur)
    base = determinant(uu)
    ratio = float(determinant(schur)/base)
    # Analytic accretive bound: log(det ratio) <= k(n-k)/n^2.
    assert log(ratio) <= k*(n-k)/n**2+1e-12


def known_scaling_diagnostic(n, rng):
    # A doubly stochastic tournament adjacency matrix, including its zeros.
    s = carousel(n)
    b = [[F(int(s[i][j] == 1)*2, n-1) for j in range(n)] for i in range(n)]
    # Safe bound for all nonprincipal singular values of this regular matrix.
    q = sqrt((1+n*(n-1)/2)/(n-1)**2)
    assert q < 1
    xx = [rng.uniform(-0.04, 0.04) for _ in range(n)]
    yy = [rng.uniform(-0.04, 0.04) for _ in range(n)]
    mx, my = sum(xx)/n, sum(yy)/n
    xx = [x-mx+0.01 for x in xx]
    yy = [y-my+0.01 for y in yy]
    assert abs(sum(xx)-sum(yy)) < 1e-12
    xmat = [[float(b[i][j])*exp(-xx[i]-yy[j]) for j in range(n)]
            for i in range(n)]
    delta = max(abs(x+y) for x in xx for y in yy)
    residual = [sum(row)-1 for row in xmat]
    residual += [sum(xmat[i][j] for i in range(n))-1 for j in range(n)]
    gnorm = sqrt(sum(x*x for x in residual))
    znorm = sqrt(sum(x*x for x in xx+yy))
    density = n*max(map(max, xmat))
    movement = norm([[float(b[i][j])-xmat[i][j] for j in range(n)] for i in range(n)])
    assert znorm <= exp(delta)/(1-q)*gnorm+1e-12
    assert movement <= sqrt(2)*density*exp(2*delta)/(1-q)*gnorm/sqrt(n)+1e-12
    potential_gap = sum(map(sum, xmat))-n+sum(xx)+sum(yy)
    assert potential_gap >= -1e-12
    assert potential_gap <= exp(delta)/(2*(1-q))*gnorm**2+1e-12
    return sqrt(n)*movement/gnorm


if __name__ == "__main__":
    rng = Random(2026092711)
    exact_cases = 0
    max_deletion_ratio = 0.0
    for n in (3, 4, 5, 7, 9, 12, 17, 25):
        samples = [random_skew(n, rng) for _ in range(3)]
        if n % 2:
            samples.append(carousel(n))
        for s in samples:
            exact_gram_identity(s)
            exact_cases += 1
            full_logs = spectral_logs(s, n)
            for k in range(1, min(3, n//2)+1):
                schur_identity(s, k)
                rest = [row[k:] for row in s[k:]]
                sub_logs = spectral_logs(rest, n-k)
                error = sum(abs(x-y) for x, y in zip(full_logs, sub_logs))
                max_deletion_ratio = max(max_deletion_ratio, error*n/k)
                # Deliberately loose consequence of the analytic proof.
                assert error <= 50*k/n+1e-12
        print("Exact Gram and Schur identities passed n =", n, flush=True)
    print("Exact matrix cases:", exact_cases, flush=True)
    print("Diagnostic maximum n/k * combined log-spectral deletion error:",
          max_deletion_ratio, flush=True)
    for n in (5, 9, 17, 31, 63):
        ratios = [known_scaling_diagnostic(n, rng) for _ in range(4)]
        print("Known-scaling L2 diagnostics n =", n,
              "maximum sqrt(n)*movement/residual =", max(ratios), flush=True)
