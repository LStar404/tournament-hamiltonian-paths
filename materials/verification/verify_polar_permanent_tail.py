"""Checks for the polar/Cauchy tail argument.

Exact rational tests check general centered diagrams. Floating-point tests of
polar comparison are diagnostics, not a substitute for its tensor proof.
"""
from fractions import Fraction as F
from math import atan2, cos, sin, sqrt, factorial, isqrt, pi
from random import Random

from centered_permanent_coefficients import coefficients, carousel
from verify_spectral_core_window import gaussian, direct_core_sum
from verify_first_kernel_correction import verify_resolvent_signs


def permanent(a):
    n = len(a)
    dp = [0]*(1 << n)
    dp[0] = 1
    for mask in range((1 << n)-1):
        i = mask.bit_count()
        free = ((1 << n)-1)^mask
        while free:
            bit = free & -free
            j = bit.bit_length()-1
            dp[mask | bit] += dp[mask]*a[i][j]
            free -= bit
    return dp[-1]


def centered_matrix(n, rng):
    raw = [[rng.randrange(-1, 2) for _ in range(n)] for _ in range(n)]
    rows = [F(sum(row), n) for row in raw]
    cols = [F(sum(raw[i][j] for i in range(n)), n) for j in range(n)]
    mean = sum(rows)/n
    return [[(raw[i][j]-rows[i]-cols[j]+mean)/2
             for j in range(n)] for i in range(n)]


def check_general_diagrams():
    rng = Random(2026092706)
    for n, degree in [(3, 3), (3, 4), (4, 3), (4, 4), (5, 4)]:
        e = centered_matrix(n, rng)
        assert all(sum(row) == 0 for row in e)
        assert all(sum(e[i][j] for i in range(n)) == 0 for j in range(n))
        a = coefficients(e, min(n, degree))
        g_even = gaussian(e, degree//2)
        g = [g_even[k//2] if k % 2 == 0 else F(0) for k in range(degree+1)]
        c = [F(1)]
        for k in range(1, degree+1):
            normalized = (a[k]*F(factorial(n), factorial(n-k)*n**k)
                          if k <= n else F(0))
            c.append(normalized-sum(g[j]*c[k-j] for j in range(1, k+1)))
        direct, _ = direct_core_sum(e, degree)
        assert direct == c[degree], (n, degree, direct, c[degree])
        print("Exact general centered diagram", n, degree, direct, flush=True)


def spectral_sqrt(a):
    """Small real symmetric PSD square root via Jacobi; checks residual."""
    n = len(a)
    d = [[float(x) for x in row] for row in a]
    v = [[float(i == j) for j in range(n)] for i in range(n)]
    for _ in range(100*n*n):
        p, q = max(((i, j) for i in range(n) for j in range(i+1, n)),
                   key=lambda ij: abs(d[ij[0]][ij[1]]))
        if abs(d[p][q]) < 1e-14:
            break
        angle = atan2(2*d[p][q], d[q][q]-d[p][p])/2
        c, s = cos(angle), sin(angle)
        for k in range(n):
            if k not in (p, q):
                x, y = d[k][p], d[k][q]
                d[k][p] = d[p][k] = c*x-s*y
                d[k][q] = d[q][k] = s*x+c*y
        x, y, z = d[p][p], d[p][q], d[q][q]
        d[p][p] = c*c*x-2*c*s*y+s*s*z
        d[q][q] = s*s*x+2*c*s*y+c*c*z
        d[p][q] = d[q][p] = 0.0
        for k in range(n):
            x, y = v[k][p], v[k][q]
            v[k][p], v[k][q] = c*x-s*y, s*x+c*y
    values = [d[k][k] for k in range(n)]
    assert min(values) >= -1e-12
    roots = [sqrt(max(0.0, x)) if x > 1e-13 else 0.0 for x in values]
    root = [[sum(v[i][k]*roots[k]*v[j][k] for k in range(n))
             for j in range(n)] for i in range(n)]
    residual = max(abs(sum(root[i][k]*root[k][j] for k in range(n))-a[i][j])
                   for i in range(n) for j in range(n))
    assert residual < 1e-10
    return root, roots


def check_polar_and_circle():
    rng = Random(2026092707)
    radius = 1.1
    for n in range(3, 10):
        for trial in range(3):
            e = centered_matrix(n, rng)
            b = [[float(x)/n for x in row] for row in e]
            gram_right = [[sum(b[k][i]*b[k][j] for k in range(n))
                           for j in range(n)] for i in range(n)]
            gram_left = [[sum(b[i][k]*b[j][k] for k in range(n))
                          for j in range(n)] for i in range(n)]
            right, singular = spectral_sqrt(gram_right)
            left, _ = spectral_sqrt(gram_left)
            assert max(singular) <= 0.5+1e-10
            polar_r = [[1/n+radius*right[i][j] for j in range(n)] for i in range(n)]
            polar_l = [[1/n+radius*left[i][j] for j in range(n)] for i in range(n)]
            bound = sqrt(permanent(polar_r)*permanent(polar_l))
            spectral = factorial(n)/n**n
            for value in singular:
                spectral /= 1-radius*value
            assert bound <= spectral*(1+1e-8)
            for j in range(12):
                z = radius*complex(cos(j*pi/6), sin(j*pi/6))
                a = [[1/n+z*b[i][k] for k in range(n)] for i in range(n)]
                assert abs(permanent(a)) <= bound*(1+1e-8)
        print("Polar and circle numerical diagnostics passed", n, flush=True)


def rank_one_asymptotic():
    # E=c*u*v^T, u,v balanced +/-1 vectors of norm sqrt(n).
    # For n divisible by four they may be chosen orthogonal: E^2=0 but
    # ||E/n||=c. This checks that the theorem uses singular, not eigen, values.
    c = F(2, 5)
    target = 1/sqrt(1-float(c*c))
    for n in (20, 40, 80, 160, 320):
        value = F(1)
        term = F(1)
        for m in range(1, n//2+1):
            term *= F((2*m)*(2*m-1)*(n//2-m+1)**2,
                      m*m*(n-2*m+2)*(n-2*m+1))*c*c
            value += term
        error = float(value)-target
        assert abs(error)*n < 1
        print("Nonnormal rank-one family", n, "n*error", n*error, flush=True)
    radius = F(11, 10)
    # Exact rational proof that R/(1-R/sqrt(2)) < 5.
    assert (5-radius)**2 > (5*radius)**2/2
    print("Regular circle exponent constant < 5 verified exactly.", flush=True)


def determinant(a):
    matrix = [[F(x) for x in row] for row in a]
    n = len(matrix)
    result = F(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if matrix[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            result = -result
        x = matrix[j][j]
        result *= x
        for i in range(j+1, n):
            scale = matrix[i][j]/x
            for k in range(j+1, n):
                matrix[i][k] -= scale*matrix[j][k]
    return result


def complete_first_correction():
    for n in (3, 5, 7, 9, 11, 13, 15, 17):
        s = carousel(n)
        correction = verify_resolvent_signs(s)
        gram = [[F(sum(s[i][a]*s[j][a] for a in range(n)), n*n)
                 for j in range(n)] for i in range(n)]
        det = determinant([[int(i == j)-gram[i][j] for j in range(n)]
                           for i in range(n)])
        p, q = isqrt(det.numerator), isqrt(det.denominator)
        assert p*p == det.numerator and q*q == det.denominator
        gaussian_value = F(q, p)
        actual = F(permanent([[1+x for x in row] for row in s]), factorial(n))
        scaled_residual = n*n*(actual/gaussian_value-1-correction)
        print("Complete carousel first-correction check", n,
              "n^2*relative_residual", float(scaled_residual), flush=True)


if __name__ == "__main__":
    check_general_diagrams()
    check_polar_and_circle()
    rank_one_asymptotic()
    complete_first_correction()
