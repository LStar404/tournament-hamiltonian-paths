"""Exact switched-transitive minor weights and raw kernel cube identities.

No permanent asymptotic, numerical scaling, or path-extremality assumption
enters these checks. Phase diagnostics at the end do not certify error bounds.
"""
from fractions import Fraction as F
from itertools import combinations
from math import comb
from random import Random

from verify_first_kernel_correction import inverse


def determinant_integer(a):
    n = len(a)
    if not n:
        return 1
    a = [row[:] for row in a]
    previous = sign = 1
    for k in range(n-1):
        if not a[k][k]:
            pivot = next((i for i in range(k+1, n) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = pivot*a[i][j]-a[i][k]*a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator//previous
            a[i][k] = 0
        previous = pivot
    return sign*a[-1][-1]


def adjacency_plus_identity(colors):
    n = len(colors)
    return [[1 if i == j else int((i < j) == (colors[i] == colors[j]))
             for j in range(n)] for i in range(n)]


def minor_weight(colors):
    if not colors:
        return 1
    changes = sum(a != b for a, b in zip(colors, colors[1:]))
    return 1+changes//2


def subsequence_polynomial(colors, mandatory=()):
    """Sum det(I+A[W]) x^|W|, with the given labels forced into W."""
    n = len(colors)
    mandatory = set(mandatory)
    if any(i < 0 or i >= n for i in mandatory):
        raise ValueError("mandatory label outside the word")
    states = {}
    empty = 1
    for label, color in enumerate(colors):
        forced = label in mandatory
        nxt = {} if forced else {
            key: (mass[:], changes[:]) for key, (mass, changes) in states.items()}
        if empty:
            mass, changes = nxt.setdefault((color, 0), ([0]*(n+1), [0]*(n+1)))
            mass[1] += 1
        for (last, parity), (old_mass, old_changes) in states.items():
            change = int(last != color)
            mass, changes = nxt.setdefault(
                (color, parity ^ change), ([0]*(n+1), [0]*(n+1)))
            for degree in range(label+1):
                mass[degree+1] += old_mass[degree]
                changes[degree+1] += old_changes[degree]+change*old_mass[degree]
        states = nxt
        empty = empty and not forced
    result = [0]*(n+1)
    result[0] = int(empty)
    for (_, parity), (mass, changes) in states.items():
        for degree in range(1, n+1):
            numerator = changes[degree]-parity*mass[degree]
            assert numerator % 2 == 0
            result[degree] += mass[degree]+numerator//2
    return result


def pair_correlation_polynomial(colors):
    n = len(colors)
    d = [(-1)**color for color in colors]
    out = [3*comb(n, k) for k in range(n+1)]
    out[0] += 1
    if n:
        out[1] += n
    for i in range(n):
        for j in range(i+1, n):
            distance = j-i
            a, b = n-distance-1, distance-1
            for k in range(n-1):
                ca = comb(a, k) if k <= a else 0
                cb = comb(b, k) if k <= b else 0
                out[k+2] += ca+d[i]*d[j]*(cb-ca)
    assert all(value % 4 == 0 for value in out)
    return [value//4 for value in out]


def direct_minor_polynomial(colors, mandatory=()):
    n = len(colors)
    required = sum(1 << i for i in mandatory)
    result = [0]*(n+1)
    for mask in range(1 << n):
        if mask & required != required:
            continue
        subword = tuple(colors[i] for i in range(n) if mask >> i & 1)
        result[len(subword)] += determinant_integer(adjacency_plus_identity(subword))
    return result


def complex_power_parts(z, n):
    real, imag = F(1), F(0)
    for _ in range(n):
        real, imag = real-z*imag, imag+z*real
    return real, imag


def kernel_parameters(n, z):
    assert n % 2 == 0
    real, imag = complex_power_parts(z, n)
    if not real:
        raise ValueError("resolvent pole")
    cosine = real/(1+z*z)**(n//2)
    c = z/((1+z*z)*cosine)
    h = z*z/(1+z*z)
    diagonal = (z*imag/real-z*z)/(1+z*z)
    return c, h, diagonal


def gram_resolvent(n, z):
    # Exact T_n^2: diagonal -(n-1), off diagonal 2*|i-j|-n.
    square = [[-(n-1) if i == j else 2*abs(i-j)-n
               for j in range(n)] for i in range(n)]
    r = inverse([[F(i == j)+z*z*square[i][j] for j in range(n)] for i in range(n)])
    return [[r[i][j]-int(i == j) for j in range(n)] for i in range(n)]


def quadratic(matrix, d):
    return sum(d[i]*matrix[i][j]*d[j]
               for i in range(len(d)) for j in range(len(d)))


def cube_identity(n):
    z = F(1, n)
    tripled = (3*z-z**3)/(1-3*z*z)
    q, q3 = gram_resolvent(n, z), gram_resolvent(n, tripled)
    c, h, diagonal = kernel_parameters(n, z)
    c3, h3, _ = kernel_parameters(n, tripled)
    a, b = F(3, 4)*c*c, c**3/(4*c3)
    constant = a*h-b*h3+diagonal**3-(diagonal+h)**3
    for i in range(n):
        assert q[i][i] == diagonal
        for j in range(n):
            assert q[i][j]**3 == a*q[i][j]-b*q3[i][j]+constant*(i == j)
    return q, q3, a, b, constant


def word(pattern, n):
    return tuple(int(pattern[i % len(pattern)]) for i in range(n))


def minor_checks():
    full = 0
    for n in range(1, 10):
        for bits in range(1 << (n-1)):
            colors = (0,)+tuple((bits >> i) & 1 for i in range(n-1))
            assert determinant_integer(adjacency_plus_identity(colors)) == minor_weight(colors)
            full += 1
    rng = Random(202610051)
    coefficient = marked = 0
    for n in (4, 6, 8, 10):
        samples = [word(p, n) for p in ("01", "0110", "01101001")]
        samples += [tuple(i.bit_count() % 2 for i in range(n)),
                    tuple(rng.randrange(2) for _ in range(n))]
        for colors in samples:
            reference = direct_minor_polynomial(colors)
            assert subsequence_polynomial(colors) == reference
            assert pair_correlation_polynomial(colors) == reference
            coefficient += n+1
            for labels in ((0,), (n-1,), (0, n-1), (1, 2), (0, 1, n-2, n-1)):
                assert subsequence_polynomial(colors, labels) == \
                    direct_minor_polynomial(colors, labels)
                marked += 1
    print("PASS full integer determinants:", full,
          "three-way polynomial coefficients:", coefficient,
          "marked-subset polynomials:", marked, flush=True)


def cube_checks():
    entries = quadratics = 0
    for n in range(2, 21, 2):
        q, q3, a, b, constant = cube_identity(n)
        entries += n*n
        for colors in (word("01", n), word("0110", n), word("01101001", n)):
            d = [(-1)**color for color in colors]
            direct = sum(d[i]*d[j]*q[i][j]**3 for i in range(n) for j in range(n))
            expected = a*quadratic(q, d)-b*quadratic(q3, d)+constant*n
            assert direct == expected
            quadratics += 1
        if n % 4 == 0:
            d_old = [(-1)**c for c in word("0110", n)]
            d_new = [(-1)**c for c in word("01101001", n)]
            delta_theta = quadratic(q, d_new)-quadratic(q, d_old)
            delta_cube = a*delta_theta-b*(quadratic(q3, d_new)-quadratic(q3, d_old))
            diagonal = q[0][0]
            delta_xi = -F(2, 3)*delta_cube-diagonal**2*delta_theta
            print("DIAGNOSTIC raw core", n, "n5*new-old", float(n**5*delta_xi), flush=True)
    print("PASS Hadamard cube matrix entries:", entries,
          "switched word contractions:", quadratics, flush=True)
    print("Raw kernels only; no true-scaling, path remainder, or maximum certification.", flush=True)


if __name__ == "__main__":
    minor_checks()
    cube_checks()
