"""Exact checks of the excess-one resolvent formula; no floating point.

Finite checks supplement, and do not replace, the all-orders diagram proof.
"""
from fractions import Fraction as F
from itertools import product
from math import factorial, prod
from random import Random

from centered_permanent_coefficients import carousel, triangle_flip
from check_higher_coefficient_envelope import multiply
from derive_centered_c6_symbolic import partitions
from verify_spectral_core_window import no_pure_cycle_component


def correction_coefficient(s, half_degree):
    n = len(s)
    gram = [[sum(s[i][a]*s[j][a] for a in range(n))
             for j in range(n)] for i in range(n)]
    powers = [[[int(i == j) for j in range(n)] for i in range(n)]]
    for _ in range(half_degree):
        powers.append(multiply(powers[-1], gram))
    result = F(0)
    for a in range(1, half_degree):
        b = half_degree-a
        result -= F(3, 2)*sum(powers[a][i][i]*powers[b][i][i]
                              for i in range(n))
        for b in range(1, half_degree-a):
            c = half_degree-a-b
            result -= sum(powers[a][i][i]*powers[b][i][j]*powers[c][j][j]
                          for i in range(n) for j in range(n))
            result -= F(2, 3)*sum(powers[a][i][j]*powers[b][i][j]*powers[c][i][j]
                                  for i in range(n) for j in range(n))
    return result/n**(2*half_degree)


def direct_excess_one(s, degree):
    n = len(s)
    total = 0
    diagrams = 0
    ps = partitions(degree)
    hom_cache = {}
    for pi in ps:
        rows = {x: i for i, block in enumerate(pi) for x in block}
        for sigma in ps:
            if len(pi)+len(sigma) != degree-1:
                continue
            columns = {x: len(pi)+j for j, block in enumerate(sigma) for x in block}
            edges = tuple(sorted((rows[x], columns[x]) for x in range(degree)))
            if not no_pure_cycle_component(degree-1, edges):
                continue
            diagrams += 1
            if edges not in hom_cache:
                hom_cache[edges] = sum(
                    prod(s[labels[a]][labels[b]] for a, b in edges)
                    for labels in product(range(n), repeat=degree-1))
            weight = (-1)**(degree-1)*prod(
                factorial(len(block)-1) for block in pi+sigma)
            total += weight*hom_cache[edges]
    return F(total, factorial(degree)*n**degree), diagrams


def inverse(a):
    n = len(a)
    aug = [[F(x) for x in row]+[F(int(i == j)) for j in range(n)]
           for i, row in enumerate(a)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if aug[i][j])
        aug[j], aug[pivot] = aug[pivot], aug[j]
        scale = aug[j][j]
        aug[j] = [x/scale for x in aug[j]]
        for i in range(n):
            if i != j:
                scale = aug[i][j]
                aug[i] = [x-scale*y for x, y in zip(aug[i], aug[j])]
    return [row[n:] for row in aug]


def verify_resolvent_signs(s):
    n = len(s)
    m = [[F(sum(s[i][a]*s[j][a] for a in range(n)), n*n)
          for j in range(n)] for i in range(n)]
    inv = inverse([[int(i == j)-m[i][j] for j in range(n)] for i in range(n)])
    e = [[inv[i][j]-int(i == j) for j in range(n)] for i in range(n)]
    diagonal = [e[i][i] for i in range(n)]
    u = sum(diagonal)
    v = sum(e[i][j]**2 for i in range(n) for j in range(n))
    bouquet = sum(x*x for x in diagonal)
    dumbbell = sum(diagonal[i]*e[i][j]*diagonal[j]
                   for i in range(n) for j in range(n))
    theta = sum(e[i][j]**3 for i in range(n) for j in range(n))
    assert dumbbell >= 0 and theta >= 0 and bouquet >= u*u/n
    # A purely spectral inequality, with paired positive eigenvalues.
    assert 2*u*u-u-2*v >= 1-F(3, n)-F(1, 4*n*n)
    correction = (u*u+u+2*v)/(2*n)-F(3, 2)*bouquet-dumbbell-F(2, 3)*theta
    assert correction <= -F(1, 2*n)+F(3, 2*n*n)+F(1, 8*n**3)
    return correction


if __name__ == "__main__":
    for n, k in [(3, 3), (3, 4), (3, 5), (3, 6), (5, 4), (5, 6)]:
        s = carousel(n)
        direct, diagrams = direct_excess_one(s, k)
        formula = correction_coefficient(s, k//2) if k % 2 == 0 else F(0)
        assert direct == formula, (n, k, direct, formula)
        print("Direct excess-one check", n, k, diagrams, direct, flush=True)
    rng = Random(2026092705)
    for n in [3, 5, 7, 9, 11, 13, 15, 17]:
        s = carousel(n)
        for trial in range(3):
            if trial:
                for _ in range(n*n):
                    triangle_flip(s, rng)
            correction = verify_resolvent_signs(s)
        print("Exact resolvent and sign inequalities passed", n,
              "last n*correction =", float(n*correction), flush=True)
