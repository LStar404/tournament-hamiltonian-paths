"""Exact low-degree checks of the manuscript's compressed-core examples.

These finite identities are regression tests, not an all-order proof.
"""
from fractions import Fraction as Q
from itertools import permutations
from math import factorial
import unittest


def distinct_coefficient(matrix, k):
    n = len(matrix)
    total = Q(0)
    for rows in permutations(range(n), k):
        for cols in permutations(range(n), k):
            term = Q(1)
            for i, j in zip(rows, cols):
                term *= matrix[i][j]
            total += term
    return total / factorial(k)


class CoreExampleTests(unittest.TestCase):
    def test_signed_cubic_and_loop_bouquet(self):
        examples = [
            [[1, -1], [-1, 1]],
            [[2, -1, -1], [-2, 3, -1], [0, -2, 2]],
            [[2, -1, -1, 0], [-2, 3, -1, 0], [1, -2, 2, -1], [-1, 0, 0, 1]],
        ]
        for entries in examples:
            with self.subTest(order=len(entries)):
                b = [[Q(x, 20) for x in row] for row in entries]
                n = len(b)
                self.assertTrue(all(sum(row) == 0 for row in b))
                self.assertTrue(all(sum(b[i][j] for i in range(n)) == 0 for j in range(n)))
                cubic = Q(2, 3) * sum(x**3 for row in b for x in row)
                self.assertEqual(distinct_coefficient(b, 3), cubic)
                gram = [[sum(b[i][k]*b[j][k] for k in range(n)) for j in range(n)] for i in range(n)]
                trace = sum(gram[i][i] for i in range(n))
                gaussian4 = trace**2 / 8 + sum(x*x for row in gram for x in row) / 4
                row_bouquets = sum(sum(x*x for x in row)**2 for row in b)
                col_bouquets = sum(sum(b[i][j]**2 for i in range(n))**2 for j in range(n))
                four_parallel = Q(3, 2) * sum(x**4 for row in b for x in row)
                expected = gaussian4 - Q(3, 4)*(row_bouquets + col_bouquets) + four_parallel
                self.assertEqual(distinct_coefficient(b, 4), expected)


if __name__ == '__main__':
    unittest.main()
