"""Exact determinant and two-permanent reduction for switched transitive words.

Checks are integer-only. The formula is NOT valid for arbitrary tournaments.
No permanent asymptotic or global extremality claim enters this script.
"""
from itertools import product

from carousel_path_cover_recurrence import count_paths, switched_rows
from verify_extreme_local_max import count_paths as subset_paths
from verify_word_minor_and_cube import (
    adjacency_plus_identity, determinant_integer, minor_weight, word,
)


def subset_permanent(rows):
    """Row-by-row perfect-matching DP, independent of the path-cover DP."""
    n = len(rows)
    values = [0]*(1 << n)
    values[0] = 1
    for mask in range(1 << n):
        row = mask.bit_count()
        if row == n or not values[mask]:
            continue
        free = rows[row] & ~mask
        while free:
            bit = free & -free
            values[mask | bit] += values[mask]
            free -= bit
    return values[-1]


def check_word(colors, check_paths=False):
    n = len(colors)
    rows = switched_rows(colors)
    matrix = adjacency_plus_identity(colors)
    adjacency = [[v-int(i == j) for j, v in enumerate(row)]
                 for i, row in enumerate(matrix)]
    changes_half = minor_weight(colors)-1
    assert determinant_integer(adjacency) == (-1)**(n+1)*changes_half
    assert determinant_integer(matrix) == 1+changes_half
    permanent = subset_permanent(rows)
    fixed_point_permanent = subset_permanent(tuple(row | (1 << i)
                                                  for i, row in enumerate(rows)))
    actual = count_paths(colors)[0]
    assert actual == permanent+fixed_point_permanent, (colors, actual, permanent,
                                                      fixed_point_permanent)
    if check_paths:
        assert actual == subset_paths(rows)
    return actual, permanent, fixed_point_permanent


def main():
    complete = 0
    for n in range(1, 10):
        for tail in product((0, 1), repeat=n-1):
            check_word((0,)+tail, check_paths=True)
            complete += 1
    samples = 0
    for n in (10, 12, 14, 16):
        for colors in (word("01", n), word("0110", n), word("01101001", n),
                       tuple(i.bit_count() % 2 for i in range(n))):
            check_word(colors)
            samples += 1
    # Two directed triangles with every edge from the first to the second.
    # This graph is not switched transitive and disproves a global extension.
    counterexample = (58, 60, 57, 16, 32, 8)
    h = subset_paths(counterexample)
    p = subset_permanent(counterexample)
    ip = subset_permanent(tuple(row | (1 << i)
                               for i, row in enumerate(counterexample)))
    assert (h, p, ip) == (9, 1, 4)
    print("PASS complete color words:", complete,
          "(two determinants, two permanents, two independent path DPs)", flush=True)
    print("PASS larger integer samples:", samples, "orders 10, 12, 14, 16", flush=True)
    print("PASS scope counterexample: H =", h, "per(A) =", p,
          "per(I+A) =", ip, "so H != their sum", flush=True)
    print("Exact local formula only; no asymptotic or global maximum certificate.", flush=True)


if __name__ == "__main__":
    main()
