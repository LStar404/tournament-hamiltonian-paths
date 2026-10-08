"""Exact small-order audit of switching/round repair and discrete defects.

Exhaustive coverage is limited to the orders printed. A minimum found in that
coverage is not an all-order claim, nor a Hamilton-path maximality certificate.
"""
from collections import Counter
from itertools import combinations

from centered_permanent_coefficients import carousel
from verify_quantitative_carousel_repair import forbidden_sets, repair_check


def all_tournaments(n):
    edges = list(combinations(range(n), 2))
    for mask in range(1 << len(edges)):
        s = [[0]*n for _ in range(n)]
        for bit, (i, j) in enumerate(edges):
            s[i][j] = 1 if mask >> bit & 1 else -1
            s[j][i] = -s[i][j]
        yield s


def regular_tournaments(n):
    """Generate every labeled regular tournament by row-wise degree completion."""
    assert n % 2
    target = n//2
    wins = [0]*n
    s = [[0]*n for _ in range(n)]

    def extend(i):
        if i == n:
            assert all(w == target for w in wins)
            yield [row[:] for row in s]
            return
        required = target-wins[i]
        vertices = list(range(i+1, n))
        if not 0 <= required <= len(vertices):
            return
        for chosen in combinations(vertices, required):
            outgoing = set(chosen)
            wins[i] += required
            for j in vertices:
                s[i][j] = 1 if j in outgoing else -1
                s[j][i] = -s[i][j]
                if j not in outgoing:
                    wins[j] += 1
            unassigned_per_vertex = n-i-2
            if all(wins[j] <= target <= wins[j]+unassigned_per_vertex for j in vertices):
                yield from extend(i+1)
            for j in vertices:
                if j not in outgoing:
                    wins[j] -= 1
            wins[i] -= required

    yield from extend(0)


def check_graph(s):
    n = len(s)
    bad = len(forbidden_sets(s))
    edits, distance = repair_check(s)
    score_l1 = sum(abs(sum(row)) for row in s)
    # The exact repair inequality, with no square roots or floating tolerances.
    positive_excess = max(0, 4*distance-score_l1-(n if n % 2 == 0 else 0))
    assert positive_excess**2 <= (432**2)*bad
    assert bad == 0 or (4*bad >= n and bad >= n-3)
    if score_l1 == 0:
        assert n % 2
        assert distance**2 <= 108**2*bad
        if bad == 0:
            assert distance == 0
    return bad, distance


def exhaustive_checks():
    count = 0
    for n in range(3, 7):
        for s in all_tournaments(n):
            check_graph(s)
            count += 1
    print("PASS complete labeled tournaments, orders 3..6:", count, flush=True)

    # Independent coverage audit for the new degree-constrained generator.
    for n in (3, 5):
        encode = lambda s: tuple(s[i][j] for i in range(n) for j in range(i+1, n))
        reference = {encode(s) for s in all_tournaments(n)
                     if all(sum(row) == 0 for row in s)}
        generated = [encode(s) for s in regular_tournaments(n)]
        assert len(generated) == len(set(generated))
        assert set(generated) == reference
    print("PASS row-completion coverage against unrestricted enumeration, n=3,5", flush=True)

    profile = Counter()
    regular_count = 0
    for s in regular_tournaments(7):
        bad, _ = check_graph(s)
        profile[bad] += 1
        regular_count += 1
    assert regular_count == 2640
    print("PASS all labeled regular tournaments, n=7:", regular_count, flush=True)
    print("Exact n=7 regular forbidden-four profile:", dict(sorted(profile.items())), flush=True)


def narrow_triangle_diagnostics():
    for n in (7, 9, 11, 17, 25, 33):
        s = [row[:] for row in carousel(n)]
        i, j, k = 0, 2, n//2+1
        assert s[i][j] == s[j][k] == s[k][i] == 1
        for a, b in ((i, j), (j, k), (k, i)):
            s[a][b] *= -1
            s[b][a] *= -1
        assert all(sum(row) == 0 for row in s)
        bad = len(forbidden_sets(s))
        assert bad > 0 and 4*bad >= n
        print("DIAGNOSTIC one narrow triangle reversal:", n, "forbidden-four", bad, flush=True)


def sharp_general_defect_examples():
    for n in range(4, 26):
        s = [[0 if i == j else 1 if i < j else -1 for j in range(n)]
             for i in range(n)]
        s[0][2], s[2][0] = -1, 1
        assert len(forbidden_sets(s)) == n-3
    print("PASS 22 sharp examples for the general forbidden-four gap n-3", flush=True)


if __name__ == "__main__":
    exhaustive_checks()
    narrow_triangle_diagnostics()
    sharp_general_defect_examples()
