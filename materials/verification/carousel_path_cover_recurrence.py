"""Exact polynomial-state path-cover DP for switched transitive tournaments.

For i < j, edge i -> j iff their prescribed colors agree. Alternating colors
give the odd carousel tournament and its vertex-deleted even counterpart.
State counts directed path components by (first color, last color).
All counts are Python integers; no floating-point arithmetic enters the DP.
"""
from collections import defaultdict
from math import cos, cosh, factorial
from time import perf_counter
import argparse


def count_paths(colors, progress=False):
    colors = tuple(colors)
    n = len(colors)
    if not n:
        return 0, 1
    dp = {(0, 0, 0, 0): 1}
    peak = 1
    for step, color in enumerate(colors, 1):
        # A future vertex can merge at most two old components.
        max_components = n-step+1
        nxt = defaultdict(int)
        for (a, b, c, d), ways in dp.items():
            total = a+b+c+d
            if total+1 <= max_components:
                state = (a+1, b, c, d) if color == 0 else (a, b, c, d+1)
                nxt[state] += ways
            if total <= max_components:
                append = a+c if color == 0 else b+d
                if append:
                    nxt[a, b, c, d] += append*ways
                if color == 0:
                    if c:
                        nxt[a+1, b, c-1, d] += c*ways
                    if d:
                        nxt[a, b+1, c, d-1] += d*ways
                else:
                    if a:
                        nxt[a-1, b, c+1, d] += a*ways
                    if b:
                        nxt[a, b-1, c, d+1] += b*ways
            if total-1 <= max_components:
                if color == 0:
                    merges = c*(a+c+d-1)
                    if merges:
                        nxt[a, b, c-1, d] += merges*ways
                    if a and d:
                        nxt[a-1, b+1, c, d-1] += a*d*ways
                else:
                    merges = b*(a+b+d-1)
                    if merges:
                        nxt[a, b-1, c, d] += merges*ways
                    if a and d:
                        nxt[a-1, b, c+1, d-1] += a*d*ways
        dp = nxt
        peak = max(peak, len(dp))
        if progress and (step % 10 == 0 or step == n):
            print("progress", n, step, "states", len(dp), flush=True)
    assert all(sum(state) == 1 for state in dp)
    return sum(dp.values()), peak


def switched_rows(colors):
    n = len(colors)
    rows = [0]*n
    for i in range(n):
        for j in range(i+1, n):
            u, v = (i, j) if colors[i] == colors[j] else (j, i)
            rows[u] |= 1 << v
    return tuple(rows)


def verify_small():
    from verify_extreme_local_max import count_paths as subset_count
    checked = 0
    for n in range(1, 9):
        # Complementing every color leaves the tournament unchanged.
        for bits in range(1 << (n-1)):
            colors = (0,)+tuple((bits >> i) & 1 for i in range(n-1))
            actual, _ = count_paths(colors)
            expected = subset_count(switched_rows(colors))
            assert actual == expected, (colors, actual, expected)
            checked += 1
    known = {3: 3, 5: 15, 7: 175, 9: 3267, 11: 93027,
             13: 3711175, 15: 198464295, 17: 13689269499,
             19: 1184212824763}
    for n, expected in known.items():
        actual, _ = count_paths(i % 2 for i in range(n))
        assert actual == expected, (n, actual, expected)
    for n in range(2, 13, 2):
        larger = n+1
        rows = tuple(sum(1 << (j-1) for j in range(1, larger)
                         if 1 <= (j-i) % larger <= larger//2)
                     for i in range(1, larger))
        actual, _ = count_paths(i % 2 for i in range(n))
        assert actual == subset_count(rows), (n, actual)
    print("Exact cross-checks passed:", checked, "color words and",
          len(known), "odd carousel counts and 6 even deleted carousels", flush=True)


def class_maximum(n):
    best, multiplicity, witness = 0, 0, None
    for bits in range(1 << (n-1)):
        colors = (0,)+tuple((bits >> i) & 1 for i in range(n-1))
        value, _ = count_paths(colors)
        if value > best:
            best, multiplicity, witness = value, 1, colors
        elif value == best:
            multiplicity += 1
    alternating, _ = count_paths(i % 2 for i in range(n))
    print("Exact switched-transitive class maximum n =", n, "maximum =", best,
          "alternating =", alternating, "maximizing color words =", multiplicity,
          "witness =", "".join(map(str, witness)), flush=True)
    return best, multiplicity


def balanced_words(n):
    if n < 2 or n % 2:
        raise ValueError("balanced_words requires a positive even order")
    for bits in range(1 << (n//2-1)):
        middle = tuple(x for j in range(n//2-1)
                       for x in (((bits >> j) & 1), 1-((bits >> j) & 1)))
        yield (0, 1)+middle
        yield (0,)+middle+(0,)


def balanced_class_maximum(n):
    best, multiplicity, witness = 0, 0, None
    seen = 0
    for colors in balanced_words(n):
        value, _ = count_paths(colors)
        seen += 1
        if value > best:
            best, multiplicity, witness = value, 1, colors
        elif value == best:
            multiplicity += 1
    print("Exact BALANCED switched-transitive maximum n =", n,
          "maximum =", best, "words tested =", seen,
          "maximizing words =", multiplicity,
          "witness =", "".join(map(str, witness)), flush=True)
    return best, multiplicity, witness


def verify_balanced_words():
    for n in range(2, 13, 2):
        generated = set(balanced_words(n))
        direct = set()
        for bits in range(1 << (n-1)):
            colors = (0,)+tuple((bits >> i) & 1 for i in range(n-1))
            rows = switched_rows(colors)
            if all(abs(2*row.bit_count()-(n-1)) == 1 for row in rows):
                direct.add(colors)
        assert generated == direct
        assert len(generated) == 1 << (n//2)
    print("Exact balanced-color-word characterization passed even n = 2..12", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("orders", nargs="*", type=int)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--progress", action="store_true")
    parser.add_argument("--class-max", type=int, default=0)
    parser.add_argument("--balanced-max", nargs="*", type=int, default=[])
    args = parser.parse_args()
    if args.verify:
        verify_small()
        verify_balanced_words()
    if args.class_max:
        if not 1 <= args.class_max <= 16:
            parser.error("--class-max must be between 1 and 16 (exhaustive-search guard)")
        for n in range(1, args.class_max+1):
            class_maximum(n)
    for n in args.balanced_max:
        if n < 2 or n > 26 or n % 2:
            parser.error("--balanced-max orders must be even and between 2 and 26")
        balanced_class_maximum(n)
    limit = cosh(1)/cos(1)
    for n in args.orders:
        if n < 1 or n > 151:
            parser.error("orders must be between 1 and 151 (resource guard)")
        start = perf_counter()
        value, peak = count_paths((i % 2 for i in range(n)), args.progress)
        ratio = value*2**(n-1)/factorial(n)
        print("n =", n, "H =", value, "H/mu =", format(ratio, ".15g"),
              "n*(H/mu-L) =", format(n*(ratio-limit), ".12g"),
              "peak_states =", peak,
              "seconds =", round(perf_counter()-start, 3), flush=True)
