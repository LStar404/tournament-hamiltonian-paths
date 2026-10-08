"""Exact small-order check of an imbalanced arc-local path-count maximum."""

def carousel_with_two_extremes(m: int) -> tuple[int, ...]:
    assert m >= 3 and m % 2 == 1
    x, y = m, m + 1
    rows = [0] * (m + 2)
    for i in range(m):
        for j in range(m):
            if 1 <= (j - i) % m <= (m - 1) // 2:
                rows[i] |= 1 << j
        rows[i] |= 1 << x
    rows[x] = 1 << y
    rows[y] = (1 << m) - 1
    return tuple(rows)


def count_paths(rows: tuple[int, ...]) -> int:
    n = len(rows)
    full = (1 << n) - 1
    dp = [[0] * n for _ in range(1 << n)]
    for v in range(n):
        dp[1 << v][v] = 1
    for mask in range(1, 1 << n):
        for last in range(n):
            count = dp[mask][last]
            if not count:
                continue
            next_vertices = rows[last] & (full ^ mask)
            while next_vertices:
                bit = next_vertices & -next_vertices
                dp[mask | bit][bit.bit_length() - 1] += count
                next_vertices ^= bit
    return sum(dp[full])


def flipped(rows: tuple[int, ...], i: int, j: int) -> tuple[int, ...]:
    changed = list(rows)
    changed[i] ^= 1 << j
    changed[j] ^= 1 << i
    return tuple(changed)


def main() -> None:
    expected = {3: 15, 5: 135, 7: 2163, 9: 52875, 11: 1854039}
    for m, expected_h in expected.items():
        rows = carousel_with_two_extremes(m)
        h = count_paths(rows)
        assert h == expected_h, (m, h)
        changes = []
        for i in range(m + 2):
            for j in range(i + 1, m + 2):
                changes.append(h - count_paths(flipped(rows, i, j)))
        minimum_loss = min(changes)
        assert minimum_loss >= 0, (m, minimum_loss)
        print(
            f"m={m}, n={m+2}, H={h}, K={(m-1)//2}, "
            f"minimum single-arc-flip loss={minimum_loss}"
        )


if __name__ == "__main__":
    main()
