"""Audit coverage metadata and independently recount catalogue witnesses.

The catalogue's exhaustiveness is attributed to Brendan McKay, not re-proved
here. Full scans provide the upper bounds; witness recounts alone do not.
"""
import hashlib
import json
from pathlib import Path
from verify_hamilton_witnesses import check_tournament, walk_inclusion_exclusion
from verify_extreme_local_max import count_paths

ROOT = Path(__file__).resolve().parent


def parse(line, n):
    assert len(line) == n*(n-1)//2
    rows = [0]*n
    k = 0
    for i in range(n):
        for j in range(i+1, n):
            assert line[k] in "01"
            if line[k] == "1":
                rows[i] |= 1 << j
            else:
                rows[j] |= 1 << i
            k += 1
    check_tournament(rows)
    return tuple(rows)


def delete(rows, vertex):
    lower = (1 << vertex)-1
    return tuple((row & lower) | ((row >> (vertex+1)) << vertex)
                 for i, row in enumerate(rows) if i != vertex)


def complete_regular(rows):
    n = len(rows)
    assert n % 2 == 0
    m = n//2
    new = 0
    result = []
    for i, row in enumerate(rows):
        degree = row.bit_count()
        assert degree in (m-1, m)
        if degree == m:
            new |= 1 << i
            result.append(row)
        else:
            result.append(row | (1 << n))
    result.append(new)
    assert all(row.bit_count() == m for row in result)
    return tuple(result)


def main():
    manifest = json.loads((ROOT/"regular13_scan_certificate.json").read_text(encoding="utf-8"))
    expected_count = manifest["catalogue_count"]
    for filename, digest in manifest["data_sha256"].items():
        with (ROOT/filename).open("rb") as f:
            actual = hashlib.file_digest(f, "sha256").hexdigest()
        assert actual.lower() == digest.lower(), filename
    scans = manifest["parts"]
    assert {r["part"] for r in scans} == set(range(4))
    assert len(scans) == 4
    for r in scans:
        assert r["order"] == 13 and r["parts"] == 4 and not r["limited"]
        assert r["lines_seen"] == expected_count
        assert r["selected"] == (expected_count+3-r["part"])//4
    assert sum(r["selected"] for r in scans) == expected_count
    top = max(r["max_full"] for r in scans)
    deleted_top = max(r["max_deleted"] for r in scans)
    assert top == 3719893 and deleted_top == 531205
    wanted = {r["best_full_line"] for r in scans} | {r["best_deleted_line"] for r in scans}
    records = {}
    lines = 0
    with (ROOT/"rt13.txt").open("r", encoding="ascii") as f:
        for lines, line in enumerate(f, 1):
            if lines in wanted:
                records[lines] = parse(line.rstrip("\r\n"), 13)
    assert lines == expected_count
    assert set(records) == wanted
    for r in scans:
        a = records[r["best_full_line"]]
        assert tuple(r["best_full_rows"]) == a
        assert all(row.bit_count() == 6 for row in a)
        assert count_paths(a) == r["max_full"]
        parent = records[r["best_deleted_line"]]
        assert tuple(r["best_deleted_parent_rows"]) == parent
        sub = delete(parent, r["best_deleted_vertex"])
        check_tournament(sub)
        assert count_paths(sub) == r["max_deleted"]
        assert sorted(row.bit_count() for row in sub) == [5]*6+[6]*6
        # Complete back to the same parent, after moving its deleted vertex last.
        completion = complete_regular(sub)
        v = r["best_deleted_vertex"]
        ordering = [i for i in range(13) if i != v] + [v]
        relabeled = tuple(sum(((parent[i] >> j) & 1) << k
                              for k, j in enumerate(ordering)) for i in ordering)
        assert completion == relabeled
        print("verified part", r["part"], "full", r["max_full"],
              "deleted", r["max_deleted"], flush=True)
    winning_lines = {r["best_full_line"] for r in scans if r["max_full"] == top}
    for line in sorted(winning_lines):
        assert walk_inclusion_exclusion(records[line]) == top
        print("walk inclusion-exclusion verified winner at line", line, flush=True)
    print("coverage verified:", expected_count,
          "regular graphs and", 13*expected_count, "vertex deletions", flush=True)
    print("max_regular13 =", top, "; max_balanced12 =", deleted_top, flush=True)


if __name__ == "__main__":
    main()
