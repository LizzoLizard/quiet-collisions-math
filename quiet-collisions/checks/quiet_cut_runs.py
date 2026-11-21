"""Exhaustive tests of the low-wire collision bound and bilinear cut interfaces."""
from itertools import combinations
from random import Random

from mask_recovery import dot, mix


def weight(word):
    return bin(word).count("1")


def transform(histogram):
    values = list(histogram)
    step = 1
    while step < len(values):
        for start in range(0, len(values), 2 * step):
            for i in range(start, start + step):
                a, b = values[i], values[i + step]
                values[i], values[i + step] = a + b, a - b
        step *= 2
    return values


def locate_buckets(n, probe):
    single = [probe(1 << i) for i in range(n)]
    anchor = next(i for i, value in enumerate(single) if value)
    double, empty = 0, 0
    for i, value in enumerate(single):
        if value:
            double |= int(value == -2) << i
            empty |= int(value == 2) << i
        elif probe((1 << anchor) | (1 << i)) == -single[anchor]:
            double |= 1 << i
            empty |= 1 << i
    return double, empty


def check_isolated():
    trials = 0
    for n in range(1, 6):
        for u in range(1 << n):
            for v in range(1 << n):
                if u == v:
                    continue
                counts = [1] * (1 << n)
                counts[u], counts[v] = 2, 0
                spectrum = transform(counts)
                queries = []

                def probe(c):
                    queries.append(c)
                    return spectrum[c]

                assert locate_buckets(n, probe) == (u, v)
                assert len(queries) <= 2*n-1
                trials += 1
    return trials


def ring(n, d):
    m = max((n + 1) // 2, d + 1)
    s = n - m
    mask = (1 << m) - 1
    free = (1 << s) - 1
    histogram = [0] * (1 << n)
    for w in range(1 << n):
        t, x = w >> m, w & mask
        controls = t | (mask ^ free)
        next_wires = (x >> 1) | ((x & 1) << (m - 1))
        residual = next_wires ^ (controls & x)
        histogram[(t << m) | residual] += 1
    for w, count in enumerate(histogram):
        expected = 1
        if w >> m == free:
            expected += (-1) ** weight(w & mask)
        assert count == expected
    spectrum = transform(histogram)
    assert spectrum[0] == 1 << n
    for c in range(1, len(spectrum)):
        expected = ((-1) ** weight(c >> m) * (1 << m)) if c & mask == mask else 0
        assert spectrum[c] == expected
    first = min(weight(c) for c in range(1, len(spectrum)) if spectrum[c])
    excess = sum(z*(z-1) for z in histogram)
    assert first == m and excess == (1 << m)
    return first, histogram.count(0), histogram.count(2), excess


def factor_rows(rows):
    """Return independent original rows and the coefficients of all rows in them."""
    pivots, basis, coordinates = {}, [], []
    for row in rows:
        remainder, code = row, 0
        while remainder:
            p = remainder.bit_length() - 1
            if p in pivots:
                reduced, label = pivots[p]
                remainder ^= reduced
                code ^= label
            else:
                unit = 1 << len(basis)
                pivots[p] = remainder, code ^ unit
                basis.append(row)
                code = unit
                break
        coordinates.append(code)
        assert mix(basis, code) == row
    return basis, coordinates


def cut_test(rows, m, rng):
    n = len(rows)
    basis, coordinates = factor_rows(rows)
    rank = len(basis)
    # Use arbitrary side predicates. After fixing the message, the two sums separate.
    left = [rng.randrange(2) for _ in range(1 << n)]
    right = [rng.randrange(2) for _ in range(1 << m)]
    left_counts = [0] * (1 << rank)
    for x, accepted in enumerate(left):
        left_counts[mix(coordinates, x)] += accepted
    total = 0
    for message, count in enumerate(left_counts):
        right_mask = mix(basis, message)
        total += count * sum(accept and not dot(right_mask, y) for y, accept in enumerate(right))
    brute = sum(accept and allow and not dot(mix(rows, x), y)
                for x, accept in enumerate(left) for y, allow in enumerate(right))
    assert total == brute
    assert len({mix(rows, x) for x in range(1 << n)}) == (1 << rank)
    return rank


def balanced_graph_cuts():
    # Fourteen-vertex cubic bipartite incidence graph of the Fano plane.
    neighbors = [0] * 14
    for i in range(7):
        for shift in (0, 1, 3):
            j = 7 + (i + shift) % 7
            neighbors[i] |= 1 << j
            neighbors[j] |= 1 << i
    counts, ranks = [], []
    for rest in combinations(range(1, 14), 6):
        left = (0,) + rest
        right = ((1 << 14) - 1) ^ sum(1 << v for v in left)
        rows = [neighbors[v] & right for v in left]
        edges = sum(weight(row) for row in rows)
        basis, _ = factor_rows(rows)
        rank = len(basis)
        assert edges <= 9 * rank
        counts.append(edges)
        ranks.append(rank)
    return len(ranks), min(counts), min(ranks), max(ranks)


if __name__ == '__main__':
    print(f"{check_isolated()} isolated cracks: both output buckets recovered.")
    for n in range(1, 13):
        for d in range(n):
            ring(n, d)
    print("78 (N,d) cases through 12 bits: every bucket and signed mask matched.")
    for n, d in ((10, 1), (10, 4), (10, 7), (11, 4)):
        first, empty, double, excess = ring(n, d)
        print(f"N={n}, d={d}: first weight {first}, {empty} empty, {double} double, excess {excess}")
    rng = Random(20261121)
    assert cut_test([255] * 8, 8, rng) == 1
    assert cut_test([1 << i for i in range(8)], 8, rng) == 8
    for _ in range(80):
        n, m = rng.randrange(1, 8), rng.randrange(1, 8)
        cut_test([rng.randrange(1 << m) for _ in range(n)], m, rng)
    print("82 interfaces: all conditional counts and numbers of distinct right functions matched.")
    cuts, edges, low, high = balanced_graph_cuts()
    print(f"Cubic 14-vertex graph: {cuts} balanced cuts, minimum crossing edges {edges}, rank range {low}..{high}.")
