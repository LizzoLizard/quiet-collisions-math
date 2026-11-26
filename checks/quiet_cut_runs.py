"""Exhaustive tests of the low-wire collision bound and bilinear cut interfaces."""
from itertools import combinations, combinations_with_replacement
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


def anf_coefficients(values):
    """Subset Möbius inversion in GF(2), processing every output bit at once."""
    coeffs = list(values)
    step = 1
    while step < len(coeffs):
        for start in range(0, len(coeffs), 2 * step):
            for i in range(start, start + step):
                coeffs[i + step] ^= coeffs[i]
        step *= 2
    return coeffs


def check_grouped_ring(n, k, d):
    length = max((n + k - 1) // k, d + 1)
    control_count = n - length
    ring_mask = (1 << length) - 1
    all_controls = (1 << control_count) - 1
    groups = []
    for edge in range(length):
        start = edge * (k - 1)
        size = min(k - 1, max(control_count - start, 0))
        groups.append(((1 << size) - 1) << start)

    values, histogram = [], [0] * (1 << n)
    for word in range(1 << n):
        controls, wires = word >> length, word & ring_mask
        output = controls << length
        for i, group in enumerate(groups):
            gain = int(controls & group == group)
            following = (wires >> ((i + 1) % length)) & 1
            this = (wires >> i) & 1
            output |= (following ^ (this & gain)) << i
        values.append(output)
        histogram[output] += 1

    for y, count in enumerate(histogram):
        expected = 1
        if y >> length == all_controls:
            expected += (-1) ** weight(y & ring_mask)
        assert count == expected, (n, k, d, y)
    assert sum(t * (t - 1) for t in histogram) == 1 << length
    for mask, coefficient in enumerate(transform(histogram)):
        expected = 0
        if mask == 0:
            expected = 1 << n
        elif mask & ring_mask == ring_mask:
            expected = (1 << length) * (-1) ** weight(mask >> length)
        assert coefficient == expected, (n, k, d, mask)

    coeffs = anf_coefficients(values)
    for wire in range(n):
        degree = max((weight(a) for a, v in enumerate(coeffs) if v & (1 << wire)), default=0)
        expected = 1 if wire >= length else 1 + weight(groups[wire])
        if n == 1:
            expected = 0  # The sole output is r XOR r.
        assert degree == expected and degree <= k, (n, k, d, wire)


def check_tiny_minima():
    """Enumerate all maps up to output translations and coordinate permutations.

    Both symmetries preserve degree, collision excess, and the weights of
    audible masks. Normalizing Q(0)=0 and sorting the coordinate truth tables
    leaves a representative of every map.
    """
    reps = 0
    for n in range(1, 4):
        count = 1 << n
        coords = []
        for table in range(0, 1 << count, 2):
            bits = [(table >> i) & 1 for i in range(count)]
            degree = max((weight(a) for a, v in enumerate(anf_coefficients(bits)) if v), default=0)
            coords.append((bits, degree))
        minima = {}
        for rows in combinations_with_replacement(coords, n):
            reps += 1
            degree = max(deg for bits, deg in rows)
            words = [0] * count
            for j, (bits, _) in enumerate(rows):
                for x, bit in enumerate(bits):
                    words[x] |= bit << j
            hist = [0] * count
            for y in words:
                hist[y] += 1
            excess = sum(t * (t - 1) for t in hist)
            if excess == 0:
                continue
            first = min(weight(c) for c, value in enumerate(transform(hist)) if c and value)
            for k in range(max(1, degree), n + 3):
                for d in range(first):
                    key = k, d
                    minima[key] = min(minima.get(key, excess), excess)
        for k in range(1, n + 3):
            for d in range(n):
                assert minima[k, d] == 1 << max((n + k - 1) // k, d + 1), (n, k, d)
    return reps


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
    grouped = 0
    for n in range(1, 11):
        for k in range(1, n + 3):
            for d in range(n):
                check_grouped_ring(n, k, d)
                grouped += 1
    print(f"{grouped} grouped rings through 10 bits matched every bucket, signed mask, and coordinate degree.")
    reps = check_tiny_minima()
    print(f"Exhaustive minima through 3 bits matched the formula ({reps} square-map symmetry representatives).")
    rng = Random(20261121)
    assert cut_test([255] * 8, 8, rng) == 1
    assert cut_test([1 << i for i in range(8)], 8, rng) == 8
    for _ in range(80):
        n, m = rng.randrange(1, 8), rng.randrange(1, 8)
        cut_test([rng.randrange(1 << m) for _ in range(n)], m, rng)
    print("82 interfaces: all conditional counts and numbers of distinct right functions matched.")
    cuts, edges, low, high = balanced_graph_cuts()
    print(f"Cubic 14-vertex graph: {cuts} balanced cuts, minimum crossing edges {edges}, rank range {low}..{high}.")
