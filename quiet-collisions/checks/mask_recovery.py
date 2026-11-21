"""Recover the distinguishing Walsh mask of the padded pair after linear mixing."""
from dataclasses import dataclass
from itertools import combinations
from random import Random


def indices(word):
    while word:
        bit = word & -word
        yield bit.bit_length() - 1
        word ^= bit


def dot(a, b):
    return bin(a & b).count("1") % 2


def linear_solve(n, equations):
    """Return one solution and a basis of homogeneous solutions, or None."""
    pivots = {}
    for row, rhs in equations:
        while row:
            i = row.bit_length() - 1
            if i not in pivots:
                pivots[i] = (row, rhs)
                break
            reduced, value = pivots[i]
            row ^= reduced
            rhs ^= value
        else:
            if rhs:
                return None

    ordered = sorted(pivots.items())

    def fill(free, homogeneous):
        for i, (row, rhs) in ordered:
            value = dot(row, free) ^ (0 if homogeneous else rhs)
            free |= value << i
        return free

    return fill(0, False), [fill(1 << j, True) for j in range(n) if j not in pivots]


@dataclass
class QuadraticMap:
    const: int
    linear: list
    cross: dict

    def value(self, x):
        result = self.const
        for i in indices(x):
            result ^= self.linear[i]
        for (i, j), coefficient in self.cross.items():
            if (x >> i) & (x >> j) & 1:
                result ^= coefficient
        return result


def polar_matrix(q):
    """For this family every nonzero cross coefficient is the same output word."""
    directions = set(q.cross.values())
    if len(directions) != 1:
        raise ValueError("Expected one nonzero quadratic output direction")
    rows = [0] * len(q.linear)
    for i, j in q.cross:
        rows[i] |= 1 << j
        rows[j] |= 1 << i
    return directions.pop(), rows


def flat_constraints(q):
    cross, polar = polar_matrix(q)
    _, flat_inputs = linear_solve(len(polar), ((row, 0) for row in polar))
    return cross, [(q.value(d) ^ q.const, 0) for d in flat_inputs]


def locate(a, b):
    """Takes only square maps in expanded form. The hidden pair has a unique answer."""
    if a.cross != b.cross or a.linear != b.linear:
        raise ValueError("The two maps must differ by an output translation")
    n = len(a.linear)
    cross, equations = flat_constraints(a)
    dimension = len(equations)
    equations.extend([(cross, 1), (a.const ^ b.const, 1)])
    answer = linear_solve(n, equations)
    if answer is None or answer[1]:
        raise ValueError("The mask equations do not have a unique solution")
    return answer[0], dimension


def signed_probe(q, mask):
    """Evaluate the probe for a map with a single rank-two quadratic part."""
    n = len(q.linear)
    linear = sum(dot(mask, v) << i for i, v in enumerate(q.linear))
    scale = (-1 if dot(mask, q.const) else 1) * (1 << n)
    cross, polar = polar_matrix(q)
    if not dot(mask, cross):
        return scale if linear == 0 else 0

    # For rank two, rows p and q at either end of an edge factor the quadratic.
    i, j = next(iter(q.cross))
    p, s = polar[i], polar[j]
    for k in range(n):
        expected = (s if p >> k & 1 else 0) ^ (p if s >> k & 1 else 0)
        if polar[k] != expected:
            raise ValueError("Expected a rank-two polar matrix")
    linear ^= p & s  # The diagonal of the product contributes linear terms.
    return (scale // 2) * (int(linear == 0) + int(linear == p)
                           + int(linear == s) - int(linear == p ^ s))


def count_one_system(q):
    n = len(q.linear)
    _, flat = flat_constraints(q)
    _, basis = linear_solve(n, flat)
    candidates = [0]
    for direction in basis:
        candidates += [c ^ direction for c in candidates]
    mass = sum(signed_probe(q, c) for c in candidates)
    count, remainder = divmod(mass, 1 << n)
    assert remainder == 0
    return count, len(candidates)


def mix(columns, x):
    value = 0
    for i in indices(x):
        value ^= columns[i]
    return value


def random_basis(n, rng):
    columns, pivots = [], {}
    while len(columns) < n:
        original = candidate = rng.getrandbits(n)
        while candidate:
            i = candidate.bit_length() - 1
            if i not in pivots:
                pivots[i] = candidate
                columns.append(original)
                break
            candidate ^= pivots[i]
    return columns


def expand(n, f):
    """Obtain all degree-at-most-two coefficients using zero, units and pairs."""
    const = f(0)
    linear = [f(1 << i) ^ const for i in range(n)]
    cross = {}
    for i, j in combinations(range(n), 2):
        coefficient = f((1 << i) | (1 << j)) ^ linear[i] ^ linear[j] ^ const
        if coefficient:
            cross[i, j] = coefficient
    return QuadraticMap(const, linear, cross)


def exhaustive_spectrum(q):
    # Transform the directly enumerated histogram into all signed coefficients.
    size = 1 << len(q.linear)
    values = [0] * size
    for x in range(size):
        values[q.value(x)] += 1
    step = 1
    while step < size:
        for start in range(0, size, 2 * step):
            for i in range(start, start + step):
                low, high = values[i], values[i + step]
                values[i], values[i + step] = low + high, low - high
        step *= 2
    return values


def experiment(n, rng, exhaustive):
    inputs, outputs = random_basis(n, rng), random_basis(n, rng)

    def original(x):
        u = mix(inputs, x)
        return u ^ ((u & 1) & (u >> 1))

    a = expand(n, lambda x: mix(outputs, original(x)))
    b = expand(n, lambda x: mix(outputs, original(x) ^ 3))
    mask, flat = locate(a, b)
    # Only the test harness sees the planted basis.
    assert [dot(mask, col) for col in outputs] == [1] + [0] * (n - 1)
    assert flat == n - 2
    assert count_one_system(a) == (1, 4)
    assert count_one_system(b) == (0, 4)
    signals = (signed_probe(a, mask), signed_probe(b, mask))
    assert signals == (1 << (n - 1), -(1 << (n - 1)))
    if exhaustive:
        wa, wb = exhaustive_spectrum(a), exhaustive_spectrum(b)
        assert [c for c in range(1 << n) if wa[c] != wb[c]] == [mask]
        assert all(signed_probe(a, c) == wa[c] and signed_probe(b, c) == wb[c]
                   for c in range(1 << n))
    return mask, flat, signals


if __name__ == "__main__":
    rng = Random(20261121)
    for n in range(2, 10):
        for _ in range(12):
            experiment(n, rng, True)
    print("96 mixed pairs checked exhaustively at 2 through 9 bits.")
    print("Counting either system alone used four masks and returned 1 and 0 respectively.")
    for n in (16, 32, 64, 128):
        mask, flat, (wa, wb) = experiment(n, rng, False)
        print(f"{n} bits, {flat} flat input directions, mask {mask:#x}, probes {wa}, {wb}")
