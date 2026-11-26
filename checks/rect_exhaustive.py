"""Exhaustive check of the rectangular minimum for small sizes.

For every map Q: F_2^n -> F_2^m whose coordinates have degree <= k, that is
silent through d and has C(Q) > 2^(2n-m), compute the least C(Q) - 2^(2n-m)
and compare it with 2^max(2*ceil(n/k) - m, ceil(n/k), d + 1).

Uses 2^m * (C(Q) - 2^(2n-m)) = sum over nonzero masks c of W_Q(c)^2.
Reductions that keep the answer unchanged: output coordinates in sorted
order (a coordinate permutation preserves mask weights and collisions), and
no constant terms (an output translation only flips signs of W_Q(c)).
"""
import itertools
import numpy as np


def reed_muller(n, k):
    """All Boolean functions of degree <= k with no constant term, as 2^n-bit integers."""
    N = 1 << n
    monos = [S for r in range(1, k + 1) for S in itertools.combinations(range(n), r)]
    words = np.zeros(1, dtype=np.uint64)
    for S in monos:
        col = np.uint64(sum(1 << x for x in range(N) if all(x >> i & 1 for i in S)))
        words = np.concatenate([words, words ^ col])
    return np.unique(words)


def minimum(n, m, k, d):
    N = 1 << n
    cw = reed_muller(n, k)
    walsh = N - 2 * np.bitwise_count(cw).astype(np.int64)
    if d >= 1:                                   # every single coordinate must be balanced
        keep = walsh == 0
        cw, walsh = cw[keep], walsh[keep]
    best = None

    def extend(prefix, start):
        # prefix: list of codeword indices; comps[c] = XOR for masks c on the prefix
        nonlocal best
        j = len(prefix)
        if j == m - 1:                           # vectorise the last coordinate
            last = np.arange(start, len(cw))
            tot = np.zeros(len(last), dtype=np.int64)
            ok = np.ones(len(last), dtype=bool)
            for c in range(1, 1 << m):
                comp = np.zeros(len(last), dtype=np.uint64)
                for i in range(m - 1):
                    if c >> i & 1:
                        comp ^= cw[prefix[i]]
                if c >> (m - 1) & 1:
                    comp = comp ^ cw[last]
                w = N - 2 * np.bitwise_count(comp).astype(np.int64)
                tot += w * w
                if bin(c).count("1") <= d:
                    ok &= w == 0
            ex = tot[ok & (tot > 0)]
            if len(ex):
                b = int(ex.min())
                best = b if best is None else min(best, b)
            return
        for idx in range(start, len(cw)):
            p = prefix + [idx]
            good = True                          # prune masks living on the prefix
            for c in range(1, 1 << len(p)):
                if bin(c).count("1") <= d:
                    comp = np.uint64(0)
                    for i in range(len(p)):
                        if c >> i & 1:
                            comp ^= cw[p[i]]
                    if N - 2 * int(np.bitwise_count(comp)) != 0:
                        good = False
                        break
            if good:
                extend(p, idx)

    extend([], 0)
    assert best is not None and best % (1 << m) == 0
    return best >> m


def main():
    cases = [(n, m, k, d) for (n, k, mmax) in
             [(3, 1, 3), (3, 2, 3), (4, 1, 3), (4, 2, 3), (4, 3, 1), (5, 1, 2), (5, 2, 1), (6, 2, 1)]
             for m in range(1, mmax + 1) for d in range(m)]
    bad = 0
    for n, m, k, d in cases:
        L = -(-n // k)
        want = 2 ** max(2 * L - m, L, d + 1)
        got = minimum(n, m, k, d)
        regime = "m = n" if m == n else ("deep" if m < L else "shallow")
        print(f"n={n} m={m} k={k} d={d} ({regime}): minimum {got}, formula {want}"
              + ("" if got == want else "  MISMATCH"), flush=True)
        bad += got != want
    print(f"{len(cases)} cases, {bad} mismatches")
    assert bad == 0


if __name__ == "__main__":
    main()
