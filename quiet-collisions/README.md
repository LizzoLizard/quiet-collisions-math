# The exact collision cost of low-weight uniformity for quadratic maps

**Ayomide (Daniel) Shittu**, November 2026 · [paper (PDF)](paper/quiet_collisions.pdf)

Let Q: F₂ᴺ → F₂ᴺ have coordinates of degree at most two. Suppose its output on a
uniform input is d-wise uniform (every Walsh coefficient on a nonzero mask of
weight ≤ d vanishes), but Q is not a bijection. Then the smallest possible
number of ordered collisions C(Q) = #{(x, x′) : Q(x) = Q(x′)} satisfies

```
min (C(Q) − 2^N) = 2^max(⌈N/2⌉, d+1)        for 0 ≤ d < N.
```

The lower bound is the larger of two classical bounds. One is the
Reed–Muller dual-distance bound, which gives 2^(d+1). The other is the
divisibility of quadratic Walsh coefficients, which gives 2^⌈N/2⌉. The point of
this note is that the larger bound is always attained, by an explicit ring of
quadratic gates. For example, at N = 10 and d = 4 the ring has 16 double
buckets and 16 empty ones, every mask of 4 or fewer bits reads 0, and the
5-bit all-wires mask reads +32.

I could not find this exact statement in the literature. If you know a
reference, please open an issue.

## A note on this repository

This exists to put the result out there. It is not a polished paper, and I
apologise for the informal write-up. I hope to write a more careful version
when I have the time. Comments, corrections and pointers to prior work are very
welcome.

## Contents

| Path | What it is |
|---|---|
| `paper/` | The note (PDF and LaTeX source) |
| `lean/SilentRoom.lean` | Lower bounds: `quiet_support`, `quadratic_divisibility`, `minimum_excess_bound` |
| `lean/RingCracks.lean` | The matching construction: `ring_histogram`, `reduced_spectrum`, `optimal_ring` |
| `lean/*.lean` (others) | Supporting definitions: Walsh sums, the quadratic counter, collision law |
| `checks/` | Independent Python checks: every bucket and mask of the ring for 78 (N, d) pairs up to N = 12 |

## Verify

You need [Lean 4.15.0](https://lean-lang.org) (no Mathlib) and Python 3:

```sh
./verify.sh
```

Each Lean file prints `#print axioms` for its theorems. Every theorem uses only
Lean's standard axioms (`propext`, `Quot.sound`, `Classical.choice`). None uses
`sorry`.

## Acknowledgements

I thank Claude (an AI model by Anthropic), which helped with the proofs, the
Lean formalization and the write-up, and Astra and Gemini Neon for their help.

## License

Code: MIT (see `LICENSE`). Paper: CC BY 4.0.
