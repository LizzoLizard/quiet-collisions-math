# Quiet collisions: the exact collision cost of low-weight uniformity

**Ayomide (Daniel) Shittu**, November 2026 · [paper (PDF)](paper/quiet_collisions.pdf) · [plain-language explainer (PDF)](explainer/explainer.pdf)

Let Q: F₂ᴺ → F₂ᴺ have coordinates of algebraic degree at most k. Suppose its
output on a uniform input is d-wise uniform, meaning every Walsh coefficient on
a nonzero mask of weight ≤ d vanishes, but Q is not a bijection. Then the
smallest possible number of ordered collisions
C(Q) = #{(x, x′) : Q(x) = Q(x′)} satisfies

```
min (C(Q) − 2^N) = 2^max(⌈N/k⌉, d+1)        for k ≥ 1 and 0 ≤ d < N.
```

The lower bound is the larger of two classical bounds:

- The support bound for functions whose low-weight Fourier coefficients
  vanish (Reed–Muller dual distance) gives 2^(d+1).
- McEliece-type divisibility of signed sums of degree-k Boolean polynomials
  gives 2^⌈N/k⌉.

The point of this note is that the larger bound is always attained, by an
explicit ring of gates. The ring has L = max(⌈N/k⌉, d+1) wires, and up to k−1
control bits sit on each edge.

**Example (quadratic, k = 2).** At N = 10 and d = 4 the ring has 16 double
buckets and 16 empty ones. Every mask of 4 or fewer bits reads 0, and the
5-bit all-wires mask reads +32.

**Rectangular maps (part 3).** The same question for Q: F₂ⁿ → F₂ᵐ with
1 ≤ m ≤ n, where a uniform map has 2^(2n−m) collisions, has the answer

```
min (C(Q) − 2^(2n−m)) = 2^max(2⌈n/k⌉ − m, ⌈n/k⌉, d+1)        for k ≥ 1 and 0 ≤ d < m.
```

When m ≥ ⌈n/k⌉ this is 2^max(⌈n/k⌉, d+1), the square answer: drop n − m
control wires from the ring's output. When m < ⌈n/k⌉ there are too few output
bits for the ring, and the answer jumps to 2^(2⌈n/k⌉ − m). A third bound
(Parseval: a single nonzero Walsh value, a multiple of 2^⌈n/k⌉, already costs
2^(2⌈n/k⌉ − m)) takes over. It is attained by XOR-folding the surplus ring
wires into one output, which leaves exactly one nonzero Walsh value, on the
all-ones mask.

I could not find these exact statements in the literature. If you know a
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
| `explainer/` | A no-math explainer for non-specialists |
| `lean/ExactCollisionMinimum.lean` | The main theorem `exact_minimum`, for every degree k: attained, and a lower bound for every eligible map |
| `lean/RectangularCollisionMinimum.lean` | Part 3, `rect_exact_minimum`: the rectangular minimum for 1 ≤ m ≤ n, attained and a lower bound for every eligible map |
| `lean/DegreeDivisibility.lean` | `mceliece_divisibility`: degree-k signed sums are divisible by 2^⌈N/k⌉ |
| `lean/GroupedRing.lean` | The grouped-control ring: histogram, spectrum, degree, silence |
| `lean/SilentRoom.lean` | The support bound `quiet_support`, plus the quadratic case `minimum_excess_bound` |
| `lean/RingCracks.lean` | The quadratic ring: `ring_histogram`, `reduced_spectrum`, `optimal_ring` |
| `lean/*.lean` (others) | Supporting definitions: Walsh sums, collision law, permutations |
| `checks/` | Independent Python checks. The 78 quadratic rings and 495 grouped rings up to 10–12 bits are checked in every bucket and mask. Every square map up to 3 bits is enumerated exhaustively. `rect_exhaustive.py` enumerates every eligible rectangular map in 30 small cases (n ≤ 6). |

## Verify

You need [Lean 4.15.0](https://lean-lang.org) (no Mathlib), Python 3 and NumPy 2:

```sh
./verify.sh
```

Each Lean file prints `#print axioms` for its theorems. Every theorem uses only
Lean's standard axioms (`propext`, `Quot.sound`, `Classical.choice`). None uses
`sorry`.

## History

- **Part 1.** The quadratic case: min = 2^max(⌈N/2⌉, d+1).
- **Part 2.** Every degree k: min = 2^max(⌈N/k⌉, d+1). This answers Question 2 of
  the first draft.
- **Part 3.** Rectangular maps F₂ⁿ → F₂ᵐ with m ≤ n (compression):
  min = 2^max(2⌈n/k⌉ − m, ⌈n/k⌉, d+1). This answers the compression half of
  Question 1. Stretching maps (m > n) are still open.

## Acknowledgements

I thank Claude (an AI model by Anthropic), which helped with the proofs, the
Lean formalization and the write-up, and Astra and Gemini Neon for their help.

## License

Code: MIT (see `LICENSE`). Paper and explainer: CC BY 4.0.
