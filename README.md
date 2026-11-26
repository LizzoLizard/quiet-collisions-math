# Quiet collisions: the exact collision cost of low-weight uniformity for polynomial maps over GF(2)

[![lean](https://github.com/LizzoLizard/quiet-collisions-math/actions/workflows/lean.yml/badge.svg)](https://github.com/LizzoLizard/quiet-collisions-math/actions/workflows/lean.yml)
![Lean 4.15.0](https://img.shields.io/badge/Lean-4.15.0-blue)
![no sorry](https://img.shields.io/badge/sorry-0-brightgreen)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.24427416-blue)](https://doi.org/10.5281/zenodo.24427416)
[![License: MIT](https://img.shields.io/badge/code-MIT-green)](LICENSE)
[![Paper: CC BY 4.0](https://img.shields.io/badge/paper-CC%20BY%204.0-lightgrey)](paper/LICENSE)

**Daniel Ayomide Shittu**, Rowan University · November 2026 · [paper (PDF)](paper/quiet_collisions.pdf) · [plain-language explainer (PDF)](explainer/explainer.pdf) · [project page](https://lizzolizard.github.io/quiet-collisions-math/)

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

Both lower bounds are classical. The contribution here is that the larger one is
always attained, and the corresponding exact answer for compressing maps. We have not
found these exact statements in the literature; if you know a reference, please open an
issue.

## In plain words

Take a rule that scrambles n-bit strings into n-bit strings, built from simple
polynomial formulas of degree at most k. If the rule never sends two inputs to the same
output (a *bijection*), its output on a random input is perfectly random. Now ask for less:
the output only has to look perfectly random when you inspect any d output bits at a
time. Such a rule can have *collisions* (two inputs with the same output). How few
collisions can it get away with, if it is not a bijection?

The answer is an exact power of two, and both halves are proved: no such rule can do
better, and an explicit "ring of gates" achieves it. Every step is checked by the Lean
proof assistant, and independent Python enumeration confirms the small cases.

## Contents

| Path | What it is |
|---|---|
| `paper/` | The paper (PDF and LaTeX source, 7 pages) |
| `explainer/` | A no-math explainer for non-specialists (3 pages) |
| `lean/ChallengeDefs.lean` | Every definition used in the main statements (bit-vectors, Walsh sums, collisions, degree, d-wise uniformity). No imports. |
| `lean/Challenge.lean` | The two main theorems, each with `sorry`. With `ChallengeDefs.lean`, this is everything a reader has to trust. |
| `lean/Solution.lean` | Proofs of those two statements, taken from the proof files |
| `lean/ExactCollisionMinimum.lean` | Square maps, every degree k: `exact_minimum` (attained, and a lower bound for every eligible map) |
| `lean/RectangularCollisionMinimum.lean` | Compressing maps 1 ≤ m ≤ n: `rect_exact_minimum` |
| `lean/DegreeDivisibility.lean` | `mceliece_divisibility`: degree-k signed sums are divisible by 2^⌈N/k⌉ |
| `lean/GroupedRing.lean` | The grouped-control ring: histogram, spectrum, degree, silence |
| `lean/SilentRoom.lean` | The support bound `quiet_support`, plus the quadratic case `minimum_excess_bound` |
| `lean/RingCracks.lean` | The quadratic ring: `ring_histogram`, `reduced_spectrum`, `optimal_ring` |
| `lean/*.lean` (others) | Supporting lemmas: Walsh sums, collision law, permutations |
| `lean/config.json`, `lean/check_comparator.sh` | Comparator check: Solution must prove exactly the statements of Challenge |
| `checks/` | Independent Python checks: 78 quadratic and 495 grouped rings checked in every bucket and mask; every square map up to 3 bits; every eligible compressing map in 30 cases with n ≤ 6 |
| `formalization.yaml` | Machine-readable summary of what is formalized ([format](https://github.com/mathlib-initiative/formalization.yaml)) |
| `verify.sh` | Runs every check below; GitHub Actions runs it on every push |
| `CITATION.cff`, `.zenodo.json` | Citation metadata |

## Verify

You need [Lean 4.15.0](https://lean-lang.org) (no Mathlib), Python 3 and NumPy. Then run

```sh
./verify.sh
```

It stops at the first failure. It checks the Lean version and the SHA-256 sums of all Lean
files; scans for `sorry`, `admit`, `axiom` and `native_decide` outside comments; compiles
all 16 Lean files; runs the comparator check (both statements in `Solution.lean` must be
identical to those in `Challenge.lean`, over identical definitions, using only `propext`,
`Quot.sound` and `Classical.choice`); checks that every `#print axioms` report (77
theorems) lists only those three axioms; and runs the Python checks. It takes under a
minute. With Lake: `lake build`, then `lean/check_comparator.sh`.

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

## Citing

Archived on Zenodo: https://doi.org/10.5281/zenodo.24427416 (this DOI always points to the latest version).
GitHub's "Cite this repository" button uses `CITATION.cff`.

```bibtex
@misc{shittu2026quiet,
  author = {Shittu, Daniel Ayomide},
  title  = {The exact collision cost of low-weight uniformity for polynomial maps over {GF(2)}},
  year   = {2026},
  doi    = {10.5281/zenodo.24427416},
  note   = {Preprint. Paper and Lean 4 proof}
}
```

## License

Code (Lean files and scripts): MIT, see `LICENSE`. Paper and explainer: CC BY 4.0, see `paper/LICENSE`.
