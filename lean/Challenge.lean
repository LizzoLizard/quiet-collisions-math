/-
  Challenge.lean: the two main theorems, with `sorry` as placeholder.

  Imports only `ChallengeDefs`. The comparator check (`config.json`, `check_comparator.sh`)
  confirms that `Solution.lean` proves exactly these statements, over the same definitions,
  using only the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/
import ChallengeDefs

namespace QuietCollisionsChallenge
open FrozenShells CollisionLaw ExactCollisionMinimum RectangularCollisionMinimum

/-- Square maps. For every degree bound `k ≥ 1` and `0 ≤ d < n`, the smallest ordered-collision
    excess `C(Q) − 2^n` of a non-bijective map `Q : F_2^n → F_2^n` of degree `≤ k` whose output is
    `d`-wise uniform is `2^max(⌈n/k⌉, d+1)`: this value is attained, and no such map does better. -/
theorem exact_minimum (n k d : Nat) (hk : 0 < k) (hd : d < n) :
    Attainable n k d (many (max ((n+k-1)/k) (d+1))) ∧
    ∀ value, Attainable n k d value → many (max ((n+k-1)/k) (d+1)) ≤ value := sorry

/-- Compressing maps `Q : F_2^n → F_2^m`, `m ≤ n`. The smallest excess `C(Q) − 2^(2n−m)` is
    `2^max(2⌈n/k⌉ − m, ⌈n/k⌉, d+1)` (`rectExp`): attained, and a lower bound for every eligible map. -/
theorem rect_exact_minimum (n m k d : Nat) (hm : m ≤ n) (hk : 0 < k) (hd : d < m) :
    RectAttainable n m k d (many (rectExp n m k d)) ∧
    ∀ value, RectAttainable n m k d value → many (rectExp n m k d) ≤ value := sorry

end QuietCollisionsChallenge
