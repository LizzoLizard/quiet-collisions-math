import GroupedRing
import CubePermutation

/-! The exact minimum is expressed by an attainable integer and a lower bound
for every attainable integer. Collision counts are ordered and include the diagonal. -/
namespace ExactCollisionMinimum
open FrozenShells CollisionLaw MaskRecovery SilentRoom DegreeDivisibility CubePermutation

theorem lower_bound (hk : 0 < k) (possible : Attainable n k d value) :
    many (max ((n+k-1)/k) (d+1)) ≤ value := by
  obtain ⟨Q,degree,quiet,nonperm,rfl⟩ := possible
  have coll := (positive_iff_nonpermutation Q).mpr nonperm
  have byDegree := divisibility_excess Q _ (walsh_dvd hk Q degree) coll
  have bySilence := quiet_excess Q d coll (by
    intro c wt
    by_cases z : c = zero n
    · simp [offZero,z]
    · simp [offZero,z,quiet c z wt])
  cases Nat.le_total ((n+k-1)/k) (d+1) with
  | inl h => simpa only [Nat.max_eq_right h] using bySilence
  | inr h => simpa only [Nat.max_eq_left h] using byDegree

/-- With L = max(ceil(n/k), d+1), the n−L controls fit into L groups
    of at most k−1. Represent L as h+1 to include the one-wire ring. -/
private theorem ring_sizes (n k d : Nat) (hk : 0 < k) (hd : d < n) :
    ∃ h s : Nat, (h+1)+s = n ∧ h+1 = max ((n+k-1)/k) (d+1) ∧
      s ≤ (h+1)*(k-1) ∧ d < h+1 := by
  let L := max ((n+k-1)/k) (d+1)
  have hc : (n+k-1)/k ≤ L := Nat.le_max_left _ _
  have hs : d+1 ≤ L := Nat.le_max_right _ _
  have nLe : n ≤ n*k := by simpa using Nat.mul_le_mul_left n hk
  have len : L ≤ n := by
    apply Nat.max_le.mpr
    refine ⟨Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hk).mpr ?_), by omega⟩
    rw [Nat.succ_mul]
    omega
  have enough : n ≤ L*k := by
    have rem := Nat.mod_lt (n+k-1) hk
    have eq := Nat.div_add_mod (n+k-1) k
    rw [Nat.mul_comm k] at eq
    have mul := Nat.mul_le_mul_right k hc
    omega
  obtain ⟨h,hl⟩ : ∃ h, L = h+1 := ⟨L-1,by omega⟩
  refine ⟨h,n-L,by omega,hl.symm,?_,by omega⟩
  rw [←hl,Nat.mul_sub_one]
  omega

theorem grouped_attainment (hk : 0 < k) (hd : d < n) :
    Attainable n k d (many (max ((n+k-1)/k) (d+1))) := by
  obtain ⟨h,s,dim,length,cap,low⟩ := ring_sizes n k d hk hd
  subst n
  let Q := GroupedRing.ring (k-1) h s
  have degree : MapDegree k ((h+1)+s) Q := by
    simpa only [show k-1+1 = k by omega] using GroupedRing.grouped_degree (k-1) h s
  have cost := GroupedRing.grouped_excess (k-1) h s cap
  have pos := many_pos (h+1)
  refine ⟨Q,degree,?_,(positive_iff_nonpermutation Q).mp (by dsimp [Q]; omega),?_⟩
  · intro c nz wt
    simpa only [offZero,nz,if_false] using GroupedRing.grouped_quiet (k-1) h s d cap low c wt
  · rw [←length]
    exact cost

/-- For each positive degree bound and 0 ≤ d < n the stated power of two
    occurs, and no eligible map has smaller ordered collision excess. -/
theorem exact_minimum (n k d : Nat) (hk : 0 < k) (hd : d < n) :
    Attainable n k d (many (max ((n+k-1)/k) (d+1))) ∧
    ∀ value, Attainable n k d value → many (max ((n+k-1)/k) (d+1)) ≤ value :=
  ⟨grouped_attainment hk hd, fun _ => lower_bound hk⟩

#print axioms lower_bound
#print axioms grouped_attainment
#print axioms exact_minimum
end ExactCollisionMinimum
