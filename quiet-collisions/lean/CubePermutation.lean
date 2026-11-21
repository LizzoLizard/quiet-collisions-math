import SilentRoom

namespace CubePermutation
open FrozenShells CandyKnots CollisionLaw MaskRecovery SilentRoom

/-- Each output has exactly one preimage. -/
def IsPermutation (Q : W n → W n) : Prop :=
  ∀ y, ∃ x, Q x = y ∧ ∀ z, Q z = y → z = x

private theorem term_le_total (f : W n → Int) (nn : ∀ z, 0 ≤ f z) (x : W n) :
    f x ≤ total n f := by
  rw [← select n x f]
  apply total_mono
  intro z
  by_cases h : x = z <;> simp [hits,h,nn]

theorem histogram_one_iff (Q : W n → W m) (y : W m) :
    histogram Q y = 1 ↔ ∃ x, Q x = y ∧ ∀ z, Q z = y → z = x := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ : ∃ x, Q x = y := by
      by_cases ex : ∃ x, Q x = y
      · exact ex
      · have empty (x : W n) : hits (Q x) y = 0 := by
          simp [hits, show Q x ≠ y from fun e => ex ⟨x,e⟩]
        simp [histogram,empty,total_zero] at h
    refine ⟨x,hx,?_⟩
    let f := fun z => hits (Q z) y - hits x z
    have nn (z : W n) : 0 ≤ f z := by
      by_cases e : x = z
      · subst z; simp [f,hits,hx]
      · simp only [f,hits,e,if_false,Int.sub_zero]; split <;> decide
    have sum : total n f = 0 := by
      change total n (fun z => hits (Q z) y - hits x z) = 0
      rw [total_sub,diagonal, ← histogram,h]; decide
    intro z hz
    by_cases e : x = z
    · exact e.symm
    · have bad := term_le_total f nn z
      rw [sum] at bad
      simp [f,hits,hz,e] at bad
  · rintro ⟨x,hx,unique⟩
    have eq (z : W n) : hits (Q z) y = hits x z := by
      have e : Q z = y ↔ x = z := ⟨fun h => (unique z h).symm,fun h => h ▸ hx⟩
      simp only [hits,e]
    simp [histogram,eq,diagonal]

theorem positive_iff_nonpermutation (Q : W n → W n) :
    many n < collisions Q ↔ ¬ IsPermutation Q := by
  constructor
  · intro pos perm
    have vanish (y : W n) : deviation Q y = 0 := by
      simp [deviation,(histogram_one_iff Q y).mpr (perm y)]
    have e := excess Q
    simp [vanish,total_zero] at e
    omega
  · intro nonperm
    by_cases pos : many n < collisions Q
    · exact pos
    · exfalso
      apply nonperm
      intro y
      apply (histogram_one_iff Q y).mp
      have nn (z : W n) : 0 ≤ deviation Q z * deviation Q z := by
        rw [← Int.natAbs_mul_self]; exact Int.ofNat_zero_le _
      have bound := term_le_total _ nn y
      rw [excess] at bound
      have sq : deviation Q y * deviation Q y = 0 := by have := nn y; omega
      have val := Int.mul_eq_zero.mp sq
      unfold deviation at val
      omega

#print axioms positive_iff_nonpermutation
end CubePermutation
