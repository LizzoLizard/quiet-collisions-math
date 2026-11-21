import CollisionCircuit

namespace SilentRoom
open FrozenShells CandyKnots FreezeMovies CollisionLaw MaskRecovery

def weight : (n : Nat) → W n → Nat
  | 0, _ => 0
  | n+1, c => weight n c.2 + (if c.1 then 1 else 0)

def transform (f : W n → Int) (c : W n) := total n (fun y => f y * chr c y)
def histogram (Q : W n → W m) (y : W m) := total n (fun x => hits (Q x) y)
def changed (f : W n → Int) := total n (fun x => if f x = 0 then 0 else 1)

theorem by_histogram (Q : W n → W m) (c : W m) : walsh Q c = transform (histogram Q) c := by
  unfold walsh transform histogram
  have eq (y : W m) :
      total n (fun x => hits (Q x) y) * chr c y = total n (fun x => hits (Q x) y * chr c y) := by
    simp only [Int.mul_comm _ (chr c y),total_scale]
  simp only [eq]
  rw [swap]
  simp only [select]

theorem crack_formula (Q : W n → W n) (u v c : W n)
    (h : ∀ y, histogram Q y = 1 + hits u y - hits v y) (nz : c ≠ zero n) :
    walsh Q c = chr c u - chr c v := by
  rw [by_histogram]
  simp only [transform,h,Int.sub_mul,Int.add_mul,Int.one_mul,total_sub,total_add,select]
  have e := identity_spectrum n c
  simp only [walsh, nz, if_false] at e
  rw [e]; omega

/-- Once a singleton detects a crack, adding it to a silent singleton
    reveals the common bit at the silent position through the sign. -/
theorem reference_probe (Q : W n → W n) (u v a c : W n)
    (h : ∀ y, histogram Q y = 1 + hits u y - hits v y)
    (anchor : a ≠ zero n) (pair : add n c a ≠ zero n) (same : dot n c u = dot n c v) :
    walsh Q (add n c a) = chr c u * walsh Q a := by
  rw [crack_formula Q u v _ h pair,crack_formula Q u v _ h anchor]
  simp only [chr,dot_add,signMul,same,Int.mul_sub]

theorem weight_zero (n : Nat) : weight n (zero n) = 0 := by induction n <;> simp [weight,zero, *]

theorem separating_wire (n : Nat) (u v : W n) (ne : u ≠ v) :
    ∃ c, weight n c = 1 ∧ dot n c u ≠ dot n c v := by
  induction n with
  | zero => cases u; cases v; contradiction
  | succ n ih =>
    rcases u with ⟨a,u⟩; rcases v with ⟨b,v⟩
    by_cases h : a = b
    · subst b
      obtain ⟨c,w,d⟩ := ih u v (fun e => ne (e ▸ rfl))
      exact ⟨(false,c),by simpa [weight] using w, by simpa [dot] using d⟩
    · exact ⟨(true,zero n),by simp [weight,weight_zero],by simpa [dot,dot_zero] using h⟩

theorem isolated_crack (Q : W n → W n) (u v : W n) (ne : u ≠ v)
    (h : ∀ y, histogram Q y = 1 + hits u y - hits v y) :
    ∃ c, weight n c = 1 ∧ (walsh Q c = 2 ∨ walsh Q c = -2) := by
  obtain ⟨c,w,d⟩ := separating_wire n u v ne
  have nz : c ≠ zero n := fun e => by rw [e,weight_zero] at w; contradiction
  refine ⟨c,w,?_⟩
  rw [crack_formula Q u v c h nz]
  cases a : dot n c u <;> cases b : dot n c v <;> simp_all [chr,sign]

theorem detected (n : Nat) (f : W n → Int) (x : W n) (h : f x ≠ 0) : 1 ≤ changed f := by
  have point (y : W n) : hits x y ≤ (if f y = 0 then 0 else 1) := by
    by_cases e : x = y
    · subst y; simp [hits,h]
    · simp only [hits,e,if_false]; split <;> decide
  have := total_mono n _ _ point
  rwa [diagonal] at this

theorem head_transform (f : W (n+1) → Int) (b : Bool) (c : W n) :
    transform f (b,c) = transform (fun x => f (false,x)) c +
      (if b then -transform (fun x => f (true,x)) c else transform (fun x => f (true,x)) c) := by
  unfold transform
  rw [total]
  have lo (x : W n) : chr (r := n+1) (b,c) (false,x) = chr c x := by simp [chr,dot]
  have hi (x : W n) : chr (r := n+1) (b,c) (true,x) = sign b * chr c x := by
    simp [chr,dot,signMul]
  cases b <;> simp [lo,hi,sign,twice_total]

/-- If every mask of weight below k is silent, any nonzero deviation must
    occupy at least 2^k distinct output buckets. -/
theorem quiet_support (n k : Nat) (f : W n → Int)
    (quiet : ∀ c, weight n c < k → transform f c = 0) (live : ∃ y, f y ≠ 0) :
    many k ≤ changed f := by
  induction n generalizing k with
  | zero =>
    obtain ⟨⟨⟩,h⟩ := live
    cases k with
    | zero => exact detected 0 f () h
    | succ k => have e := quiet () (by simp [weight]); simp [transform,total,chr,dot,sign] at e; contradiction
  | succ n ih =>
    classical
    cases k with
    | zero => obtain ⟨x,h⟩ := live; exact detected (n+1) f x h
    | succ k =>
      let g := fun x : W n => f (false,x) + f (true,x)
      have low (c : W n) (h : weight n c < k+1) :=
        quiet (false,c) (by simpa [weight] using h)
      have high (c : W n) (h : weight n c < k) :=
        quiet (true,c) (by simpa [weight] using h)
      by_cases nonzero : ∃ x, g x ≠ 0
      · have q (c : W n) (h : weight n c < k+1) : transform g c = 0 := by
          have e := low c h
          rw [head_transform] at e
          simpa [g,transform,Int.add_mul,total_add] using e
        apply Int.le_trans (ih (k+1) g q nonzero)
        unfold changed
        rw [total,←total_add]
        apply total_mono
        intro x
        dsimp only [g]
        split <;> split <;> split <;> omega
      · have opp (x : W n) : f (true,x) = -f (false,x) := by
          have h : g x = 0 := by by_cases e : g x = 0; exact e; exact False.elim (nonzero ⟨x,e⟩)
          dsimp only [g] at h; omega
        have nz : ∃ x, f (false,x) ≠ 0 := by
          obtain ⟨⟨b,x⟩,h⟩ := live
          cases b with
          | false => exact ⟨x,h⟩
          | true => exact ⟨x,by rw [opp] at h; omega⟩
        have q (c : W n) (h : weight n c < k) : transform (fun x => f (false,x)) c = 0 := by
          have a := low c (by omega)
          have b := high c h
          simp only [head_transform,if_true,Bool.false_eq_true,if_false] at a b
          omega
        have bound := ih k _ q nz
        have dup : changed f = changed (fun x : W n => f (false,x)) + changed (fun x : W n => f (false,x)) := by
          simp [changed,total,opp]
        rw [dup]; unfold many at *; rw [Int.pow_succ]; omega

theorem double_dvd {a v : Int} (h : a ∣ v) : a*2 ∣ 2*v := by
  obtain ⟨z,rfl⟩ := h
  exact ⟨z,by rw [Int.mul_comm a 2,Int.mul_assoc]⟩

/-- At least one factor of two survives per pair of quadratic input variables. -/
theorem quadratic_divisibility : (n k : Nat) → (q : Quad n) → 2*k ≤ n+1 → many k ∣ countBias n q
  | n, 0, q, _ => ⟨countBias n q, by simp [many]⟩
  | 0, k+1, _, h => by omega
  | 1, k+1, q, h => by
    have ek : k = 0 := by omega
    subst k
    cases e : q.1.const with
    | false => exact ⟨sign q.2,by simp [countBias,many,e]⟩
    | true => exact ⟨0,by simp [countBias,many,e]⟩
  | n+2, k+1, q, h => by
    simp only [many,Int.pow_succ]
    cases e : pick q.1.bits with
    | none =>
      simp only [countBias,e]
      split
      · exact ⟨0,by simp⟩
      · exact double_dvd (quadratic_divisibility (n+1) k _ (by omega))
    | some i =>
      simp only [countBias,e]
      exact double_dvd (quadratic_divisibility n k _ (by omega))
termination_by n k _ _ => n+k

theorem no_quadratic_crack (large : 3 ≤ n)
    (Q : W n → W n) (rep : ∀ c, ∃ q : Quad n, walsh Q c = countBias n q)
    (u v : W n) (ne : u ≠ v) : ¬∀ y, histogram Q y = 1 + hits u y - hits v y := by
  intro h
  obtain ⟨c,_,w⟩ := isolated_crack Q u v ne h
  obtain ⟨q,e⟩ := rep c
  have div := quadratic_divisibility n 2 q (by omega)
  change (4:Int) ∣ countBias n q at div
  omega

def deviation (Q : W n → W n) (y : W n) := histogram Q y - 1

theorem deviation_transform (Q : W n → W n) (c : W n) :
    transform (deviation Q) c = offZero Q c := by
  simp only [transform,deviation,Int.sub_mul,Int.one_mul,total_sub]
  have unit := identity_spectrum n c
  change total n (chr c) = _ at unit
  change transform (histogram Q) c - total n (chr c) = _
  rw [← by_histogram,unit]
  by_cases z : c = zero n
  · subst c; simp [offZero,walsh,chr,dot_zero,sign,total_const]
  · simp [offZero,z]

theorem histogram_mass (Q : W n → W n) : total n (histogram Q) = many n := by
  unfold histogram
  rw [swap]
  simp [diagonal,total_const]

theorem histogram_square (Q : W n → W n) :
    total n (fun y => histogram Q y * histogram Q y) = collisions Q := by
  have expand (y : W n) : histogram Q y * histogram Q y =
      total n (fun x => hits (Q x) y * histogram Q y) := by
    simp only [Int.mul_comm _ (histogram Q y),total_scale]
    rfl
  simp only [expand]
  rw [swap]
  simp only [select]
  unfold histogram collisions
  apply congrArg (total n); funext x
  apply congrArg (total n); funext y
  simp [hits,eq_comm]

theorem excess (Q : W n → W n) :
    total n (fun y => deviation Q y * deviation Q y) = collisions Q - many n := by
  simp only [deviation,Int.sub_mul,Int.mul_sub,Int.one_mul,Int.mul_one,total_sub,
    total_add,histogram_square,histogram_mass,total_const]
  omega

theorem probe_bounds (Q : W n → W n) (c : W n) (nz : c ≠ zero n) :
    -(collisions Q - many n) ≤ walsh Q c ∧ walsh Q c ≤ collisions Q - many n := by
  have bounds (z : Int) : - (z*z) ≤ z ∧ z ≤ z*z := by
    have a := Int.mul_nonneg_of_nonpos_of_nonpos (a := z) (b := z-1)
    have b := Int.mul_nonneg (a := z) (b := z-1)
    have c' := Int.mul_nonneg_of_nonpos_of_nonpos (a := z) (b := z+1)
    have d := Int.mul_nonneg (a := z) (b := z+1)
    simp only [Int.mul_sub,Int.mul_add,Int.mul_one] at *
    by_cases h : z ≤ -1 <;> by_cases h' : 1 ≤ z <;> omega
  have e (y : W n) : -(deviation Q y * deviation Q y) ≤ deviation Q y * chr c y ∧
      deviation Q y * chr c y ≤ deviation Q y * deviation Q y := by
    have b := bounds (deviation Q y)
    cases h : dot n c y <;> simp [chr,h,sign] <;> omega
  have l := total_mono n _ _ (fun y => (e y).1)
  have u := total_mono n _ _ (fun y => (e y).2)
  have t := deviation_transform Q c
  simp only [offZero,nz,if_false,transform] at t
  simp only [twice_total,excess,t] at l u
  exact ⟨l,u⟩

theorem divisibility_excess (Q : W n → W n) (m : Nat) (div : ∀ c, many m ∣ walsh Q c)
    (collision : many n < collisions Q) : many m ≤ collisions Q - many n := by
  classical
  have ex : ∃ c, offZero Q c ≠ 0 := by
    by_cases h : ∃ c, offZero Q c ≠ 0
    · exact h
    · have allzero (c : W n) : offZero Q c = 0 := by
        by_cases e : offZero Q c = 0; exact e; exact False.elim (h ⟨c,e⟩)
      have E := residual_energy Q
      simp only [allzero,Int.zero_mul,total_zero,← Int.mul_sub] at E
      have pos := Int.mul_pos (many_pos n) (show 0 < collisions Q - many n by omega)
      omega
  obtain ⟨c,h⟩ := ex
  have nz : c ≠ zero n := by intro z; subst c; simp [offZero] at h
  simp only [offZero,nz,if_false] at h
  have b := probe_bounds Q c nz
  obtain ⟨z,wp⟩ := div c
  have pp : 0 ≤ many m := many_nonneg _
  by_cases zero : z = 0
  · simp [zero] at wp; contradiction
  · by_cases pos : 1 ≤ z
    · have bound := Int.mul_le_mul_of_nonneg_left pos pp
      simp only [Int.mul_one] at bound; omega
    · have bound := Int.mul_le_mul_of_nonneg_left (show z ≤ -1 by omega) pp
      simp at bound; omega

theorem quadratic_excess (Q : W n → W n) (rep : ∀ c, ∃ q : Quad n, walsh Q c = countBias n q)
    (collision : many n < collisions Q) : many ((n+1)/2) ≤ collisions Q - many n := by
  apply divisibility_excess Q _ _ collision
  intro c
  obtain ⟨q,e⟩ := rep c
  rw [e]
  exact quadratic_divisibility n ((n+1)/2) q (by omega)

theorem quiet_excess (Q : W n → W n) (d : Nat) (collision : many n < collisions Q)
    (quiet : ∀ c, weight n c ≤ d → offZero Q c = 0) :
    many (d+1) ≤ collisions Q - many n := by
  classical
  have live : ∃ x, deviation Q x ≠ 0 := by
    by_cases e : ∃ x, deviation Q x ≠ 0
    · exact e
    · have hz (x : W n) : deviation Q x = 0 := by
        by_cases h : deviation Q x = 0; exact h; exact False.elim (e ⟨x,h⟩)
      have sq := excess Q
      simp only [hz,Int.zero_mul,total_zero] at sq
      omega
  have lower := quiet_support n (d+1) (deviation Q)
    (fun c h => (deviation_transform Q c).trans (quiet c (by omega))) live
  rw [← excess]
  apply Int.le_trans lower
  apply total_mono
  intro x
  generalize deviation Q x = z
  by_cases h : z = 0
  · simp [h]
  · simp only [h,if_false]
    by_cases pos : 0 < z
    · have e := Int.mul_pos pos pos; omega
    · have e := Int.mul_pos (show 0 < -z by omega) (show 0 < -z by omega)
      simp at e; omega

/-- Transport a listed system into square coordinates when it has n rows. -/
def asSquare (ps : List (Quad n)) (h : ps.length = n) (x : W n) : W n :=
  cast (congrArg W h) (outputs ps x)

theorem transport_probe (F : W n → W r) (h : r = m) (c : W m) :
    walsh (fun x => cast (congrArg W h) (F x)) c = walsh F (cast (congrArg W h.symm) c) := by
  subst m; rfl

/-- Joint lower bound for exactly the quadratic representation used by the lab. -/
theorem minimum_excess_bound (ps : List (Quad n)) (h : ps.length = n) (d : Nat)
    (collision : many n < collisions (asSquare ps h))
    (quiet : ∀ c, weight n c ≤ d → offZero (asSquare ps h) c = 0) :
    many (max ((n+1)/2) (d+1)) ≤ collisions (asSquare ps h) - many n := by
  have rep (c : W n) : ∃ q : Quad n, walsh (asSquare ps h) c = countBias n q := by
    unfold asSquare
    rw [transport_probe (outputs ps) h]
    exact ⟨_,(fast_probe ps _).symm⟩
  have quad := quadratic_excess _ rep collision
  have sparse := quiet_excess _ d collision quiet
  cases Nat.le_total ((n+1)/2) (d+1) with
  | inl e => simpa only [Nat.max_eq_right e] using sparse
  | inr e => simpa only [Nat.max_eq_left e] using quad

/-- Repeated positive literal, the one-clause formula (x OR x OR x). -/
def oneClause : List (CollisionCircuit.Clause 1) :=
  let falsity : Form 1 := ⟨(true,()),true⟩
  [⟨falsity,falsity,falsity⟩]

def circuitProbe (a : W 1) (b : W 4) :=
  total 1 (fun x => chr a x * walsh (CollisionCircuit.wires oneClause x) b)

theorem circuit_example : CollisionCircuit.orderedCollisions oneClause = 48 ∧
    (∀ (a : W 1) (b : W 4), weight 1 a + weight 4 b = 1 → circuitProbe a b = 0) ∧
    circuitProbe (zero 1) (true,false,false,true,()) = 16 := by
  refine ⟨?_,?_,by decide⟩
  · rw [CollisionCircuit.collision_count]; decide
  · rintro ⟨a,⟨⟩⟩ ⟨b,c,d,e,⟨⟩⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

#print axioms isolated_crack
#print axioms reference_probe
#print axioms quiet_support
#print axioms quadratic_divisibility
#print axioms no_quadratic_crack
#print axioms quadratic_excess
#print axioms quiet_excess
#print axioms minimum_excess_bound
#print axioms circuit_example
end SilentRoom
