import GroupedRing

namespace RectangularCollisionMinimum
open FrozenShells CandyKnots CollisionLaw MaskRecovery SilentRoom DegreeDivisibility RingCracks GroupedRing

theorem many_add (a b : Nat) : many (a + b) = many a * many b := by
  induction b with
  | zero => simp [many]
  | succ b ih =>
    rw [Nat.add_succ]
    simp only [many, Int.pow_succ] at ih ⊢
    rw [ih, Int.mul_assoc]

theorem many_mul_cancel {a b c : Int} (ha : 0 < a) (h : a * b = a * c) : b = c := by
  have h0 : a * (b - c) = 0 := by rw [Int.mul_sub]; omega
  rcases Int.mul_eq_zero.mp h0 with _ | _ <;> omega

theorem many_mul_le_cancel {a b c : Int} (ha : 0 < a) (h : a * b ≤ a * c) : b ≤ c := by
  by_cases hle : b ≤ c
  · exact hle
  · have hlt : c < b := by omega
    have hgt : a * c < a * b := Int.mul_lt_mul_of_pos_left hlt ha
    omega

def rectHist (Q : W n → W m) (y : W m) : Int :=
  total n (fun x => hits (Q x) y)

def rectDev (n m : Nat) (Q : W n → W m) (y : W m) : Int :=
  rectHist Q y - many (n - m)

def rectOffZero (Q : W n → W m) (c : W m) : Int :=
  if c = zero m then 0 else walsh Q c

def RectSilentThrough (d : Nat) (Q : W n → W m) : Prop :=
  ∀ c, c ≠ zero m → weight m c ≤ d → walsh Q c = 0

def rectExp (n m k d : Nat) : Nat :=
  max (max (2 * ((n + k - 1) / k) - m) ((n + k - 1) / k)) (d + 1)

def RectAttainable (n m k d : Nat) (value : Int) : Prop :=
  ∃ Q : W n → W m, MapDegree k m Q ∧ RectSilentThrough d Q ∧
    many (2 * n - m) < collisions Q ∧ collisions Q - many (2 * n - m) = value

theorem rect_walsh_zero (Q : W n → W m) : walsh Q (zero m) = many n := by
  simp [walsh, chr, dot_zero, sign, total_const]

theorem rect_by_hist (Q : W n → W m) (c : W m) :
    transform (rectHist Q) c = walsh Q c := by
  unfold transform rectHist walsh
  have expand (y : W m) : total n (fun x => hits (Q x) y) * chr c y =
      total n (fun x => hits (Q x) y * chr c y) := by
    rw [Int.mul_comm, ← total_scale]
    apply congrArg (total n); funext x; exact Int.mul_comm ..
  simp only [expand]
  rw [swap m n]
  apply congrArg (total n); funext x
  exact select m (Q x) (chr c)

theorem rect_hist_mass (Q : W n → W m) : total m (rectHist Q) = many n := by
  unfold rectHist
  rw [swap m n]
  simp [diagonal, total_const]

theorem rect_hist_sq (Q : W n → W m) :
    total m (fun y => rectHist Q y * rectHist Q y) = collisions Q := by
  have expand (y : W m) : rectHist Q y * rectHist Q y =
      total n (fun x => hits (Q x) y * rectHist Q y) := by
    simp only [Int.mul_comm _ (rectHist Q y), total_scale]; rfl
  simp only [expand]
  rw [swap m n]
  simp only [select]
  unfold rectHist collisions
  apply congrArg (total n); funext x
  apply congrArg (total n); funext y
  simp [hits, eq_comm]

theorem rect_excess (hm : m ≤ n) (Q : W n → W m) :
    total m (fun y => rectDev n m Q y * rectDev n m Q y) =
      collisions Q - many (2 * n - m) := by
  have h1 : many n * many (n - m) = many (2 * n - m) := by
    rw [← many_add]; congr 1; omega
  have h2 : many m * (many (n - m) * many (n - m)) = many (2 * n - m) := by
    rw [← many_add, ← many_add]; congr 1; omega
  have expand (y : W m) : rectDev n m Q y * rectDev n m Q y =
      rectHist Q y * rectHist Q y - many (n - m) * rectHist Q y -
      many (n - m) * rectHist Q y + many (n - m) * many (n - m) := by
    unfold rectDev
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm (rectHist Q y) (many (n - m))]
    omega
  simp only [expand, total_add, total_sub, total_scale, total_const, rect_hist_sq, rect_hist_mass]
  have h2' : many (n - m) * (many m * many (n - m)) = many (2 * n - m) := by
    rw [show many (n - m) * (many m * many (n - m)) = many m * (many (n - m) * many (n - m)) by ac_rfl, h2]
  rw [Int.mul_comm (many (n - m)) (many n), h1, h2']
  omega

theorem rect_dev_transform (hm : m ≤ n) (Q : W n → W m) (c : W m) :
    transform (rectDev n m Q) c = rectOffZero Q c := by
  have split (y : W m) : rectDev n m Q y * chr c y =
      rectHist Q y * chr c y - many (n - m) * chr c y := by
    unfold rectDev; exact Int.sub_mul ..
  unfold transform
  simp only [split, total_sub, total_scale]
  change transform (rectHist Q) c - many (n - m) * total m (chr c) = _
  rw [rect_by_hist]
  have unit := identity_spectrum m c
  change total m (chr c) = _ at unit
  rw [unit]
  by_cases z : c = zero m
  · subst c
    have hm' : many (n - m) * many m = many n := by
      rw [← many_add]; congr 1; omega
    simp [rectOffZero, rect_walsh_zero, hm']
  · simp [rectOffZero, z]

theorem rect_residual_energy (hm : m ≤ n) (Q : W n → W m) :
    total m (fun c => rectOffZero Q c * rectOffZero Q c) =
      many m * (collisions Q - many (2 * n - m)) := by
  have split (c : W m) : walsh Q c * walsh Q c =
      rectOffZero Q c * rectOffZero Q c + hits (zero m) c * (many n * many n) := by
    by_cases z : c = zero m
    · subst c; simp [rectOffZero, hits, rect_walsh_zero]
    · have nz : zero m ≠ c := fun e => z e.symm
      simp [rectOffZero, z, hits, nz]
  have p := parseval_collision_law Q
  simp only [split, total_add] at p
  have h0 : total m (fun c => hits (zero m) c * (many n * many n)) = many n * many n := by
    have hcomm : (fun c => hits (zero m) c * (many n * many n)) =
        (fun c => (many n * many n) * hits (zero m) c) := by
      funext c; exact Int.mul_comm ..
    rw [hcomm, total_scale, diagonal, Int.mul_one]
  rw [h0] at p
  have h2 : many m * many (2 * n - m) = many n * many n := by
    rw [← many_add, ← many_add]; congr 1; omega
  rw [Int.mul_sub, h2]
  omega

private theorem exists_nonzero_mode (hm : m ≤ n) (Q : W n → W m)
    (coll : many (2 * n - m) < collisions Q) : ∃ c, rectOffZero Q c ≠ 0 := by
  classical
  by_cases h : ∃ c, rectOffZero Q c ≠ 0
  · exact h
  · have allzero (c : W m) : rectOffZero Q c = 0 := by
      by_cases e : rectOffZero Q c = 0
      · exact e
      · exact False.elim (h ⟨c, e⟩)
    have E := rect_residual_energy hm Q
    simp only [allzero, Int.zero_mul, total_zero] at E
    have pos := Int.mul_pos (many_pos m) (show 0 < collisions Q - many (2 * n - m) by omega)
    omega

theorem rect_one_mode_bound (hm : m ≤ n) (Q : W n → W m) (r : Nat)
    (div : ∀ c, many r ∣ walsh Q c) (coll : many (2 * n - m) < collisions Q) :
    many (2 * r - m) ≤ collisions Q - many (2 * n - m) := by
  by_cases hmr : m ≤ 2 * r
  · obtain ⟨c, hc⟩ := exists_nonzero_mode hm Q coll
    have nz : c ≠ zero m := by intro z; subst c; simp [rectOffZero] at hc
    simp only [rectOffZero, nz, if_false] at hc
    obtain ⟨z, hz⟩ := div c
    have zne : z ≠ 0 := by intro e; rw [e, Int.mul_zero] at hz; exact hc hz
    have zsq : 1 ≤ z * z := by
      by_cases zp : 0 < z
      · have := Int.mul_pos zp zp; omega
      · have zm : 0 < -z := by omega
        have := Int.mul_pos zm zm; simp at this; omega
    have wsq : many r * many r ≤ rectOffZero Q c * rectOffZero Q c := by
      simp only [rectOffZero, nz, if_false, hz]
      have rearr : many r * z * (many r * z) = (many r * many r) * (z * z) := by ac_rfl
      rw [rearr]
      have mr2 : 0 ≤ many r * many r := Int.mul_nonneg (many_nonneg r) (many_nonneg r)
      simpa [Int.mul_one] using Int.mul_le_mul_of_nonneg_left zsq mr2
    have single : rectOffZero Q c * rectOffZero Q c ≤
        total m (fun a => rectOffZero Q a * rectOffZero Q a) := by
      have hle (a : W m) : hits c a * (rectOffZero Q c * rectOffZero Q c) ≤
          rectOffZero Q a * rectOffZero Q a := by
        by_cases e : c = a
        · subst a; simp [hits]
        · simp only [hits, e, if_false, Int.zero_mul]
          by_cases h0 : 0 ≤ rectOffZero Q a
          · exact Int.mul_nonneg h0 h0
          · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      have tm := total_mono m _ _ hle
      have hsum : total m (fun a => hits c a * (rectOffZero Q c * rectOffZero Q c)) =
          rectOffZero Q c * rectOffZero Q c := by
        have hcomm : (fun a => hits c a * (rectOffZero Q c * rectOffZero Q c)) =
            (fun a => (rectOffZero Q c * rectOffZero Q c) * hits c a) := by
          funext a; exact Int.mul_comm ..
        rw [hcomm, total_scale, diagonal, Int.mul_one]
      rw [hsum] at tm
      exact tm
    have E := rect_residual_energy hm Q
    have comb : many m * many (2 * r - m) ≤ many m * (collisions Q - many (2 * n - m)) := by
      have hm2 : many m * many (2 * r - m) = many r * many r := by
        rw [← many_add, ← many_add]; congr 1; omega
      rw [hm2, ← E]
      exact Int.le_trans wsq single
    exact many_mul_le_cancel (many_pos m) comb
  · have hzero : 2 * r - m = 0 := by omega
    rw [hzero]
    change (1 : Int) ≤ _
    omega

theorem rect_probe_bounds (hm : m ≤ n) (Q : W n → W m) (c : W m) (nz : c ≠ zero m) :
    -(collisions Q - many (2 * n - m)) ≤ walsh Q c ∧
      walsh Q c ≤ collisions Q - many (2 * n - m) := by
  have bounds (z : Int) : -(z * z) ≤ z ∧ z ≤ z * z := by
    have a := Int.mul_nonneg_of_nonpos_of_nonpos (a := z) (b := z - 1)
    have b := Int.mul_nonneg (a := z) (b := z - 1)
    have c' := Int.mul_nonneg_of_nonpos_of_nonpos (a := z) (b := z + 1)
    have d := Int.mul_nonneg (a := z) (b := z + 1)
    simp only [Int.mul_sub, Int.mul_add, Int.mul_one] at *
    by_cases h : z ≤ -1 <;> by_cases h' : 1 ≤ z <;> omega
  have e (y : W m) : -(rectDev n m Q y * rectDev n m Q y) ≤ rectDev n m Q y * chr c y ∧
      rectDev n m Q y * chr c y ≤ rectDev n m Q y * rectDev n m Q y := by
    have b := bounds (rectDev n m Q y)
    cases h : dot m c y <;> simp [chr, h, sign] <;> omega
  have l := total_mono m _ _ (fun y => (e y).1)
  have u := total_mono m _ _ (fun y => (e y).2)
  have t := rect_dev_transform hm Q c
  simp only [rectOffZero, nz, if_false, transform] at t
  simp only [twice_total, rect_excess hm, t] at l u
  exact ⟨l, u⟩

theorem rect_divisibility_bound (hm : m ≤ n) (Q : W n → W m) (r : Nat)
    (div : ∀ c, many r ∣ walsh Q c) (coll : many (2 * n - m) < collisions Q) :
    many r ≤ collisions Q - many (2 * n - m) := by
  obtain ⟨c, h⟩ := exists_nonzero_mode hm Q coll
  have nz : c ≠ zero m := by intro z; subst c; simp [rectOffZero] at h
  simp only [rectOffZero, nz, if_false] at h
  have b := rect_probe_bounds hm Q c nz
  obtain ⟨z, wp⟩ := div c
  have pp : 0 ≤ many r := many_nonneg r
  by_cases hz : z = 0
  · simp [hz] at wp; contradiction
  · by_cases pos : 1 ≤ z
    · have bd := Int.mul_le_mul_of_nonneg_left pos pp
      simp only [Int.mul_one] at bd; omega
    · have bd := Int.mul_le_mul_of_nonneg_left (show z ≤ -1 by omega) pp
      simp at bd; omega

theorem rect_quiet_bound (hm : m ≤ n) (Q : W n → W m) (d : Nat)
    (coll : many (2 * n - m) < collisions Q)
    (quiet : ∀ c, weight m c ≤ d → rectOffZero Q c = 0) :
    many (d + 1) ≤ collisions Q - many (2 * n - m) := by
  classical
  have live : ∃ y, rectDev n m Q y ≠ 0 := by
    by_cases e : ∃ y, rectDev n m Q y ≠ 0
    · exact e
    · have hz (y : W m) : rectDev n m Q y = 0 := by
        by_cases h : rectDev n m Q y = 0; exact h; exact False.elim (e ⟨y, h⟩)
      have sq := rect_excess hm Q
      simp only [hz, Int.zero_mul, total_zero] at sq
      omega
  have lower := quiet_support m (d + 1) (rectDev n m Q)
    (fun c h => (rect_dev_transform hm Q c).trans (quiet c (by omega))) live
  rw [← rect_excess hm]
  apply Int.le_trans lower
  apply total_mono
  intro y
  generalize rectDev n m Q y = z
  by_cases h : z = 0
  · simp [h]
  · simp only [h, if_false]
    by_cases pos : 0 < z
    · have e := Int.mul_pos pos pos; omega
    · have e := Int.mul_pos (show 0 < -z by omega) (show 0 < -z by omega)
      simp at e; omega

theorem rect_lower_bound (hm : m ≤ n) (hk : 0 < k) (possible : RectAttainable n m k d value) :
    many (rectExp n m k d) ≤ value := by
  obtain ⟨Q, deg, quiet, coll, rfl⟩ := possible
  have b1 := rect_one_mode_bound hm Q _ (walsh_dvd hk Q deg) coll
  have b2 := rect_divisibility_bound hm Q _ (walsh_dvd hk Q deg) coll
  have b3 := rect_quiet_bound hm Q d coll (fun c wt => by
    by_cases z : c = zero m
    · simp [rectOffZero, z]
    · simp [rectOffZero, z, quiet c z wt])
  unfold rectExp
  cases Nat.le_total (max (2 * ((n + k - 1) / k) - m) ((n + k - 1) / k)) (d + 1) with
  | inl h => simpa only [Nat.max_eq_right h] using b3
  | inr h =>
    rw [Nat.max_eq_left h]
    cases Nat.le_total (2 * ((n + k - 1) / k) - m) ((n + k - 1) / k) with
    | inl h' => simpa only [Nat.max_eq_right h'] using b2
    | inr h' => simpa only [Nat.max_eq_left h'] using b1

def dropControls (l q : Nat) : (r : Nat) → W (l + (q + r)) → W (l + q)
  | 0, w => w
  | r + 1, w => dropControls l q r w.2

def padControls (l q : Nat) : (r : Nat) → W (l + q) → W (l + (q + r))
  | 0, c => c
  | r + 1, c => (false, padControls l q r c)

def padWord (q : Nat) : (r : Nat) → W q → W (q + r)
  | 0, a => a
  | r + 1, a => (false, padWord q r a)

private theorem dot_padControls (l q r : Nat) (c : W (l + q)) (w : W (l + (q + r))) :
    dot (l + (q + r)) (padControls l q r c) w = dot (l + q) c (dropControls l q r w) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases w with ⟨b, w⟩
    change xor (false && b) (dot (l + (q + r)) (padControls l q r c) w) = _
    simp [ih, dropControls]

private theorem degree_dropControls (l q r : Nat) (F : W n → W (l + (q + r)))
    (hf : MapDegree k (l + (q + r)) F) :
    MapDegree k (l + q) (fun x => dropControls l q r (F x)) := by
  induction r with
  | zero => exact hf
  | succ r ih => exact ih (fun x => (F x).2) hf.2

private theorem walsh_dropControls (l q r : Nat) (F : W n → W (l + (q + r))) (c : W (l + q)) :
    walsh (fun x => dropControls l q r (F x)) c = walsh F (padControls l q r c) := by
  unfold walsh
  apply congrArg (total n); funext x
  simp [chr, dot_padControls]

private theorem padControls_join (l q r : Nat) (a : W q) (b : W l) :
    padControls l q r (join l q a b) = join l (q + r) (padWord q r a) b := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (false, padControls l q r (join l q a b)) = (false, join l (q + r) (padWord q r a) b)
    exact congrArg (false, ·) ih

private theorem padWord_eq_zero (q r : Nat) (a : W q) :
    padWord q r a = zero (q + r) ↔ a = zero q := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change ((false, padWord q r a) : W (q + r + 1)) = (false, zero (q + r)) ↔ a = zero q
    simp [ih]

private theorem dot_padWord_ones (q r : Nat) (a : W q) :
    dot (q + r) (padWord q r a) (ones (q + r)) = dot q a (ones q) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change xor (false && true) (dot (q + r) (padWord q r a) (ones (q + r))) = dot q a (ones q)
    simpa using ih

private theorem chr_sq_one (a b : W q) : chr a b * chr a b = 1 := by
  cases h : dot q a b <;> simp [chr, h, sign]

private theorem projRing_walsh (width h q r : Nat) (cap : q + r ≤ (h + 1) * width)
    (a : W q) (b : W (h + 1)) :
    let Q := fun x => dropControls (h + 1) q r (ring width h (q + r) x)
    walsh Q (join (h + 1) q a b) =
      (if a = zero q ∧ b = zero (h + 1) then many (h + 1) * many (q + r) else 0) +
      chr a (ones q) * (many (h + 1) * hits (ones (h + 1)) b) := by
  intro Q
  rw [walsh_dropControls, padControls_join, ring_walsh width h (q + r) cap]
  simp only [padWord_eq_zero, chr, dot_padWord_ones]

private theorem projRing_excess (width h q r : Nat) (cap : q + r ≤ (h + 1) * width) :
    let Q := fun x => dropControls (h + 1) q r (ring width h (q + r) x)
    collisions Q - many (2 * ((h + 1) + (q + r)) - ((h + 1) + q)) = many (h + 1) := by
  intro Q
  have p := parseval_collision_law Q
  rw [join_total (h + 1) q] at p
  have one_ne_zero : ones (h + 1) ≠ zero (h + 1) := by
    intro e
    have := congrArg (weight (h + 1)) e
    simp [ones_weight, weight_zero] at this
  have sq_term (a : W q) (b : W (h + 1)) :
      walsh Q (join (h + 1) q a b) * walsh Q (join (h + 1) q a b) =
      (if a = zero q ∧ b = zero (h + 1) then (many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r)) else 0) +
      (many (h + 1) * many (h + 1)) * hits (ones (h + 1)) b := by
    rw [projRing_walsh width h q r cap a b]
    by_cases h1 : a = zero q ∧ b = zero (h + 1)
    · rcases h1 with ⟨rfl, rfl⟩
      simp [hits, one_ne_zero]
    · simp only [h1, if_false, Int.zero_add]
      have c1 : chr a (ones q) * chr a (ones q) = 1 := chr_sq_one a (ones q)
      have hsq : hits (ones (h + 1)) b * hits (ones (h + 1)) b = hits (ones (h + 1)) b := by
        by_cases e : ones (h + 1) = b <;> simp [hits, e]
      calc (chr a (ones q) * (many (h + 1) * hits (ones (h + 1)) b)) *
           (chr a (ones q) * (many (h + 1) * hits (ones (h + 1)) b))
        _ = (chr a (ones q) * chr a (ones q)) *
            ((many (h + 1) * many (h + 1)) * (hits (ones (h + 1)) b * hits (ones (h + 1)) b)) := by ac_rfl
        _ = (many (h + 1) * many (h + 1)) * hits (ones (h + 1)) b := by rw [c1, hsq, Int.one_mul]
  have sum1 : total q (fun a => total (h + 1) (fun b =>
      if a = zero q ∧ b = zero (h + 1) then (many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r)) else 0)) =
      (many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r)) := by
    have rw_inner (a : W q) :
        total (h + 1) (fun b =>
          if a = zero q ∧ b = zero (h + 1) then (many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r)) else 0) =
        hits (zero q) a * ((many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r))) := by
      by_cases ha : a = zero q
      · subst a
        have eqf (b : W (h + 1)) :
            (if zero q = zero q ∧ b = zero (h + 1) then (many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r)) else 0) =
            ((many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r))) * hits (zero (h + 1)) b := by
          by_cases hb : b = zero (h + 1)
          · subst b; simp [hits]
          · have hnb : zero (h + 1) ≠ b := fun e => hb e.symm
            simp [hits, hb, hnb]
        rw [show (fun b => if zero q = zero q ∧ b = zero (h + 1) then
              (many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r)) else 0) =
            (fun b => ((many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r))) * hits (zero (h + 1)) b)
          from funext eqf]
        rw [total_scale, diagonal, Int.mul_one]
        simp [hits]
      · have hna : zero q ≠ a := fun e => ha e.symm
        simp [ha, hna, hits, total_zero]
    simp only [rw_inner]
    have hcomm : (fun a => hits (zero q) a * ((many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r)))) =
        (fun a => ((many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r))) * hits (zero q) a) := by
      funext a; exact Int.mul_comm ..
    rw [hcomm, total_scale, diagonal, Int.mul_one]
  have sum2 : total q (fun _ => total (h + 1) (fun b =>
      (many (h + 1) * many (h + 1)) * hits (ones (h + 1)) b)) =
      many ((h + 1) + q) * many (h + 1) := by
    simp only [total_scale, diagonal, Int.mul_one, total_const]
    rw [← many_add, ← many_add, ← many_add]
    congr 1; omega
  simp only [sq_term, total_add] at p
  rw [sum1, sum2] at p
  have hbase : (many (h + 1) * many (q + r)) * (many (h + 1) * many (q + r)) =
      many ((h + 1) + q) * many (2 * ((h + 1) + (q + r)) - ((h + 1) + q)) := by
    have hstep : many (h + 1) * many (q + r) = many ((h + 1) + (q + r)) := (many_add _ _).symm
    rw [hstep, ← many_add, ← many_add]; congr 1; omega
  rw [hbase, ← Int.mul_add] at p
  have hcol := many_mul_cancel (many_pos ((h + 1) + q)) p.symm
  omega

private theorem projRing_quiet (width h q r d : Nat) (cap : q + r ≤ (h + 1) * width)
    (low : d < h + 1) :
    RectSilentThrough d (fun x => dropControls (h + 1) q r (ring width h (q + r) x)) := by
  intro c nz wt
  obtain ⟨a, b, rfl⟩ : ∃ a b, join (h + 1) q a b = c := ⟨_, _, join_split _ _ c⟩
  rw [join_weight] at wt
  have ne : ones (h + 1) ≠ b := by rintro rfl; rw [ones_weight] at wt; omega
  have hnz : ¬(a = zero q ∧ b = zero (h + 1)) := by
    rintro ⟨rfl, rfl⟩; exact nz (join_zero _ _)
  rw [projRing_walsh width h q r cap a b]
  simp [hnz, hits, ne]

def dropFront (l : Nat) : (s : Nat) → W (l + s) → W l
  | 0, w => w
  | s + 1, w => dropFront l s w.2

def padFront (l : Nat) : (s : Nat) → W l → W (l + s)
  | 0, c => c
  | s + 1, c => (false, padFront l s c)

private theorem dot_padFront (l s : Nat) (c : W l) (w : W (l + s)) :
    dot (l + s) (padFront l s c) w = dot l c (dropFront l s w) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rcases w with ⟨b, w⟩
    change xor (false && b) (dot (l + s) (padFront l s c) w) = _
    simp [ih, dropFront]

private theorem degree_dropFront (l s : Nat) (F : W n → W (l + s))
    (hf : MapDegree k (l + s) F) :
    MapDegree k l (fun x => dropFront l s (F x)) := by
  induction s with
  | zero => exact hf
  | succ s ih => exact ih (fun x => (F x).2) hf.2

private theorem padFront_eq_join (l s : Nat) (b : W l) :
    padFront l s b = join l s (zero s) b := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change (false, padFront l s b) = (false, join l s (zero s) b)
    exact congrArg (false, ·) ih

def foldHead (m' : Nat) : (t : Nat) → W ((m' + t) + 1) → W (m' + 1)
  | 0, y => y
  | t + 1, (b, y) =>
    let z := foldHead m' t y
    (xor b z.1, z.2)

def repFront (m' : Nat) : (t : Nat) → W (m' + 1) → W ((m' + t) + 1)
  | 0, c => c
  | t + 1, c => (c.1, repFront m' t c)

private theorem dot_repFront (m' t : Nat) (c : W (m' + 1)) (y : W ((m' + t) + 1)) :
    dot ((m' + t) + 1) (repFront m' t c) y = dot (m' + 1) c (foldHead m' t y) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rcases y with ⟨b, y⟩
    rcases c with ⟨c0, cr⟩
    change xor (c0 && b) (dot ((m' + t) + 1) (repFront m' t (c0, cr)) y) =
      dot (m' + 1) (c0, cr) (xor b (foldHead m' t y).1, (foldHead m' t y).2)
    rw [ih]
    rcases foldHead m' t y with ⟨z0, zr⟩
    change xor (c0 && b) (xor (c0 && z0) (dot m' cr zr)) = xor (c0 && xor b z0) (dot m' cr zr)
    cases c0 <;> cases b <;> cases z0 <;> simp

private theorem degree_foldHead (m' t : Nat) (F : W n → W ((m' + t) + 1))
    (hf : MapDegree k ((m' + t) + 1) F) :
    MapDegree k (m' + 1) (fun x => foldHead m' t (F x)) := by
  induction t with
  | zero => exact hf
  | succ t ih =>
    have tail := ih (fun x => (F x).2) hf.2
    exact ⟨degree_xor hf.1 tail.1, tail.2⟩

private theorem repFront_eq_zero (m' t : Nat) (c : W (m' + 1)) :
    repFront m' t c = zero ((m' + t) + 1) ↔ c = zero (m' + 1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rcases c with ⟨c0, cr⟩
    change ((c0, repFront m' t (c0, cr)) : W (((m' + t) + 1) + 1)) = (false, zero ((m' + t) + 1)) ↔
      ((c0, cr) : W (m' + 1)) = (false, zero m')
    rw [Prod.mk.injEq, ih]
    cases c0
    · simp only [true_and]; rfl
    · simp [zero]

private theorem ones_eq_repFront (m' t : Nat) (c : W (m' + 1)) :
    ones ((m' + t) + 1) = repFront m' t c ↔ ones (m' + 1) = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rcases c with ⟨c0, cr⟩
    change ((true, ones ((m' + t) + 1)) : W (((m' + t) + 1) + 1)) = (c0, repFront m' t (c0, cr)) ↔
      ((true, ones m') : W (m' + 1)) = (c0, cr)
    rw [Prod.mk.injEq, ih]
    cases c0
    · simp [ones]
    · simp only [true_and]; rfl

private theorem foldRing_walsh (width m' t s : Nat) (cap : s ≤ ((m' + t) + 1) * width)
    (c : W (m' + 1)) :
    let Q := fun x : W (((m' + t) + 1) + s) =>
      foldHead m' t (dropFront ((m' + t) + 1) s (ring width (m' + t) s x))
    walsh Q c =
      (if c = zero (m' + 1) then many ((m' + t) + 1) * many s else 0) +
      many ((m' + t) + 1) * hits (ones (m' + 1)) c := by
  intro Q
  have hw : walsh Q c =
      walsh (ring width (m' + t) s) (join ((m' + t) + 1) s (zero s) (repFront m' t c)) := by
    unfold walsh
    apply congrArg (total (((m' + t) + 1) + s)); funext x
    change sign (dot (m' + 1) c (foldHead m' t (dropFront ((m' + t) + 1) s (ring width (m' + t) s x)))) =
      sign (dot (((m' + t) + 1) + s) (join ((m' + t) + 1) s (zero s) (repFront m' t c))
        (ring width (m' + t) s x))
    rw [← dot_repFront, ← dot_padFront, padFront_eq_join]
  rw [hw, ring_walsh width (m' + t) s cap (zero s) (repFront m' t c)]
  have hchr : chr (zero s) (ones s) = 1 := by simp [chr, dot_zero, sign]
  have ho : hits (ones ((m' + t) + 1)) (repFront m' t c) = hits (ones (m' + 1)) c := by
    simp [hits, ones_eq_repFront]
  simp [hchr, repFront_eq_zero, ho]

private theorem foldRing_excess (width m' t s : Nat) (cap : s ≤ ((m' + t) + 1) * width) :
    let Q := fun x : W (((m' + t) + 1) + s) =>
      foldHead m' t (dropFront ((m' + t) + 1) s (ring width (m' + t) s x))
    collisions Q - many (2 * (((m' + t) + 1) + s) - (m' + 1)) =
      many (2 * ((m' + t) + 1) - (m' + 1)) := by
  intro Q
  have p := parseval_collision_law Q
  have one_ne_zero : ones (m' + 1) ≠ zero (m' + 1) := by
    intro e
    have := congrArg (weight (m' + 1)) e
    simp [ones_weight, weight_zero] at this
  have sq_term (c : W (m' + 1)) :
      walsh Q c * walsh Q c =
      hits (zero (m' + 1)) c * ((many ((m' + t) + 1) * many s) * (many ((m' + t) + 1) * many s)) +
      hits (ones (m' + 1)) c * (many ((m' + t) + 1) * many ((m' + t) + 1)) := by
    rw [foldRing_walsh width m' t s cap c]
    by_cases hz : c = zero (m' + 1)
    · subst c; simp [hits, one_ne_zero]
    · have hnz : zero (m' + 1) ≠ c := fun e => hz e.symm
      by_cases ho : ones (m' + 1) = c
      · subst c; simp [hits, hz, hnz]
      · simp [hits, hz, hnz, ho]
  simp only [sq_term, total_add] at p
  have hsum (u : W (m' + 1)) (v : Int) : total (m' + 1) (fun c => hits u c * v) = v := by
    have hc : (fun c => hits u c * v) = (fun c => v * hits u c) := by funext c; exact Int.mul_comm ..
    rw [hc, total_scale, diagonal, Int.mul_one]
  rw [hsum, hsum] at p
  have h1 : (many ((m' + t) + 1) * many s) * (many ((m' + t) + 1) * many s) =
      many (m' + 1) * many (2 * (((m' + t) + 1) + s) - (m' + 1)) := by
    have hstep : many ((m' + t) + 1) * many s = many (((m' + t) + 1) + s) := (many_add _ _).symm
    rw [hstep, ← many_add, ← many_add]; congr 1; omega
  have h2 : many ((m' + t) + 1) * many ((m' + t) + 1) =
      many (m' + 1) * many (2 * ((m' + t) + 1) - (m' + 1)) := by
    rw [← many_add, ← many_add]; congr 1; omega
  rw [h1, h2, ← Int.mul_add] at p
  have hcol := many_mul_cancel (many_pos (m' + 1)) p.symm
  omega

private theorem foldRing_quiet (width m' t s d : Nat) (cap : s ≤ ((m' + t) + 1) * width)
    (hd : d < m' + 1) :
    RectSilentThrough d (fun x : W (((m' + t) + 1) + s) =>
      foldHead m' t (dropFront ((m' + t) + 1) s (ring width (m' + t) s x))) := by
  intro c nz wt
  rw [foldRing_walsh width m' t s cap c]
  have ne : ones (m' + 1) ≠ c := by
    rintro rfl; rw [ones_weight] at wt; omega
  simp [nz, hits, ne]

private theorem ceil_bounds (n k : Nat) (hn : 1 ≤ n) (hk : 0 < k) :
    1 ≤ (n + k - 1) / k ∧ (n + k - 1) / k ≤ n ∧
      n - (n + k - 1) / k ≤ ((n + k - 1) / k) * (k - 1) := by
  have hpos : 1 ≤ (n + k - 1) / k :=
    (Nat.le_div_iff_mul_le hk).mpr (by omega)
  have hle : (n + k - 1) / k ≤ n := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hk).mpr
    have hnk : n ≤ n * k := by simpa using Nat.mul_le_mul_left n hk
    rw [Nat.succ_mul]
    omega
  have hcap : n ≤ ((n + k - 1) / k) * k := by
    have rem := Nat.mod_lt (n + k - 1) hk
    have eq := Nat.div_add_mod (n + k - 1) k
    rw [Nat.mul_comm k] at eq
    omega
  refine ⟨hpos, hle, ?_⟩
  rw [Nat.mul_sub_one]
  omega

private theorem shallow_params (n m k d : Nat) (hm : m ≤ n) (hk : 0 < k) (hd : d < m)
    (hregime : (n + k - 1) / k ≤ m) :
    ∃ h q r : Nat,
      (h + 1) + q = m ∧ (h + 1) + (q + r) = n ∧
      h + 1 = rectExp n m k d ∧
      q + r ≤ (h + 1) * (k - 1) ∧ d < h + 1 := by
  obtain ⟨hR1, _, hRcap⟩ := ceil_bounds n k (by omega) hk
  let L := max ((n + k - 1) / k) (d + 1)
  have hL_eq : L = rectExp n m k d := by
    unfold rectExp
    have h2 : 2 * ((n + k - 1) / k) - m ≤ (n + k - 1) / k := by omega
    rw [Nat.max_eq_right h2]
  have hRL : (n + k - 1) / k ≤ L := Nat.le_max_left _ _
  have hLm : L ≤ m := by dsimp [L]; omega
  obtain ⟨h, hl⟩ : ∃ h, L = h + 1 := ⟨L - 1, by dsimp [L]; omega⟩
  refine ⟨h, m - L, n - m, by omega, by omega, by rw [← hl, hL_eq], ?_, by dsimp [L] at hl; omega⟩
  have hmul : ((n + k - 1) / k) * (k - 1) ≤ (h + 1) * (k - 1) :=
    Nat.mul_le_mul_right (k - 1) (by omega)
  omega

private theorem deep_params (n m k d : Nat) (hm : m ≤ n) (hk : 0 < k) (hd : d < m)
    (hregime : m < (n + k - 1) / k) :
    ∃ m' t s : Nat,
      m' + 1 = m ∧ ((m' + t) + 1) + s = n ∧
      2 * ((m' + t) + 1) - (m' + 1) = rectExp n m k d ∧
      s ≤ ((m' + t) + 1) * (k - 1) ∧ d < m' + 1 := by
  obtain ⟨_, hRn, hRcap⟩ := ceil_bounds n k (by omega) hk
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  let t := (n + k - 1) / k - m
  let s := n - (n + k - 1) / k
  have hR_eq : (m' + t) + 1 = (n + k - 1) / k := by dsimp [t]; omega
  have hExp : rectExp n m k d = 2 * ((n + k - 1) / k) - m := by
    unfold rectExp
    have h1 : (n + k - 1) / k ≤ 2 * ((n + k - 1) / k) - m := by omega
    have h2 : d + 1 ≤ 2 * ((n + k - 1) / k) - m := by omega
    rw [Nat.max_eq_left h1, Nat.max_eq_left h2]
  refine ⟨m', t, s, hm'.symm, by dsimp [s]; omega, ?_, ?_, by omega⟩
  · rw [hExp, hR_eq, hm']
  · rw [hR_eq]; exact hRcap

theorem rect_attainment (hm : m ≤ n) (hk : 0 < k) (hd : d < m) :
    RectAttainable n m k d (many (rectExp n m k d)) := by
  by_cases hregime : (n + k - 1) / k ≤ m
  · obtain ⟨h, q, r, hm_eq, hn_eq, hexp, hcap, hlow⟩ := shallow_params n m k d hm hk hd hregime
    subst hm_eq
    subst hn_eq
    let Q := fun x => dropControls (h + 1) q r (ring (k - 1) h (q + r) x)
    have hdeg : MapDegree k ((h + 1) + q) Q := by
      apply degree_dropControls
      simpa only [show k - 1 + 1 = k by omega] using grouped_degree (k - 1) h (q + r)
    have hq : RectSilentThrough d Q := projRing_quiet (k - 1) h q r d hcap hlow
    have hex : collisions Q - many (2 * ((h + 1) + (q + r)) - ((h + 1) + q)) = many (h + 1) :=
      projRing_excess (k - 1) h q r hcap
    have hpos := many_pos (h + 1)
    refine ⟨Q, hdeg, hq, by omega, hex.trans (congrArg many hexp)⟩
  · obtain ⟨m', t, s, hm_eq, hn_eq, hexp, hcap, hd'⟩ :=
      deep_params n m k d hm hk hd (by omega)
    subst hm_eq
    subst hn_eq
    let Q := fun x : W (((m' + t) + 1) + s) =>
      foldHead m' t (dropFront ((m' + t) + 1) s (ring (k - 1) (m' + t) s x))
    have hdeg : MapDegree k (m' + 1) Q := by
      apply degree_foldHead
      apply degree_dropFront
      simpa only [show k - 1 + 1 = k by omega] using grouped_degree (k - 1) (m' + t) s
    have hq : RectSilentThrough d Q := foldRing_quiet (k - 1) m' t s d hcap hd'
    have hex : collisions Q - many (2 * (((m' + t) + 1) + s) - (m' + 1)) =
        many (2 * ((m' + t) + 1) - (m' + 1)) := foldRing_excess (k - 1) m' t s hcap
    have hpos := many_pos (2 * ((m' + t) + 1) - (m' + 1))
    refine ⟨Q, hdeg, hq, by omega, hex.trans (congrArg many hexp)⟩

theorem rect_exact_minimum (n m k d : Nat) (hm : m ≤ n) (hk : 0 < k) (hd : d < m) :
    RectAttainable n m k d (many (rectExp n m k d)) ∧
    ∀ value, RectAttainable n m k d value → many (rectExp n m k d) ≤ value :=
  ⟨rect_attainment hm hk hd, fun _ => rect_lower_bound hm hk⟩

#print axioms rect_lower_bound
#print axioms rect_attainment
#print axioms rect_exact_minimum
end RectangularCollisionMinimum
