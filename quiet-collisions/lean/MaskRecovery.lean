import CollisionLaw

namespace MaskRecovery
open FrozenShells CandyKnots FreezeMovies CollisionLaw

theorem add_zero_left (n : Nat) (w : W n) : add n (zero n) w = w := by
  induction n with
  | zero => cases w; rfl
  | succ n ih => rcases w with ⟨b,w⟩; simp [add,zero,ih]

theorem add_self (n : Nat) (w : W n) : add n w w = zero n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [add,zero,ih]

theorem add_comm (n : Nat) (x y : W n) : add n x y = add n y x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [add]; rw [Bool.xor_comm,ih]

theorem dot_comm (n : Nat) (x y : W n) : dot n x y = dot n y x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dot]; rw [Bool.and_comm,ih]

theorem dot_right (n : Nat) (c a b : W n) :
    dot n c (add n a b) = xor (dot n c a) (dot n c b) := by
  rw [dot_comm, dot_add, dot_comm n a, dot_comm n b]

theorem sum_shift (n : Nat) (d : W n) (f : W n → Int) :
    total n (fun x => f (add n d x)) = total n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases d with ⟨b,d⟩
    have term (v : Bool) := ih d (fun x => f (v,x))
    cases b <;> simp [total,add,term,Int.add_comm]

/-- An input translation producing the same output difference everywhere. -/
def shift (Q : W n → W r) (d : W n) (v : W r) :=
  ∀ x, Q (add n d x) = add r v (Q x)

theorem shift_kills (Q : W n → W r) {d v} (h : shift Q d v)
    (c : W r) (odd : dot r c v = true) : walsh Q c = 0 := by
  have e := sum_shift n d (fun x => chr c (Q x))
  have term (x : W n) : chr c (Q (add n d x)) = -chr c (Q x) := by
    rw [h x]
    unfold chr
    rw [dot_right,odd,signMul]
    cases dot r c (Q x) <;> decide
  simp only [term,twice_total] at e
  unfold walsh
  omega

/-- Coordinates of a linear form from its values on the unit vectors. -/
def readMask : (n : Nat) → (W n → Bool) → W n
  | 0, _ => ()
  | n+1, f => (f (true,zero n),readMask n (fun w => f (false,w)))

def additive (f : W n → W r) := ∀ x y, f (add n x y) = add r (f x) (f y)

theorem readMask_spec (n : Nat) (f : W n → Bool)
    (lin : ∀ x y, f (add n x y) = xor (f x) (f y)) (x : W n) :
    dot n (readMask n f) x = f x := by
  induction n with
  | zero => cases x; have e := lin () (); cases h : f () <;> simp_all [add,dot]
  | succ n ih =>
    rcases x with ⟨b,x⟩
    have rest := ih (fun w => f (false,w)) (fun u v => lin (false,u) (false,v)) x
    cases b
    · simpa [dot,readMask] using rest
    · have split := lin (true,zero n) (false,x)
      simpa [dot,readMask,rest,add,add_zero_left] using split.symm

def pullMask (V : W n → W r) (c : W r) := readMask n (fun x => dot r c (V x))

theorem pull_eval (V : W n → W r) (h : additive V) (c : W r) (x : W n) :
    dot n (pullMask V c) x = dot r c (V x) :=
  readMask_spec n _ (fun a b => by rw [h,dot_right]) x

theorem select (n : Nat) (a : W n) (f : W n → Int) :
    total n (fun x => hits a x * f x) = f a := by
  induction n with
  | zero => cases a; simp [total,hits,W]
  | succ n ih =>
    rcases a with ⟨a,t⟩
    cases a <;> simp [total,hit_cons,total_zero,ih]

/-- Reindexing an exhaustive sum by a bijection leaves it unchanged. -/
theorem reindex (U I : W n → W n) (left : ∀ x, I (U x) = x) (right : ∀ x, U (I x) = x)
    (f : W n → Int) : total n (fun x => f (U x)) = total n f := by
  have atPoint (x y : W n) : hits (U x) y = hits (I y) x := by
    have eqv : U x = y ↔ I y = x := ⟨fun h => h ▸ left x, fun h => h ▸ right y⟩
    simp only [hits,eqv]
  calc
    _ = total n (fun x => total n (fun y => hits (U x) y * f y)) := by simp [select]
    _ = total n (fun y => total n (fun x => hits (U x) y * f y)) := swap ..
    _ = total n f := by
      apply congrArg (total n)
      funext y
      simp only [atPoint,Int.mul_comm _ (f y),total_scale,diagonal,Int.mul_one]

theorem mixed_walsh (F : W n → W r) (U I : W n → W n)
    (left : ∀ x, I (U x) = x) (right : ∀ x, U (I x) = x)
    (V : W r → W r) (lin : additive V) (c : W r) :
    walsh (fun x => V (F (U x))) c = walsh F (pullMask V c) := by
  unfold walsh chr
  simp only [pull_eval V lin]
  exact reindex U I left right (fun x => sign (dot r c (V (F x))))

/-- The signature of a nonzero cross term in the hidden pair. -/
def firstAxis (k : Nat) : W (k+2) := (true,false,zero k)
def offset (k : Nat) : W (k+2) := (true,true,zero k)
def tailDir (k : Nat) (u : W k) : W (k+2) := (false,false,u)

theorem dot_detects (n : Nat) (c : W n) : (∀ u, dot n c u = false) ↔ c = zero n := by
  constructor
  · intro h
    induction n with
    | zero => cases c; rfl
    | succ n ih =>
      have head := h (true,zero n)
      have tail := ih c.2 (fun w => by simpa [dot] using h (false,w))
      exact Prod.ext (by simpa [dot,dot_zero_right] using head) tail
  · rintro rfl; exact dot_zero n

/-- Linear tests characterizing the one distinguishing mask in mixed coordinates. -/
theorem hidden_mask (k : Nat) (U I V : W (k+2) → W (k+2))
    (left : ∀ x, I (U x) = x) (right : ∀ x, U (I x) = x) (lin : additive V)
    (c : W (k+2)) :
    walsh (fun x => V (pad k base (U x))) c ≠ walsh (fun x => V (pad k shifted (U x))) c ↔
      dot (k+2) c (V (firstAxis k)) = true ∧ dot (k+2) c (V (offset k)) = true ∧
      ∀ u, dot (k+2) c (V (tailDir k u)) = false := by
  rw [mixed_walsh _ U I left right V lin, mixed_walsh _ U I left right V lin,
      one_distinguishing_mask]
  simp only [← pull_eval V lin]
  rcases pullMask V c with ⟨a,b,t⟩
  simp only [firstAxis,offset,tailDir,dot,dot_zero_right,Bool.and_true,Bool.and_false,
    Bool.xor_false,Bool.false_xor,dot_detects,Prod.mk.injEq]
  have eqv : ((a,b,t) : W (k+2)) = (true,false,zero k) ↔ a = true ∧ b = false ∧ t = zero k :=
    ⟨fun h => ⟨congrArg Prod.fst h, congrArg (fun w => w.2.1) h,
      congrArg (fun w => w.2.2) h⟩, fun ⟨ha,hb,ht⟩ => by subst_vars; rfl⟩
  rw [eqv]
  cases a <;> cases b <;> simp

def bend (Q : W n → W r) (x y : W n) : W r :=
  add r (add r (Q (zero n)) (Q x)) (add r (Q y) (Q (add n x y)))

theorem zero_image (F : W n → W r) (lin : additive F) : F (zero n) = zero r := by
  have eq := lin (zero n) (zero n)
  simpa only [add_self] using eq

def mix (F : W n → W r) (U : W m → W n) (V : W r → W s) (x : W m) := V (F (U x))

theorem bend_mix (F : W n → W r) (U : W m → W n) (V : W r → W s)
    (hU : additive U) (hV : additive V) (x y : W m) :
    bend (mix F U V) x y = V (bend F (U x) (U y)) := by
  simp only [bend,mix,zero_image U hU,hU _ _,hV _ _]

theorem xor_four (k : Nat) (u v : W k) :
    add k (add k (zero k) u) (add k v (add k u v)) = zero k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases u with ⟨a,u⟩
    rcases v with ⟨b,v⟩
    cases a <;> cases b <;> simp only [add,zero,ih] <;> rfl

theorem base_bend (k : Nat) (x y : W (k+2)) :
    bend (pad k base) x y = zero (k+2) ∨ bend (pad k base) x y = firstAxis k := by
  rcases x with ⟨a,b,u⟩
  rcases y with ⟨c,d,v⟩
  have tail := xor_four k u v
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [bend,pad,base,zero,add,firstAxis,tail]

theorem add_shuffle (n : Nat) (v a x : W n) :
    add n a (add n v x) = add n v (add n a x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [add,ih,Bool.xor_left_comm v.1]

theorem translate_shift (Q : W n → W r) (t : W r) {d v} (h : shift Q d v) :
    shift (fun x => add r t (Q x)) d v := fun x => by
  dsimp only; rw [h x,add_shuffle]

theorem tail_shift (k : Nat) (u : W k) : shift (pad k base) (tailDir k u) (tailDir k u) := by
  rintro ⟨a,b,x⟩
  simp [tailDir,pad,base,add]

theorem shift_mix (F : W n → W r) (U : W m → W n) (V : W r → W s)
    (hU : additive U) (hV : additive V) (d : W m) {v} (h : shift F (U d) v) :
    shift (mix F U V) d (V v) := by
  intro x
  simp only [mix,hU _ _,h (U x),hV _ _]

theorem pad_offset (k : Nat) (x : W (k+2)) :
    pad k shifted x = add (k+2) (offset k) (pad k base x) := by
  rcases x with ⟨a,b,u⟩
  simp [pad,shifted,base,offset,add,add_zero_left]

/-- Every quantity on the right is observable from the pair of systems.
    Any nonzero second difference works. Constant derivatives give homogeneous
    linear equations for the mask. The offset and the cross term give two more. -/
theorem recover_from_equations (k : Nat) (U I V : W (k+2) → W (k+2))
    (left : ∀ x, I (U x) = x) (right : ∀ x, U (I x) = x) (hU : additive U) (hV : additive V)
    (p q c : W (k+2))
    (hb : bend (mix (pad k base) U V) p q ≠ zero (k+2)) :
    let A := mix (pad k base) U V
    let B := mix (pad k shifted) U V
    walsh A c ≠ walsh B c ↔
      dot (k+2) c (bend A p q) = true ∧
      dot (k+2) c (add (k+2) (A (zero _)) (B (zero _))) = true ∧
      ∀ d v, shift A d v → dot (k+2) c v = false := by
  dsimp only
  let A := mix (pad k base) U V
  let B := mix (pad k shifted) U V
  have bend_eq : bend A p q = V (firstAxis k) := by
    rw [bend_mix _ _ _ hU hV]
    rcases base_bend k (U p) (U q) with h | h
    · exact False.elim (hb (by rw [bend_mix _ _ _ hU hV,h,zero_image V hV]))
    · rw [h]
  have trans : B = fun x => add (k+2) (V (offset k)) (A x) := by
    funext x
    simp only [A,B,mix,pad_offset,hV _ _]
  have a0 : A (zero _) = zero _ := by
    have f0 : pad k base (zero (k+2)) = zero (k+2) := rfl
    simp only [A,mix,zero_image U hU,f0,zero_image V hV]
  have difference : add (k+2) (A (zero _)) (B (zero _)) = V (offset k) := by
    simp only [trans,a0,add_zero_left]; rw [add_comm,add_zero_left]
  change walsh A c ≠ walsh B c ↔ _
  rw [bend_eq,difference]
  have hidden := hidden_mask k U I V left right hV c
  constructor
  · intro distinct
    obtain ⟨cross,off,_⟩ := hidden.mp distinct
    refine ⟨cross,off,fun d v h => ?_⟩
    cases he : dot (k+2) c v with
    | false => rfl
    | true =>
      have za := shift_kills A h c he
      have zb : walsh B c = 0 := by
        rw [trans]; exact shift_kills _ (translate_shift A _ h) c he
      exact False.elim (distinct (za.trans zb.symm))
  · rintro ⟨cross,off,flat⟩
    apply hidden.mpr
    refine ⟨cross,off,fun u => ?_⟩
    apply flat (I (tailDir k u))
    apply shift_mix _ _ _ hU hV
    rw [right]
    exact tail_shift k u

theorem dot_ext (n : Nat) (a b : W n) (h : ∀ x, dot n a x = dot n b x) : a = b := by
  induction n with
  | zero => cases a; cases b; rfl
  | succ n ih =>
    apply Prod.ext
    · simpa [dot,dot_zero_right] using h (true,zero n)
    · apply ih
      intro x
      simpa [dot] using h (false,x)

theorem pull_inverse (V J : W n → W n) (lv : ∀ x, J (V x) = x) (rv : ∀ x, V (J x) = x)
    (hv : additive V) (hj : additive J) (c mask : W n) :
    pullMask V c = mask ↔ c = pullMask J mask := by
  constructor
  · intro h
    apply dot_ext; intro y
    have e := pull_eval V hv c (J y)
    rw [h,rv] at e
    rw [pull_eval J hj,e]
  · rintro rfl
    apply dot_ext; intro y
    rw [pull_eval V hv,pull_eval J hj,lv]

/-- Invertible output coordinates give exactly one solution to the mask test. -/
theorem unique_hidden_mask (k : Nat) (U I V J : W (k+2) → W (k+2))
    (lu : ∀ x, I (U x) = x) (ru : ∀ x, U (I x) = x)
    (lv : ∀ x, J (V x) = x) (rv : ∀ x, V (J x) = x) (hv : additive V) (hj : additive J)
    (c : W (k+2)) :
    walsh (mix (pad k base) U V) c ≠ walsh (mix (pad k shifted) U V) c ↔
      c = pullMask J (firstAxis k) := by
  unfold mix
  rw [mixed_walsh _ U I lu ru V hv,mixed_walsh _ U I lu ru V hv,one_distinguishing_mask]
  exact pull_inverse V J lv rv hv hj c (firstAxis k)

/-- For any padded two-bit map in hidden coordinates, one system has at most
    four potentially nonzero probes. -/
theorem four_candidates (k : Nat) (F : W 2 → W 2) (U I V J : W (k+2) → W (k+2))
    (lu : ∀ x, I (U x) = x) (ru : ∀ x, U (I x) = x)
    (lv : ∀ x, J (V x) = x) (rv : ∀ x, V (J x) = x) (hv : additive V) (hj : additive J)
    (c : W (k+2)) (h : walsh (mix (pad k F) U V) c ≠ 0) :
    ∃ a b : Bool, c = pullMask J (a,b,zero k) := by
  unfold mix at h
  rw [mixed_walsh _ U I lu ru V hv,pad_walsh,identity_spectrum] at h
  have tail : (pullMask V c).2.2 = zero k := by
    by_cases he : (pullMask V c).2.2 = zero k
    · exact he
    · simp [he] at h
  refine ⟨(pullMask V c).1,(pullMask V c).2.1,(pull_inverse V J lv rv hv hj _ _).mp ?_⟩
  rcases hp : pullMask V c with ⟨a,b,u⟩
  rw [hp] at tail
  exact congrArg (fun w => (a,b,w)) tail

/-- The Boolean difference q(x+d)+q(x) of a quadratic is an affine form in x. -/
def derivative : (n : Nat) → Quad n → W n → Form n
  | 0, _, _ => nilForm 0
  | n+1, q, (h,d) =>
    let slope := dot n q.1.bits d
    consF slope (plus (derivative n q.2 d)
      (plus (gateF h q.1) (constF n (h && slope))))

theorem derivative_exact (n : Nat) (q : Quad n) (d x : W n) :
    val (derivative n q d) x = xor (evalQ n q (add n d x)) (evalQ n q x) := by
  induction n with
  | zero => simp [evalQ,derivative,nilForm,val,dot]
  | succ n ih =>
    rcases d with ⟨h,d⟩
    rcases x with ⟨b,x⟩
    have plus_val : val q.1 (add n d x) = xor (dot n q.1.bits d) (val q.1 x) := by
      simp [val,dot_right,Bool.xor_assoc]
    simp only [derivative,val_consF,val_plus,val_gate,val_const,ih,evalQ,add,plus_val]
    cases h <;> cases b <;> cases dot n q.1.bits d <;> cases val q.1 x <;>
      cases evalQ n q.2 (add n d x) <;> cases evalQ n q.2 x <;> rfl

theorem interchange (n : Nat) (x y z v : W n) :
    add n (add n x y) (add n z v) = add n (add n x z) (add n y v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [add,ih]
    cases x.1 <;> cases y.1 <;> cases z.1 <;> cases v.1 <;> rfl

theorem derivative_linear (n : Nat) (q : Quad n) (d e : W n) :
    (derivative n q (add n d e)).bits =
      add n (derivative n q d).bits (derivative n q e).bits := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases d with ⟨a,d⟩
    rcases e with ⟨b,e⟩
    have right_zero (w : W n) : add n w (zero n) = w := by rw [add_comm,add_zero_left]
    cases a <;> cases b <;>
      simp only [derivative,add,consF,plus,constF,gateF,nilForm,dot_right,ih,
        Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true,if_true,
        Bool.false_eq_true,if_false,right_zero,add_zero_left]
    all_goals apply congrArg (fun tail : W n => (xor (dot n q.1.bits d) (dot n q.1.bits e),tail))
    · simpa only [right_zero,add_zero_left] using
        interchange n (derivative n q.2 d).bits (derivative n q.2 e).bits (zero n) q.1.bits
    · simpa only [right_zero,add_zero_left] using
        interchange n (derivative n q.2 d).bits (derivative n q.2 e).bits q.1.bits (zero n)
    · simpa only [right_zero,add_self] using
        interchange n (derivative n q.2 d).bits (derivative n q.2 e).bits q.1.bits q.1.bits

/-- Constant derivatives are exactly the kernel of the linear derivative slopes. -/
theorem flat_test (q : Quad n) (d : W n) :
    (∃ b, ∀ x, xor (evalQ n q (add n d x)) (evalQ n q x) = b) ↔
      (derivative n q d).bits = zero n := by
  simp only [← derivative_exact]
  let f := derivative n q d
  change (∃ b, ∀ x, val f x = b) ↔ f.bits = zero n
  constructor
  · rintro ⟨b,h⟩
    apply (dot_detects ..).mp
    intro x
    have e := (h x).trans (h (zero n)).symm
    simp only [val,dot_zero_right,Bool.false_xor] at e
    cases f.const <;> cases hdot : dot n f.bits x <;> simp_all
  · intro h; exact ⟨f.const,fun x => by simp [val,h,dot_zero]⟩

/-- Remove the zero mask's known contribution before measuring energy. -/
def offZero (Q : W n → W r) (c : W r) : Int :=
  if c = zero r then 0 else walsh Q c

theorem residual_energy (Q : W n → W r) :
    total r (fun c => offZero Q c * offZero Q c) =
      many r * collisions Q - many n * many n := by
  have dc : walsh Q (zero r) = many n := by simp [walsh,chr,dot_zero,sign,total_const]
  have split (c : W r) : offZero Q c * offZero Q c =
      walsh Q c * walsh Q c - hits (zero r) c * (many n * many n) := by
    by_cases h : c = zero r
    · subst c; simp [offZero,dc,hits]
    · simp [offZero,h,hits,Ne.symm h]
  simp only [split,total_sub,parseval_collision_law,select]

theorem identity_off_zero (n : Nat) (c : W n) : offZero (fun x : W n => x) c = 0 := by
  simp only [offZero,identity_spectrum]
  split <;> simp_all

/-- A zeroed-out probe can be omitted from Fourier inversion as soon as a
    constant derivative certifies its cancellation. -/
theorem screened_count (Q : W n → W r) (keep : W r → Bool)
    (skip : ∀ c, keep c = false → ∃ d v, shift Q d v ∧ dot r c v = true) :
    total r (fun c => if keep c then walsh Q c else 0) = many r * solutions Q := by
  rw [← first_moment]
  apply congrArg (total r)
  funext c
  cases h : keep c with
  | true => rfl
  | false =>
    obtain ⟨d,v,flat,odd⟩ := skip c h
    exact (shift_kills Q flat c odd).symm

/-- Independent AND outputs give a quadratic example with full spectral support. -/
def andMap : (m : Nat) → W (dim m) → W m
  | 0, _ => ()
  | m+1, w => (w.1 && w.2.1,andMap m w.2.2)

theorem and_product (m : Nat) (c : W (m+1)) :
    walsh (andMap (m+1)) c = (if c.1 then 2 else 4) * walsh (andMap m) c.2 := by
  have piece (a b : Bool) :
      total (dim m) (fun u => chr c (andMap (m+1) (a,b,u))) =
        sign (c.1 && (a && b)) * walsh (andMap m) c.2 := by
    simp [andMap,chr,dot,signMul,total_scale,walsh]
  change total (dim m+2) (fun w => chr c (andMap (m+1) w)) = _
  rw [four]
  simp only [piece]
  cases c.1 <;> simp [sign] <;> omega

theorem full_support (m : Nat) (c : W m) : 0 < walsh (andMap m) c := by
  induction m with
  | zero => cases c; decide
  | succ m ih =>
    rw [and_product]
    have h := ih c.2
    cases c.1 <;> simp <;> omega

#print axioms shift_kills
#print axioms recover_from_equations
#print axioms unique_hidden_mask
#print axioms derivative_exact
#print axioms derivative_linear
#print axioms flat_test
#print axioms four_candidates
#print axioms screened_count
#print axioms full_support
#print axioms residual_energy
#print axioms identity_off_zero
end MaskRecovery
