import SilentRoom

namespace RingCracks
open FrozenShells CandyKnots FreezeMovies CollisionLaw MaskRecovery SilentRoom

def ones : (n : Nat) → W n
  | 0 => ()
  | n+1 => (true,ones n)

def gain : (n : Nat) → W n → Bool
  | 0, _ => true
  | n+1, t => t.1 && gain n t.2

theorem gain_iff (n : Nat) (t : W n) : gain n t = true ↔ t = ones n := by
  induction n with
  | zero => cases t; simp [gain,ones]
  | succ n ih =>
    rcases t with ⟨b,t⟩
    change (b && gain n t) = true ↔ (b,t) = (true,ones n)
    simp [ih]

/-- Walk along the path. Each discrepancy is next XOR (control AND previous).
    The returned first component is the last input wire. -/
def walk : (n : Nat) → W n → Bool → W n → Bool × W n
  | 0, _, s, _ => (s,())
  | n+1, t, s, x =>
    let (last,res) := walk n t.2 x.1 x.2
    (last,(xor x.1 (t.1 && s),res))

def undoPath : (n : Nat) → W n → Bool → W n → W n
  | 0, _, _, _ => ()
  | n+1, t, s, y =>
    let z := xor y.1 (t.1 && s)
    (z,undoPath n t.2 z y.2)

def finish : (n : Nat) → W n → Bool → W n → Bool
  | 0, _, s, _ => s
  | n+1, t, s, y => finish n t.2 (xor y.1 (t.1 && s)) y.2

theorem walk_path (n : Nat) (t : W n) (s : Bool) (x y : W n) :
    (walk n t s x).2 = y ↔ x = undoPath n t s y := by
  induction n generalizing s with
  | zero => cases x; cases y; exact Iff.rfl
  | succ n ih =>
    rcases x with ⟨b,x⟩; rcases y with ⟨c,y⟩
    change (xor b (t.1 && s),(walk n t.2 b x).2) = (c,y) ↔
      (b,x) = (xor c (t.1 && s),undoPath n t.2 (xor c (t.1 && s)) y)
    simp only [Prod.mk.injEq,ih]
    cases b <;> cases c <;> cases t.1 && s <;> simp

theorem walk_last (n : Nat) (t : W n) (s : Bool) (y : W n) :
    (walk n t s (undoPath n t s y)).1 = finish n t s y := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih _ _ _

theorem finish_affine (n : Nat) (t : W n) (s a : Bool) (y : W n) :
    finish n t (xor s a) y = xor (gain n t && s) (finish n t a y) := by
  induction n generalizing s a with
  | zero => rfl
  | succ n ih =>
    simp only [finish,gain]
    have eq : xor y.1 (t.1 && xor s a) = xor (t.1 && s) (xor y.1 (t.1 && a)) := by
      cases t.1 <;> cases y.1 <;> cases s <;> cases a <;> rfl
    rw [eq,ih]
    cases t.1 <;> cases s <;> cases gain n t.2 <;> rfl

theorem finish_ones (n : Nat) (s : Bool) (y : W n) :
    finish n (ones n) s y = xor s (parity n y) := by
  induction n generalizing s with
  | zero => simp [finish,parity]
  | succ n ih => simp [finish,ones,parity,ih,Bool.xor_left_comm]

/-- Close the path using its last edge. The full square map copies t and
    outputs these discrepancies. The first coordinate is the closing edge. -/
def residual (k : Nat) (t x : W (k+1)) : W (k+1) :=
  let w := walk k t.2 x.1 x.2
  (xor x.1 (t.1 && w.1),w.2)

/-- Compile the ring's discrepancies into the lab's triangular quadratic
    tables, allowing any affine input wires, including fixed controls. -/
def Rows (α : Type) : Nat → Type
  | 0 => Unit
  | m+1 => α × Rows α m

def readRows (f : α → Bool) : (m : Nat) → Rows α m → W m
  | 0, _ => ()
  | m+1, w => (f w.1,readRows f m w.2)

def edge (next ctrl prev : Form n) :=
  addQ n (times n next (constF n true)) (times n ctrl prev)

theorem edge_eval (next ctrl prev : Form n) (x : W n) :
    evalQ n (edge next ctrl prev) x = xor (val next x) (val ctrl x && val prev x) := by
  simp [edge,eval_addQ,eval_times,val_const]

def compilePath : (k : Nat) → Rows (Form n) k → Form n → Rows (Form n) k →
    Form n × Rows (Quad n) k
  | 0, _, s, _ => (s,())
  | k+1, t, s, x =>
    let (last,rest) := compilePath k t.2 x.1 x.2
    (last,(edge x.1 t.1 s,rest))

theorem compile_path_exact (k : Nat) (t : Rows (Form n) k) (s : Form n)
    (w : Rows (Form n) k) (x : W n) :
    walk k (readRows (fun f => val f x) k t) (val s x) (readRows (fun f => val f x) k w) =
      (val (compilePath k t s w).1 x,readRows (fun q => evalQ n q x) k (compilePath k t s w).2) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp only [compilePath,walk,readRows,ih,edge_eval]

def compileRing (k : Nat) (t w : Rows (Form n) (k+1)) : Rows (Quad n) (k+1) :=
  let (last,rest) := compilePath k t.2 w.1 w.2
  (edge w.1 t.1 last,rest)

theorem ring_is_quadratic (k : Nat) (t w : Rows (Form n) (k+1)) (x : W n) :
    residual k (readRows (fun f => val f x) (k+1) t) (readRows (fun f => val f x) (k+1) w) =
      readRows (fun q => evalQ n q x) (k+1) (compileRing k t w) := by
  simp only [residual,compileRing,readRows,compile_path_exact,edge_eval]

theorem slice (k : Nat) (t y : W (k+1)) (s : Bool) :
    total k (fun x => hits (residual k t (s,x)) y) =
      if xor s (t.1 && finish k t.2 s y.2) = y.1 then 1 else 0 := by
  rcases y with ⟨b,y⟩
  let pre := undoPath k t.2 s y
  have eq (x : W k) : hits (residual k t (s,x)) (b,y) =
      (if xor s (t.1 && finish k t.2 s y) = b then 1 else 0) * hits pre x := by
    have p := walk_path k t.2 s x y
    change hits (r := k+1) (xor s (t.1 && (walk k t.2 s x).1),(walk k t.2 s x).2) (b,y) = _
    rw [hit_cons]
    by_cases h : x = pre
    · subst x
      have path := p.mpr rfl
      rw [path]
      simp only [hits,pre,walk_last,if_true,Int.mul_one]
    · have nh : (walk k t.2 s x).2 ≠ y := fun e => h (p.mp e)
      simp [hits,nh,Ne.symm h]
  simp only [eq,total_scale,diagonal,Int.mul_one]

/-- With a zero control each bucket has one preimage. At all ones its size
    alternates between two and zero according to the parity of the wire output. -/
theorem ring_histogram (k : Nat) (t y : W (k+1)) :
    histogram (residual k t) y = 1 + (if t = ones (k+1) then sign (parity (k+1) y) else 0) := by
  rcases t with ⟨b,t⟩; rcases y with ⟨v,y⟩
  unfold histogram
  rw [total,slice,slice]
  change (if xor false (b && finish k t false y) = v then _ else _) +
      (if xor true (b && finish k t true y) = v then _ else _) =
        1 + (if (b,t) = (true,ones k) then sign (xor v (parity k y)) else 0)
  cases b with
  | false => cases v <;> simp [Prod.mk.injEq]
  | true =>
    by_cases h : t = ones k
    · subst t; cases v <;> cases p : parity k y <;> simp [finish_ones,p,sign]
    · have g : gain k t = false := by cases e : gain k t <;> simp_all [gain_iff]
      have f := finish_affine k t true false y
      simp [g] at f
      cases v <;> cases e : finish k t false y <;> simp [Prod.mk.injEq,h,f,e]

theorem dot_ones (n : Nat) (w : W n) : dot n (ones n) w = parity n w := by
  induction n <;> simp [dot,ones,parity, *]

theorem character_sum (n : Nat) (a b : W n) :
    total n (fun y => chr a y * chr b y) = many n * hits a b := by
  have flip (c d : W n) : chr c d = chr d c := by simp [chr,dot_comm n c d]
  simpa only [flip a,flip b] using orthogonal n a b

def spectrum (k : Nat) (a b : W (k+1)) :=
  total (k+1) (fun t => chr a t * walsh (residual k t) b)

theorem slice_walsh (k : Nat) (t b : W (k+1)) : walsh (residual k t) b =
    (if b = zero _ then many (k+1) else 0) + hits (ones (k+1)) t * (many (k+1) * hits (ones (k+1)) b) := by
  let m := k+1
  have basic (c : W m) : total m (chr c) = if c = zero m then many m else 0 :=
    identity_spectrum m c
  rw [by_histogram]
  unfold transform
  by_cases h : t = ones m
  · subst t
    simp only [ring_histogram,if_true,Int.add_mul,Int.one_mul,total_add,basic,hits,
      ← dot_ones]
    change _ + total m (fun y => chr (ones m) y * chr b y) = _
    rw [character_sum]
    simp [hits]
  · simp only [ring_histogram,h,if_false,Int.add_zero,Int.one_mul,basic,hits,Ne.symm h,
      Int.zero_mul,Int.add_zero]

/-- Keep s controls and fix the others high. Only the all-ones slice is singular. -/
theorem reduced_spectrum (k s : Nat) (controls : W s → W (k+1))
    (onlyOnes : ∀ t, ones (k+1) = controls t ↔ ones s = t) (a : W s) (b : W (k+1)) :
    total s (fun t => chr a t * walsh (residual k (controls t)) b) =
      (if a = zero _ ∧ b = zero _ then many (k+1) * many s else 0) +
      chr a (ones s) * (many (k+1) * hits (ones (k+1)) b) := by
  have delta (t : W s) : hits (ones (k+1)) (controls t) = hits (ones s) t := by
    simp only [hits,onlyOnes]
  simp only [slice_walsh,delta,Int.mul_add,total_add]
  have constPart (z : Int) : total s (fun t => chr a t * z) = z * total s (chr a) := by
    simp only [Int.mul_comm _ z,total_scale]
  have spike (z : Int) : total s (fun t => chr a t * (hits (ones s) t * z)) = chr a (ones s) * z := by
    have eq (t : W s) : chr a t * (hits (ones s) t * z) = hits (ones s) t * (chr a t * z) :=
      Int.mul_left_comm ..
    simp only [eq,select]
  rw [constPart,spike,show total s (chr a) = _ from identity_spectrum s a]
  by_cases ha : a = zero s <;> by_cases hb : b = zero (k+1) <;> simp [ha,hb]

theorem ring_spectrum (k : Nat) (a b : W (k+1)) :
    spectrum k a b =
      (if a = zero _ ∧ b = zero _ then many (k+1) * many (k+1) else 0) +
      chr a (ones (k+1)) * (many (k+1) * hits (ones (k+1)) b) :=
  reduced_spectrum k (k+1) id (fun _ => Iff.rfl) a b

theorem slice_excess (k : Nat) (t : W (k+1)) :
    collisions (residual k t) - many (k+1) = hits (ones (k+1)) t * many (k+1) := by
  rw [← excess]
  by_cases h : t = ones (k+1)
  · subst t
    have sq (y : W (k+1)) : deviation (residual k (ones (k+1))) y *
        deviation (residual k (ones (k+1))) y = 1 := by
      simp only [deviation,ring_histogram,if_true]
      cases parity (k+1) y <;> decide
    simp [sq,total_const,hits]
  · simp [deviation,ring_histogram,h,Ne.symm h,hits,total_zero]

/-- The controls are copied to the output, so excesses add over the slices. -/
theorem ring_excess (k : Nat) :
    total (k+1) (fun t => collisions (residual k t) - many (k+1)) = many (k+1) := by
  simp only [slice_excess,select]

/-- Fix one control high and omit it from input and output. With 2k+1 inputs
    the remaining k controls still include the exceptional all-ones slice. -/
theorem odd_ring_excess (k : Nat) :
    total k (fun t => collisions (residual k (true,t)) - many (k+1)) = many (k+1) := by
  simp only [slice_excess,ones,hit_cons,if_true,select]

def fixHigh (s : Nat) : (j : Nat) → W s → W (s+j)
  | 0,t => t
  | j+1,t => (true,fixHigh s j t)

theorem fixHigh_ones (s j : Nat) (t : W s) : ones (s+j) = fixHigh s j t ↔ ones s = t := by
  induction j with
  | zero => exact Iff.rfl
  | succ j ih =>
    change (true,ones (s+j)) = (true,fixHigh s j t) ↔ _
    simp [ih]

theorem reduced_excess (k s : Nat) (controls : W s → W (k+1))
    (onlyOnes : ∀ t, ones (k+1) = controls t ↔ ones s = t) :
    total s (fun t => collisions (residual k (controls t)) - many (k+1)) = many (k+1) := by
  have delta (t : W s) : hits (ones (k+1)) (controls t) = hits (ones s) t := by simp only [hits,onlyOnes]
  simp only [slice_excess,delta,select]

theorem ones_weight (n : Nat) : weight n (ones n) = n := by
  induction n <;> simp [ones,weight, *]

theorem silent_below (k : Nat) (a b : W (k+1))
    (pos : 0 < weight (k+1) a + weight (k+1) b) (low : weight (k+1) a + weight (k+1) b < k+1) :
    spectrum k a b = 0 := by
  have ne : ones (k+1) ≠ b := by rintro rfl; rw [ones_weight] at low; omega
  have nz : ¬ (a = zero _ ∧ b = zero _) := by rintro ⟨rfl,rfl⟩; simp [weight_zero] at pos
  simp [ring_spectrum,nz,hits,ne]

theorem first_audible (k : Nat) :
    spectrum k (zero _) (ones _) = many (k+1) := by
  have ne : ones (k+1) ≠ zero (k+1) := by intro h; have e := congrArg Prod.fst h; contradiction
  simp [ring_spectrum,ne,hits,chr,dot_zero,sign]

def onlyFixHigh (s m : Nat) (E : W s → W m) :=
  ∃ (j : Nat) (h : s+j = m), ∀ t, E t = cast (congrArg W h) (fixHigh s j t)

theorem control_embedding (s m : Nat) (h : s ≤ m) :
    ∃ E : W s → W m, onlyFixHigh s m E ∧ ∀ t, ones m = E t ↔ ones s = t := by
  obtain ⟨j,rfl⟩ : ∃ j, m = s+j := ⟨m-s,by omega⟩
  exact ⟨fixHigh s j,⟨j,rfl,fun _ => rfl⟩,fixHigh_ones s j⟩

/-- Attain the simultaneous sparsity and quadratic bounds at every allowed
    dimension and silence depth. The input and output words have s+k+1 bits. -/
theorem optimal_ring (n d : Nat) (range : d < n) :
    ∃ (s k : Nat) (E : W s → W (k+1)), onlyFixHigh s (k+1) E ∧ s + (k+1) = n ∧ k+1 = max ((n+1)/2) (d+1) ∧
      total s (fun t => collisions (residual k (E t)) - many (k+1)) = many (k+1) ∧
      ∀ (a : W s) (b : W (k+1)), 0 < weight s a + weight (k+1) b →
        weight s a + weight (k+1) b ≤ d →
        total s (fun t => chr a t * walsh (residual k (E t)) b) = 0 := by
  let m := max ((n+1)/2) (d+1)
  have h₁ : (n+1)/2 ≤ m := Nat.le_max_left _ _
  have h₂ : d+1 ≤ m := Nat.le_max_right _ _
  have h₃ : m ≤ n := Nat.max_le.mpr ⟨by omega,by omega⟩
  obtain ⟨k,hk⟩ : ∃ k, m=k+1 := ⟨m-1,by omega⟩
  let s := n-m
  have sh : s ≤ k+1 := by dsimp [s]; omega
  obtain ⟨E,fixed,eh⟩ := control_embedding s (k+1) sh
  refine ⟨s,k,E,fixed,by dsimp [s]; omega,hk.symm,reduced_excess k s E eh,?_⟩
  intro a b pos low
  have ne : ones (k+1) ≠ b := by rintro rfl; rw [ones_weight] at low; omega
  have nz : ¬ (a = zero _ ∧ b = zero _) := by rintro ⟨rfl,rfl⟩; simp [weight_zero] at pos
  simp [reduced_spectrum k s E eh,nz,hits,ne]

#print axioms reduced_spectrum
#print axioms reduced_excess
#print axioms ring_histogram
#print axioms ring_spectrum
#print axioms ring_excess
#print axioms odd_ring_excess
#print axioms silent_below
#print axioms first_audible
#print axioms ring_is_quadratic
#print axioms optimal_ring
end RingCracks
