import CandyKnots
import FreezeMovies

namespace CollisionLaw
open FrozenShells CandyKnots FreezeMovies

def many (n : Nat) := (2:Int)^n
def chr (c s : W r) := sign (dot r c s)
def hits (s t : W r) : Int := if s = t then 1 else 0

def walsh (Q : W n → W r) (c : W r) := total n (fun x => chr c (Q x))
def solutions (Q : W n → W r) := total n (fun x => hits (Q x) (zero r))
def collisions (Q : W n → W r) := total n (fun x => total n (fun y => hits (Q x) (Q y)))

theorem total_const (n : Nat) (k : Int) : total n (fun _ => k) = many n * k := by
  induction n with
  | zero => simp [total,many]
  | succ n ih =>
    simp only [total,ih,many,Int.pow_succ]
    rw [show (2:Int)^n*2 = (2:Int)^n + (2:Int)^n by omega, Int.add_mul]

theorem total_mono (n : Nat) (f g : W n → Int) (h : ∀ w, f w ≤ g w) :
    total n f ≤ total n g := by
  induction n with
  | zero => exact h ()
  | succ n ih =>
    exact Int.add_le_add (ih _ _ (fun w => h (false,w))) (ih _ _ (fun w => h (true,w)))

theorem swap (n m : Nat) (f : W n → W m → Int) :
    total n (fun x => total m (f x)) = total m (fun y => total n (fun x => f x y)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [total,ih,ih,← total_add]
    rfl

theorem rectangular (n m : Nat) (f : W n → Int) (g : W m → Int) :
    total n f * total m g = total n (fun x => total m (fun y => f x * g y)) := by
  simp only [total_scale]
  rw [Int.mul_comm, ← total_scale]
  exact congrArg (total n) (funext (fun x => Int.mul_comm ..))

theorem twice_total (r : Nat) (f : W r → Int) :
    total r (fun c => -f c) = -total r f := by
  have eq := total_scale r (-1) f
  simpa using eq

theorem hit_cons (a b : Bool) (s t : W n) :
    hits (r := n+1) (a,s) (b,t) = (if a = b then hits s t else 0) := by
  by_cases h : a = b
  · subst b
    have eq : ((a,s) : W (n+1)) = (a,t) ↔ s=t := ⟨fun e => congrArg Prod.snd e, fun e => e ▸ rfl⟩
    simp [hits,eq]
  · have ne : ((a,s) : W (n+1)) ≠ (b,t) := fun e => h (congrArg Prod.fst e)
    simp [hits,h,ne]

theorem orthogonal (r : Nat) (s t : W r) :
    total r (fun c => chr c s * chr c t) = many r * hits s t := by
  induction r with
  | zero => cases s; cases t; decide
  | succ r ih =>
    rcases s with ⟨a,s⟩
    rcases t with ⟨b,t⟩
    have fact (u : Bool) (v : W r) (t : W r) :
        chr (r := r+1) (true,v) (u,t) = sign u * chr v t := by
      exact signMul _ _
    have pass (u : Bool) (v : W r) (t : W r) : chr (r := r+1) (false,v) (u,t) = chr v t := by
      simp [chr,dot]
    have ar : many (r+1) = many r + many r := by simp [many,Int.pow_succ]; omega
    rw [total]
    simp only [fact,pass]
    cases a <;> cases b <;>
      simp [sign,twice_total,ih,ar,hit_cons,Int.add_mul,Int.neg_mul,Int.mul_neg] <;> omega

theorem diagonal (n : Nat) (x : W n) : total n (fun y => hits x y) = 1 := by
  induction n with
  | zero => cases x; decide
  | succ n ih =>
    rcases x with ⟨b,x⟩
    rw [total]
    cases b <;> simp [hit_cons,total_zero,ih]

theorem parseval_collision_law (Q : W n → W r) :
    total r (fun c => walsh Q c * walsh Q c) = many r * collisions Q := by
  unfold walsh collisions
  simp only [rectangular n n]
  rw [swap r n]
  have inner (x : W n) :
      total r (fun c => total n (fun y => chr c (Q x) * chr c (Q y))) =
      many r * total n (fun y => hits (Q x) (Q y)) := by
    rw [swap r n]
    simp only [orthogonal,total_scale]
  exact (congrArg (total n) (funext inner)).trans (total_scale ..)

theorem collision_diagonal_bound (Q : W n → W r) : many n ≤ collisions Q := by
  have count : total n (fun x => total n (fun y => hits x y)) = many n := by simp [diagonal,total_const]
  rw [← count]
  apply total_mono
  intro x
  apply total_mono
  intro y
  by_cases h : x = y
  · subst y; simp [hits]
  · simp [hits,h]
    split <;> decide

theorem many_nonneg (n : Nat) : 0 ≤ many n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [many, Int.pow_succ] at *; omega

theorem parseval_noise_floor (Q : W n → W r) :
    many r * many n ≤ total r (fun c => walsh Q c * walsh Q c) := by
  rw [parseval_collision_law]
  exact Int.mul_le_mul_of_nonneg_left (collision_diagonal_bound Q) (many_nonneg r)

theorem dot_zero_right (n : Nat) (x : W n) : dot n x (zero n) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [dot,zero,ih]

theorem first_moment (Q : W n → W r) :
    total r (walsh Q) = many r * solutions Q := by
  unfold walsh solutions
  rw [swap r n]
  have one (x : W n) := orthogonal r (Q x) (zero r)
  simp only [chr,dot_zero_right,sign, Bool.false_eq_true, if_false, Int.mul_one] at one
  change total n (fun x => total r (fun c => sign (dot r c (Q x)))) = _
  exact (congrArg (total n) (funext one)).trans (total_scale ..)

theorem translate (Q : W n → W r) (t c : W r) :
    walsh (fun x => add r t (Q x)) c = chr c t * walsh Q c := by
  have right (k : Nat) (a b c : W k) :
      dot k c (add k a b) = xor (dot k c a) (dot k c b) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [dot,add,ih]
      cases c.1 <;> cases a.1 <;> cases b.1 <;> cases dot k c.2 a.2 <;> cases dot k c.2 b.2 <;> rfl
  simp [walsh,chr,right,signMul,total_scale]

theorem translate_square (Q : W n → W r) (t c : W r) :
    walsh (fun x => add r t (Q x)) c * walsh (fun x => add r t (Q x)) c =
    walsh Q c * walsh Q c := by
  rw [translate]
  cases e : dot r c t <;> simp [chr,e,sign]

def base (x : W 2) : W 2 := (x.1 && !x.2.1, x.2.1, ())
def shifted (x : W 2) : W 2 := add 2 (true,true,()) (base x)

theorem blind_pair :
    solutions base = 1 ∧ solutions shifted = 0 ∧ collisions base = 6 ∧
    ∀ c : W 2, walsh base c * walsh base c = walsh shifted c * walsh shifted c := by
  refine ⟨by decide, by decide, by decide, fun c => ?_⟩
  exact (translate_square base (true,true,()) c).symm

#print axioms parseval_collision_law
#print axioms parseval_noise_floor
#print axioms first_moment
#print axioms blind_pair
end CollisionLaw

namespace CollisionLaw
open FrozenShells CandyKnots FreezeMovies

theorem total_sub (n : Nat) (f g : W n → Int) :
    total n (fun x => f x - g x) = total n f - total n g := by
  simp only [Int.sub_eq_add_neg,total_add,twice_total]

theorem variance_law (Q : W n → W r) :
    total r (fun c => (walsh Q c - solutions Q) * (walsh Q c - solutions Q)) =
    many r * (collisions Q - solutions Q * solutions Q) := by
  have poly (a b : Int) : (a-b)*(a-b) = a*a - b*a - b*a + b*b := by
    rw [Int.sub_mul,Int.mul_sub,Int.mul_sub,Int.mul_comm a b]
    omega
  simp only [poly,total_add,total_sub,total_scale,total_const,parseval_collision_law,first_moment]
  rw [Int.mul_left_comm (solutions Q) (many r),Int.mul_sub]
  omega

theorem unique_variance_floor (Q : W n → W r) (h : solutions Q = 1) :
    many r * (many n - 1) ≤ total r (fun c => (walsh Q c - 1) * (walsh Q c - 1)) := by
  have v := variance_law Q
  rw [h] at v
  rw [v]
  apply Int.mul_le_mul_of_nonneg_left _ (many_nonneg r)
  have := collision_diagonal_bound Q
  omega

theorem signed_bound (n : Nat) (f : W n → Bool) :
    -many n ≤ total n (fun x => sign (f x)) := by
  have h := total_mono n (fun _ => -1) (fun x => sign (f x))
    (fun w => by change -1 ≤ sign (f w); cases f w <;> decide)
  simpa [total_const] using h

theorem negative_saturation (n : Nat) (f : W n → Bool) :
    total n (fun w => sign (f w)) = -many n ↔ ∀ w, f w = true := by
  induction n with
  | zero => cases e : f () <;> simp [total,many,sign,e,W]
  | succ n ih =>
    have ar : many (n+1) = many n + many n := by simp [many,Int.pow_succ]; omega
    rw [total,ar]
    constructor
    · intro he
      have lo := signed_bound n (fun w => f (false,w))
      have hi := signed_bound n (fun w => f (true,w))
      have low : total n (fun w => sign (f (false,w))) = -many n := by omega
      have high : total n (fun w => sign (f (true,w))) = -many n := by omega
      intro ⟨b,w⟩
      cases b
      · exact (ih _).mp low w
      · exact (ih _).mp high w
    · intro h
      have low := (ih (fun w => f (false,w))).mpr (fun w => h (false,w))
      have high := (ih (fun w => f (true,w))).mpr (fun w => h (true,w))
      omega

theorem contradiction_peek (Q : W n → W r) (c : W r) :
    walsh Q c = -many n ↔ ∀ x, dot r c (Q x) = true := negative_saturation n _

theorem identity_spectrum (n : Nat) (c : W n) :
    walsh (fun x : W n => x) c = if c = zero n then many n else 0 := by
  have e := orthogonal n c (zero n)
  have flip (m : Nat) (a b : W m) : dot m a b = dot m b a := by
    induction m with
    | zero => rfl
    | succ m ih => simp only [dot]; rw [Bool.and_comm,ih]
  have h (x : W n) : chr x c * chr x (zero n) = chr c x := by
    simp [chr,dot_zero_right,sign]; rw [flip]
  simp only [h] at e
  change total n (fun x => chr c x) = _
  rw [e]
  by_cases eq : c = zero n <;> simp [hits,eq]

/-- Compute each signed Walsh probe using the verified single-quadratic counter. -/
def outputs : (ps : List (Quad n)) → W n → W ps.length
  | [], _ => ()
  | p::ps, w => (evalQ n p w,outputs ps w)

def combined : (ps : List (Quad n)) → W ps.length → Quad n
  | [], _ => origin n
  | p::ps, c =>
    let q := combined ps c.2
    if c.1 then addQ n p q else q

theorem combined_eval (ps : List (Quad n)) (c : W ps.length) (w : W n) :
    evalQ n (combined ps c) w = dot ps.length c (outputs ps w) := by
  induction ps with
  | nil => simp [combined,outputs,dot,eval_origin]
  | cons p ps ih =>
    rcases c with ⟨b,c⟩
    cases b <;> simp [combined,outputs,dot,eval_addQ,ih]

theorem fast_probe (ps : List (Quad n)) (c : W ps.length) :
    countBias n (combined ps c) = walsh (outputs ps) c := by
  rw [countBias_exact]
  simp [bias,walsh,chr,combined_eval]

#print axioms variance_law
#print axioms unique_variance_floor
#print axioms contradiction_peek
#print axioms identity_spectrum
#print axioms fast_probe
#eval (worlds 2).map (fun c => (walsh base c,walsh shifted c))
end CollisionLaw

namespace CollisionLaw
open FrozenShells CandyKnots FreezeMovies

/-- Add k independent copy-to-output bits to a two-bit map. -/
def pad (k : Nat) (F : W 2 → W 2) (w : W (k+2)) : W (k+2) :=
  let v := F (w.1,w.2.1,())
  (v.1,v.2.1,w.2.2)

def headTwo (c : W (k+2)) : W 2 := (c.1,c.2.1,())

theorem four (k : Nat) (f : W (k+2) → Int) : total (k+2) f =
    (total k (fun u => f (false,false,u)) + total k (fun u => f (false,true,u))) +
    (total k (fun u => f (true,false,u)) + total k (fun u => f (true,true,u))) := rfl

theorem pad_walsh (k : Nat) (F : W 2 → W 2) (c : W (k+2)) :
    walsh (pad k F) c = walsh F (headTwo c) * walsh (fun u : W k => u) c.2.2 := by
  have term (a b : Bool) :
      total k (fun u => chr c (pad k F (a,b,u))) =
      chr (headTwo c) (F (a,b,())) * walsh (fun u : W k => u) c.2.2 := by
    rw [walsh, ← total_scale]
    apply congrArg (total k)
    funext u
    simp only [chr,headTwo,pad,dot,Bool.xor_false]
    rw [←signMul,Bool.xor_assoc]
  change total (k+2) (fun w => chr c (pad k F w)) = _
  rw [four]
  simp only [term]
  rw [←Int.add_mul,←Int.add_mul,←Int.add_mul]
  rfl

theorem pad_solutions (k : Nat) (F : W 2 → W 2) :
    solutions (pad k F) = solutions F := by
  have tailOne : total k (fun u => hits u (zero k)) = 1 := by
    have symm (u : W k) : hits u (zero k) = hits (zero k) u := by
      simp [hits,eq_comm]
    simp only [symm,diagonal]
  have term (a b : Bool) :
      total k (fun u => hits (pad k F (a,b,u)) (zero (k+2))) =
      hits (F (a,b,())) (zero 2) := by
    generalize hx : F (a,b,()) = v
    have eq (u : W k) :
        hits (pad k F (a,b,u)) (zero (k+2)) = hits v (zero 2) * hits u (zero k) := by
      rcases v with ⟨i,j,z⟩
      cases z
      simp only [pad,hx,zero]
      rw [hit_cons (n := k+1) i false (j,u) (false,zero k), hit_cons (n := k) j false u (zero k),
          hit_cons (n := 1) i false (j,()) (false,()), hit_cons (n := 0) j false () ()]
      have one : hits (r := 0) () () = 1 := rfl
      cases i <;> cases j <;> simp [one]
    simp only [eq,total_scale,tailOne,Int.mul_one]
  unfold solutions
  rw [four]
  simp only [term]
  rfl

theorem many_pos (k : Nat) : 0 < many k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [many,Int.pow_succ] at *; omega

/-- For every input/output dimension k+2, only one signed coefficient
    distinguishes this satisfiable and unsatisfiable pair. -/
theorem one_distinguishing_mask (k : Nat) (c : W (k+2)) :
    walsh (pad k base) c ≠ walsh (pad k shifted) c ↔
      c = (true,false,zero k) := by
  rw [pad_walsh,pad_walsh,identity_spectrum]
  rcases c with ⟨a,b,u⟩
  have head (a b : Bool) : walsh base (a,b,()) ≠ walsh shifted (a,b,()) ↔
      a = true ∧ b = false := by cases a <;> cases b <;> decide
  change walsh base (a,b,()) * (if u = zero k then many k else 0) ≠
         walsh shifted (a,b,()) * (if u = zero k then many k else 0) ↔ _
  by_cases e : u = zero k
  · subst u
    have cancel (x y : Int) : x * many k = y * many k ↔ x = y :=
      ⟨fun h => Int.eq_of_mul_eq_mul_right (by have := many_pos k; omega) h, fun h => h ▸ rfl⟩
    simp only [ite_true, ne_eq, cancel]
    apply (head a b).trans
    constructor
    · rintro ⟨rfl,rfl⟩; rfl
    · intro h; cases h; exact ⟨rfl,rfl⟩
  · have ne : (a,b,u) ≠ (true,false,zero k) := fun h => e (congrArg (fun w => w.2.2) h)
    simp [e,ne]

theorem padded_pair (k : Nat) :
    solutions (pad k base) = 1 ∧ solutions (pad k shifted) = 0 ∧
    ∀ c, walsh (pad k base) c * walsh (pad k base) c =
         walsh (pad k shifted) c * walsh (pad k shifted) c := by
  refine ⟨(pad_solutions k base).trans blind_pair.1,
    (pad_solutions k shifted).trans blind_pair.2.1,fun c => ?_⟩
  simp only [pad_walsh]
  have regroup (x y : Int) : (x*y)*(x*y) = (x*x)*(y*y) := by
    rw [Int.mul_assoc, ←Int.mul_assoc y x y, Int.mul_comm y x, Int.mul_assoc x y y,
        ←Int.mul_assoc]
  rw [regroup,regroup,blind_pair.2.2.2]

#print axioms padded_pair
#print axioms one_distinguishing_mask
end CollisionLaw
