import FrozenShells

namespace CandyKnots
open FrozenShells

/-- Each row is q(x,y) = x L(y) + Q(y), all polynomial operations modulo two. -/
def Quad : Nat → Type
  | 0 => Bool
  | n+1 => Form n × Quad n

def evalQ : (n : Nat) → Quad n → W n → Bool
  | 0, c, _ => c
  | n+1, q, w => xor (w.1 && val q.1 w.2) (evalQ n q.2 w.2)

def addQ : (n : Nat) → Quad n → Quad n → Quad n
  | 0, a, b => xor a b
  | n+1, a, b => (plus a.1 b.1, addQ n a.2 b.2)

theorem eval_addQ (n : Nat) (a b : Quad n) (w : W n) :
    evalQ n (addQ n a b) w = xor (evalQ n a w) (evalQ n b w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [evalQ, addQ, val_plus, ih]
    cases w.1 <;> cases val a.1 w.2 <;> cases val b.1 w.2 <;>
      cases evalQ n a.2 w.2 <;> cases evalQ n b.2 w.2 <;> rfl

def constF (n : Nat) (b : Bool) : Form n := ⟨zero n,b⟩
def gateF (b : Bool) (f : Form n) := if b then f else nilForm n

theorem val_const (b : Bool) (w : W n) : val (constF n b) w = b := by
  simp [val, constF, dot_zero]
theorem val_gate (b : Bool) (f : Form n) (w : W n) : val (gateF b f) w = (b && val f w) := by
  cases b <;> simp [gateF, nilForm, val, dot_zero]

def times : (n : Nat) → Form n → Form n → Quad n
  | 0, a, b => a.const && b.const
  | n+1, a, b =>
    (plus (constF _ (a.bits.1 && b.bits.1))
      (plus (gateF a.bits.1 (trim b)) (gateF b.bits.1 (trim a))),
     times n (trim a) (trim b))

theorem eval_times (n : Nat) (a b : Form n) (w : W n) :
    evalQ n (times n a b) w = (val a w && val b w) := by
  induction n with
  | zero => simp [times, evalQ, val, dot]
  | succ n ih =>
    rcases w with ⟨h,t⟩
    simp only [evalQ, times, ih, val_plus, val_gate, val_const, val_cons]
    cases h <;> cases a.bits.1 <;> cases b.bits.1 <;>
      cases val (trim a) t <;> cases val (trim b) t <;> rfl

/-- Select one coordinate in a word of length n+1. -/
inductive Pos : Nat → Type
  | first : Pos n
  | next : Pos n → Pos (n+1)

def insert : {n : Nat} → Pos n → Bool → W n → W (n+1)
  | _, .first, b, v => (b,v)
  | _, .next i, b, v => (v.1,insert i b v.2)

def consF (b : Bool) (f : Form n) : Form (n+1) := ⟨(b,f.bits), f.const⟩

theorem val_consF (b v : Bool) (f : Form n) (w : W n) :
    val (consF b f) (v,w) = xor (b && v) (val f w) := val_cons ..

def splitF : {n : Nat} → Pos n → Form (n+1) → Bool × Form n
  | _, .first, f => (f.bits.1, trim f)
  | _, .next i, f =>
    let p := splitF i (trim f)
    (p.1,consF f.bits.1 p.2)

theorem splitF_eval (i : Pos n) (f : Form (n+1)) (b : Bool) (w : W n) :
    val f (insert i b w) = xor ((splitF i f).1 && b) (val (splitF i f).2 w) := by
  induction i with
  | first => exact val_cons ..
  | next i ih =>
    rcases w with ⟨v,w⟩
    simp only [insert, splitF, val_consF, val_cons, ih]
    exact Bool.xor_left_comm ..

def splitQ : {n : Nat} → Pos n → Quad (n+1) → Form n × Quad n
  | _, .first, q => q
  | _, .next i, q =>
    let p := splitF i q.1
    let z := splitQ i q.2
    (consF p.1 z.1,(p.2,z.2))

theorem splitQ_eval (i : Pos n) (q : Quad (n+1)) (b : Bool) (w : W n) :
    evalQ (n+1) q (insert i b w) =
      xor (b && val (splitQ i q).1 w) (evalQ n (splitQ i q).2 w) := by
  induction i with
  | first => rfl
  | @next n i ih =>
    rcases w with ⟨v,w⟩
    change xor (v && val q.1 (insert i b w)) (evalQ (n+1) q.2 (insert i b w)) =
      xor (b && val (consF (splitF i q.1).1 (splitQ i q.2).1) (v,w))
          (xor (v && val (splitF i q.1).2 w) (evalQ n (splitQ i q.2).2 w))
    rw [splitF_eval, ih, val_consF]
    cases v <;> cases b <;> cases (splitF i q.1).1 <;> cases val (splitF i q.1).2 w <;>
      cases val (splitQ i q.2).1 w <;> cases evalQ n (splitQ i q.2).2 w <;> rfl

def pick : {n : Nat} → W (n+1) → Option (Pos n)
  | 0, w => if w.1 then some .first else none
  | _+1, w => if w.1 then some .first else (pick w.2).map Pos.next

theorem pick_none (f : Form (n+1)) (h : pick f.bits = none) : f.bits = zero (n+1) := by
  induction n with
  | zero =>
    rcases f with ⟨⟨a, u⟩, c⟩; cases u; cases a <;> simp_all [pick, zero]
  | succ n ih =>
    cases e : f.bits.1 with
    | true => simp [pick,e] at h
    | false =>
      have hn : pick (trim f).bits = none := by
        cases hp : pick (trim f).bits with
        | none => rfl
        | some i => change pick f.bits.2 = some i at hp; simp [pick,e,hp] at h
      exact Prod.ext e (ih (trim f) hn)

theorem pick_some (f : Form (n+1)) (i : Pos n) (h : pick f.bits = some i) :
    (splitF i f).1 = true := by
  induction n with
  | zero =>
    cases e : f.bits.1 <;> simp [pick,e] at h
    subst i; exact e
  | succ n ih =>
    cases e : f.bits.1 with
    | true => simp [pick,e] at h; subst i; exact e
    | false =>
      cases p : pick (trim f).bits with
      | none => change pick f.bits.2 = none at p; simp [pick,e,p] at h
      | some j =>
        change pick f.bits.2 = some j at p
        simp [pick,e,p] at h
        subst i
        exact ih (trim f) j p

/-- The reference sum is for the specification only. -/
def total : (n : Nat) → (W n → Int) → Int
  | 0, f => f ()
  | n+1, f => total n (fun w => f (false,w)) + total n (fun w => f (true,w))

theorem total_add (n : Nat) (f g : W n → Int) :
    total n (fun w => f w + g w) = total n f + total n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [total, ih]
    omega

theorem total_two (n : Nat) (f : W n → Int) :
    total n (fun w => 2 * f w) = 2 * total n f := by
  have dup (z : Int) : 2*z = z+z := by omega
  simpa only [dup] using total_add n f f

theorem total_zero (n : Nat) : total n (fun _ => 0) = 0 := by
  induction n <;> simp [total, *]

theorem pivot_sum (i : Pos n) (f : W (n+1) → Int) :
    total (n+1) f = total n (fun w => f (insert i false w) + f (insert i true w)) := by
  induction i with
  | first => exact (total_add ..).symm
  | @next n i ih =>
    change total (n+1) (fun w => f (false,w)) + total (n+1) (fun w => f (true,w)) = _
    rw [ih (fun w => f (false,w)), ih (fun w => f (true,w))]
    rfl

def sign (b : Bool) : Int := if b then -1 else 1

/-- Sum out x,y in xy + x*A + y*B + C. No restriction on A,B,C here. -/
theorem pair_identity (a b c : Bool) :
    sign c + sign (xor a c) + (sign (xor b c) + sign (xor (!a) (xor b c))) =
      2 * sign (xor (a && b) c) := by
  cases a <;> cases b <;> cases c <;> decide

def bias (n : Nat) (q : Quad n) := total n (fun w => sign (evalQ n q w))

theorem pair_bias (q : Quad (n+2)) (i : Pos n) (h : (splitF i q.1).1 = true) :
    bias (n+2) q = 2 * bias n
      (addQ n (times n (splitF i q.1).2 (splitQ i q.2).1) (splitQ i q.2).2) := by
  unfold bias
  rw [total]
  change total (n+1) (fun w => sign (xor (false && val q.1 w) (evalQ (n+1) q.2 w))) +
         total (n+1) (fun w => sign (xor (true && val q.1 w) (evalQ (n+1) q.2 w))) = _
  simp only [Bool.false_and, Bool.false_xor, Bool.true_and]
  rw [← total_add, pivot_sum i, ← total_two]
  congr 1
  funext w
  simp only [splitF_eval, splitQ_eval, h, eval_addQ, eval_times, Bool.and_false,
    Bool.and_true, Bool.true_and, Bool.false_and, Bool.false_xor, Bool.true_xor]
  exact pair_identity ..

theorem unary_bias (q : Quad (n+1)) (h : q.1.bits = zero n) :
    bias (n+1) q = if q.1.const then 0 else 2 * bias n q.2 := by
  unfold bias
  rw [total]
  change total n (fun w => sign (xor (false && val q.1 w) (evalQ n q.2 w))) +
    total n (fun w => sign (xor (true && val q.1 w) (evalQ n q.2 w))) = _
  simp only [Bool.false_and, Bool.false_xor, Bool.true_and]
  rw [← total_add]
  have eq (w : W n) : val q.1 w = q.1.const := by simp [val,h,dot_zero]
  simp only [eq]
  cases e : q.1.const with
  | false => simp [Bool.false_xor, total_add]; omega
  | true =>
    have opp (b : Bool) : sign b + sign (!b) = 0 := by cases b <;> decide
    simp [opp, total_zero]

/-- Executable compact signed counter. The reduction makes one recursive call. -/
def countBias : (n : Nat) → Quad n → Int
  | 0, q => sign q
  | 1, q => if q.1.const then 0 else 2 * sign q.2
  | n+2, q =>
    match pick q.1.bits with
    | none => if q.1.const then 0 else 2 * countBias (n+1) q.2
    | some i =>
      let a := (splitF i q.1).2
      let (b,c) := splitQ i q.2
      2 * countBias n (addQ n (times n a b) c)

theorem countBias_exact : (n : Nat) → (q : Quad n) → countBias n q = bias n q
  | 0, _ => rfl
  | 1, q => by
    have := unary_bias (n := 0) q (by cases q.1.bits; rfl)
    exact this.symm
  | n+2, q => by
    cases e : pick q.1.bits with
    | none => rw [unary_bias q (pick_none q.1 e)]; simp [countBias,e,countBias_exact (n+1)]
    | some i => rw [pair_bias q i (pick_some q.1 i e)]; simp [countBias,e,countBias_exact n]

#print axioms countBias_exact
end CandyKnots

namespace CandyKnots
open FrozenShells

theorem twin_knots (x y : Bool) : xor (x && y) (x && !y) = x := by
  cases x <;> cases y <;> rfl

theorem output_consequence {x y z₁ z₂ : Bool} (h₁ : z₁ = (x && y))
    (h₂ : z₂ = (x && !y)) : xor z₁ z₂ = x := by rw [h₁,h₂,twin_knots]

/-- The genuine products xy and x(1+y) cannot both equal one. Their lifted
    equations t=1 and x+t=1 do have the spurious solution x=0, t=1. -/
theorem lifted_false_positive :
    (∃ x t : Bool, t = true ∧ xor x t = true) ∧
    ¬∃ x y : Bool, (x && y) = true ∧ (x && !y) = true := by decide

def extendW (n : Nat) : (d : Nat) → (Nat → Bool) → W n → W (n+d)
  | 0, _, w => w
  | d+1, f, w => (f d, extendW n d f w)

theorem extension_lifts (n d : Nat) (P : W (n+d) → Prop) (f : Nat → Bool) (w : W n)
    (h : P (extendW n d f w)) : hasLift n d P w := by
  induction d with
  | zero => exact h
  | succ d ih => exact ih _ ⟨f d,h⟩

/-- The feature evaluator can supply genuine products or any other derived
    bits. Projecting them as free coordinates preserves every genuine model. -/
theorem super_candy_projection (n d : Nat) (rows : List (Tracked k (n+d)))
    (features : W n → Nat → Bool) (w : W n)
    (h : Sat rows (extendW n d (features w) w)) : Sat (project n d rows) w :=
  (project_exact ..).mpr (extension_lifts n d _ _ _ h)

def freezeHub (p : Bool) (tail arm : Form n) := plus tail (gateF p arm)

theorem frozen_hub_eval {w : W n} (hub arm tail : Form n) (p : Bool) (h : val hub w = p) :
    xor (val tail w) (val hub w && val arm w) = val (freezeHub p tail arm) w := by
  simp [freezeHub, val_plus, val_gate, h]

/-- One parity decision linearizes an arbitrary number of rows sharing one
    affine factor. Each row contains (tail,arm). -/
theorem parity_hub_system (hub : Form n) (rows : List (Form n × Form n)) :
    (∃ w : W n, ∀ r ∈ rows, xor (val r.1 w) (val hub w && val r.2 w) = false) ↔
    ∃ p : Bool, ∃ w : W n, val hub w = p ∧ ∀ r ∈ rows, val (freezeHub p r.1 r.2) w = false := by
  constructor
  · intro ⟨w,h⟩
    exact ⟨val hub w,w,rfl,fun r hr => (frozen_hub_eval hub r.2 r.1 _ rfl).symm.trans (h r hr)⟩
  · intro ⟨p,w,hp,h⟩
    exact ⟨w,fun r hr => (frozen_hub_eval _ _ _ _ hp).trans (h r hr)⟩

def signMul (a b : Bool) : sign (xor a b) = sign a * sign b := by
  cases a <;> cases b <;> decide

def origin : (n : Nat) → Quad n
  | 0 => false
  | n+1 => (nilForm n,origin n)

theorem eval_origin (n : Nat) (w : W n) : evalQ n (origin n) w = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [origin,evalQ,ih,val,nilForm,dot_zero]

/-- Enumerate subsets of the equations, never assignments to variables. -/
def spectrum (q : Quad n) : List (Quad n) → Int
  | [] => countBias n q
  | p :: ps => spectrum q ps + spectrum (addQ n q p) ps

def passes (ps : List (Quad n)) (w : W n) := ps.all (fun p => !evalQ n p w)
def mass (q : Quad n) (ps : List (Quad n)) (w : W n) : Int :=
  if passes ps w then sign (evalQ n q w) * 2^ps.length else 0

theorem spectrum_exact (ps : List (Quad n)) (q : Quad n) :
    spectrum q ps = total n (mass q ps) := by
  induction ps generalizing q with
  | nil =>
    rw [spectrum,countBias_exact]
    unfold bias
    apply congrArg (total n)
    funext w
    simp [mass, passes]
  | cons p ps ih =>
    rw [spectrum,ih,ih,← total_add]
    congr 1
    funext w
    simp only [mass,passes,List.all_cons,List.length_cons,eval_addQ]
    have combine (a p q : Bool) (v : Int) :
        (if a then sign q * v else 0) + (if a then sign (xor q p) * v else 0) =
        (if (!p && a) then sign q * (v*2) else 0) := by
      cases a <;> cases p <;> cases q <;> simp [sign] <;> omega
    rw [Int.pow_succ]
    exact combine _ _ _ _

theorem total_scale (n : Nat) (z : Int) (f : W n → Int) :
    total n (fun w => z * f w) = z * total n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total,ih,Int.mul_add]

def modelCount (ps : List (Quad n)) := total n (fun w => if passes ps w then 1 else 0)

theorem scaled_model_count (n : Nat) (ps : List (Quad n)) :
    spectrum (origin n) ps = (2:Int)^ps.length * modelCount ps := by
  rw [spectrum_exact,modelCount,← total_scale]
  congr 1
  funext w
  cases h : passes ps w <;> simp [mass, eval_origin, sign, h]

/-- n disjoint products inside one parity equation. -/
def dim : Nat → Nat
  | 0 => 0
  | r+1 => dim r + 2

theorem dim_eq (r : Nat) : dim r = 2*r := by
  induction r <;> simp [dim, *, Nat.mul_succ]

def disjoint : (r : Nat) → Quad (dim r)
  | 0 => false
  | r+1 => ((consF true (nilForm (dim r))), (nilForm (dim r),disjoint r))

theorem disjoint_bias (r : Nat) : countBias (dim r) (disjoint r) = (2:Int)^r := by
  rw [countBias_exact]
  induction r with
  | zero => rfl
  | succ r ih =>
    have count_pair (q : Quad (dim r)) :
        bias (dim r+2) (consF true (nilForm (dim r)),(nilForm (dim r),q)) = 2*bias (dim r) q := by
      rw [pair_bias _ .first (by rfl)]
      unfold bias
      apply congrArg (fun z : Int => 2*z)
      apply congrArg (total (dim r))
      funext w
      simp [splitF,splitQ,consF,trim,eval_addQ,eval_times,val,nilForm,dot_zero]
    simpa only [disjoint,dim,Int.pow_succ,Int.mul_comm (a := (2:Int)^r)] using (count_pair (disjoint r)).trans (congrArg (2 * ·) ih)

#print axioms super_candy_projection
#print axioms lifted_false_positive
#print axioms parity_hub_system
#print axioms scaled_model_count
#print axioms disjoint_bias
end CandyKnots
