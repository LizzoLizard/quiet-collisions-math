import MaskRecovery

namespace CollisionCircuit
open FrozenShells CandyKnots FreezeMovies CollisionLaw MaskRecovery

/-- Each affine test is true when its literal is false. -/
structure Clause (n : Nat) where
  first : Form n
  second : Form n
  third : Form n

def passed (c : Clause n) (x : W n) :=
  !(val c.first x && val c.second x && val c.third x)

def width : Nat → Nat
  | 0 => 0
  | k+1 => width k + 3

theorem width_exact (k : Nat) : width k = 3*k := by
  induction k <;> simp [width, *,Nat.mul_succ]

/-- For fixed input x, this is a linear map on wire bits. Read each
    intermediate wire from w and emit its discrepancy from the gate equation. -/
def run (x : W n) : (cs : List (Clause n)) → Bool → W (width cs.length) →
    Bool × W (width cs.length)
  | [], seed, _ => (seed,())
  | c::cs, seed, w =>
    let (u,v,p,tail) := w
    let (last,rest) := run x cs p tail
    (last,(xor u (val c.first x && seed),xor v (val c.second x && u),
      xor p (xor seed (val c.third x && v)),rest))

def wires (cs : List (Clause n)) (x : W n) (w : W (width cs.length+1)) :
    W (width cs.length+1) :=
  let (last,rest) := run x cs w.1 w.2
  (xor w.1 last,rest)

/-- The first coordinates copy x. Every other output is a sum of wire bits and
    products of a wire bit with an affine form in x. -/
def square (cs : List (Clause n)) (w : W n × W (width cs.length+1)) :=
  (w.1,wires cs w.1 w.2)

/-- The unique zero-discrepancy trace once the initial seed is fixed. -/
def trace (x : W n) : (cs : List (Clause n)) → Bool → W (width cs.length)
  | [], _ => ()
  | c::cs, seed =>
    let u := val c.first x && seed
    let v := val c.second x && u
    let p := xor seed (val c.third x && v)
    (u,v,p,trace x cs p)

theorem pass_step (a b c seed : Bool) : xor seed (c && (b && (a && seed))) =
    (seed && !(a && b && c)) := by cases a <;> cases b <;> cases c <;> cases seed <;> rfl

theorem xor_zero (a b : Bool) : xor a b = false ↔ a=b := by cases a <;> cases b <;> decide

theorem trace_spec (x : W n) (cs : List (Clause n)) (seed : Bool) (w : W (width cs.length)) :
    (run x cs seed w).2 = zero (width cs.length) ↔ w = trace x cs seed := by
  induction cs generalizing seed with
  | nil => cases w; simp [run,width,zero,trace]
  | cons c cs ih =>
    rcases w with ⟨u,v,p,tail⟩
    change (xor u _, xor v _, xor p _, (run x cs p tail).2) =
      (false,false,false,zero (width cs.length)) ↔ _
    simp only [Prod.mk.injEq, xor_zero,ih]
    constructor
    · rintro ⟨hu,hv,hp,ht⟩
      subst_vars; rfl
    · intro h
      injection h with hu h
      injection h with hv h
      injection h with hp ht
      subst_vars; simp

theorem trace_last (x : W n) (cs : List (Clause n)) (seed : Bool) :
    (run x cs seed (trace x cs seed)).1 = (seed && cs.all (fun c => passed c x)) := by
  induction cs generalizing seed with
  | nil => simp [trace,run]
  | cons c cs ih =>
    simp [trace,run,ih,pass_step,passed,Bool.and_assoc]

theorem trace_off (x : W n) (cs : List (Clause n)) : trace x cs false = zero (width cs.length) := by
  induction cs <;> simp [trace,zero,width, *]

theorem kernel (cs : List (Clause n)) (x : W n) (seed : Bool) (t : W (width cs.length)) :
    wires cs x (seed,t) = zero _ ↔
      t = trace x cs seed ∧ (seed = false ∨ cs.all (fun c => passed c x) = true) := by
  change (xor seed (run x cs seed t).1,(run x cs seed t).2) =
    (false,zero (width cs.length)) ↔ _
  rw [Prod.mk.injEq,trace_spec]
  constructor
  · rintro ⟨h,rfl⟩
    rw [trace_last] at h
    generalize cs.all (fun c => passed c x) = bit at *
    cases seed <;> cases bit <;> simp_all
  · rintro ⟨rfl,h⟩
    rw [trace_last]
    generalize cs.all (fun c => passed c x) = bit at *
    cases seed <;> cases bit <;> simp_all

theorem gate_linear (a s t u v : Bool) :
    xor (xor u v) (a && (xor s t)) = xor (xor u (a && s)) (xor v (a && t)) := by
  cases a <;> cases s <;> cases t <;> cases u <;> cases v <;> rfl

theorem run_linear (x : W n) (cs : List (Clause n)) (s t : Bool)
    (a b : W (width cs.length)) :
    run x cs (xor s t) (add _ a b) =
      (xor (run x cs s a).1 (run x cs t b).1,add _ (run x cs s a).2 (run x cs t b).2) := by
  induction cs generalizing s t with
  | nil => rfl
  | cons c cs ih =>
    rcases a with ⟨u,v,p,a⟩
    rcases b with ⟨u',v',p',b⟩
    simp only [run,add,ih,gate_linear]
    have rearrange (p q a b : Bool) :
        xor (xor p q) (xor a b) = xor (xor p a) (xor q b) := by
      cases p <;> cases q <;> cases a <;> cases b <;> rfl
    rw [rearrange p p']

theorem wires_linear (cs : List (Clause n)) (x : W n) : additive (wires cs x) := by
  intro a b
  rcases a with ⟨s,a⟩
  rcases b with ⟨t,b⟩
  simp only [wires,add,run_linear]
  generalize (run x cs s a).1 = u
  generalize (run x cs t b).1 = v
  cases s <;> cases t <;> cases u <;> cases v <;> rfl

theorem sum_eq_zero (n : Nat) (a b : W n) : add n a b = zero n ↔ a = b := by
  induction n with
  | zero => cases a; cases b; exact Iff.rfl
  | succ n ih =>
    rcases a with ⟨x,a⟩
    rcases b with ⟨y,b⟩
    change (xor x y,add n a b) = (false,zero n) ↔ (x,a) = (y,b)
    simp only [Prod.mk.injEq,xor_zero,ih]

/-- A 3-CNF has a satisfying assignment exactly when the constructed square MQ
    map has an off-diagonal collision. -/
theorem collision_iff_sat (cs : List (Clause n)) :
    (∃ a b, a ≠ b ∧ square cs a = square cs b) ↔ ∃ x, cs.all (fun c => passed c x) = true := by
  constructor
  · rintro ⟨⟨x,a⟩,⟨y,b⟩,ne,eq⟩
    change (x,wires cs x a) = (y,wires cs y b) at eq
    simp only [Prod.mk.injEq] at eq
    obtain ⟨rfl,e⟩ := eq
    have nonzero : add _ a b ≠ zero _ := fun h => ne (by rw [(sum_eq_zero ..).mp h])
    have ker : wires cs x (add _ a b) = zero _ := by rw [wires_linear cs x a b,e,add_self]
    rcases h : add _ a b with ⟨s,t⟩
    rw [h] at nonzero ker
    obtain ⟨rfl,hk⟩ := (kernel cs x s t).mp ker
    rcases hk with rfl | sat
    · exfalso; apply nonzero; rw [trace_off]; rfl
    · exact ⟨x,sat⟩
  · rintro ⟨x,sat⟩
    refine ⟨(x,zero _),(x,(true,trace x cs true)),?_,?_⟩
    · intro h
      have eq := congrArg (fun w : W n × W (width cs.length+1) => w.2.1) h
      contradiction
    · have z := zero_image (wires cs x) (wires_linear cs x)
      have o := (kernel cs x true (trace x cs true)).mpr ⟨rfl,Or.inr sat⟩
      exact congrArg (fun v => (x,v)) (z.trans o.symm)

/-- Count every ordered pair of full inputs with equal full outputs. -/
def orderedCollisions (cs : List (Clause n)) :=
  let k := width cs.length + 1
  total n (fun x => total k (fun a => total n (fun y => total k (fun b =>
    hits x y * hits (wires cs x a) (wires cs y b)))))

def modelsCount (cs : List (Clause n)) := total n (fun x => if cs.all (fun c => passed c x) then 1 else 0)

theorem kernel_count (cs : List (Clause n)) (x : W n) :
    total (width cs.length+1) (fun w => hits (wires cs x w) (zero _)) =
      1 + (if cs.all (fun c => passed c x) then 1 else 0) := by
  have term (s : Bool) (t : W (width cs.length)) :
      hits (wires cs x (s,t)) (zero _) =
      if s = false ∨ cs.all (fun c => passed c x) = true then hits (trace x cs s) t else 0 := by
    unfold hits
    simp only [kernel]
    by_cases pass : s = false ∨ cs.all (fun c => passed c x) = true
    · simp only [pass,and_true,if_true,eq_comm (a := t)]
    · simp only [pass,and_false,if_false]
  rw [total]
  simp only [term]
  cases h : cs.all (fun c => passed c x) <;> simp [diagonal,total_zero]

theorem collision_count (cs : List (Clause n)) :
    orderedCollisions cs = many (width cs.length+1) * (many n + modelsCount cs) := by
  let k := width cs.length + 1
  have term (x : W n) (a b : W k) :
      hits (wires cs x a) (wires cs x b) = hits (wires cs x (add k a b)) (zero k) := by
    simp only [hits,wires_linear cs x a b,sum_eq_zero]
  have fiber (x : W n) (a : W k) :
      total k (fun b => hits (wires cs x a) (wires cs x b)) =
        1 + (if cs.all (fun c => passed c x) then 1 else 0) := by
    simp only [term]
    rw [sum_shift k a (fun b => hits (wires cs x b) (zero k)),kernel_count]
  change total n (fun x => total k (fun a => total n (fun y => total k (fun b =>
    hits x y * hits (wires cs x a) (wires cs y b))))) = _
  simp only [total_scale,select,fiber,total_const,total_add,Int.mul_one,modelsCount,k]

#print axioms kernel
#print axioms collision_iff_sat
#print axioms collision_count
end CollisionCircuit
