import ChallengeDefs
import Std

namespace FrozenShells

def add : (n : Nat) → W n → W n → W n
  | 0, _, _ => ()
  | n+1, u, v => (xor u.1 v.1, add n u.2 v.2)

theorem dot_add (n : Nat) (a b w : W n) :
    dot n (add n a b) w = xor (dot n a w) (dot n b w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dot, add, ih]
    cases a.1 <;> cases b.1 <;> cases w.1 <;> cases dot n a.2 w.2 <;> cases dot n b.2 w.2 <;> rfl

theorem dot_zero (n : Nat) (w : W n) : dot n (zero n) w = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [dot, zero, ih]

/-- An affine form evaluates to false on the solutions of its equation. -/
structure Form (n : Nat) where
  bits : W n
  const : Bool

def val (f : Form n) (w : W n) := xor (dot n f.bits w) f.const
def plus (a b : Form n) : Form n := ⟨add n a.bits b.bits, xor a.const b.const⟩
def nilForm (n : Nat) : Form n := ⟨zero n, false⟩
def trim (a : Form (n+1)) : Form n := ⟨a.bits.2, a.const⟩

theorem val_plus (a b : Form n) (w : W n) :
    val (plus a b) w = xor (val a w) (val b w) := by
  simp only [val, plus, dot_add]
  cases dot n a.bits w <;> cases dot n b.bits w <;> cases a.const <;> cases b.const <;> rfl

theorem val_cons (a : Form (n+1)) (b : Bool) (w : W n) :
    val a (b,w) = xor (a.bits.1 && b) (val (trim a) w) := by
  simp [val, trim, dot, Bool.xor_assoc]

structure Tracked (k n : Nat) where
  row : Form n
  tag : Form k

def Sat (xs : List (Tracked k n)) (w : W n) :=
  ∀ t ∈ xs, val t.row w = false

def pivot (xs : List (Tracked k (n+1))) :=
  xs.find? (fun t => t.row.bits.1)

def clear (p t : Tracked k (n+1)) : Tracked k n :=
  if t.row.bits.1 then ⟨plus (trim t.row) (trim p.row), plus t.tag p.tag⟩
  else ⟨trim t.row, t.tag⟩

def step (xs : List (Tracked k (n+1))) : List (Tracked k n) :=
  let p := (pivot xs).getD ⟨nilForm _, nilForm _⟩
  xs.map (clear p)

theorem step_count (xs : List (Tracked k (n+1))) : (step xs).length = xs.length := by
  simp [step]

theorem step_some {xs : List (Tracked k (n+1))} {p : Tracked k (n+1)}
    (_hp : pivot xs = some p) (t : Tracked k (n+1)) (w : W n) :
    val (clear p t).row w = val t.row (val (trim p.row) w, w) := by
  rw [val_cons]
  cases e : t.row.bits.1 <;> simp [clear, e, val_plus, Bool.xor_comm]

/-- One elimination step projects the complete shell exactly. -/
theorem step_exact (xs : List (Tracked k (n+1))) (w : W n) :
    Sat (step xs) w ↔ ∃ b : Bool, Sat xs (b,w) := by
  cases hp : pivot xs with
  | none =>
    have hz := List.find?_eq_none.mp hp
    have hzero (t) (ht : t ∈ xs) : t.row.bits.1 = false := by simpa using hz t ht
    constructor
    · intro h
      refine ⟨false, fun t ht => ?_⟩
      have h' := h _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
      simpa [val_cons, clear, hzero t ht] using h'
    · intro ⟨b, hb⟩ t ht
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      simpa [clear, hzero u hu, val_cons] using hb u hu
  | some p =>
    have pp : p ∈ xs := List.mem_of_find?_eq_some hp
    have ph : p.row.bits.1 = true := List.find?_some (p := fun t : Tracked k (n+1) => t.row.bits.1) hp
    constructor
    · intro h
      refine ⟨val (trim p.row) w, fun t ht => ?_⟩
      rw [← step_some hp t w]
      exact h _ (by simp only [step, hp, Option.getD_some]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)
    · intro ⟨b, hb⟩ t ht
      have pe := hb p pp
      rw [val_cons, ph] at pe
      have eb : b = val (trim p.row) w := by
        cases b <;> cases e : val (trim p.row) w <;> simp_all
      simp only [step, hp, Option.getD_some, List.mem_map] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      rw [step_some hp, ← eb]
      exact hb u hu

/-- Iterate a private-variable projection, retaining arbitrary shared bits. -/
def project (n : Nat) : (d : Nat) → List (Tracked k (n+d)) → List (Tracked k n)
  | 0, xs => xs
  | d+1, xs => project n d (step xs)

def hasLift (n : Nat) : (d : Nat) → (W (n+d) → Prop) → W n → Prop
  | 0, P, w => P w
  | d+1, P, w => hasLift n d (fun y => ∃ b : Bool, P (b,y)) w

theorem project_exact (n d : Nat) (xs : List (Tracked k (n+d))) (w : W n) :
    Sat (project n d xs) w ↔ hasLift n d (Sat xs) w := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [project, hasLift, ih]
    have e : Sat (step xs) = (fun y => ∃ b : Bool, Sat xs (b,y)) :=
      funext (fun y => propext (step_exact xs y))
    exact Iff.of_eq (congrArg (fun P => hasLift n d P w) e)

theorem project_count (n d : Nat) (xs : List (Tracked k (n+d))) :
    (project n d xs).length = xs.length := by
  induction d with
  | zero => rfl
  | succ d ih => simp [project, ih, step_count]

def finish : (n : Nat) → List (Tracked k n) → List (Tracked k 0)
  | 0, xs => xs
  | n+1, xs => finish n (step xs)

theorem finish_exact (n : Nat) (xs : List (Tracked k n)) :
    Sat (finish n xs) () ↔ ∃ w, Sat xs w := by
  induction n with
  | zero =>
    constructor
    · intro h; exact ⟨(), h⟩
    · intro ⟨w,h⟩; cases w; exact h
  | succ n ih =>
    rw [finish, ih]
    constructor
    · intro ⟨w, h⟩
      obtain ⟨b, hb⟩ := (step_exact xs w).mp h
      exact ⟨(b,w), hb⟩
    · intro ⟨⟨b,w⟩, h⟩
      exact ⟨w, (step_exact xs w).mpr ⟨b,h⟩⟩

/-- Tags remember the affine contribution of the left shell. Under any
    right-shell model the residual row equals its left tag. -/
def Sound (L R : Prop) (x : W k) (w : W n) (t : Tracked k n) :=
  (L → val t.tag x = false) ∧ (R → val t.row w = val t.tag x)

theorem step_sound (L R : Prop) (x : W k) (b : Bool) (w : W n)
    (xs : List (Tracked k (n+1))) (h : ∀ t ∈ xs, Sound (n := n+1) L R x (b,w) t) :
    ∀ u ∈ step xs, Sound L R x w u := by
  intro u hu
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
  obtain ⟨hl, hr⟩ := h t ht
  cases e : t.row.bits.1 with
  | false =>
    simpa [Sound, clear, e, val_cons] using And.intro hl hr
  | true =>
    cases hp : pivot xs with
    | none => exact False.elim ((List.find?_eq_none.mp hp t ht) e)
    | some p =>
      have ph : p.row.bits.1 = true := List.find?_some (p := fun t : Tracked k (n+1) => t.row.bits.1) hp
      obtain ⟨pl, pr⟩ := h p (List.mem_of_find?_eq_some hp)
      simp only [Sound, hp, Option.getD_some, clear, e, if_true, val_plus]
      constructor
      · intro l
        simp [hl l, pl l]
      · intro r
        rw [← hr r, ← pr r, val_cons, val_cons, e, ph]
        cases b <;> cases val (trim t.row) w <;> cases val (trim p.row) w <;> rfl

theorem finish_sound (L R : Prop) (x : W k) (n : Nat) (w : W n)
    (xs : List (Tracked k n)) (h : ∀ t ∈ xs, Sound L R x w t) :
    ∀ u ∈ finish n xs, Sound (n := 0) L R x () u := by
  induction n with
  | zero => cases w; exact h
  | succ n ih => exact ih w.2 (step xs) (step_sound L R x w.1 w.2 xs h)

def models (fs : List (Form n)) (x : W n) := ∀ f ∈ fs, val f x = false

def joinRows (A B : List (Form n)) : List (Tracked n n) :=
  A.map (fun f => ⟨f,f⟩) ++ B.map (fun f => ⟨f,nilForm n⟩)

theorem join_sat (A B : List (Form n)) (w : W n) :
    Sat (joinRows A B) w ↔ models A w ∧ models B w := by
  constructor
  · intro h
    exact ⟨fun f hf => h ⟨f,f⟩ (List.mem_append_left _ (List.mem_map.mpr ⟨f,hf,rfl⟩)),
           fun f hf => h ⟨f,nilForm n⟩ (List.mem_append_right _ (List.mem_map.mpr ⟨f,hf,rfl⟩))⟩
  · intro ⟨hl,hr⟩ t ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht; exact hl f hf
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht; exact hr f hf

theorem join_sound (A B : List (Form n)) (w : W n) :
    ∀ t ∈ joinRows A B, Sound (models A w) (models B w) w w t := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht
    exact ⟨fun h => h f hf, fun _ => rfl⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht
    have hz : val (nilForm n) w = false := by simp [val, nilForm, dot_zero]
    exact ⟨fun _ => hz, fun h => (h f hf).trans hz.symm⟩

/-- A successful result is the affine form both shells can inspect. -/
def separator (A B : List (Form n)) : Option (Form n) :=
  ((finish n (joinRows A B)).find? (fun t => val (n := 0) t.row ())).map Tracked.tag

theorem separator_none (A B : List (Form n)) :
    separator A B = none ↔ ∃ x, models A x ∧ models B x := by
  have e : ((finish n (joinRows A B)).find? (fun t => val (n := 0) t.row ())) = none ↔
      Sat (finish n (joinRows A B)) () := by simp [List.find?_eq_none, Sat]
  rw [← show (∃ x, Sat (joinRows A B) x) ↔ _ from exists_congr (fun x => join_sat A B x),
      ← finish_exact, ← e]
  unfold separator
  cases (finish n (joinRows A B)).find? (fun t => val (n := 0) t.row ()) <;> simp

theorem separator_sound {A B : List (Form n)} {f : Form n} (h : separator A B = some f) :
    (∀ x, models A x → val f x = false) ∧ (∀ x, models B x → val f x = true) := by
  unfold separator at h
  cases e : (finish n (joinRows A B)).find? (fun t => val (n := 0) t.row ()) with
  | none => simp [e] at h
  | some t =>
    simp [e] at h
    subst f
    have hv : val t.row () = true := List.find?_some (p := fun t : Tracked n 0 => val t.row ()) e
    have inside := List.mem_of_find?_eq_some e
    have ht (x : W n) := finish_sound (models A x) (models B x) x n x _ (join_sound A B x) t inside
    exact ⟨fun x => (ht x).1, fun x hb => ((ht x).2 hb).symm.trans hv⟩

#print axioms project_exact
#print axioms project_count
#print axioms separator_none
#print axioms separator_sound
end FrozenShells
