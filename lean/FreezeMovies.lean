import FrozenShells

namespace FreezeMovies
open FrozenShells

def parity : (n : Nat) → W n → Bool
  | 0, _ => false
  | n+1, w => xor w.1 (parity n w.2)

/-- Every parity-b word of positive length is uniquely determined by its tail. -/
def pack (b : Bool) (u : W n) : W (n+1) := (xor b (parity n u), u)

theorem parity_pack (b : Bool) (u : W n) : parity (n+1) (pack b u) = b := by
  simp only [parity, pack]
  cases b <;> cases parity n u <;> rfl

theorem pack_tail {w : W (n+1)} {b : Bool} (hb : parity (n+1) w = b) : pack b w.2 = w := by
  rcases w with ⟨a,w⟩
  simp only [pack, parity] at *
  cases a <;> cases e : parity n w <;> simp_all

def worlds : (n : Nat) → List (W n)
  | 0 => [()]
  | n+1 => (worlds n).map (fun w => (false,w)) ++ (worlds n).map (fun w => (true,w))

theorem all_worlds (n : Nat) (w : W n) : w ∈ worlds n := by
  induction n with
  | zero => cases w; simp [worlds]
  | succ n ih =>
    rcases w with ⟨b,w⟩
    cases b with
    | false => exact List.mem_append_left _ (List.mem_map.mpr ⟨w,ih w,rfl⟩)
    | true => exact List.mem_append_right _ (List.mem_map.mpr ⟨w,ih w,rfl⟩)

theorem world_count (n : Nat) : (worlds n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [worlds, ih, Nat.pow_succ, Nat.mul_two]

theorem worlds_unique (n : Nat) : (worlds n).Nodup := by
  induction n with
  | zero => simp [worlds]
  | succ n ih =>
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_map.mpr (ih.imp (fun ne eq => ne (congrArg Prod.snd eq))),
            List.pairwise_map.mpr (ih.imp (fun ne eq => ne (congrArg Prod.snd eq))), ?_⟩
    intro a ha b hb eq
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hb
    exact Bool.noConfusion (congrArg Prod.fst eq)

def parityWords (n : Nat) (b : Bool) := (worlds n).map (pack b)

theorem parity_words (n : Nat) (b : Bool) :
    (parityWords n b).length = 2^n ∧ (parityWords n b).Nodup ∧
      ∀ w : W (n+1), w ∈ parityWords n b ↔ parity (n+1) w = b := by
  refine ⟨by simp [parityWords, world_count], ?_, ?_⟩
  · exact List.pairwise_map.mpr ((worlds_unique n).imp (fun ne eq => ne (congrArg Prod.snd eq)))
  · intro w
    constructor
    · intro hw
      obtain ⟨z,_,rfl⟩ := List.mem_map.mp hw
      exact parity_pack b z
    · intro h
      exact List.mem_map.mpr ⟨w.2, all_worlds _ _, pack_tail h⟩

/-- Freeze after choosing x. Its remaining private word u must copy x. -/
def residual (n : Nat) (x u : W n) := x = u ∧ parity n u = false

theorem distinct_live (n : Nat) {x y : W n} (hx : parity n x = false) (hne : x ≠ y) :
    ∃ u, residual n x u ∧ ¬residual n y u :=
  ⟨x, ⟨rfl,hx⟩, fun h => hne h.1.symm⟩

theorem frontier (n : Nat) :
    let xs := parityWords n false
    xs.length = 2^n ∧ xs.Nodup ∧
    (∀ x ∈ xs, ∃ u, residual (n+1) x u) ∧
    (∀ x, (∃ u, residual (n+1) x u) → x ∈ xs) ∧
    (∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → ∃ u, residual (n+1) x u ∧ ¬residual (n+1) y u) := by
  obtain ⟨len,uniq,iff⟩ := parity_words n false
  refine ⟨len,uniq,fun x hx => ⟨x,rfl,(iff x).mp hx⟩,?_,?_⟩
  · intro x hx
    obtain ⟨u, hu⟩ := hx
    exact (iff x).mpr (hu.1 ▸ hu.2)
  · intro x hx y _ ne; exact distinct_live _ ((iff x).mp hx) ne

/-- An abstract suffix computes a signature. Two demands can be merged
    precisely if equal or both impossible for every remaining suffix. -/
theorem freeze_signature {α β : Type} (suffix : α → β) (a b : β) :
    (∀ u, (suffix u = a ↔ suffix u = b)) ↔
    a = b ∨ ((∀ u, suffix u ≠ a) ∧ (∀ u, suffix u ≠ b)) := by
  constructor
  · intro h
    by_cases eq : a = b
    · exact Or.inl eq
    · exact Or.inr ⟨fun u hu => eq (hu.symm.trans ((h u).mp hu)),
                    fun u hu => eq (((h u).mpr hu).symm.trans hu)⟩
  · intro h u
    rcases h with rfl | ⟨ha,hb⟩
    · rfl
    · exact ⟨fun e => False.elim (ha u e), fun e => False.elim (hb u e)⟩

/-- With shared x and private copies u,v, the two projected shells demand
    opposite values of one parity. -/
theorem copy_projection (n : Nat) (b : Bool) (x : W n) :
    (∃ u : W n, x = u ∧ parity n u = b) ↔ parity n x = b := by
  constructor
  · intro h
    obtain ⟨u,eq,hu⟩ := h
    exact eq ▸ hu
  · intro h; exact ⟨x,rfl,h⟩

theorem no_common_copy (n : Nat) (x : W n) :
    ¬((∃ u : W n, x = u ∧ parity n u = false) ∧
      (∃ v : W n, x = v ∧ parity n v = true)) := by
  rw [copy_projection, copy_projection]
  cases parity n x <;> simp

/-- A poison pattern is a partial assignment. An ordinary non-tautological
    clause rejects exactly one such pattern, with free positions as wildcards. -/
def Pattern : Nat → Type
  | 0 => Unit
  | n+1 => Option Bool × Pattern n

def fits : (n : Nat) → Pattern n → W n → Prop
  | 0, _, _ => True
  | n+1, p, w => (∀ b, p.1 = some b → w.1 = b) ∧ fits n p.2 w.2

def fill : (n : Nat) → Pattern n → W n
  | 0, _ => ()
  | n+1, p => (p.1.getD false, fill n p.2)

def fixed : (n : Nat) → Pattern n → Prop
  | 0, _ => True
  | n+1, p => p.1 ≠ none ∧ fixed n p.2

theorem fill_fits (n : Nat) (p : Pattern n) : fits n p (fill n p) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rcases p with ⟨a,p⟩
    cases a <;> simp [fits, fill, ih p]

theorem wildcard (n : Nat) (p : Pattern n) (h : ¬fixed n p) (b : Bool) :
    ∃ w : W n, fits n p w ∧ parity n w = b := by
  induction n generalizing b with
  | zero => exact False.elim (h trivial)
  | succ n ih =>
    rcases p with ⟨a,p⟩
    cases a with
    | none =>
      refine ⟨pack b (fill n p), ?_, parity_pack b _⟩
      simp [fits, pack, fill_fits]
    | some v =>
      obtain ⟨w, hm, eq⟩ := ih p (by simpa [fixed] using h) (xor v b)
      refine ⟨(v,w), ?_, ?_⟩
      · simp [fits, hm]
      · simp only [parity, eq]; cases v <;> cases b <;> rfl

theorem fixed_match (n : Nat) (p : Pattern n) (w : W n) (hf : fixed n p)
    (hm : fits n p w) : fill n p = w := by
  induction n with
  | zero => cases w; rfl
  | succ n ih =>
    rcases p with ⟨a,p⟩
    rcases w with ⟨v,w⟩
    obtain ⟨ha,hp⟩ := hf
    obtain ⟨hv,hw⟩ := hm
    cases a with
    | none => exact False.elim (ha rfl)
    | some b =>
      have eb : v = b := hv b rfl
      simp [fill, ih p w hp hw, eb]

theorem subset_length [DecidableEq α] {xs ys : List α} (hu : xs.Nodup)
    (sub : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh,uniq⟩ := List.nodup_cons.mp hu
    have hx := sub x (by simp)
    have bound := ih uniq (ys := ys.erase x) (fun y hy =>
      (List.mem_erase_of_ne (fun e : y = x => fresh (e ▸ hy))).mpr (sub y (by simp [hy])))
    rw [List.length_erase_of_mem hx] at bound
    have pos : 0 < ys.length := by cases ys <;> simp_all
    simp only [List.length_cons]
    omega

/-- Every cover by ordinary poison patterns, safe for even worlds and
    complete for odd worlds, needs at least 2^n patterns on n+1 bits. -/
theorem poison_lower_bound (n : Nat) (ps : List (Pattern (n+1)))
    (safe : ∀ p ∈ ps, ∀ w, fits (n+1) p w → parity (n+1) w = true)
    (cover : ∀ w, parity (n+1) w = true → ∃ p ∈ ps, fits (n+1) p w) :
    2^n ≤ ps.length := by
  obtain ⟨len,uniq,mem⟩ := parity_words n true
  have sub (w) (hw : w ∈ parityWords n true) : w ∈ ps.map (fill (n+1)) := by
    obtain ⟨p,hp,hm⟩ := cover w ((mem w).mp hw)
    have hf : fixed (n+1) p := by
      apply Classical.byContradiction
      intro h
      obtain ⟨v,hv,ev⟩ := wildcard _ p h false
      have e := safe p hp v hv
      rw [ev] at e
      contradiction
    exact List.mem_map.mpr ⟨p,hp,fixed_match _ p w hf hm⟩
  have h := subset_length uniq sub
  simpa [len] using h

/-- A nonlinear example. Left shell z = x AND y. Right shell z ≠ x AND y. -/
def andShell (w : W 3) := w.2.2.1 = (w.1 && w.2.1)

theorem and_no_affine_separator :
    ¬∃ f : Form 3, (∀ w, andShell w → val f w = false) ∧
                    (∀ w, ¬andShell w → val f w = true) := by
  intro ⟨f,hL,hR⟩
  have h0 := hL (false,false,false,()) rfl
  have h1 := hL (true,false,false,()) rfl
  have h2 := hL (false,true,false,()) rfl
  have h3 := hR (true,true,false,()) (by unfold andShell; decide)
  rcases f with ⟨⟨a,b,c,_⟩,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp [val, dot] at h0 h1 h2 h3

#print axioms frontier
#print axioms freeze_signature
#print axioms no_common_copy
#print axioms poison_lower_bound
#print axioms and_no_affine_separator
end FreezeMovies

namespace FreezeMovies
open FrozenShells

/-- The lower bound counts patterns on the original bits. Introduce running
    parity bits and every local conflict has only three positions. -/
def acceptsTrace : List Bool → Bool → List Bool → Bool → Prop
  | [], initial, [], target => initial = target
  | x :: xs, initial, next :: rest, target =>
      next = xor initial x ∧ acceptsTrace xs next rest target
  | _, _, _, _ => False

def trace (initial : Bool) : List Bool → List Bool
  | [] => []
  | x :: xs => let next := xor initial x; next :: trace next xs

def finalBit (initial : Bool) (xs : List Bool) := xs.foldl xor initial

theorem trace_exact (xs : List Bool) (initial target : Bool) (states : List Bool) :
    acceptsTrace xs initial states target ↔
      states = trace initial xs ∧ finalBit initial xs = target := by
  induction xs generalizing initial states with
  | nil => cases states <;> simp [acceptsTrace, trace, finalBit]
  | cons x xs ih =>
    cases states with
    | nil => simp [acceptsTrace, trace]
    | cons next rest =>
      simp only [acceptsTrace, trace, List.cons.injEq, finalBit, List.foldl_cons]
      rw [ih]
      constructor
      · intro ⟨e,he,endEq⟩
        subst next
        exact ⟨⟨rfl, he⟩, endEq⟩
      · intro ⟨⟨e,he⟩,endEq⟩
        subst next
        exact ⟨rfl, he, endEq⟩

def localPoison : List (Bool × Bool × Bool) :=
  [(false,false,true), (false,true,false), (true,false,false), (true,true,true)]

theorem local_poison_exact (p x q : Bool) :
    ((p,x,q) ∉ localPoison) ↔ q = xor p x := by
  cases p <;> cases x <;> cases q <;> decide

/-- A one-bit split restores parity separation for the nonlinear example. -/
def conditionalTest (w : W 3) := xor w.2.2.1 (if w.1 then w.2.1 else false)
theorem conditional_separator (w : W 3) : conditionalTest w = false ↔ andShell w := by
  rcases w with ⟨a,b,c,_⟩
  cases a <;> cases b <;> cases c <;> simp [conditionalTest, andShell]

#print axioms trace_exact
#print axioms local_poison_exact
#print axioms conditional_separator
end FreezeMovies

namespace FreezeMovies

/-- At a freeze just after complete pairs, a live history keeps one bit. -/
def paired (carry : Bool) : List (Bool × Bool) → Bool
  | [] => !carry
  | (x,u) :: rest => (x == u) && paired (xor carry x) rest

def carryAfter (carry : Bool) (pairs : List (Bool × Bool)) :=
  pairs.foldl (fun b p => xor b p.1) carry

theorem paired_freeze (front back : List (Bool × Bool)) (carry : Bool) :
    paired carry (front ++ back) =
      (front.all (fun p => p.1 == p.2) && paired (carryAfter carry front) back) := by
  induction front generalizing carry with
  | nil => simp [carryAfter]
  | cons p ps ih =>
    rcases p with ⟨x,u⟩
    simp [paired, ih, carryAfter, Bool.and_assoc]

/-- The operation for identical footprints depends on what a term represents. -/
theorem witness_vs_xor (survives : Bool) :
    (survives || survives) = survives ∧ xor survives survives = false := by
  cases survives <;> decide

#print axioms paired_freeze
end FreezeMovies

namespace FreezeMovies
open FrozenShells

def pinpoint : (n : Nat) → W n → Pattern n
  | 0, _ => ()
  | n+1, w => (some w.1, pinpoint n w.2)

theorem pinpoint_iff (n : Nat) (v w : W n) : fits n (pinpoint n v) w ↔ w = v := by
  induction n with
  | zero => cases v; cases w; simp [fits]
  | succ n ih =>
    rcases v with ⟨a,v⟩
    rcases w with ⟨b,w⟩
    simp [pinpoint, fits, ih]
    constructor
    · rintro ⟨rfl,rfl⟩; rfl
    · intro e; cases e; exact ⟨rfl,rfl⟩

theorem poison_bound_attained (n : Nat) :
    ∃ ps : List (Pattern (n+1)), ps.length = 2^n ∧
      ∀ w, (∃ p ∈ ps, fits (n+1) p w) ↔ parity (n+1) w = true := by
  let ps := (parityWords n true).map (pinpoint (n+1))
  obtain ⟨len,_,mem⟩ := parity_words n true
  refine ⟨ps, by simp [ps,len], ?_⟩
  intro w
  constructor
  · intro ⟨p,hp,hw⟩
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
    exact (pinpoint_iff _ _ _).mp hw ▸ (mem v).mp hv
  · intro h
    exact ⟨_,List.mem_map.mpr ⟨w,(mem w).mpr h,rfl⟩,(pinpoint_iff _ _ _).mpr rfl⟩

#print axioms poison_bound_attained
end FreezeMovies
