import SilentRoom

/-! Divisibility of the unnormalized signed sum of a bounded-degree Boolean
polynomial. A mask specifies a squarefree monomial in the input coordinates. -/
namespace DegreeDivisibility
open FrozenShells CandyKnots CollisionLaw SilentRoom

def monomial : (n : Nat) → W n → W n → Bool
  | 0, _, _ => true
  | n+1, p, x => (!p.1 || x.1) && monomial n p.2 x.2

def evalANF {n : Nat} : List (W n) → W n → Bool
  | [], _ => false
  | p :: ps, x => xor (monomial n p x) (evalANF ps x)

def DegreeLE {n : Nat} (k : Nat) (f : W n → Bool) : Prop :=
  ∃ ps : List (W n), (∀ p ∈ ps, weight n p ≤ k) ∧ ∀ x, f x = evalANF ps x

theorem degree_mono {f : W n → Bool} (hf : DegreeLE a f) (h : a ≤ b) : DegreeLE b f := by
  obtain ⟨ps, hp, he⟩ := hf
  exact ⟨ps, fun p hmem => Nat.le_trans (hp p hmem) h, he⟩

theorem degree_monomial {p : W n} (h : weight n p ≤ k) :
    DegreeLE k (monomial n p) := by
  exact ⟨[p], by simpa using h, by simp [evalANF]⟩

theorem degree_false (n k : Nat) : DegreeLE k (fun _ : W n => false) :=
  ⟨[], by simp, fun _ => rfl⟩

theorem monomial_zero (n : Nat) (x : W n) : monomial n (zero n) x = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zero, monomial, ih]

theorem degree_true (n k : Nat) : DegreeLE k (fun _ : W n => true) := by
  have e := degree_monomial (p := zero n) (k := k) (by simp [weight_zero])
  simpa only [show monomial n (zero n) = fun _ => true from funext (monomial_zero n)] using e

theorem eval_append (ps qs : List (W n)) (x : W n) :
    evalANF (ps ++ qs) x = xor (evalANF ps x) (evalANF qs x) := by
  induction ps with
  | nil => simp [evalANF]
  | cons p ps ih => simp [evalANF, ih, Bool.xor_assoc]

theorem degree_xor {f g : W n → Bool} (hf : DegreeLE k f) (hg : DegreeLE k g) :
    DegreeLE k (fun x => xor (f x) (g x)) := by
  obtain ⟨ps, hp, ef⟩ := hf
  obtain ⟨qs, hq, eg⟩ := hg
  exact ⟨ps ++ qs, fun p h => (List.mem_append.mp h).elim (hp p) (hq p),
    fun x => by simp only [ef, eg, eval_append]⟩

def join : (n : Nat) → W n → W n → W n
  | 0, _, _ => ()
  | n+1, p, q => (p.1 || q.1, join n p.2 q.2)

theorem weight_join (n : Nat) (p q : W n) :
    weight n (join n p q) ≤ weight n p + weight n q := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rcases p with ⟨a,p⟩
    rcases q with ⟨b,q⟩
    have h := ih p q
    cases a <;> cases b <;> simp [weight, join] <;> omega

theorem monomial_join (n : Nat) (p q x : W n) :
    monomial n (join n p q) x = (monomial n p x && monomial n q x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨a,p⟩
    rcases q with ⟨b,q⟩
    rcases x with ⟨c,x⟩
    cases a <;> cases b <;> cases c <;> simp [monomial, join, ih]

private theorem eval_join_map (p : W n) (qs : List (W n)) (x : W n) :
    evalANF (qs.map (join n p)) x = (monomial n p x && evalANF qs x) := by
  induction qs with
  | nil => simp [evalANF]
  | cons q qs ih =>
    simp only [List.map_cons, evalANF, monomial_join, ih]
    cases monomial n p x <;> simp

private theorem degree_times_monomial {p : W n} (hp : weight n p ≤ i)
    (qs : List (W n)) (hq : ∀ q ∈ qs, weight n q ≤ j) :
    DegreeLE (i+j) (fun x => monomial n p x && evalANF qs x) := by
  refine ⟨qs.map (join n p), ?_, fun x => (eval_join_map p qs x).symm⟩
  intro m hm
  obtain ⟨q,hmem,rfl⟩ := List.mem_map.mp hm
  exact Nat.le_trans (weight_join n p q) (Nat.add_le_add hp (hq q hmem))

theorem degree_and {f g : W n → Bool} (hf : DegreeLE i f) (hg : DegreeLE j g) :
    DegreeLE (i+j) (fun x => f x && g x) := by
  obtain ⟨ps,hp,ef⟩ := hf
  obtain ⟨qs,hq,eg⟩ := hg
  rw [funext ef, funext eg]
  clear ef eg f g
  induction ps with
  | nil => simpa [evalANF] using degree_false n (i+j)
  | cons p ps ih =>
    have tail := ih (fun m h => hp m (List.mem_cons_of_mem _ h))
    have head := degree_times_monomial (hp p (by simp)) qs hq
    have e (x : W n) : (evalANF (p :: ps) x && evalANF qs x) =
        xor (monomial n p x && evalANF qs x) (evalANF ps x && evalANF qs x) := by
      cases h : evalANF qs x <;> simp [evalANF, h]
    exact (funext e) ▸ degree_xor head tail

private def free : (n : Nat) → W n → Nat
  | 0, _ => 0
  | n+1, p => free n p.2 + if p.1 then 0 else 1

private theorem weight_free (n : Nat) (p : W n) : weight n p + free n p = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨b,p⟩
    have h := ih p
    cases b <;> simp [weight, free] <;> omega

private def ind (b : Bool) : Int := if b then 1 else 0

private theorem many_succ (s : Nat) : many (s+1) = many s * 2 := Int.pow_succ _ _

private theorem mass_monomial (n : Nat) (p : W n) :
    total n (fun x => ind (monomial n p x)) = many (free n p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨b,p⟩
    cases b <;> simp [total, free, monomial, ih, many_succ, show ind false = 0 from rfl, total_zero] <;> omega

private theorem ceil_le {k n u : Nat} (hk : 0 < k) (hn : n ≤ u*k) :
    (n+k-1)/k ≤ u := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hk).2
  rw [Nat.succ_mul]
  omega

private theorem many_add (a b : Nat) : many (a+b) = many a * many b := by
  induction b with
  | zero => simp [many]
  | succ b ih => rw [Nat.add_succ, many_succ, ih, many_succ, Int.mul_assoc]

private theorem many_dvd {a b : Nat} (h : a ≤ b) : many a ∣ many b := by
  refine ⟨many (b-a), ?_⟩
  rw [← many_add]
  congr 1
  omega

private def partialSum {n : Nat} (u : W n) (ps : List (W n)) : Int :=
  total n (fun x => ind (monomial n u x) * sign (evalANF ps x))

private theorem partial_cons (u p : W n) (ps : List (W n)) :
    partialSum u (p :: ps) = partialSum u ps - 2 * partialSum (join n u p) ps := by
  have term (a b c : Bool) :
      ind a * sign (xor b c) = ind a * sign c - 2 * (ind (a && b) * sign c) := by
    cases a <;> cases b <;> cases c <;> rfl
  simp only [partialSum, evalANF, term, monomial_join, total_sub, total_scale]

/-- Selecting s monomials introduces a factor 2^s.  Their union covers at most
s*k coordinates, and each still-free coordinate contributes another factor 2. -/
private theorem partial_dvd (hk : 0 < k) (ps : List (W n))
    (hp : ∀ p ∈ ps, weight n p ≤ k) (s : Nat) (u : W n) (hu : weight n u ≤ s*k) :
    many ((n+k-1)/k) ∣ many s * partialSum u ps := by
  induction ps generalizing s u with
  | nil =>
    have hfree : free n u ≤ free n u * k := by
      simpa using Nat.mul_le_mul_left (free n u) (show 1 ≤ k from hk)
    have hbound : n ≤ (s + free n u) * k := by
      rw [Nat.add_mul]
      have h := weight_free n u
      omega
    have he : many s * partialSum u [] = many (s+free n u) := by
      simp only [partialSum, evalANF, show sign false = 1 from rfl, Int.mul_one, mass_monomial]
      exact (many_add ..).symm
    rw [he]
    exact many_dvd (ceil_le hk hbound)
  | cons p ps ih =>
    have htail : ∀ q ∈ ps, weight n q ≤ k := fun q h => hp q (List.mem_cons_of_mem _ h)
    have hj : weight n (join n u p) ≤ (s+1)*k := by
      rw [Nat.succ_mul]
      exact Nat.le_trans (weight_join n u p) (Nat.add_le_add hu (hp p (by simp)))
    have h1 := ih htail s u hu
    have h2 := ih htail (s+1) (join n u p) hj
    rw [partial_cons, Int.mul_sub, ←Int.mul_assoc, ←many_succ]
    exact Int.dvd_sub h1 h2

/-- Every Walsh signed sum of a scalar degree-k Boolean polynomial has the
2-adic divisibility 2^ceil(n/k). -/
theorem mceliece_divisibility {n k : Nat} (hk : 0 < k) {f : W n → Bool} (hf : DegreeLE k f) :
    many ((n+k-1)/k) ∣ total n (fun x => sign (f x)) := by
  obtain ⟨ps, hp, e⟩ := hf
  have h := partial_dvd hk ps hp 0 (zero n) (by simp [weight_zero])
  simpa only [partialSum, monomial_zero, show ind true = 1 from rfl, Int.one_mul,
    show many 0 = 1 from rfl, e] using h


/-- Every output bit has an algebraic normal form of degree at most k. -/
def MapDegree {n : Nat} (k : Nat) : (m : Nat) → (W n → W m) → Prop
  | 0, _ => True
  | m+1, Q => DegreeLE k (fun x => (Q x).1) ∧ MapDegree k m (fun x => (Q x).2)

theorem mapDegree_mono (m : Nat) (Q : W n → W m) (hf : MapDegree a m Q) (h : a ≤ b) :
    MapDegree b m Q := by
  induction m with
  | zero => trivial
  | succ m ih => exact ⟨degree_mono hf.1 h, ih _ hf.2⟩

theorem degree_dot (m : Nat) (Q : W n → W m) (hq : MapDegree k m Q) (c : W m) :
    DegreeLE k (fun x => dot m c (Q x)) := by
  induction m with
  | zero => exact degree_false n k
  | succ m ih =>
    have tail := ih _ hq.2 c.2
    cases h : c.1
    · simpa only [dot,h,Bool.false_and,Bool.false_xor] using tail
    · simpa only [dot,h,Bool.true_and] using degree_xor hq.1 tail

theorem walsh_dvd (hk : 0 < k) (Q : W n → W m) (hq : MapDegree k m Q) (c : W m) :
    many ((n+k-1)/k) ∣ walsh Q c :=
  mceliece_divisibility hk (degree_dot m Q hq c)

private theorem lift_tail {f : W n → Bool} (hf : DegreeLE k f) :
    DegreeLE k (fun x : W (n+1) => f x.2) := by
  obtain ⟨ps,hp,he⟩ := hf
  let pad := fun p : W n => ((false,p) : W (n+1))
  refine ⟨ps.map pad, ?_, ?_⟩
  · intro q hq
    obtain ⟨p,hm,rfl⟩ := List.mem_map.mp hq
    simpa [weight,pad] using hp p hm
  · intro x
    change f x.2 = _
    rw [he]
    clear he hp f
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.map_cons,evalANF]
      exact congrArg (xor (monomial n p x.2) ·) ih

private theorem lift_map_tail (m : Nat) (Q : W n → W m) (hq : MapDegree k m Q) :
    MapDegree k m (fun x : W (n+1) => Q x.2) := by
  induction m with
  | zero => trivial
  | succ m ih => exact ⟨lift_tail hq.1, ih _ hq.2⟩

theorem identity_degree (n : Nat) : MapDegree 1 n id := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hd := degree_monomial (n := n+1) (p := (true,zero n)) (k := 1)
      (by simp [weight,weight_zero])
    refine ⟨?_, lift_map_tail n id ih⟩
    simpa [monomial,monomial_zero] using hd

#print axioms walsh_dvd
#print axioms mceliece_divisibility
end DegreeDivisibility
