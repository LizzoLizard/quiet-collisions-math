import RingCracks
import DegreeDivisibility

namespace GroupedRing
open FrozenShells CandyKnots CollisionLaw MaskRecovery SilentRoom RingCracks

/-- Prefix a ring word with the copied control wires. -/
def join (l : Nat) : (s : Nat) → W s → W l → W (l+s)
  | 0, _, y => y
  | s+1, t, y => (t.1, join l s t.2 y)

def split (l : Nat) : (s : Nat) → W (l+s) → W s × W l
  | 0, w => ((),w)
  | s+1, w =>
    let (t,y) := split l s w.2
    ((w.1,t),y)

@[simp] theorem split_join (l s : Nat) (t : W s) (y : W l) :
    split l s (join l s t y) = (t,y) := by
  induction s with
  | zero => cases t; rfl
  | succ s ih => cases t; simp [split,join,ih]

@[simp] theorem join_split (l s : Nat) (w : W (l+s)) :
    join l s (split l s w).1 (split l s w).2 = w := by
  induction s with
  | zero => rfl
  | succ s ih => rcases w with ⟨b,w⟩; exact congrArg (b, ·) (ih w)

theorem join_zero (l s : Nat) : join l s (zero s) (zero l) = zero (l+s) := by
  induction s <;> simp [join,zero, *]

theorem join_weight (l s : Nat) (a : W s) (b : W l) :
    weight (l+s) (join l s a b) = weight s a + weight l b := by
  induction s with
  | zero => simp [join,weight]
  | succ s ih =>
    let z := if a.1 then 1 else 0
    change weight (l+s) (join l s a.2 b) + z = (weight s a.2 + z) + weight l b
    rw [ih]; omega

theorem join_chr (l s : Nat) (a t : W s) (b y : W l) :
    chr (join l s a b) (join l s t y) = chr a t * chr b y := by
  induction s with
  | zero => simp [join,chr,dot,sign]
  | succ s ih =>
    change sign (xor (a.1 && t.1) _) = sign (xor (a.1 && t.1) _) * _
    simp only [signMul, ← Int.mul_assoc]
    exact (Int.mul_assoc ..).symm ▸ congrArg (sign (a.1 && t.1) * ·) (ih a.2 t.2)

theorem join_total (l s : Nat) (f : W (l+s) → Int) :
    total (l+s) f = total s (fun t => total l (fun y => f (join l s t y))) := by
  induction s with
  | zero => rfl
  | succ s ih => exact congr (congrArg Int.add (ih (fun w => f (false,w)))) (ih (fun w => f (true,w)))

theorem join_hits (l s : Nat) (a t : W s) (b y : W l) :
    hits (join l s a b) (join l s t y) = hits a t * hits b y := by
  have eq : join l s a b = join l s t y ↔ a = t ∧ b = y := by
    constructor
    · intro h; simpa using congrArg (split l s) h
    · rintro ⟨rfl,rfl⟩; rfl
  simp only [hits,eq]
  by_cases ha : a = t <;> by_cases hb : b = y <;> simp [ha,hb]

/-- Group consecutive controls, allowing empty groups with product one. -/
def controls : (s : Nat) → W s → List Bool
  | 0, _ => []
  | s+1, t => t.1 :: controls s t.2

@[simp] theorem length_controls (s : Nat) (t : W s) : (controls s t).length = s := by
  induction s <;> simp [controls, *]

theorem controls_ones (s : Nat) (t : W s) :
    (controls s t).all id = true ↔ ones s = t := by
  induction s with
  | zero => cases t; simp [controls,ones]
  | succ s ih =>
    rcases t with ⟨b,u⟩
    change (b :: controls s u).all id = true ↔ (true, ones s) = (b,u)
    cases b <;> simp [ih]

def groups (width : Nat) : (l : Nat) → List Bool → W l
  | 0, _ => ()
  | l+1, bs => ((bs.take width).all id, groups width l (bs.drop width))

theorem groups_cover (width l : Nat) (bs : List Bool) (cap : bs.length ≤ l*width) :
    ones l = groups width l bs ↔ bs.all id = true := by
  induction l generalizing bs with
  | zero => cases bs <;> simp_all [ones,groups]
  | succ l ih =>
    have rest : (bs.drop width).length ≤ l * width := by
      rw [List.length_drop]; rw [Nat.succ_mul] at cap; omega
    change ((true, ones l) = (_, _)) ↔ _
    rw [Prod.mk.injEq, ih _ rest]
    have both := congrArg (fun q : List Bool => q.all id) (List.take_append_drop width bs)
    simp only [List.all_append] at both
    rw [← both, Bool.and_eq_true]
    exact and_congr eq_comm Iff.rfl

def enables (width l s : Nat) (t : W s) := groups width l (controls s t)

theorem exceptional (width l s : Nat) (cap : s ≤ l*width) (t : W s) :
    ones l = enables width l s t ↔ ones s = t := by
  unfold enables
  rw [groups_cover _ _ _ (by simpa using cap),controls_ones]

/-- The square map copies its controls and computes the ring discrepancies. -/
def ring (width h s : Nat) (w : W ((h+1)+s)) : W ((h+1)+s) :=
  let (t,x) := split (h+1) s w
  join (h+1) s t (residual h (enables width (h+1) s t) x)

@[simp] theorem ring_join (width h s : Nat) (t : W s) (x : W (h+1)) :
    ring width h s (join (h+1) s t x) =
    join (h+1) s t (residual h (enables width (h+1) s t) x) := by simp [ring]

theorem ring_walsh (width h s : Nat) (cap : s ≤ (h+1)*width) (a : W s) (b : W (h+1)) :
    walsh (ring width h s) (join (h+1) s a b) =
      (if a = zero _ ∧ b = zero _ then many (h+1) * many s else 0) +
      chr a (ones s) * (many (h+1) * hits (ones (h+1)) b) := by
  unfold walsh
  rw [join_total (h+1) s]
  simp only [ring_join,join_chr,total_scale]
  exact reduced_spectrum h s _ (exceptional _ _ _ cap) a b

theorem ring_bucket (width h s : Nat) (t : W s) (y : W (h+1)) :
    histogram (ring width h s) (join (h+1) s t y) =
      histogram (residual h (enables width (h+1) s t)) y := by
  unfold histogram
  rw [join_total (h+1) s]
  simp only [ring_join,join_hits,total_scale]
  have symm (u : W s) : hits u t = hits t u := by simp [hits,eq_comm]
  simp only [symm,select]

theorem grouped_excess (width h s : Nat) (cap : s ≤ (h+1)*width) :
    collisions (ring width h s) - many ((h+1)+s) = many (h+1) := by
  rw [← excess,join_total (h+1) s]
  simp only [deviation,ring_bucket]
  exact (show total s (fun t => total (h+1) (fun y =>
      deviation (residual h (enables width (h+1) s t)) y *
      deviation (residual h (enables width (h+1) s t)) y)) = _ by
    simp only [excess]
    exact reduced_excess h s _ (exceptional _ _ _ cap))

theorem grouped_quiet (width h s d : Nat) (cap : s ≤ (h+1)*width) (low : d < h+1)
    (c : W ((h+1)+s)) (wt : weight _ c ≤ d) : offZero (ring width h s) c = 0 := by
  by_cases z : c = zero _
  · simp [offZero,z]
  simp only [offZero,z,if_false]
  obtain ⟨a,b,e⟩ : ∃ a b, join (h+1) s a b = c := ⟨_,_,join_split _ _ c⟩
  subst c
  rw [join_weight] at wt
  have ne : ones (h+1) ≠ b := by rintro rfl; rw [ones_weight] at wt; omega
  have nz : ¬(a = zero _ ∧ b = zero _) := by rintro ⟨rfl,rfl⟩; exact z (join_zero _ _)
  simp [ring_walsh _ _ _ cap,nz,hits,ne]



/-- In full output coordinates, every defect is on the all-controls-high slice. -/
theorem grouped_histogram (width h s : Nat) (cap : s ≤ (h+1)*width)
    (t : W s) (y : W (h+1)) :
    histogram (ring width h s) (join (h+1) s t y) =
      1 + (if t = ones s then sign (FreezeMovies.parity (h+1) y) else 0) := by
  have eq : enables width (h+1) s t = ones (h+1) ↔ t = ones s := by
    calc
      _ ↔ ones (h+1) = enables width (h+1) s t := eq_comm
      _ ↔ ones s = t := exceptional _ _ _ cap t
      _ ↔ t = ones s := eq_comm
  simp only [ring_bucket,ring_histogram,eq]

/-- The mask on precisely the ring outputs reaches +2^(h+1). -/
theorem grouped_first_audible (width h s : Nat) (cap : s ≤ (h+1)*width) :
    let c := join (h+1) s (zero s) (ones (h+1))
    weight _ c = h+1 ∧ walsh (ring width h s) c = many (h+1) := by
  have ne : ones (h+1) ≠ zero (h+1) := by
    intro e
    have := congrArg (weight (h+1)) e
    simp [ones_weight,weight_zero] at this
  simp [join_weight,weight_zero,ones_weight,ring_walsh _ _ _ cap,ne,hits,chr,dot_zero,sign]

open DegreeDivisibility

private theorem split_degree (l s : Nat) (F : W n → W (l+s)) (hf : MapDegree k (l+s) F) :
    MapDegree k s (fun x => (split l s (F x)).1) ∧
    MapDegree k l (fun x => (split l s (F x)).2) := by
  induction s with
  | zero => exact ⟨trivial,hf⟩
  | succ s ih =>
    have tail := ih _ hf.2
    exact ⟨⟨hf.1,tail.1⟩,tail.2⟩

private theorem join_degree (l s : Nat) (t : W n → W s) (e : W n → W l)
    (ht : MapDegree k s t) (he : MapDegree k l e) :
    MapDegree k (l+s) (fun x => GroupedRing.join l s (t x) (e x)) := by
  induction s with
  | zero => exact he
  | succ s ih => exact ⟨ht.1, ih _ ht.2⟩

/-- The list of input functions feeding the successive control groups. -/
private def controlFunctions {n : Nat} : (s : Nat) → (W n → W s) → List (W n → Bool)
  | 0, _ => []
  | s+1, t => (fun x => (t x).1) :: controlFunctions s (fun x => (t x).2)

private theorem control_values (s : Nat) (t : W n → W s) (x : W n) :
    controls s (t x) = (controlFunctions s t).map (fun f => f x) := by
  induction s with
  | zero => rfl
  | succ s ih => exact congrArg ((t x).1 :: ·) (ih (fun z => (t z).2))

private theorem control_degrees (s : Nat) (t : W n → W s) (ht : MapDegree 1 s t) :
    ∀ f ∈ controlFunctions s t, DegreeLE 1 f := by
  induction s with
  | zero => simp [controlFunctions]
  | succ s ih =>
    intro f h
    rcases List.mem_cons.mp h with rfl | h
    · exact ht.1
    · exact ih _ ht.2 _ h

private theorem group_product_degree (fs : List (W n → Bool))
    (hf : ∀ f ∈ fs, DegreeLE 1 f) : DegreeLE fs.length (fun x => fs.all (fun f => f x)) := by
  induction fs with
  | nil => exact degree_true n 0
  | cons f fs ih =>
    have tail := ih (fun g hg => hf g (List.mem_cons_of_mem _ hg))
    simpa only [List.length_cons,List.all_cons,Nat.add_comm 1] using
      degree_and (hf f (by simp)) tail

private theorem group_degrees (width l : Nat) (fs : List (W n → Bool))
    (hf : ∀ f ∈ fs, DegreeLE 1 f) :
    MapDegree width l (fun x => groups width l (fs.map (fun f => f x))) := by
  induction l generalizing fs with
  | zero => trivial
  | succ l ih =>
    have head := group_product_degree (fs.take width)
      (fun f h => hf f (List.mem_of_mem_take h))
    have tail := ih (fs.drop width) (fun f h => hf f (List.mem_of_mem_drop h))
    refine ⟨?_,?_⟩
    · simpa only [groups,←List.map_take,List.all_map,Function.comp_def,id_eq] using
        degree_mono head (List.length_take_le width fs)
    · simpa only [groups,←List.map_drop] using tail

private theorem edge_degree {a b c : W n → Bool}
    (next : DegreeLE 1 a) (enable : DegreeLE width b) (prev : DegreeLE 1 c) :
    DegreeLE (width+1) (fun x => xor (a x) (b x && c x)) :=
  degree_xor (degree_mono next (by omega)) (degree_and enable prev)

private theorem walk_degree (l : Nat) (t : W n → W l) (start : W n → Bool) (w : W n → W l)
    (ht : MapDegree width l t) (hs : DegreeLE 1 start) (hw : MapDegree 1 l w) :
    DegreeLE 1 (fun x => (walk l (t x) (start x) (w x)).1) ∧
    MapDegree (width+1) l (fun x => (walk l (t x) (start x) (w x)).2) := by
  induction l generalizing start with
  | zero => exact ⟨hs,trivial⟩
  | succ l ih =>
    have rest := ih _ _ _ ht.2 hw.1 hw.2
    exact ⟨rest.1,edge_degree hw.1 ht.1 hs,rest.2⟩

/-- The copied bits are linear. Each discrepancy is one wire XOR a product of
    at most width controls and one wire, including on a one-edge ring. -/
theorem grouped_degree (width h s : Nat) :
    MapDegree (width+1) ((h+1)+s) (ring width h s) := by
  let t := fun x : W ((h+1)+s) => (split (h+1) s x).1
  let w := fun x : W ((h+1)+s) => (split (h+1) s x).2
  let e := fun x => enables width (h+1) s (t x)
  obtain ⟨ht,hw⟩ := split_degree (h+1) s id (identity_degree _)
  have he : MapDegree width (h+1) e := by
    simpa only [e,enables,control_values s t] using
      group_degrees width (h+1) (controlFunctions s t) (control_degrees s t ht)
  have path := walk_degree h (fun x => (e x).2) (fun x => (w x).1) (fun x => (w x).2)
    he.2 hw.1 hw.2
  exact join_degree (h+1) s t _ (mapDegree_mono s t ht (by omega))
    ⟨edge_degree hw.1 he.1 path.1,path.2⟩

#print axioms grouped_histogram
#print axioms grouped_first_audible
#print axioms grouped_degree
#print axioms grouped_excess
#print axioms grouped_quiet
end GroupedRing
