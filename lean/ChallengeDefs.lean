/-
  ChallengeDefs.lean: every definition used in the statements of Challenge.lean.

  No imports (Lean core only). The proof files import this file, so the theorems they prove
  are stated over exactly these definitions. Together with Challenge.lean this is the whole
  trusted part: a reader only has to check that these definitions mean what they say.
-/

namespace FrozenShells

def W : Nat → Type
  | 0 => Unit
  | n+1 => Bool × W n

def zero : (n : Nat) → W n
  | 0 => ()
  | n+1 => (false, zero n)

def dot : (n : Nat) → W n → W n → Bool
  | 0, _, _ => false
  | n+1, u, v => xor (u.1 && v.1) (dot n u.2 v.2)

end FrozenShells

namespace CandyKnots
open FrozenShells

/-- The reference sum is for the specification only. -/
def total : (n : Nat) → (W n → Int) → Int
  | 0, f => f ()
  | n+1, f => total n (fun w => f (false,w)) + total n (fun w => f (true,w))

def sign (b : Bool) : Int := if b then -1 else 1

end CandyKnots

namespace FreezeMovies
open FrozenShells

instance wordEq (n : Nat) : DecidableEq (W n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih => exact inferInstanceAs (DecidableEq (Bool × W n))

end FreezeMovies

namespace CollisionLaw
open FrozenShells CandyKnots FreezeMovies

def many (n : Nat) := (2:Int)^n

def chr (c s : W r) := sign (dot r c s)

def hits (s t : W r) : Int := if s = t then 1 else 0

def walsh (Q : W n → W r) (c : W r) := total n (fun x => chr c (Q x))

def collisions (Q : W n → W r) := total n (fun x => total n (fun y => hits (Q x) (Q y)))

end CollisionLaw

namespace SilentRoom
open FrozenShells CandyKnots FreezeMovies CollisionLaw

def weight : (n : Nat) → W n → Nat
  | 0, _ => 0
  | n+1, c => weight n c.2 + (if c.1 then 1 else 0)

end SilentRoom

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

/-- Every output bit has an algebraic normal form of degree at most k. -/
def MapDegree {n : Nat} (k : Nat) : (m : Nat) → (W n → W m) → Prop
  | 0, _ => True
  | m+1, Q => DegreeLE k (fun x => (Q x).1) ∧ MapDegree k m (fun x => (Q x).2)

end DegreeDivisibility

namespace CubePermutation
open FrozenShells CandyKnots CollisionLaw SilentRoom

/-- Each output has exactly one preimage. -/
def IsPermutation (Q : W n → W n) : Prop :=
  ∀ y, ∃ x, Q x = y ∧ ∀ z, Q z = y → z = x

end CubePermutation

namespace ExactCollisionMinimum
open FrozenShells CollisionLaw SilentRoom DegreeDivisibility CubePermutation

/-- Low-weight silence concerns nonconstant output characters only. -/
def SilentThrough (d : Nat) (Q : W n → W n) : Prop :=
  ∀ c, c ≠ zero n → weight n c ≤ d → walsh Q c = 0

/-- A possible value of C(Q) − 2^n for a degree-bounded silent non-permutation. -/
def Attainable (n k d : Nat) (value : Int) : Prop :=
  ∃ Q : W n → W n, MapDegree k n Q ∧ SilentThrough d Q ∧
    ¬ IsPermutation Q ∧ collisions Q - many n = value

end ExactCollisionMinimum

namespace RectangularCollisionMinimum
open FrozenShells CandyKnots CollisionLaw SilentRoom DegreeDivisibility

def RectSilentThrough (d : Nat) (Q : W n → W m) : Prop :=
  ∀ c, c ≠ zero m → weight m c ≤ d → walsh Q c = 0

def rectExp (n m k d : Nat) : Nat :=
  max (max (2 * ((n + k - 1) / k) - m) ((n + k - 1) / k)) (d + 1)

def RectAttainable (n m k d : Nat) (value : Int) : Prop :=
  ∃ Q : W n → W m, MapDegree k m Q ∧ RectSilentThrough d Q ∧
    many (2 * n - m) < collisions Q ∧ collisions Q - many (2 * n - m) = value

end RectangularCollisionMinimum
