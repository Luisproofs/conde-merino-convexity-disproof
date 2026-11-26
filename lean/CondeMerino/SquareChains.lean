import CondeMerino.Restriction
import CondeMerino.Witness

namespace CondeMerino

/-- Joint j is the far corner of block j-1; joint zero is the clique vertex 0. -/
def joint : Nat → Nat
  | 0 => 0
  | i+1 => 7+3*i

def chain (k tip : Nat) : Edges :=
  (List.range k).flatMap fun i =>
    square (joint i) (if i+1 = k then tip else joint (i+1)) (5+3*i) (6+3*i)

def openEdges (k : Nat) := chain k (joint k) ++ clique

def closedEdges : Nat → Edges
  | 0 => contract 1 0 clique
  | k+1 => chain (k+1) 1 ++ clique

theorem closed_five : closedEdges 5 = witness.edges := rfl

/-- Multiplication by a small polynomial given by its increasing coefficients. -/
def times : Coeffs → Coeffs → Coeffs
  | [], _ => []
  | c::cs, p => plus (scale c p) (0::times cs p)

theorem horner_times (x : Rat) (p q : Coeffs) :
    horner x (times p q) = horner x p * horner x q := by
  induction p with
  | nil => simp [times, horner] <;> grind
  | cons c cs ih =>
    simp only [times, horner_plus, horner_scale, horner, ih]; grind

def openBase : Coeffs := [544,-932,796,-374,106,-16,1]
def closedBase : Coeffs := [680,-1680,1898,-1240,499,-123,17,-1]

def squarePolys : Nat → Coeffs × Coeffs
  | 0 => (openBase, closedBase)
  | i+1 =>
    let (a,b) := squarePolys i
    (times [2,0,1,1] a, plus (times [1,2,1] a) (times [3,1] b))

end CondeMerino
