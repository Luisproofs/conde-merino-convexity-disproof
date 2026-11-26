import CondeMerino.Arithmetic
import CondeMerino.Real

namespace CondeMerino

open Completion

def Poly.evalReal (x y : Real) : Poly → Real
  | .one => ofRat 1
  | .xmul p => x * p.evalReal x y
  | .ymul p => y * p.evalReal x y
  | .add p q => p.evalReal x y + q.evalReal x y

theorem evalReal_ofRat (p : Poly) (x y : Rat) :
    p.evalReal (ofRat x) (ofRat y) = ofRat (p.eval x y) := by
  induction p with
  | one => rfl
  | xmul p ih => simp only [Poly.evalReal, Poly.eval, ih, ofRat_mul]
  | ymul p ih => simp only [Poly.evalReal, Poly.eval, ih, ofRat_mul]
  | add p q ih ij => simp only [Poly.evalReal, Poly.eval, ih, ij, ofRat_add]

abbrev Point := Real × Real

/-- The closed line segment from (0,2) to (2,0). -/
def OnSegment (z : Point) : Prop :=
  ofRat 0 ≤ z.1 ∧ z.1 ≤ ofRat 2 ∧ z.2 = ofRat 2 - z.1

def blend (t a b : Real) : Real := (ofRat 1 - t)*a + t*b

/-- The defining convexity inequality, for every pair of points in the
closed segment and every real weight in [0,1]. -/
def ConvexOnSegment (f : Point → Real) : Prop :=
  ∀ a b : Point, OnSegment a → OnSegment b →
  ∀ t : Real, ofRat 0 ≤ t → t ≤ ofRat 1 →
    f (blend t a.1 b.1, blend t a.2 b.2) ≤ blend t (f a) (f b)

def tutteFunction (g : Graph) (z : Point) : Real :=
  (tutte g.edges).evalReal z.1 z.2

/-- Conde and Merino (2009), Conjecture 2.4. Finite graphs are labelled by
0,...,order-1; parallel edges and loops are excluded by the hypotheses. -/
def PublishedConjecture : Prop :=
  ∀ g : Graph, TwoConnected g → Simple g → Loopless g → ConvexOnSegment (tutteFunction g)

private def point (q : Rat) : Point := (ofRat q, ofRat (2-q))

private theorem in_segment (q : Rat) (lo : 0 ≤ q) (hi : q ≤ 2) : OnSegment (point q) :=
  ⟨ofRat_le.mpr lo, ofRat_le.mpr hi, (ofRat_sub _ _).symm⟩

private theorem eval_point (q : Rat) : tutteFunction witness (point q) = ofRat (P q) :=
  evalReal_ofRat _ _ _

private theorem blend_rat (t a b : Rat) :
    blend (ofRat t) (ofRat a) (ofRat b) = ofRat ((1-t)*a+t*b) := by
  simp only [blend, ofRat_sub, ofRat_mul, ofRat_add]

private theorem midpoint :
    (blend (ofRat (1/2)) (point 0).1 (point endpoint).1,
     blend (ofRat (1/2)) (point 0).2 (point endpoint).2) = point h := by
  apply Prod.ext <;> change blend _ (ofRat _) (ofRat _) = ofRat _
  all_goals rw [blend_rat]; apply congrArg ofRat; decide +kernel

private theorem rational_test (f : Point → Real) (g : Rat → Rat)
    (hf : ∀ q, f (point q) = ofRat (g q)) (hc : ConvexOnSegment f) :
    g h ≤ (1/2) * g 0 + (1/2) * g endpoint := by
  have bad : f (point h) ≤ blend (ofRat (1/2)) (f (point 0)) (f (point endpoint)) := by
    rw [← midpoint]
    exact hc (point 0) (point endpoint)
      (in_segment 0 (by decide +kernel) (by decide +kernel))
      (in_segment endpoint (by decide +kernel) (by decide +kernel)) (ofRat (1/2))
      (ofRat_le.mpr (by decide +kernel)) (ofRat_le.mpr (by decide +kernel))
  rw [hf, hf, hf, blend_rat] at bad
  have half : (1 : Rat) - 1/2 = 1/2 := by decide +kernel
  rw [half] at bad
  exact ofRat_le.mp bad

theorem witness_not_convex : ¬ ConvexOnSegment (tutteFunction witness) :=
  fun hc => violates_midpoint (rational_test _ P eval_point hc)

theorem counterexample :
    witness.order = 19 ∧ witness.edges.length = 30 ∧ Simple witness ∧
    Loopless witness ∧ TwoConnected witness ∧ ¬ ConvexOnSegment (tutteFunction witness) :=
  ⟨counts.1, counts.2, witness_simple, witness_simple.1, witness_twoConnected, witness_not_convex⟩

theorem not_publishedConjecture : ¬ PublishedConjecture :=
  fun h => witness_not_convex (h witness witness_twoConnected witness_simple witness_simple.1)

end CondeMerino
