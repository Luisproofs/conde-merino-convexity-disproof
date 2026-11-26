import CondeMerino.Tutte

namespace CondeMerino

abbrev Coeffs := List Int

/-- Coefficients are stored in ascending order. Trailing zeros are harmless. -/
def horner (x : Rat) : Coeffs → Rat
  | [] => 0
  | a::p => (a : Rat) + x * horner x p

def plus : Coeffs → Coeffs → Coeffs
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::plus p q

theorem congrPlus {p q r s : Coeffs} (h : p = q) (k : r = s) :
    plus p r = plus q s := h ▸ k ▸ rfl

def scale (c : Int) (p : Coeffs) : Coeffs := p.map (c * ·)
def timesY (p : Coeffs) : Coeffs := plus (scale 2 p) (0::scale (-1) p)

def Poly.restrict : Poly → Coeffs
  | .one => [1]
  | .xmul p => 0::p.restrict
  | .ymul p => timesY p.restrict
  | .add p q => plus p.restrict q.restrict

theorem horner_plus (x : Rat) (p q : Coeffs) :
    horner x (plus p q) = horner x p + horner x q := by
  induction p generalizing q with
  | nil => simp [plus, horner] <;> grind
  | cons a p ih =>
    cases q with
    | nil => simp [plus, horner] <;> grind
    | cons b q => simp only [plus, horner, ih, Rat.intCast_add]; grind

theorem horner_scale (x : Rat) (c : Int) (p : Coeffs) :
    horner x (scale c p) = (c : Rat) * horner x p := by
  induction p with
  | nil => simp [scale, horner]
  | cons a p ih =>
    change (↑(c*a) : Rat) + x * horner x (scale c p) = ↑c * (↑a + x * horner x p)
    rw [ih, Rat.intCast_mul]
    grind

theorem eval_restrict (p : Poly) (x : Rat) :
    p.eval x (2-x) = horner x p.restrict := by
  induction p with
  | one => simp [Poly.eval, Poly.restrict, horner] <;> grind
  | xmul p ih => simp [Poly.eval, Poly.restrict, horner, ih] <;> grind
  | ymul p ih =>
    simp only [Poly.eval, Poly.restrict, timesY, horner_plus, horner, horner_scale, ih]
    grind
  | add p q ih ij => simp [Poly.eval, Poly.restrict, horner_plus, ih, ij]

def lineCoeffs (es : Edges) := (tutte es).restrict

theorem line_loop (u) (es : Edges) :
    lineCoeffs ((u,u)::es) = timesY (lineCoeffs es) := by
  unfold lineCoeffs; rw [tutte_loop]; rfl

theorem line_bridge (u v) (es : Edges) (h : connected es u v = false) :
    lineCoeffs ((u,v)::es) = 0::lineCoeffs (contract u v es) := by
  unfold lineCoeffs; rw [tutte_bridge]; rfl
  intro w
  have hc := (connected_iff_walk _ _ _).mpr w
  simp_all

theorem line_ordinary (u v) (es : Edges) (hne : u ≠ v) (h : connected es u v = true) :
    lineCoeffs ((u,v)::es) = plus (lineCoeffs es) (lineCoeffs (contract u v es)) := by
  unfold lineCoeffs; rw [tutte_ordinary _ _ _ hne ((connected_iff_walk _ _ _).mp h)]; rfl

end CondeMerino
