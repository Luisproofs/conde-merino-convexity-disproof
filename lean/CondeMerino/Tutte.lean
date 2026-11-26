import CondeMerino.Graph

namespace CondeMerino

/-- Expressions for bivariate polynomials with natural coefficients. Tutte
deletion–contraction only needs addition and multiplication by a variable. -/
inductive Poly where
  | one
  | xmul (p : Poly)
  | ymul (p : Poly)
  | add (p q : Poly)

def Poly.eval (x y : Rat) : Poly → Rat
  | .one => 1
  | .xmul p => x * p.eval x y
  | .ymul p => y * p.eval x y
  | .add p q => p.eval x y + q.eval x y

/-- Ordinary deletion–contraction definition of the bivariate Tutte polynomial.
A nonloop is a bridge precisely when its ends are disconnected in its deletion
(`connected_iff_walk`). The fuel used in `tutte` is exactly the edge count. -/
def tutteAux : Nat → Edges → Poly
  | 0, _ => .one
  | _+1, [] => .one
  | k+1, (u,v)::es =>
    if u = v then .ymul (tutteAux k es)
    else if connected es u v then
      .add (tutteAux k es) (tutteAux k (contract u v es))
    else .xmul (tutteAux k (contract u v es))

def tutte (es : Edges) : Poly := tutteAux es.length es

theorem tutte_nil : tutte [] = .one := rfl

/-- Recurrence at the selected edge, stated with graph-theoretic hypotheses. -/
theorem tutte_loop (v) (es : Edges) : tutte ((v,v)::es) = .ymul (tutte es) := by
  simp [tutte, tutteAux]

theorem tutte_ordinary (u v) (es : Edges) (hne : u ≠ v) (h : Walk es u v) :
    tutte ((u,v)::es) = .add (tutte es) (tutte (contract u v es)) := by
  have hc := (connected_iff_walk es u v).mpr h
  simp [tutte, tutteAux, hne, hc, contract]

theorem tutte_bridge (u v) (es : Edges) (h : ¬ Walk es u v) :
    tutte ((u,v)::es) = .xmul (tutte (contract u v es)) := by
  have hne : u ≠ v := fun he => h (he ▸ Walk.refl _)
  have hc : connected es u v = false := by
    cases he : connected es u v <;> simp_all [connected_iff_walk]
  simp [tutte, tutteAux, hne, hc, contract]

end CondeMerino
