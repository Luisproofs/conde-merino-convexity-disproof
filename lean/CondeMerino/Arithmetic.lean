import CondeMerino.Minors

namespace CondeMerino

def lineAt (es : Edges) (x : Rat) := (tutte es).eval x (2-x)

private theorem chain_values (i : Fin 6) (x : Rat) :
    lineAt (openEdges i) x = horner x (squarePolys i).1 ∧
    lineAt (closedEdges i) x = horner x (squarePolys i).2 := by
  have cc := chain_coefficients i
  constructor
  · exact (eval_restrict _ _).trans (congrArg (horner x) cc.1)
  · exact (eval_restrict _ _).trans (congrArg (horner x) cc.2)

/-- The two identities of the finite proof, for each of the five actual
attachments, at every rational argument. -/
theorem finite_square_steps (i : Fin 5) (x : Rat) :
    lineAt (openEdges (i.val+1)) x =
      (2+x*x+x*x*x) * lineAt (openEdges i) x ∧
    lineAt (closedEdges (i.val+1)) x =
      (1+x)*(1+x)*lineAt (openEdges i) x + (3+x)*lineAt (closedEdges i) x := by
  have cur := chain_values ⟨i.val, by omega⟩ x
  have nxt := chain_values ⟨i.val+1, by omega⟩ x
  dsimp only at cur nxt
  rw [cur.1, cur.2, nxt.1, nxt.2]
  simp only [squarePolys, horner_times, horner_plus, horner]
  constructor <;> grind

def P (x : Rat) := (tutte witness.edges).eval x (2-x)

theorem evaluation (x : Rat) : P x = horner x coefficients := by
  unfold P
  rw [eval_restrict]
  exact congrArg (horner x) witness_coefficients

def h : Rat := 1/256
def endpoint : Rat := 1/128
def excess : Rat := 26123280769243048353292998299952433382036731393 / 2^159

theorem value_zero : P 0 = 280024 := by rw [evaluation]; decide +kernel
theorem value_mid : P h =
    409287515873028912132169022994186495320958651554461185 / 2^160 := by
  rw [evaluation]; decide +kernel
theorem value_end : P endpoint =
    390357441909358527194187829786140398446004566785 / 2^140 := by
  rw [evaluation]; decide +kernel

theorem exact_excess : 2 * P h - P 0 - P endpoint = excess := by
  rw [value_zero, value_mid, value_end]; decide +kernel

theorem excess_gt : (1 : Rat)/32 < excess := by decide +kernel

theorem violates_midpoint : ¬ P h ≤ (1/2) * P 0 + (1/2) * P endpoint := by
  rw [value_zero, value_mid, value_end]; decide +kernel

end CondeMerino
