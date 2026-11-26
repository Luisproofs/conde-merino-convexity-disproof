import CondeMerino.Tutte

namespace CondeMerino

/-- Two internally disjoint two-edge paths from s to t. -/
def square (s t a b : Nat) : Edges := [(a,s),(b,s),(t,a),(t,b)]

def squares : Edges :=
  square 0 7 5 6 ++ square 7 10 8 9 ++ square 10 13 11 12 ++
  square 13 16 14 15 ++ square 16 1 17 18

def clique : Edges :=
  [(1,0),(2,0),(3,0),(4,0),(2,1),(3,1),(4,1),(3,2),(4,2),(4,3)]

def witness : Graph := ⟨19, squares ++ clique, by decide⟩

theorem counts : witness.order = 19 ∧ witness.edges.length = 30 := by decide

theorem witness_simple : Simple witness := by
  constructor
  · unfold Loopless
    decide
  · decide

private def root (v : Fin 19) : Fin 19 := if v = 0 then 1 else 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem allRoots :
    ∀ v a : Fin 19, a ≠ v → connected (without witness.edges v) (root v) a = true := by
  decide

private theorem deletedWalk (v a b : Fin 19) (ha : a ≠ v) (hb : b ≠ v) :
    Walk (without witness.edges v) a b :=
  ((connected_iff_walk _ _ _).mp (allRoots v a ha)).symm.trans
    ((connected_iff_walk _ _ _).mp (allRoots v b hb))

private theorem liftWalk {es fs : Edges} (sub : ∀ e ∈ es, e ∈ fs)
    {a b : Nat} (w : Walk es a b) : Walk fs a b := by
  induction w with
  | refl => exact .refl _
  | edge he => exact .edge (sub _ he)
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij

theorem witness_twoConnected : TwoConnected witness := by
  refine ⟨by decide, ?_, deletedWalk⟩
  intro a b
  have h : ∀ i j : Fin 19, ∃ k : Fin 19, i ≠ k ∧ j ≠ k := by decide
  obtain ⟨v, ha, hb⟩ := h a b
  exact liftWalk (fun _ he => (List.mem_filter.mp he).1) (deletedWalk v a b ha hb)

end CondeMerino
