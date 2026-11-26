import CondeMerino.Graph

namespace CondeMerino

/-- When two classes are joined, their smaller representative survives. -/
private def joinLabels (a b z : Nat) :=
  if z = max a b then min a b else z

private theorem join_le (a b z : Nat) : joinLabels a b z ≤ z := by
  unfold joinLabels; split <;> omega

/-- The least vertex label in the walk component of x. -/
def representative : Edges → Nat → Nat
  | [], x => x
  | (u,v)::es, x => joinLabels (representative es u) (representative es v) (representative es x)

theorem representative_le (es : Edges) (x : Nat) : representative es x ≤ x := by
  induction es with
  | nil => exact Nat.le_refl _
  | cons e es ih => exact Nat.le_trans (join_le _ _ _) ih

private theorem same_on_edge (es : Edges) (e : Edge) (he : e ∈ es) :
    representative es e.1 = representative es e.2 := by
  induction es with
  | nil => simp at he
  | cons f es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · simp only [representative, joinLabels]; split <;> split <;> omega
    · simp only [representative, ih he]

theorem representative_eq_of_walk {es : Edges} {a b} (w : Walk es a b) :
    representative es a = representative es b := by
  induction w with
  | refl => rfl
  | edge he => exact same_on_edge _ _ he
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij

theorem Walk.mono {es fs : Edges} (sub : es ⊆ fs) {a b} (w : Walk es a b) : Walk fs a b := by
  induction w with
  | refl => exact .refl _
  | edge he => exact .edge (sub he)
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij

theorem walk_representative (es : Edges) (x : Nat) : Walk es x (representative es x) := by
  induction es generalizing x with
  | nil => exact .refl _
  | cons e es ih =>
    obtain ⟨u,v⟩ := e
    have old (a) : Walk ((u,v)::es) a (representative es a) :=
      (ih a).mono (by intro _ h; exact .tail _ h)
    have cross := (old u).symm.trans ((Walk.edge (List.mem_cons_self (a := (u,v)))).trans (old v))
    change Walk _ x (joinLabels _ _ _)
    apply (old x).trans
    unfold joinLabels
    split
    next he =>
      by_cases h : representative es u ≤ representative es v
      · rw [Nat.max_eq_right h] at he
        rw [he, Nat.min_eq_left h]
        exact cross.symm
      · have h' : representative es v ≤ representative es u := by omega
        rw [Nat.max_eq_left h'] at he
        rw [he, Nat.min_eq_right h']
        exact cross
    next => exact .refl _

theorem representative_eq_iff {es : Edges} {a b} :
    representative es a = representative es b ↔ Walk es a b := by
  refine ⟨fun h => ?_, representative_eq_of_walk⟩
  exact (walk_representative es a).trans (h ▸ (walk_representative es b).symm)

private theorem rep_mono {es fs : Edges}
    (h : ∀ a b, Walk es a b → Walk fs a b) (a) : representative fs a ≤ representative es a := by
  rw [representative_eq_of_walk (h _ _ (walk_representative es a))]
  exact representative_le _ _

theorem representative_fixed_iff (es : Edges) (v : Nat) :
    representative es v = v ↔ ∀ w, Walk es v w → v ≤ w := by
  constructor
  · intro hv w hw
    rw [← hv, representative_eq_of_walk hw]
    exact representative_le es w
  · intro h
    exact Nat.le_antisymm (representative_le es v) (h _ (walk_representative es v))

/-- Count each spanning walk component at its least vertex. This definition
uses only walk reachability and the full vertex range, including isolates. -/
noncomputable def componentCount (n : Nat) (es : Edges) : Nat := by
  classical
  exact (List.range n).countP fun v => decide (∀ w, Walk es v w → v ≤ w)

theorem componentCount_eq (n : Nat) (es : Edges) :
    componentCount n es = (List.range n).countP fun x => representative es x == x := by
  apply List.countP_congr
  intro x _
  simp [representative_fixed_iff]

/-- Count the nonrepresentatives. This is |V| minus the number of components. -/
def graphicRank (n : Nat) (es : Edges) :=
  (List.range n).countP fun x => representative es x != x

theorem graphicRank_eq (n) (es : Edges) : graphicRank n es = n - componentCount n es := by
  have hh := List.length_eq_countP_add_countP (fun x => representative es x == x) (l := List.range n)
  simp only [List.length_range] at hh
  have eq : n = componentCount n es + graphicRank n es := by
    simpa [componentCount_eq, graphicRank, bne, Bool.beq_eq_decide_eq] using hh
  omega

private theorem rank_mono_walk {es fs : Edges} (n)
    (h : ∀ a b, Walk es a b → Walk fs a b) : graphicRank n es ≤ graphicRank n fs := by
  apply List.countP_mono_left
  intro x _ hx
  have := rep_mono h x
  have := representative_le es x
  simp at hx ⊢
  omega

theorem graphicRank_mono {es fs : Edges} (sub : es ⊆ fs) (n) :
    graphicRank n es ≤ graphicRank n fs := rank_mono_walk n fun _ _ w => w.mono sub

private theorem rank_insert_count (n u v : Nat) (es : Edges) :
    graphicRank n ((u,v)::es) = graphicRank n es +
      if representative es u ≠ representative es v ∧
          max (representative es u) (representative es v) < n then 1 else 0 := by
  induction n with
  | zero => simp [graphicRank]
  | succ n ih =>
    have step (fs : Edges) : graphicRank (n+1) fs =
        graphicRank n fs + if representative fs n ≠ n then 1 else 0 := by
      simp [graphicRank, List.range_succ, List.countP_append]
    rw [step, step, ih]
    have bound := representative_le es n
    have fixed (a) : representative es (representative es a) = representative es a :=
      (representative_eq_of_walk (walk_representative es a)).symm
    have atMax : representative es (max (representative es u) (representative es v)) =
        max (representative es u) (representative es v) := by
      cases Nat.le_total (representative es u) (representative es v) with
      | inl h => simpa only [Nat.max_eq_right h] using fixed v
      | inr h => simpa only [Nat.max_eq_left h] using fixed u
    simp only [representative, joinLabels]
    by_cases hn : n = max (representative es u) (representative es v)
    · rw [← hn] at atMax
      simp only [atMax]
      (repeat' split) <;> omega
    · (repeat' split) <;> omega

def EndpointsBelow (n : Nat) (es : Edges) := ∀ e ∈ es, e.1 < n ∧ e.2 < n

theorem rank_insert (u v n) (es : Edges) (hu : u < n) (hv : v < n) :
    graphicRank n ((u,v)::es) = graphicRank n es + if connected es u v then 0 else 1 := by
  rw [rank_insert_count]
  have h₁ := representative_le es u
  have h₂ := representative_le es v
  have hc := (connected_iff_walk es u v).trans representative_eq_iff.symm
  split <;> split <;> simp_all <;> omega

private theorem same_partition (es : Edges) (u v a b : Nat) :
    Walk ((u,v)::es) a b ↔ Walk ((u,v)::contract u v es) a b := by
  rw [walk_iff_joined, walk_iff_joined]
  have cuts (c : Nat → Bool) (huv : c u = c v) :
      (∀ e ∈ es, c e.1 = c e.2) ↔ (∀ e ∈ contract u v es, c e.1 = c e.2) := by
    have fixed (x) : c (merge u v x) = c x := by unfold merge; split <;> grind
    constructor
    · intro h e he
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      exact (fixed _).trans ((h d hd).trans (fixed _).symm)
    · intro h e he
      have hh := h _ (List.mem_map.mpr ⟨e, he, rfl⟩)
      exact (fixed _).symm.trans (hh.trans (fixed _))
  unfold Joined
  simp only [List.forall_mem_cons]
  exact forall_congr' fun c => by
    constructor <;> intro h he
    · exact h ⟨he.1, (cuts c he.1).mpr he.2⟩
    · exact h ⟨he.1, (cuts c he.1).mp he.2⟩

private theorem isolated_after_contract (es : Edges) {u v : Nat} (hne : u ≠ v) :
    ¬ Walk (contract u v es) u v := by
  intro w
  have hu := walk_iff_joined.mp w (fun a => a == v)
  have h (a) : (merge u v a == v) = false := by unfold merge; split <;> simp_all
  have hh := hu (by
    intro e he
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp he
    exact (h _).trans (h _).symm)
  simp_all

/-- A nonloop contraction costs one unit of rank. The deleted label remains
in the fixed vertex range as an isolated vertex of the contracted graph. -/
theorem rank_contract (n u v) (es : Edges) (hu : u < n) (hv : v < n) (hne : u ≠ v) :
    graphicRank n ((u,v)::es) = graphicRank n (contract u v es) + 1 := by
  have hw := same_partition es u v
  have hr := Nat.le_antisymm (rank_mono_walk n fun a b => (hw a b).mp)
    (rank_mono_walk n fun a b => (hw a b).mpr)
  rw [hr, rank_insert _ _ _ _ hu hv]
  have hc : connected (contract u v es) u v = false := by
    cases hh : connected (contract u v es) u v
    · rfl
    · exact False.elim (isolated_after_contract es hne ((connected_iff_walk _ _ _).mp hh))
  simp [hc]

theorem rank_nil (n) : graphicRank n [] = 0 := by simp [graphicRank, representative]

theorem rank_le_size (n) (es : Edges) : graphicRank n es ≤ es.length := by
  induction es with
  | nil => simp [rank_nil]
  | cons e es ih => rw [rank_insert_count]; split <;> simp_all <;> omega

end CondeMerino
