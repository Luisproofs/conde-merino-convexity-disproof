import Std

namespace CondeMerino

abbrev Edge := Nat × Nat
abbrev Edges := List Edge

/-- A finite undirected multigraph on the labels below `order`. Edge occurrences
are distinguished, including parallel edges. An ordered pair stores an
undirected edge in either orientation. -/
structure Graph where
  order : Nat
  edges : Edges
  valid : ∀ e ∈ edges, e.1 < order ∧ e.2 < order

def Loopless (g : Graph) : Prop := ∀ e ∈ g.edges, e.1 ≠ e.2

def Simple (g : Graph) : Prop :=
  Loopless g ∧ (g.edges.map (fun (u,v) => (min u v, max u v))).Nodup

/-- Two vertices lie on the same side of every cut crossed by no edge. -/
def Joined (es : Edges) (a b : Nat) : Prop :=
  ∀ c : Nat → Bool, (∀ e ∈ es, c e.1 = c e.2) → c a = c b

/-- Usual undirected walk reachability, including the zero-length walk. -/
inductive Walk (es : Edges) : Nat → Nat → Prop
  | refl (a) : Walk es a a
  | edge {a b} : (a,b) ∈ es → Walk es a b
  | symm {a b} : Walk es a b → Walk es b a
  | trans {a b c} : Walk es a b → Walk es b c → Walk es a c

theorem walk_iff_joined {es : Edges} {a b : Nat} : Walk es a b ↔ Joined es a b := by
  constructor
  · intro w col h
    induction w with
    | refl => rfl
    | edge he => exact h _ he
    | symm _ ih => exact ih.symm
    | trans _ _ ih ij => exact ih.trans ij
  · classical
    intro h
    let col := fun x => decide (Walk es a x)
    have mono : ∀ e ∈ es, col e.1 = col e.2 := by
      intro e he
      have w : Walk es e.1 e.2 := .edge he
      exact decide_eq_decide.mpr ⟨fun p => p.trans w, fun p => p.trans w.symm⟩
    have hb := h col mono
    simpa [col, Walk.refl] using hb

def without (es : Edges) (v : Nat) : Edges :=
  es.filter fun e => e.1 != v && e.2 != v

def TwoConnected (g : Graph) : Prop :=
  3 ≤ g.order ∧ (∀ a b : Fin g.order, Walk g.edges a b) ∧
    ∀ v a b : Fin g.order, a ≠ v → b ≠ v → Walk (without g.edges v) a b

/-- Identify v with u; the vacated label becomes an isolated vertex. -/
def merge (u v x : Nat) : Nat := if x = v then u else x

def contract (u v : Nat) (es : Edges) : Edges :=
  es.map fun e => (merge u v e.1, merge u v e.2)

private theorem joined_contract (es : Edges) (u v a b : Nat) :
    Joined ((u,v)::es) a b ↔ Joined (contract u v es) (merge u v a) (merge u v b) := by
  constructor
  · intro h c hc
    apply h (fun x => c (merge u v x))
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · simp [merge]
    · exact hc _ (List.mem_map.mpr ⟨e, he, rfl⟩)
  · intro h c hc
    have huv := hc (u,v) (by simp)
    have fixed (x) : c (merge u v x) = c x := by
      by_cases hx : x = v <;> simp_all [merge]
    have hm : ∀ e ∈ contract u v es, c e.1 = c e.2 := by
      intro e he
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      simpa only [fixed] using (show c (merge u v d.1) = c (merge u v d.2) by
        rw [fixed, fixed]; exact hc d (.tail _ hd))
    simpa only [fixed] using h c hm

/-- Contract all listed edges and test whether the two labels coalesce. -/
def connectedAux : Nat → Edges → Nat → Nat → Bool
  | 0, _, a, b => a == b
  | _+1, [], a, b => a == b
  | k+1, (u,v)::es, a, b =>
    connectedAux k (contract u v es) (merge u v a) (merge u v b)

private theorem joined_nil_iff (a b : Nat) : Joined [] a b ↔ a = b := by
  constructor
  · intro h
    simpa using (h (fun x => decide (a = x)) (by simp))
  · rintro rfl _ _
    rfl

theorem connectedAux_correct (k) (es : Edges) (a b : Nat) (hk : es.length ≤ k) :
    connectedAux k es a b = true ↔ Joined es a b := by
  induction k generalizing es a b with
  | zero =>
    have : es = [] := List.length_eq_zero_iff.mp (by omega)
    simp [this, connectedAux, joined_nil_iff]
  | succ k ih =>
    cases es with
    | nil => simp [connectedAux, joined_nil_iff]
    | cons e es =>
      obtain ⟨u,v⟩ := e
      rw [connectedAux, joined_contract]
      apply ih
      simpa [contract] using hk

def connected (es : Edges) (a b : Nat) : Bool := connectedAux es.length es a b

theorem connected_iff_walk (es : Edges) (a b : Nat) :
    connected es a b = true ↔ Walk es a b :=
  (connectedAux_correct _ _ _ _ (Nat.le_refl _)).trans walk_iff_joined.symm

end CondeMerino
