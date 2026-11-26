import CondeMerino.GraphicRank
import CondeMerino.Tutte

namespace CondeMerino

/-- Enumerate subsets of edge occurrences by omitting or selecting the head.
Parallel copies give different choices even when their endpoints agree. -/
def edgeSubsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | e::es => let ss := edgeSubsets es; ss ++ ss.map (e :: ·)

theorem size_edgeSubsets {α : Type} (es : List α) : (edgeSubsets es).length = 2^es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [edgeSubsets, ih, Nat.pow_succ]; omega

private theorem subset_of_mem {α : Type} {es s : List α} (h : s ∈ edgeSubsets es) : s ⊆ es := by
  induction es generalizing s with
  | nil => simp [edgeSubsets] at h; simp [h]
  | cons e es ih =>
    rcases List.mem_append.mp h with h | h
    · exact fun _ hx => .tail _ (ih h hx)
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
      exact List.cons_subset_cons _ (ih ht)

private theorem map_subsets {α β : Type} (f : α → β) (es : List α) :
    edgeSubsets (es.map f) = (edgeSubsets es).map (List.map f) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [edgeSubsets, ih, List.map_map, Function.comp_def]

/-- Boolean masks index subsets of edge positions. -/
def edgeMasks : Nat → List (List Bool)
  | 0 => [[]]
  | k+1 => (edgeMasks k).map (false :: ·) ++ (edgeMasks k).map (true :: ·)

theorem mem_edgeMasks (n : Nat) (bs : List Bool) : bs ∈ edgeMasks n ↔ bs.length = n := by
  induction n generalizing bs with
  | zero => simp [edgeMasks]
  | succ n ih =>
    cases bs with
    | nil => simp [edgeMasks]
    | cons b bs => cases b <;> simp [edgeMasks, ih]

theorem nodup_edgeMasks (n) : (edgeMasks n).Nodup := by
  induction n with
  | zero => simp [edgeMasks]
  | succ n ih =>
    apply List.nodup_append.mpr
    refine ⟨ih.map _ (by simp), ih.map _ (by simp), ?_⟩
    simp

def selectEdges {α : Type} : List Bool → List α → List α
  | b::bs, a::as => if b then a :: selectEdges bs as else selectEdges bs as
  | _, _ => []

theorem selections_eq_subsets {α : Type} (es : List α) :
    (edgeMasks es.length).map (fun bs => selectEdges bs es) = edgeSubsets es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.length_cons, edgeMasks, List.map_append, List.map_map,
      Function.comp_def, selectEdges, Bool.false_eq_true, ↓reduceIte, edgeSubsets]
    rw [← ih]
    simp [List.map_map, Function.comp_def]

open Lean.Grind

section
variable {R : Type u} [CommRing R]

/-- Interpret the project's bivariate expression in a commutative ring. -/
def Poly.evalIn (x y : R) : Poly → R
  | .one => 1
  | .xmul p => x * p.evalIn x y
  | .ymul p => y * p.evalIn x y
  | .add p q => p.evalIn x y + q.evalIn x y

private def total {α : Type} (f : α → R) : List α → R
  | [] => 0
  | a::as => f a + total f as

private theorem total_congr {α : Type} (as : List α) (f g : α → R)
    (h : ∀ a ∈ as, f a = g a) : total f as = total g as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [total, total, h a (.head _), ih (fun b hb => h b (.tail _ hb))]

private theorem total_map {α β : Type} (as : List α) (f : α → β) (g : β → R) :
    total g (as.map f) = total (fun a => g (f a)) as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, total, ih]

private theorem total_append {α : Type} (as bs : List α) (f : α → R) :
    total f (as ++ bs) = total f as + total f bs := by
  induction as with
  | nil => simp only [List.nil_append, total]; grind
  | cons a as ih => simp only [List.cons_append, total, ih]; grind

private theorem total_mul {α : Type} (as : List α) (c : R) (f : α → R) :
    total (fun a => c * f a) as = c * total f as := by
  induction as with
  | nil => simp only [total]; grind
  | cons a as ih => simp only [total, ih]; grind

/-- The rank-generating monomial at a fixed full rank r. -/
def rankTerm (n r : Nat) (x y : R) (s : Edges) : R :=
  (x-1)^(r - graphicRank n s) * (y-1)^(s.length - graphicRank n s)

/-- The classical spanning-subgraph sum. Vertex labels range from 0 to n-1
for every term. The two coordinates are arbitrary ring elements. -/
def rankSubset (n : Nat) (es : Edges) (x y : R) : R :=
  total (rankTerm n (graphicRank n es) x y) (edgeSubsets es)

private theorem sum_split (n u v : Nat) (es : Edges) (x y : R) :
    let r := graphicRank n ((u,v)::es)
    rankSubset n ((u,v)::es) x y = total (rankTerm n r x y) (edgeSubsets es) +
      total (fun s => rankTerm n r x y ((u,v)::s)) (edgeSubsets es) := by
  simp [rankSubset, edgeSubsets, total_append, total_map]

private theorem sum_contract (n u v : Nat) (es : Edges) (x y : R) :
    rankSubset n (contract u v es) x y =
      total (fun s => rankTerm n (graphicRank n (contract u v es)) x y (contract u v s))
        (edgeSubsets es) := by
  unfold rankSubset contract
  rw [map_subsets, total_map]

private theorem loop_rank (n u : Nat) (es : Edges) (hu : u < n) :
    graphicRank n ((u,u)::es) = graphicRank n es := by
  rw [rank_insert _ _ _ _ hu hu]
  simp [(connected_iff_walk es u u).mpr (.refl u)]

private theorem subset_loop (n u : Nat) (es : Edges) (hu : u < n) (x y : R) :
    rankSubset n ((u,u)::es) x y = y * rankSubset n es x y := by
  rw [sum_split, loop_rank _ _ _ hu]
  have term (s : Edges) : rankTerm n (graphicRank n es) x y ((u,u)::s) =
      (y-1) * rankTerm n (graphicRank n es) x y s := by
    simp only [rankTerm, loop_rank _ _ _ hu, List.length_cons]
    have hr := rank_le_size n s
    rw [show s.length + 1 - graphicRank n s = (s.length - graphicRank n s) + 1 by omega,
      Semiring.pow_succ]
    grind
  simp only [term, total_mul, rankSubset]
  grind

private theorem subset_nonloop (n u v : Nat) (es : Edges) (hu : u < n) (hv : v < n)
    (hne : u ≠ v) (x y : R) :
    rankSubset n ((u,v)::es) x y =
      total (rankTerm n (graphicRank n ((u,v)::es)) x y) (edgeSubsets es) +
      rankSubset n (contract u v es) x y := by
  rw [sum_split, sum_contract]
  apply congrArg (_ + ·)
  apply total_congr
  intro s _
  simp only [rankTerm, rank_contract _ _ _ _ hu hv hne, List.length_cons]
  simp [contract]

private theorem disconnected_ranks (n u v : Nat) (es : Edges) (hu : u < n) (hv : v < n)
    (hne : u ≠ v) (hd : connected es u v = false) :
    graphicRank n (contract u v es) = graphicRank n es := by
  have hh := rank_contract n u v es hu hv hne
  rw [rank_insert _ _ _ _ hu hv, hd] at hh
  simp only [Bool.false_eq_true, ↓reduceIte] at hh
  omega

private theorem subset_bridge (n u v : Nat) (es : Edges) (hu : u < n) (hv : v < n)
    (hne : u ≠ v) (hd : connected es u v = false) (x y : R) :
    rankSubset n ((u,v)::es) x y = x * rankSubset n (contract u v es) x y := by
  rw [subset_nonloop _ _ _ _ hu hv hne, sum_contract]
  have hr := disconnected_ranks n u v es hu hv hne hd
  have excluded := rank_insert u v n es hu hv
  rw [hd] at excluded
  have splitTerm (s) (hs : s ∈ edgeSubsets es) :
      rankTerm n (graphicRank n ((u,v)::es)) x y s =
      (x-1) * rankTerm n (graphicRank n (contract u v es)) x y (contract u v s) := by
    have sub := subset_of_mem hs
    have hd' : connected s u v = false := by
      cases hh : connected s u v
      · rfl
      · have := (connected_iff_walk es u v).mpr (((connected_iff_walk s u v).mp hh).mono sub)
        simp_all
    have hrs := disconnected_ranks n u v s hu hv hne hd'
    have hle := graphicRank_mono sub n
    simp only [rankTerm, hr, hrs, excluded, Bool.false_eq_true, ↓reduceIte]
    rw [show graphicRank n es + 1 - graphicRank n s = (graphicRank n es - graphicRank n s)+1
      by omega, Semiring.pow_succ]
    simp only [contract, List.length_map]
    grind
  rw [total_congr _ _ _ splitTerm, total_mul]
  grind

/-- Universal bivariate identity over every commutative ring. No graph
hypothesis beyond the finite vertex bound is needed. -/
theorem tutte_eq_rankSubset (n : Nat) (es : Edges) (valid : EndpointsBelow n es) (x y : R) :
    (tutte es).evalIn x y = rankSubset n es x y := by
  induction len : es.length using Nat.strongRecOn generalizing es with
  | ind k ih =>
    cases es with
    | nil =>
      simp [tutte_nil, Poly.evalIn, rankSubset, edgeSubsets, total, rankTerm, rank_nil,
        Semiring.pow_zero, Semiring.mul_one, Semiring.add_zero]
    | cons e es =>
      obtain ⟨u,v⟩ := e
      obtain ⟨hu,hv⟩ := valid _ (.head _)
      have hdel : EndpointsBelow n es := fun e he => valid e (.tail _ he)
      have hcon : EndpointsBelow n (contract u v es) := by
        intro e he
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        have := hdel d hd
        simp only [merge]; grind
      have shorter : es.length < k := by simp only [List.length_cons] at len; omega
      have del := ih _ shorter es hdel rfl
      have con := ih _ (by simpa [contract] using shorter) (contract u v es) hcon rfl
      by_cases he : u = v
      · subst v
        rw [tutte_loop, Poly.evalIn, del, subset_loop _ _ _ hu]
      · cases hc : connected es u v with
        | false =>
          have hw : ¬ Walk es u v := by rw [← connected_iff_walk, hc]; decide
          rw [tutte_bridge _ _ _ hw, Poly.evalIn, con, subset_bridge _ _ _ _ hu hv he hc]
        | true =>
          have hw := (connected_iff_walk es u v).mp hc
          rw [tutte_ordinary _ _ _ he hw, Poly.evalIn, del, con,
            subset_nonloop _ _ _ _ hu hv he, rank_insert _ _ _ _ hu hv, hc]
          rfl

/-- The classical component formula, summed once for each Boolean choice
of the labelled edge occurrences. The component counts use all n vertices. -/
noncomputable def classicalTutte (n : Nat) (es : Edges) (x y : R) : R :=
  ((edgeMasks es.length).map fun bs =>
    let s := selectEdges bs es
    let k := componentCount n s
    (x-1)^(k - componentCount n es) * (y-1)^(s.length + k - n)).sum

private theorem total_eq_sum {α : Type} (f : α → R) (as : List α) :
    total f as = (as.map f).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [total, ih]

private theorem subset_eq_classical (n : Nat) (es : Edges) (x y : R) :
    rankSubset n es x y = classicalTutte n es x y := by
  unfold rankSubset classicalTutte
  rw [← total_eq_sum, ← selections_eq_subsets, total_map]
  apply total_congr
  intro bs _
  dsimp only
  let s := selectEdges bs es
  have bound (fs : Edges) : componentCount n fs ≤ n := by
    simpa [componentCount_eq] using (List.countP_le_length
      (l := List.range n) (p := fun a => representative fs a == a))
  have h := bound es
  have hs := bound s
  have hd : graphicRank n es - graphicRank n s = componentCount n s - componentCount n es := by
    rw [graphicRank_eq, graphicRank_eq]; omega
  have hj : s.length - graphicRank n s = s.length + componentCount n s - n := by
    rw [graphicRank_eq]; omega
  change (x-1)^(_ - graphicRank n s) * (y-1)^(s.length - graphicRank n s) = _
  rw [hd, hj]

/-- Equality as a bivariate polynomial identity, with values in an arbitrary
commutative ring. It applies also to disconnected graphs and to multigraphs. -/
theorem tutte_eq_classicalTutte (g : Graph) (x y : R) :
    (tutte g.edges).evalIn x y = classicalTutte g.order g.edges x y :=
  (tutte_eq_rankSubset _ _ g.valid _ _).trans (subset_eq_classical _ _ _ _)

end

theorem evalIn_rat (p : Poly) (x y : Rat) : p.evalIn x y = p.eval x y := by
  induction p with
  | one => rfl
  | xmul p ih => simp only [Poly.eval, Poly.evalIn, ih]
  | ymul p ih => simp only [Poly.eval, Poly.evalIn, ih]
  | add p q ih ij => simp only [Poly.eval, Poly.evalIn, ih, ij]

theorem tutte_eval_eq_rankSubset (g : Graph) (x y : Rat) :
    (tutte g.edges).eval x y = rankSubset g.order g.edges x y :=
  (evalIn_rat _ _ _).symm.trans (tutte_eq_rankSubset _ _ g.valid x y)

end CondeMerino
