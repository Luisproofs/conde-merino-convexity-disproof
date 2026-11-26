import Std

/-! The Cauchy completion of the rationals. This file supplies the real
arithmetic used in the statement, without external library dependencies. -/
namespace CondeMerino.Completion

abbrev Seq := Nat → Rat

def Near (a b : Seq) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ N, ∀ n m, N ≤ n → N ≤ m → (a n - b m).abs ≤ ε

def Bounded (a : Seq) : Prop := ∃ K : Rat, ∀ n, (a n).abs ≤ K

private theorem abs_le {x b : Rat} : x.abs ≤ b ↔ -b ≤ x ∧ x ≤ b := by
  unfold Rat.abs; split <;> grind

private theorem abs_add (x y : Rat) : (x+y).abs ≤ x.abs + y.abs := by
  have hx := (abs_le (x := x) (b := x.abs)).mp Rat.le_refl
  have hy := (abs_le (x := y) (b := y.abs)).mp Rat.le_refl
  apply abs_le.mpr; grind

private theorem abs_mul (x y : Rat) : (x*y).abs = x.abs*y.abs := by
  have h₁ : 0 ≤ x → 0 ≤ -y → 0 ≤ x*(-y) := Rat.mul_nonneg
  have h₂ : 0 ≤ -x → 0 ≤ y → 0 ≤ (-x)*y := Rat.mul_nonneg
  have h₃ : 0 ≤ -x → 0 ≤ -y → 0 ≤ (-x)*(-y) := Rat.mul_nonneg
  unfold Rat.abs
  split <;> split <;> split <;> grind [Rat.mul_nonneg, Rat.mul_pos]

private theorem split_budget (ε K : Rat) (he : 0 < ε) (hK : 0 < K) :
    0 < ε/K ∧ K * (ε/K) = ε := by
  constructor
  · apply (Rat.lt_div_iff hK).mpr; grind
  · rw [Rat.mul_comm, Rat.div_mul_cancel (by grind : K ≠ 0)]

theorem Near.symm {a b : Seq} (h : Near a b) : Near b a := by
  intro ε he
  obtain ⟨N, hh⟩ := h ε he
  exact ⟨N, fun n m hn hm => Rat.abs_sub_comm (x := b n) (y := a m) ▸ hh m n hm hn⟩

theorem Near.trans {a b c : Seq} (h : Near a b) (k : Near b c) : Near a c := by
  intro ε he
  obtain ⟨hp, heq⟩ := split_budget ε 2 he (by decide +kernel)
  obtain ⟨N, hN⟩ := h _ hp
  obtain ⟨M, hM⟩ := k _ hp
  refine ⟨max N M, fun n m hn hm => ?_⟩
  have h₁ := abs_le.mp (hN n n (by omega) (by omega))
  have h₂ := abs_le.mp (hM n m (by omega) (by omega))
  apply abs_le.mpr; grind

theorem Near.add {a b c d : Seq} (h : Near a c) (k : Near b d) :
    Near (fun n => a n + b n) (fun n => c n + d n) := by
  intro ε he
  obtain ⟨hp, heq⟩ := split_budget ε 2 he (by decide +kernel)
  obtain ⟨N, hN⟩ := h _ hp
  obtain ⟨M, hM⟩ := k _ hp
  refine ⟨max N M, fun n m hn hm => ?_⟩
  have h₁ := abs_le.mp (hN n m (by omega) (by omega))
  have h₂ := abs_le.mp (hM n m (by omega) (by omega))
  apply abs_le.mpr; grind

theorem Near.neg {a b : Seq} (h : Near a b) :
    Near (fun n => -a n) (fun n => -b n) := by
  intro ε he
  obtain ⟨N, hN⟩ := h _ he
  refine ⟨N, fun n m hn hm => ?_⟩
  have hh := abs_le.mp (hN n m hn hm)
  apply abs_le.mpr; grind

private theorem product_bound {a b c d A D δ : Rat}
    (ha : a.abs ≤ A) (hd : d.abs ≤ D) (hac : (a-c).abs ≤ δ) (hbd : (b-d).abs ≤ δ) :
    (a*b-c*d).abs ≤ (A+D)*δ := by
  have h₁ := Rat.mul_le_mul_of_nonneg_right ha (Rat.abs_nonneg (x := b-d))
  have h₂ := Rat.mul_le_mul_of_nonneg_left hbd (Rat.le_trans Rat.abs_nonneg ha)
  have h₃ := Rat.mul_le_mul_of_nonneg_right hd (Rat.abs_nonneg (x := a-c))
  have h₄ := Rat.mul_le_mul_of_nonneg_left hac (Rat.le_trans Rat.abs_nonneg hd)
  have eqn : a*b-c*d = a*(b-d) + d*(a-c) := by grind
  rw [eqn]
  apply Rat.le_trans (abs_add _ _)
  rw [abs_mul, abs_mul]
  grind

theorem Near.mul {a b c d : Seq} (ba : Bounded a) (bd : Bounded d)
    (h : Near a c) (k : Near b d) :
    Near (fun n => a n*b n) (fun n => c n*d n) := by
  obtain ⟨A, hA⟩ := ba
  obtain ⟨D, hD⟩ := bd
  have ha := Rat.le_trans Rat.abs_nonneg (hA 0)
  have hd := Rat.le_trans Rat.abs_nonneg (hD 0)
  intro ε he
  obtain ⟨hp, heq⟩ := split_budget ε (A+D+1) he (by grind)
  obtain ⟨N, hN⟩ := h _ hp
  obtain ⟨M, hM⟩ := k _ hp
  refine ⟨max N M, fun n m hn hm => ?_⟩
  have hh := product_bound (hA n) (hD m) (hN n m (by omega) (by omega))
    (hM n m (by omega) (by omega))
  grind

private theorem prefix_bound (a : Seq) (N : Nat) :
    ∃ B : Rat, ∀ n < N, (a n).abs ≤ B := by
  induction N with
  | zero => exact ⟨0, by omega⟩
  | succ N ih =>
    obtain ⟨B, hb⟩ := ih
    refine ⟨max B (a N).abs, fun n hn => ?_⟩
    by_cases h : n < N
    · have := hb n h
      grind
    · have : n = N := by omega
      grind

/-- Requiring a bound in a name permits every rational Cauchy sequence. -/
theorem bounded_of_cauchy {a : Seq} (h : Near a a) : Bounded a := by
  obtain ⟨N, hn⟩ := h 1 (by decide +kernel)
  obtain ⟨B, hb⟩ := prefix_bound a N
  refine ⟨max B (1+(a N).abs), fun n => ?_⟩
  by_cases h : n < N
  · have := hb n h
    grind
  · have h₁ := hn n N (by omega) (by omega)
    have h₂ := abs_add (a n - a N) (a N)
    rw [Rat.sub_add_cancel] at h₂
    grind

/-- A bounded rational Cauchy sequence represents a real number. -/
structure Name where
  seq : Seq
  bound : Bounded seq
  cauchy : Near seq seq

instance : Setoid Name where
  r a b := Near a.seq b.seq
  iseqv := ⟨fun a => a.cauchy, Near.symm, Near.trans⟩

def Real := Quotient (inferInstance : Setoid Name)

def const (q : Rat) : Name where
  seq := fun _ => q
  bound := ⟨q.abs, fun _ => Rat.le_refl⟩
  cauchy := by
    intro ε he; exact ⟨0, fun _ _ _ _ => by simp only [Rat.sub_self, Rat.abs_zero]; grind⟩

def ofRat (q : Rat) : Real := Quotient.mk _ (const q)

private def addName (a b : Name) : Name where
  seq n := a.seq n + b.seq n
  bound := by
    obtain ⟨A, hA⟩ := a.bound
    obtain ⟨B, hB⟩ := b.bound
    exact ⟨A+B, fun n => Rat.le_trans (abs_add _ _) (by have := hA n; have := hB n; grind)⟩
  cauchy := a.cauchy.add b.cauchy

private def negName (a : Name) : Name where
  seq n := -a.seq n
  bound := by simpa only [Bounded, Rat.abs_neg] using a.bound
  cauchy := a.cauchy.neg

private def mulName (a b : Name) : Name where
  seq n := a.seq n * b.seq n
  bound := by
    obtain ⟨A, hA⟩ := a.bound
    obtain ⟨B, hB⟩ := b.bound
    refine ⟨A*B, fun n => ?_⟩
    rw [abs_mul]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (hA n) Rat.abs_nonneg)
      (Rat.mul_le_mul_of_nonneg_left (hB n) (Rat.le_trans Rat.abs_nonneg (hA n)))
  cauchy := a.cauchy.mul a.bound b.bound b.cauchy

instance : Add Real := ⟨Quotient.lift₂ (fun a b => Quotient.mk _ (addName a b))
  (fun _ _ _ _ h k => Quotient.sound (Near.add h k))⟩
instance : Neg Real := ⟨Quotient.lift (fun a => Quotient.mk _ (negName a))
  (fun _ _ h => Quotient.sound (Near.neg h))⟩
instance : Mul Real := ⟨Quotient.lift₂ (fun a b => Quotient.mk _ (mulName a b))
  (fun a _ _ d h k => Quotient.sound (Near.mul a.bound d.bound h k))⟩
instance : Sub Real := ⟨fun a b => a + -b⟩

private def Below (a b : Seq) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ N, ∀ n, N ≤ n → a n ≤ b n + ε

private theorem below_congr {a b c d : Seq} (h : Near a c) (k : Near b d)
    (old : Below a b) : Below c d := by
  intro ε he
  obtain ⟨hp, heq⟩ := split_budget ε 3 he (by decide +kernel)
  obtain ⟨N, hN⟩ := h _ hp
  obtain ⟨M, hM⟩ := k _ hp
  obtain ⟨L, hL⟩ := old _ hp
  refine ⟨max N (max M L), fun n hn => ?_⟩
  have h₁ := abs_le.mp (hN n n (by omega) (by omega))
  have h₂ := abs_le.mp (hM n n (by omega) (by omega))
  have h₃ := hL n (by omega)
  grind

instance : LE Real := ⟨Quotient.lift₂ (fun a b : Name => Below a.seq b.seq)
  (fun _ _ _ _ h k => propext ⟨below_congr h k, below_congr h.symm k.symm⟩)⟩

theorem ofRat_add (a b : Rat) : ofRat a + ofRat b = ofRat (a+b) := rfl
theorem ofRat_mul (a b : Rat) : ofRat a * ofRat b = ofRat (a*b) := rfl
theorem ofRat_sub (a b : Rat) : ofRat a - ofRat b = ofRat (a-b) := by
  change ofRat (a + -b) = _
  rw [Rat.sub_eq_add_neg]

theorem ofRat_le {a b : Rat} : ofRat a ≤ ofRat b ↔ a ≤ b := by
  change Below (fun _ => a) (fun _ => b) ↔ _
  constructor
  · intro h
    apply Classical.byContradiction
    intro hh
    obtain ⟨hp, he⟩ := split_budget (a-b) 2 (by grind) (by decide +kernel)
    obtain ⟨N, hN⟩ := h _ hp
    have := hN N (Nat.le_refl _)
    grind
  · intro h ε he
    exact ⟨0, fun _ _ => by grind⟩

end CondeMerino.Completion
