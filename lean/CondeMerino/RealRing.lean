import CondeMerino.Real

namespace CondeMerino.Completion

open Lean.Grind

private theorem eq_pointwise {a b : Name} (h : ∀ i, a.seq i = b.seq i) :
    Quotient.mk (inferInstance : Setoid Name) a = Quotient.mk _ b := by
  have eq := funext h
  apply Quotient.sound
  change Near a.seq b.seq
  rw [← eq]
  exact a.cauchy

private def realPow (x : Real) : Nat → Real
  | 0 => ofRat 1
  | n+1 => realPow x n * x

local instance : NatCast Real := ⟨fun n => ofRat (n : Rat)⟩
local instance (n : Nat) : OfNat Real n := ⟨ofRat (n : Rat)⟩
local instance : IntCast Real := ⟨fun i => ofRat (i : Rat)⟩
local instance : HPow Real Nat Real := ⟨realPow⟩
local instance : SMul Nat Real := ⟨fun n x => ofRat (n : Rat) * x⟩
local instance : SMul Int Real := ⟨fun i x => ofRat (i : Rat) * x⟩

/-- Ring structure on the Cauchy completion used in the convexity statement.
Each identity descends from the corresponding pointwise rational identity. -/
scoped instance realCommRing : CommRing Real where
  add_zero a := Quotient.inductionOn a fun A =>
    eq_pointwise fun i => Rat.add_zero (A.seq i)
  add_comm a b := Quotient.inductionOn₂ a b fun A B =>
    eq_pointwise fun i => Rat.add_comm (A.seq i) (B.seq i)
  add_assoc a b c := Quotient.inductionOn₃ a b c fun A B C =>
    eq_pointwise fun i => Rat.add_assoc (A.seq i) (B.seq i) (C.seq i)
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun A B C =>
    eq_pointwise fun i => Rat.mul_assoc (A.seq i) (B.seq i) (C.seq i)
  mul_comm a b := Quotient.inductionOn₂ a b fun A B =>
    eq_pointwise fun i => Rat.mul_comm (A.seq i) (B.seq i)
  mul_one a := Quotient.inductionOn a fun A =>
    eq_pointwise fun i => Rat.mul_one (A.seq i)
  one_mul a := Quotient.inductionOn a fun A =>
    eq_pointwise fun i => Rat.one_mul (A.seq i)
  left_distrib a b c := Quotient.inductionOn₃ a b c fun A B C =>
    eq_pointwise fun i => Rat.mul_add (A.seq i) (B.seq i) (C.seq i)
  right_distrib a b c := Quotient.inductionOn₃ a b c fun A B C =>
    eq_pointwise fun i => Rat.add_mul (A.seq i) (B.seq i) (C.seq i)
  zero_mul a := Quotient.inductionOn a fun A =>
    eq_pointwise fun i => Rat.zero_mul (A.seq i)
  mul_zero a := Quotient.inductionOn a fun A =>
    eq_pointwise fun i => Rat.mul_zero (A.seq i)
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  neg_add_cancel a := Quotient.inductionOn a fun A =>
    eq_pointwise fun i => (show -(A.seq i) + A.seq i = 0 by grind)
  sub_eq_add_neg _ _ := rfl
  neg_zsmul z a := Quotient.inductionOn a fun A =>
    eq_pointwise fun i => (show ((-z : Int) : Rat) * A.seq i = -((z : Rat) * A.seq i) by grind)
  ofNat_succ n := by
    change ofRat ((n+1 : Nat) : Rat) = ofRat ((n : Rat)+1)
    apply congrArg ofRat
    grind
  intCast_neg z := by
    change ofRat ((-z : Int) : Rat) = ofRat (-(z : Rat))
    apply congrArg ofRat
    grind

end CondeMerino.Completion
