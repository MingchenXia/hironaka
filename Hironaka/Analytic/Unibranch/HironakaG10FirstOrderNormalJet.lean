import Hironaka.Resolution.HironakaRelativeNormalMonomialBasis

/-! The actual first normal infinitesimal neighborhood splits into constant and linear coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
namespace Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet
noncomputable section

private theorem degree_eq (a : ℕ) (α : Fin a →₀ ℕ) :
    normalExponentDegree α = α.degree := by
  simp [normalExponentDegree, Finsupp.degree_eq_sum]

/-- The degree-below-two exponents are exactly zero and the distinct coordinate exponents. -/
def firstOrderExponentEquiv (a : ℕ) : Option (Fin a) ≃ normalExponentIndex a 2 := by
  classical
  let e : Option (Fin a) → normalExponentIndex a 2 := fun x =>
    match x with
    | none => ⟨0, by simp [normalExponentDegree]⟩
    | some i => ⟨Finsupp.single i 1, by simp [degree_eq, Finsupp.degree_single]⟩
  apply Equiv.ofBijective e
  constructor
  · intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some j =>
        have h' := congrArg Subtype.val h
        change (0 : Fin a →₀ ℕ) = Finsupp.single j 1 at h'
        have hj := congrArg (fun z : Fin a →₀ ℕ => z j) h'
        simp at hj
    | some i =>
      cases y with
      | none =>
        have h' := congrArg Subtype.val h
        simp [e] at h'
      | some j =>
        have h' := congrArg Subtype.val h
        have hij : i = j := Finsupp.single_left_injective (one_ne_zero : (1 : ℕ) ≠ 0) h'
        simp [hij]
  · intro α
    have hlt : α.val.degree < 2 := by simpa [degree_eq] using α.property
    have hc : α.val.degree = 0 ∨ α.val.degree = 1 := by omega
    rcases hc with h0 | h1
    · have he : α.val = 0 := (Finsupp.degree_eq_zero_iff α.val).mp h0
      refine ⟨none, ?_⟩
      apply Subtype.ext
      exact he.symm
    · obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff α.val).mp h1
      refine ⟨some i, ?_⟩
      apply Subtype.ext
      exact hi.symm

/-- The actual square-normal-ideal quotient is linearly the constant coefficient
and one coefficient for each original normal coordinate. -/
def firstOrderNormalLinearEquiv (d a : ℕ) :
    letI := tangentAlgebra d a
    (HolGerm (ComplexModel d) × (Fin a → HolGerm (ComplexModel d))) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+a)) ⧸ normalIdeal d a ^ 2) := by
  letI := tangentAlgebra d a
  letI := normalExponentFintype a 2
  let e := firstOrderExponentEquiv a
  let f : (HolGerm (ComplexModel d) × (Fin a → HolGerm (ComplexModel d))) ≃ₗ[HolGerm (ComplexModel d)]
      (normalExponentIndex a 2 → HolGerm (ComplexModel d)) := {
    toFun := fun p α => match e.symm α with | none => p.1 | some i => p.2 i
    invFun := fun v => (v (e none), fun i => v (e (some i)))
    left_inv := by intro p; cases p; simp
    right_inv := by
      intro v; funext α
      have he := e.apply_symm_apply α
      cases h : e.symm α <;> simp [h] at he ⊢ <;> simp [he]
    map_add' := by intro p q; funext α; cases h : e.symm α <;> simp [h]
    map_smul' := by intro r p; funext α; cases h : e.symm α <;> simp [h]
  }
  exact f.trans (normalPowerLinearEquiv d a 2)
end
end Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet
