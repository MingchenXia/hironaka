import Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet

/-! Explicit constant and coordinate images of the first normal jet splitting. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet
namespace Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJetApply
noncomputable section

/-- A coefficient supported at one exponent maps to its actual normal monomial. -/
theorem normalPowerLinearEquiv_single (d a q : ℕ) (α : normalExponentIndex a q)
    (b : HolGerm (ComplexModel d)) :
    letI := tangentAlgebra d a
    (normalPowerLinearEquiv d a q) (Pi.single α b) =
      b • Ideal.Quotient.mk (normalIdeal d a ^ q) (normalExponentMonomial d a α.val) := by
  classical
  letI := tangentAlgebra d a
  letI := normalExponentFintype a q
  change normalMonomialCombination d a q (Pi.single α b) = _
  simp [normalMonomialCombination]

/-- The coefficient tuple supported on one option maps to its monomial. -/
theorem firstOrderNormalLinearEquiv_option_single (d a : ℕ) (o : Option (Fin a))
    (b : HolGerm (ComplexModel d)) :
    letI := tangentAlgebra d a
    firstOrderNormalLinearEquiv d a
      (match o with | none => (b,0) | some i => (0,Pi.single i b)) =
      b • Ideal.Quotient.mk (normalIdeal d a ^ 2)
        (normalExponentMonomial d a ((firstOrderExponentEquiv a) o).val) := by
  classical
  letI := tangentAlgebra d a
  letI := normalExponentFintype a 2
  let e := firstOrderExponentEquiv a
  have hf : (fun α : normalExponentIndex a 2 =>
      match e.symm α with
      | none => (match o with | none => b | some _ => 0)
      | some j => (match o with | none => 0 | some i => (Pi.single i b : Fin a → HolGerm (ComplexModel d)) j)) = Pi.single (e o) b := by
    funext α
    cases ho : e.symm α with
    | none =>
      have he : α = e none := by rw [← ho]; exact (e.apply_symm_apply α).symm
      subst α
      cases o <;> simp [ho]
    | some j =>
      have he : α = e (some j) := by rw [← ho]; exact (e.apply_symm_apply α).symm
      subst α
      cases o with
      | none => simp
      | some i =>
        by_cases hij : i = j
        · subst j; simp
        · have hne : e (some i) ≠ e (some j) := by
            intro h
            exact hij (Option.some.inj (e.injective h))
          simp [Pi.single_apply, hij, hne]
  cases o with
  | none =>
    change normalPowerLinearEquiv d a 2 (fun α => match e.symm α with | none => b | some _ => 0) = _
    rw [hf]
    exact normalPowerLinearEquiv_single d a 2 (e none) b
  | some i =>
    change normalPowerLinearEquiv d a 2 (fun α => match e.symm α with | none => 0 | some j => (Pi.single i b : Fin a → HolGerm (ComplexModel d)) j) = _
    rw [hf]
    exact normalPowerLinearEquiv_single d a 2 (e (some i)) b
end
end Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJetApply
