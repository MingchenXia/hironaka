import Hironaka.Resolution.HironakaActualInheritedNestedContactFlag
import Hironaka.Resolution.HironakaActualMultiDerivativeBlowup
import Hironaka.Resolution.HironakaActualFormalBlowupAllDirections
import Hironaka.Resolution.HironakaActualFixedInheritedSelectorPermutation

/-! Whole prefix support of SAME entire members through genuine shears,
coordinate renames and marked normalization. These lower statements do not
assert a target diagram or retain arbitrary member heads under a permutation.
The derivative/substitution identities already established for actual blowups
are reused; no new density proof is needed. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInheritedWholePrefixNormalization
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualCanonicalBlockJacobian HironakaActualInheritedNestedContactFlag
  HironakaActualMultiDerivativeBlowup HironakaActualNormalizedBlowupDerivative
  HironakaActualFormalBlowupAllDirections HironakaActualFormalMonomialBlowupReflection
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalStrictGenerators
  HironakaActualFormalCoordinatePowerDivision
  HironakaActualFixedInheritedSelectorPermutation
variable {n : ℕ}

/-- A whole centre shear commutes with every actual nonpivot normal partial.
The whole-series proof is actual blowup factorization, chain rule and injectivity. -/
theorem pderiv_actualFormalCenterShear
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (w : Fin n → ℂ)
    (j : Fin n) (hj : j ∈ A) (hje : j ≠ e) (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.pderiv ℂ j (actualFormalCenterShear A e w F) =
      actualFormalCenterShear A e w (MvPowerSeries.pderiv ℂ j F) := by
  have h := congrArg (MvPowerSeries.pderiv ℂ j)
    (actualFormalBlowup_eq_zero_comp_centerShear A e he w F)
  rw [pderiv_actualFormalBlowup A e w j hj hje,
    pderiv_actualFormalBlowup A e (fun _ => 0) j hj hje,
    actualFormalBlowup_eq_zero_comp_centerShear A e he w
      (MvPowerSeries.pderiv ℂ j F)] at h
  apply actualFormalBlowup_zero_injective A e
  apply mul_left_cancel₀ (actualFormalExceptional_ne_zero e)
  exact h.symm

private theorem degree_add_single (β : Fin n →₀ ℕ) (i : Fin n) :
    normalExponentDegree (β + Finsupp.single i 1) = normalExponentDegree β + 1 := by
  simp [normalExponentDegree, Finsupp.add_apply, Finset.sum_add_distrib]

/-- The SAME accepted actual higher derivative commutes with the entire shear
when its exponent is supported in nonpivot normal directions. -/
theorem actualFormalMultiDerivative_centerShear
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (w : Fin n → ℂ)
    (β : Fin n →₀ ℕ) (hβ : (↑β.support : Set (Fin n)) ⊆ A \ {e})
    (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalMultiDerivative β (actualFormalCenterShear A e w F) =
      actualFormalCenterShear A e w (actualFormalMultiDerivative β F) := by
  induction β using (measure normalExponentDegree).wf.induction with
  | h β ih =>
    by_cases hz : β = 0
    · subst β
      rw [actualFormalMultiDerivative_zero, actualFormalMultiDerivative_zero]
    · obtain ⟨i, hi⟩ : ∃ i, β i ≠ 0 := by
        by_contra! hzero
        exact hz (Finsupp.ext hzero)
      have hsingle : Finsupp.single i 1 ≤ β := by
        intro j
        by_cases hji : j = i
        · subst j
          simpa only [Finsupp.single_eq_same] using Nat.one_le_iff_ne_zero.mpr hi
        · simp [Finsupp.single_eq_of_ne hji]
      let γ := β - Finsupp.single i 1
      have hdecomp : γ + Finsupp.single i 1 = β := tsub_add_cancel_of_le hsingle
      have hdegree : normalExponentDegree γ + 1 = normalExponentDegree β := by
        simpa only [degree_add_single] using congrArg normalExponentDegree hdecomp
      have hγlt : normalExponentDegree γ < normalExponentDegree β := by omega
      have hγle : γ ≤ β := tsub_le_self
      have hγ : (↑γ.support : Set (Fin n)) ⊆ A \ {e} := by
        intro j hj
        apply hβ
        apply Finsupp.mem_support_iff.mpr
        intro hjzero
        exact (Finsupp.mem_support_iff.mp hj)
          (Nat.eq_zero_of_le_zero (by simpa only [hjzero] using hγle j))
      have hiA : i ∈ A := (hβ (Finsupp.mem_support_iff.mpr hi)).1
      have hie : i ≠ e := by
        simpa only [Set.mem_singleton_iff] using (hβ (Finsupp.mem_support_iff.mpr hi)).2
      rw [← hdecomp, actualFormalMultiDerivative_add_single,
        actualFormalMultiDerivative_add_single, ih γ hγlt hγ,
        pderiv_actualFormalCenterShear A e he w i hiA hie]

/-- Whole forbidden-cone coefficients survive SAME marked normalization.
The lower mark's source membership is produced by the generic derivative theorem. -/
theorem actualNormalizedFormalMember_cone_zero
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (w : Fin n → ℂ)
    (β : Fin n →₀ ℕ) (hβ : (↑β.support : Set (Fin n)) ⊆ A \ {e})
    (μ : ℕ) (hβμ : normalExponentDegree β ≤ μ)
    (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ)
    (hz : ∀ α : Fin n →₀ ℕ, β ≤ α → MvPowerSeries.coeff α F = 0) :
    ∀ α : Fin n →₀ ℕ, β ≤ α →
      MvPowerSeries.coeff α (actualNormalizedFormalMember A e he w μ F hF) = 0 := by
  apply (actualFormalMultiDerivative_eq_zero_iff_cone β _).mp
  have hDF : actualFormalMultiDerivative β F = 0 :=
    (actualFormalMultiDerivative_eq_zero_iff_cone β F).mpr hz
  rw [actualMultiDerivative_actualNormalizedFormalMember A e he w β hβ μ hβμ]
  have hp := actualMultiDerivative_mem_centre_sub A β (fun i hi => (hβ hi).1)
    μ hβμ F hF
  symm
  apply actualNormalizedFormalMember_unique A e he w
    (μ - normalExponentDegree β) (actualFormalMultiDerivative β F) hp 0
  rw [hDF, map_zero, mul_zero]

/-- Whole cone avoidance of a SAME member is transported by the actual shear
and a genuine exponent rename. This asserts no arbitrary head covariance. -/
theorem shear_rename_cone_zero
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (w : Fin n → ℂ)
    (p : Fin n ≃ Fin n) (β : Fin n →₀ ℕ)
    (hβ : (↑β.support : Set (Fin n)) ⊆ A \ {e})
    (F : MvPowerSeries (Fin n) ℂ)
    (hz : ∀ α : Fin n →₀ ℕ, β ≤ α → MvPowerSeries.coeff α F = 0) :
    ∀ α : Fin n →₀ ℕ, Finsupp.domCongr p β ≤ α →
      MvPowerSeries.coeff α
        (MvPowerSeries.rename p (actualFormalCenterShear A e w F)) = 0 := by
  apply (actualFormalMultiDerivative_eq_zero_iff_cone (Finsupp.domCongr p β) _).mp
  have hDF : actualFormalMultiDerivative β F = 0 :=
    (actualFormalMultiDerivative_eq_zero_iff_cone β F).mpr hz
  rw [actualFormalMultiDerivative_rename,
    actualFormalMultiDerivative_centerShear A e he w β hβ F, hDF, map_zero, map_zero]

end
end Hironaka.HironakaActualInheritedWholePrefixNormalization
