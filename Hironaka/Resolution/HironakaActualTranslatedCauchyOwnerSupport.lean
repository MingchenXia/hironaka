import Hironaka.Resolution.HironakaActualCauchyEnumeratedPartition
import Hironaka.Resolution.HironakaActualInheritedNestedContactFlag
import Hironaka.Resolution.HironakaRelativeNormalTranslatedTaylorFunctions
import Mathlib.Analysis.Analytic.Uniqueness

/-! Real translation of ENTIRE native Cauchy owner supports on an actual
connected coordinate ball. Forbidden cones become genuine analytic higher
derivatives; their zero germs extend over the same connected ball before
translation. No nonzero constant is substituted into a formal series.
The original owner regions and off-diagram remainder support are retained;
no actual nearby initial-diagram equality is assumed or concluded.
Blueprint: hir:actual-translated-cauchy-owner-support.
Initial source-only draft; elaboration and acceptance are not claimed. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualTranslatedCauchyOwnerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm OkaRelationSheaf HolomorphicTaylorTail
  HironakaRelativeNormalTaylorCoefficients HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalTranslatedTaylorFunctions
  HironakaActualCoefficientPresentationCentrePower HironakaActualCauchyCoordinateDivision
  HironakaActualCauchyTaylorSupport HironakaActualCauchyMonomialDivision
  HironakaActualCauchyDiagramPartition HironakaActualInheritedAnalyticBlockJacobian
  HironakaActualInheritedNestedContactFlag

variable {n k : ℕ}

/-- The holomorphicity of the actual translated function is produced by the
genuine affine map and the actual ball inclusion. -/
theorem actual_coordinate_translation_differentiableOn {R r : ℝ}
    {Q : CoordinateSpace n → ℂ} (hQ : DifferentiableOn ℂ Q (ball 0 R))
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p + z) (ball 0 r) (ball 0 R)) :
    DifferentiableOn ℂ (fun z => Q (p + z)) (ball 0 r) :=
  hQ.comp (((differentiable_const p).add differentiable_id).differentiableOn) hdom

/-- This is the literal native owner region, with no new support operator.
Taking a = 0 also gives downward closure of the remainder complement. -/
theorem actual_cauchy_owner_region_downward_closed
    (L : List (CoordinateWord n)) (a : Fin n →₀ ℕ)
    {β γ : Fin n →₀ ℕ} (hγβ : γ ≤ β)
    (hβ : AvoidsCones L (β + a)) : AvoidsCones L (γ + a) := by
  intro w hw hwa
  apply hβ w hw
  apply hwa.trans
  intro j
  have hj := hγβ j
  simp only [Finsupp.add_apply]
  omega

private theorem exponent_le_add_iff_sub_le (c a β : Fin n →₀ ℕ) :
    c ≤ β + a ↔ c - a ≤ β := by
  constructor
  · intro h i
    have hi := h i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at *
    omega
  · intro h i
    have hi := h i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at *
    omega

private theorem iterDeriv_zero_on_model_domain {R : ℝ} (hR : 0 < R)
    (Q : CoordinateSpace n → ℂ) (hQ : DifferentiableOn ℂ Q (ball 0 R))
    (δ : Fin n →₀ ℕ)
    (hsupport : ∀ α : Fin n →₀ ℕ, δ ≤ α →
      MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n (modelGerm hR hQ)) = 0) :
    ∀ z : ComplexModel n,
      EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z ∈ ball (0 : CoordinateSpace n) R →
      iterDeriv ((actualCoordinateDerivativeWord δ).map
        (fun i => EuclideanSpace.single i (1 : ℂ))) (modelFunction Q) z = 0 := by
  let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
  let U : Set (ComplexModel n) := e ⁻¹' ball 0 R
  let L := (actualCoordinateDerivativeWord δ).map
    (fun i => EuclideanSpace.single i (1 : ℂ))
  have hU : IsOpen U := isOpen_ball.preimage e.continuous
  have h0U : (0 : ComplexModel n) ∈ U := by
    change e 0 ∈ ball (0 : CoordinateSpace n) R
    simpa only [map_zero] using mem_ball_self hR
  have hconv : Convex ℝ U := by
    exact (convex_ball (0 : CoordinateSpace n) R).linear_preimage
      (e.toLinearMap.restrictScalars ℝ)
  have hF : DifferentiableOn ℂ (modelFunction Q) U := by
    intro z hz
    exact (((hQ (e z) hz).differentiableAt (isOpen_ball.mem_nhds hz)).comp z
      e.differentiableAt).differentiableWithinAt
  have hD : DifferentiableOn ℂ (iterDeriv L (modelFunction Q)) U :=
    differentiableOn_iterDeriv hF hU L
  have hzero : actualAnalyticMultiDerivative δ (modelGerm hR hQ) = 0 :=
    (actualAnalyticMultiDerivative_eq_zero_iff_cone δ _).mpr hsupport
  rw [actualAnalyticMultiDerivative, actualAnalyticWordDerivative, modelGerm,
    iteratedDerivativeGerm_mk, ← HolGerm.mk_zero] at hzero
  have hev : iterDeriv L (modelFunction Q) =ᶠ[𝓝 (0 : ComplexModel n)]
      (fun _ => (0 : ℂ)) := HolGerm.mk_eq_mk_iff.mp hzero
  have haD : AnalyticOnNhd ℂ (iterDeriv L (modelFunction Q)) U := fun z hz =>
    HolomorphicAnalytic.analyticAt_of_differentiableOn hU hD hz
  have ha0 : AnalyticOnNhd ℂ (fun _ : ComplexModel n => (0 : ℂ)) U :=
    fun _ _ => analyticAt_const
  exact haD.eqOn_of_preconnected_of_eventuallyEq ha0 hconv.isPreconnected h0U hev

private theorem actual_translated_cone_support {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (Q : CoordinateSpace n → ℂ) (hQ : DifferentiableOn ℂ Q (ball 0 R))
    (δ : Fin n →₀ ℕ)
    (hsupport : ∀ α : Fin n →₀ ℕ, δ ≤ α →
      MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n (modelGerm hR hQ)) = 0)
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p + z) (ball 0 r) (ball 0 R)) :
    ∀ α : Fin n →₀ ℕ, δ ≤ α → MvPowerSeries.coeff α
      (actualUnshiftedTaylorAlgHom n (modelGerm hr
        (actual_coordinate_translation_differentiableOn hQ p hdom))) = 0 := by
  apply (actualAnalyticMultiDerivative_eq_zero_iff_cone δ _).mp
  rw [actualAnalyticMultiDerivative, actualAnalyticWordDerivative, modelGerm,
    iteratedDerivativeGerm_mk, ← HolGerm.mk_zero]
  apply HolGerm.mk_eq_mk_iff.mpr
  let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
  let P : ComplexModel n := e.symm p
  let U : Set (ComplexModel n) := e ⁻¹' ball 0 R
  let L := (actualCoordinateDerivativeWord δ).map
    (fun i => EuclideanSpace.single i (1 : ℂ))
  have hU : IsOpen U := isOpen_ball.preimage e.continuous
  have hP : P ∈ U := by
    change e (e.symm p) ∈ ball (0 : CoordinateSpace n) R
    rw [e.apply_symm_apply]
    simpa only [add_zero] using hdom (mem_ball_self hr)
  have hF : DifferentiableOn ℂ (modelFunction Q) U := by
    intro z hz
    exact (((hQ (e z) hz).differentiableAt (isOpen_ball.mem_nhds hz)).comp z
      e.differentiableAt).differentiableWithinAt
  have hreal : modelFunction (fun z => Q (p + z)) =
      modelFunction Q ∘ actualAffineTranslation n P := by
    funext z
    change Q (p + e z) = Q (e (e.symm p + z))
    rw [e.map_add, e.apply_symm_apply]
  filter_upwards [actualTranslatedSourceOpen_mem_nhds hU hP] with z hz
  change iterDeriv L (modelFunction (fun z => Q (p + z))) z = 0
  rw [hreal, iterDeriv_actualAffineTranslation hU hF P L z hz]
  exact iterDeriv_zero_on_model_domain hR Q hQ δ hsupport
    (actualAffineTranslation n P z) hz

private theorem actual_translated_shifted_owner_support
    {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (L : List (CoordinateWord n)) (a : Fin n →₀ ℕ)
    (Q : CoordinateSpace n → ℂ) (hQ : DifferentiableOn ℂ Q (ball 0 R))
    (hsupport : ∀ β : Fin n →₀ ℕ, ¬ AvoidsCones L (β + a) →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (modelGerm hR hQ)) = 0)
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p + z) (ball 0 r) (ball 0 R)) :
    ∀ β : Fin n →₀ ℕ, ¬ AvoidsCones L (β + a) → MvPowerSeries.coeff β
      (actualUnshiftedTaylorAlgHom n (modelGerm hr
        (actual_coordinate_translation_differentiableOn hQ p hdom))) = 0 := by
  intro β hβ
  have hex : ∃ w ∈ L, wordExponent w ≤ β + a := by
    by_contra hnone
    apply hβ
    intro v hv hva
    exact hnone ⟨v, hv, hva⟩
  obtain ⟨w, hw, hwa⟩ := hex
  let δ : Fin n →₀ ℕ := wordExponent w - a
  have hδβ : δ ≤ β := (exponent_le_add_iff_sub_le (wordExponent w) a β).mp hwa
  have hcone : ∀ α : Fin n →₀ ℕ, δ ≤ α →
      MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n (modelGerm hR hQ)) = 0 := by
    intro α hδα
    apply hsupport α
    intro hα
    exact hα w hw ((exponent_le_add_iff_sub_le (wordExponent w) a α).mpr hδα)
  exact actual_translated_cone_support hR hr Q hQ δ hcone p hdom β hδβ

/-- EVERY legal real translation retains the ENTIRE SAME native quotient
owner support, with the original fixed words and original fixed index.
All derivative vanishing and translated holomorphicity are internal. -/
theorem actual_translated_cauchy_owner_support {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (w : Fin k → CoordinateWord n) (i : Fin k)
    (Q : CoordinateSpace n → ℂ) (hQ : DifferentiableOn ℂ Q (ball 0 R))
    (hsupport : ∀ β : Fin n →₀ ℕ,
      ¬ AvoidsCones ((List.ofFn w).take i.val) (β + wordExponent (w i)) →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (modelGerm hR hQ)) = 0)
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p + z) (ball 0 r) (ball 0 R)) :
    ∀ β : Fin n →₀ ℕ,
      ¬ AvoidsCones ((List.ofFn w).take i.val) (β + wordExponent (w i)) →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (modelGerm hr
        (actual_coordinate_translation_differentiableOn hQ p hdom))) = 0 :=
  actual_translated_shifted_owner_support hR hr ((List.ofFn w).take i.val)
    (wordExponent (w i)) Q hQ hsupport p hdom

/-- The off-cone remainder region is also a downset and has the same
ENTIRE analytic real-translation property. This does not identify an
actual nearby initial diagram with the original diagram. -/
theorem actual_translated_cauchy_remainder_support {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (L : List (CoordinateWord n))
    (Q : CoordinateSpace n → ℂ) (hQ : DifferentiableOn ℂ Q (ball 0 R))
    (hsupport : ∀ α : Fin n →₀ ℕ, ¬ AvoidsCones L α →
      MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n (modelGerm hR hQ)) = 0)
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p + z) (ball 0 r) (ball 0 R)) :
    ∀ α : Fin n →₀ ℕ, ¬ AvoidsCones L α → MvPowerSeries.coeff α
      (actualUnshiftedTaylorAlgHom n (modelGerm hr
        (actual_coordinate_translation_differentiableOn hQ p hdom))) = 0 := by
  have hs : ∀ α : Fin n →₀ ℕ, ¬ AvoidsCones L (α + 0) →
      MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n (modelGerm hR hQ)) = 0 := by
    simpa only [add_zero] using hsupport
  simpa only [add_zero] using
    actual_translated_shifted_owner_support hR hr L 0 Q hQ hs p hdom

end
end Hironaka.HironakaActualTranslatedCauchyOwnerSupport
