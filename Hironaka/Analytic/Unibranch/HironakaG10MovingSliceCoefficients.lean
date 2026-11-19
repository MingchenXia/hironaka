import Hironaka.Analytic.Unibranch.HironakaG10NormalSlicePolynomial
import Hironaka.Analytic.Unibranch.HironakaG10NormalCoefficientCoordinates

/-! # Whole original parameter slices from the same moving coefficients -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10MovingSliceCoefficients
open Hironaka Hironaka
  OkaRelationSheaf HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualJointBaseFibre HironakaRelativeNormalNormalPowerSpread
  HironakaActualRelativeCoefficientGerms
  HironakaRelativeNormalCoherentTranslatedJets HironakaHolomorphicJetMonomialSpan
  Hironaka.Analytic.Unibranch.HironakaG10MovingParameterSlice
  Hironaka.Analytic.Unibranch.HironakaG10NormalSlicePolynomial
  Hironaka.Analytic.Unibranch.HironakaG10NormalCoefficientCoordinates

/-- The same finite holomorphic coefficient functions simultaneously represent
the original joint germ and all nearby parameter-slice values. -/
theorem exists_moving_slice_coefficient_functions
    {Q : Type*} [CommRing Q] [Algebra ℂ Q] (t d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (F : ComplexModel (t+d) → ℂ) (hF : HolAt F 0) :
    let := tangentAlgebra t d
    let := normalExponentFintype d (q+1)
    ∃ U : Set (ComplexModel (t+d)), IsOpen U ∧ 0 ∈ U ∧
      ∃ C : normalExponentIndex d (q+1) → ComplexModel t → ℂ,
      ∃ hC : ∀ α, HolAt (C α) 0,
      ∃ hFU : ∀ a ∈ U, HolAt (F ∘ actualAffineTranslation (t+d) a) 0,
      (∀ α, actualNormalAnalyticCoefficientGerm t d (HolGerm.mk F hF) α.val =
        HolGerm.mk (C α) (hC α)) ∧
      ∀ᶠ y in 𝓝 (0 : ComplexModel t),
        ∀ hy : tangentInclusion t d y ∈ U,
          φ (jointBaseZeroTrace t d
            (HolGerm.mk (F ∘ actualAffineTranslation (t+d) (tangentInclusion t d y))
              (hFU _ hy))) =
          ∑ α, (∏ i : Fin d, φ (coordinateGerm i) ^ α.val i) * algebraMap ℂ Q (C α y) := by
  classical
  let := tangentAlgebra t d
  let := normalExponentFintype d (q+1)
  obtain ⟨C,hC,hcoeff,hquot⟩ := exists_actual_whole_basis_coefficient_functions t d (q+1) F hF
  obtain ⟨U,hU,h0,hFU,hPU,hslice⟩ := exists_nearby_parameterSlice_identity t d (q+1) φ hφ hF
    (actualNormalPolynomialFunction_holAt t d (q+1) C hC) hquot
  refine ⟨U,hU,h0,C,hC,hFU,?_,?_⟩
  · intro α
    exact (normalMonomialBasis_repr_eq_coefficient t d (q+1) _ α).symm.trans (hcoeff α)
  · have hnear : ∀ᶠ y in 𝓝 (0 : ComplexModel t), ∀ α, HolAt (C α) y := by
      apply eventually_all.mpr
      intro α
      exact eventually_eventually_nhds.mpr (hC α)
    filter_upwards [hnear] with y hyC
    intro hy
    let a := tangentInclusion t d y
    have hplane : a ∈ complexCoordinatePlane (t+d) t := tangentInclusion_mem_plane t d y
    have hc : ∀ α, HolAt (C α ∘ actualAffineTranslation t y) 0 :=
      fun α => actualAffineTranslation_holAt (hyC α)
    have heq : HolGerm.mk
        (actualNormalPolynomialFunction t d (q+1) C ∘ actualAffineTranslation (t+d) a)
          (hPU a hy) =
        HolGerm.mk (actualNormalPolynomialFunction t d (q+1)
          (fun α => C α ∘ actualAffineTranslation t y))
          (actualNormalPolynomialFunction_holAt t d (q+1) _ hc) := by
      apply HolGerm.mk_eq_mk_iff.mpr
      have hp := actualNormalPolynomialFunction_actualAffineTranslation t d (q+1) C hplane
      simpa only [a,tangentProjection_tangentInclusion] using Filter.EventuallyEq.of_eq hp
    have h := hslice a hy hplane
    rw [heq, parameterSlice_actualNormalPolynomial t d (q+1) φ _ hc] at h
    simpa only [Function.comp_apply, actualAffineTranslation, add_zero] using h

end Hironaka.Analytic.Unibranch.HironakaG10MovingSliceCoefficients
