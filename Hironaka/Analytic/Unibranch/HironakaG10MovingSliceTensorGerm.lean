import Hironaka.Analytic.Unibranch.HironakaG10MovingSliceCoefficients
import Hironaka.Analytic.Unibranch.HironakaG10TensorGermFiniteExpansion

/-! # Moving source slices and the actual whole tensor fibre germ -/
set_option autoImplicit false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10MovingSliceTensorGerm
open Hironaka Hironaka
  OkaRelationSheaf OkaGermBridge HironakaRelativeNormalIdeal
  HironakaRelativeNormalMonomialBasis HironakaRelativeNormalCoherentTranslatedJets
  HironakaActualJointBaseFibre HironakaG10ArtinianParameterPullback
  HironakaHolomorphicJetMonomialSpan HironakaActualRelativeCoefficientGerms
  Hironaka.Analytic.Unibranch.HironakaG10MovingSliceCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix
  Hironaka.Analytic.Unibranch.HironakaG10TensorGermFiniteExpansion

/-- A holomorphic finite-parameter family with the actual nearby parameter
slices of an original joint germ has exactly its actual whole substituted
fibre germ.  The neighborhood and the slice holomorphy are obtained from the
original joint germ; agreement is only required at those actual slices. -/
theorem exists_moving_slice_tensor_germ
    {Q ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Q) (t d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (F : ComplexModel (t+d) → ℂ) (hF : HolAt F 0) :
    ∃ U : Set (ComplexModel (t+d)), IsOpen U ∧ 0 ∈ U ∧
      ∃ hFU : ∀ a ∈ U, HolAt (F ∘ actualAffineTranslation (t+d) a) 0,
      ∀ M : ComplexModel t → Q, (∀ᶠ y in 𝓝 (0 : ComplexModel t), DifferentiableAt ℂ M y) →
        (∀ᶠ y in 𝓝 (0 : ComplexModel t), ∀ hy : tangentInclusion t d y ∈ U,
          M y = φ (jointBaseZeroTrace t d
            (HolGerm.mk (F ∘ actualAffineTranslation (t+d) (tangentInclusion t d y))
              (hFU _ hy)))) →
        tensorGermAt b 0 M = actualArtinianParameterPullback d t q φ hφ
          ((swapParameterFibre d t).symm (HolGerm.mk F hF)) := by
  classical
  let := tangentAlgebra t d
  let := normalExponentFintype d (q+1)
  obtain ⟨U,hU,h0,C,hC,hFU,hcoeff,hformula⟩ :=
    exists_moving_slice_coefficient_functions t d q φ hφ F hF
  refine ⟨U,hU,h0,hFU,?_⟩
  intro M hM hslice
  let a : normalExponentIndex d (q+1) → Q := fun α =>
    ∏ i : Fin d, φ (coordinateGerm i) ^ α.val i
  have hplane : ∀ᶠ y in 𝓝 (0 : ComplexModel t), tangentInclusion t d y ∈ U := by
    have ht : Tendsto (tangentInclusion t d) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using (tangentInclusion t d).continuous.tendsto 0
    exact ht.eventually (hU.mem_nhds h0)
  have hsum : M =ᶠ[𝓝 0] fun y => ∑ α, C α y • a α := by
    filter_upwards [hplane,hslice,hformula] with y hy hs hf
    rw [hs hy, hf hy]
    apply Finset.sum_congr rfl
    intro α _
    simp only [a, Algebra.smul_def, mul_comm]
  rw [tensorGermAt_eq_finite_expansion b Finset.univ M hM C
    (fun α _ => hC α) a hsum, actualArtinianParameterPullback_eq_sum]
  apply Finset.sum_congr rfl
  intro α _
  congr 1
  change germAt 0 (C α) = actualNormalAnalyticCoefficientGerm t d
    (swapParameterFibre d t ((swapParameterFibre d t).symm (HolGerm.mk F hF))) α.val
  rw [AlgEquiv.apply_symm_apply, hcoeff α, germAt_of_holAt (hC α)]
  congr 1
  funext y
  simp

end Hironaka.Analytic.Unibranch.HironakaG10MovingSliceTensorGerm
