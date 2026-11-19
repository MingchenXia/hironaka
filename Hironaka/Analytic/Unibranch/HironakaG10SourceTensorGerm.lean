import Hironaka.Analytic.Unibranch.HironakaG10MovingSliceTensorGerm
import Hironaka.Analytic.Unibranch.HironakaG10TensorGermTranslate
import Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension

/-! # Whole substituted fibre germs of the actual source family -/
set_option autoImplicit false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10SourceTensorGerm
open Hironaka Hironaka
  OkaRelationSheaf OkaGermBridge HironakaRelativeNormalIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaActualCentreJointJets
  HironakaActualJointBaseFibre HironakaHolomorphicJetChartInvariance
  HironakaG10ArtinianParameterPullback
  Hironaka.Analytic.Unibranch.HironakaG10MovingSliceTensorGerm
  Hironaka.Analytic.Unibranch.HironakaG10TensorGermTranslate
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension

/-- The original joint family, in fibre-first coordinates and centered at
the actual fibre point. -/
noncomputable def sourceJointFibreFirst (t d : ℕ) (x : ComplexModel t)
    (F : ComplexModel d × ComplexModel t → ℂ) (z : ComplexModel (t+d)) : ℂ :=
  F (actualJointNormalProjection t d z, x + tangentProjection t d z)

/-- A jointly holomorphic source matrix entry produces exactly the whole
substituted original joint germ as its actual finite-parameter fibre stalk. -/
theorem sourceParameterExtension_tensorGerm
    {Q ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] (d t q : ℕ) {K : Set (ComplexModel t)} [CompactSpace K]
    (b : Module.Basis ι ℂ Q)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : ComplexModel d × ComplexModel t → ℂ} (hF : DifferentiableOn ℂ F O)
    (hK : ∀ z ∈ K, (0,z) ∈ O) (x : ComplexModel t) (hx : x ∈ interior K) :
    ∃ hG : HolAt (sourceJointFibreFirst t d x F) 0,
      tensorGermAt b x (sourceParameterExtension (K := K) b d q φ hF) =
        actualArtinianParameterPullback d t q φ hφ
          ((swapParameterFibre d t).symm (HolGerm.mk (sourceJointFibreFirst t d x F) hG)) := by
  let L : ComplexModel (t+d) → ComplexModel d × ComplexModel t := fun z =>
    (actualJointNormalProjection t d z, x + tangentProjection t d z)
  have hL : Differentiable ℂ L := fun z =>
    (actualJointNormalProjection t d).differentiableAt.prodMk
      ((differentiableAt_const x).add (tangentProjection t d).differentiableAt)
  have hL0 : L 0 = (0,x) := by simp [L]
  have hnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (t+d)), L z ∈ O := by
    have ht : Tendsto L (𝓝 0) (𝓝 (0,x)) := by simpa only [hL0] using hL.continuous.tendsto 0
    exact ht.eventually (hO.mem_nhds (hK x (interior_subset hx)))
  have hG : HolAt (sourceJointFibreFirst t d x F) 0 := by
    filter_upwards [hnear] with z hz
    exact ((hF (L z) hz).differentiableAt (hO.mem_nhds hz)).comp z (hL z)
  refine ⟨hG,?_⟩
  obtain ⟨U,hU,h0,hGU,hmatch⟩ :=
    exists_moving_slice_tensor_germ b t d q φ hφ (sourceJointFibreFirst t d x F) hG
  let M := sourceParameterExtension (K := K) b d q φ hF
  have hM : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ M z := by
    filter_upwards [isOpen_interior.mem_nhds hx] with z hz
    exact (differentiableOn_sourceParameterExtension b d q φ hF z hz).differentiableAt
      (isOpen_interior.mem_nhds hz)
  have ht : Tendsto (fun y : ComplexModel t => x+y) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun y : ComplexModel t => x+y) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : ComplexModel t)
  have hMt : ∀ᶠ y in 𝓝 (0 : ComplexModel t), DifferentiableAt ℂ (fun y => M (x+y)) y := by
    filter_upwards [ht.eventually hM] with y hy
    exact hy.comp y ((differentiableAt_const x).add differentiableAt_id)
  have hslice : ∀ᶠ y in 𝓝 (0 : ComplexModel t), ∀ hy : tangentInclusion t d y ∈ U,
      M (x+y) = φ (jointBaseZeroTrace t d
        (HolGerm.mk (sourceJointFibreFirst t d x F ∘
          actualAffineTranslation (t+d) (tangentInclusion t d y)) (hGU _ hy))) := by
    filter_upwards [ht.eventually (isOpen_interior.mem_nhds hx)] with y hy hyU
    obtain ⟨hg,hvalue⟩ := sourceParameterExtension_eq_original b d q φ hφ hO hF hK
      ⟨x+y,interior_subset hy⟩
    change M (x+y) = φ (HolGerm.mk (fun s => F (s,x+y)) hg) at hvalue
    rw [hvalue]
    apply congrArg φ
    unfold jointBaseZeroTrace
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro s
    simp [sourceJointFibreFirst, actualAffineTranslation, Function.comp_def, map_add,
      tangentProjection_tangentInclusion]
  rw [tensorGermAt_translate b x M hM]
  exact hmatch (fun y => M (x+y)) hMt hslice

end Hironaka.Analytic.Unibranch.HironakaG10SourceTensorGerm
