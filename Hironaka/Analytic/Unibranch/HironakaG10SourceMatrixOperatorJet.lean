import Hironaka.Analytic.Unibranch.HironakaG10MatrixOperatorJetWhole
import Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
import Hironaka.Resolution.HironakaG10FlatPolydiscParametric

/-! # Original joint source matrix and its actual Artinian operator jet -/
set_option autoImplicit false
open Filter Set Metric
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10SourceMatrixOperatorJet
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
  Hironaka.Analytic.Unibranch.HironakaG10MatrixOperatorJetWhole

/-- On every coefficient input, the actual operator jet of the original
joint source matrix restricted to the smaller compact K₁ is exactly the
Artinian matrix action of the Q-valued family constructed from K₀. -/
theorem sourceMatrixOperatorJet_eq_artinian_whole
    {Q X r a ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    {K₀ K₁ : Set X} [CompactSpace K₀] [CompactSpace K₁]
    [Fintype r] [Fintype a] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) (d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    {O : Set (ComplexModel d × X)} (hO : IsOpen O)
    {F : a → r → ComplexModel d × X → ℂ} (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O) (hK₁ : K₁ ⊆ interior K₀) :
    ∃ hFQ : ∀ i j, DifferentiableOn ℂ
      (sourceParameterMatrix (K := K₀) b d q φ hF i j) (interior K₀),
    ∀ v : ι → r → holSubalgebra K₁,
      parameterTensorEquiv (E := a → holSubalgebra K₁) b
        (tensorOperator (Γ := Q) (E := r → holSubalgebra K₁) (F := a → holSubalgebra K₁)
          (banachJet (E := (r → holSubalgebra K₁) →L[ℂ] (a → holSubalgebra K₁)) d q φ
            (fun s => matrixOperator (fun i j => restrictParam K₁ (hF i j) s)))
          ((parameterTensorEquiv (E := r → holSubalgebra K₁) b).symm v)) =
      banachMatrixCLM b hK₁ (sourceParameterMatrix (K := K₀) b d q φ hF) hFQ v := by
  classical
  have hK₁O : ∀ z ∈ K₁, (0,z) ∈ O := fun z hz => hK₀ z (interior_subset (hK₁ hz))
  have hzero : DifferentiableOn ℂ (fun _ : ComplexModel d × X => (0 : ℂ)) O :=
    differentiableOn_const 0
  obtain ⟨δ,hδ,L,hL,hballs,hbound⟩ := exists_tube_bound K₁ hO hzero hK₁O
  have hnear : ∀ᶠ s in 𝓝 (0 : ComplexModel d), ∀ z ∈ K₁, (s,z) ∈ O := by
    filter_upwards [ball_mem_nhds (0 : ComplexModel d) hδ] with s hs z hz
    apply hballs z hz
    simpa only [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hs
  let M : ComplexModel d → a → r → holSubalgebra K₁ :=
    fun s i j => restrictParam K₁ (hF i j) s
  have hM : ∀ i j, ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun s => M s i j) s := by
    intro i j
    exact hnear.mono fun _ hs => differentiableAt_restrictParam K₁ hO (hF i j) hs
  let FQ := sourceParameterMatrix (K := K₀) b d q φ hF
  have hFQ : ∀ i j, DifferentiableOn ℂ (FQ i j) (interior K₀) := by
    intro i j
    exact differentiableOn_sourceParameterExtension (K := K₀) b d q φ (hF i j)
  have hpoint : ∀ (z : K₁) i j, ∃ hg : ∀ᶠ s in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun s => ((M s i j : holSubalgebra K₁) : C(K₁,ℂ)) z) s,
      φ (HolGerm.mk (fun s => ((M s i j : holSubalgebra K₁) : C(K₁,ℂ)) z) hg) = FQ i j z := by
    intro z i j
    let Lz := (ContinuousMap.evalCLM ℂ z).comp (holSubalgebra K₁).toSubmodule.subtypeL
    have hm : ∀ᶠ s in 𝓝 (0 : ComplexModel d),
        DifferentiableAt ℂ (fun s => ((M s i j : holSubalgebra K₁) : C(K₁,ℂ)) z) s :=
      (hM i j).mono fun _ h => Lz.differentiableAt.comp _ h
    let z₀ : K₀ := ⟨z.1, interior_subset (hK₁ z.property)⟩
    obtain ⟨hg,hsource⟩ := sourceParameterMatrix_eq_original b d q φ hφ hO hF hK₀ z₀ i j
    have heq : HolGerm.mk (fun s => ((M s i j : holSubalgebra K₁) : C(K₁,ℂ)) z) hm =
        HolGerm.mk (fun s => F i j (s,z)) hg := by
      apply HolGerm.mk_eq_mk_iff.mpr
      filter_upwards [hnear] with s hs
      exact restrictParam_apply K₁ (hF i j) hs z
    refine ⟨hm,?_⟩
    rw [heq]
    exact hsource.symm
  refine ⟨hFQ,?_⟩
  exact matrixOperatorJet_eq_artinian_whole b d q φ hφ M hM FQ hK₁ hFQ hpoint

end Hironaka.Analytic.Unibranch.HironakaG10SourceMatrixOperatorJet
