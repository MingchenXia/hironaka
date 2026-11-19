import Hironaka.Analytic.Unibranch.HironakaG10BanachJetCoordinates
import Hironaka.Resolution.HironakaG10FlatPolydiscParametric

/-! # Jet coefficients of the original joint holomorphic family -/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10JointSourceJet
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetCoordinates
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients

/-- A genuinely jointly holomorphic source family gives the exact quotient
value of each original parameter slice from the coefficients of its actual
polydisc Banach-space jet. -/
theorem joint_source_germ_eq_coefficient_jet
    {Q X ι : Type*} [CommRing Q] [Algebra ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    {K : Set X} [CompactSpace K] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) (d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    {O : Set (ComplexModel d × X)} (hO : IsOpen O)
    {F : ComplexModel d × X → ℂ} (hF : DifferentiableOn ℂ F O)
    (hK : ∀ z ∈ K, (0, z) ∈ O) (z : K) :
    ∃ (_hf : ∀ᶠ s in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (restrictParam K hF) s)
      (hg : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun s => F (s,z)) s),
      φ (HolGerm.mk (fun s => F (s,z)) hg) =
        ∑ i, (((parameterTensorEquiv b (banachJet d q φ (restrictParam K hF)) i :
          holSubalgebra K) : C(K,ℂ)) z) • b i := by
  obtain ⟨δ,hδ,L,hL0,hballs,hbound⟩ := exists_tube_bound K hO hF hK
  have hnear : ∀ᶠ s in 𝓝 (0 : ComplexModel d), ∀ z ∈ K, (s,z) ∈ O := by
    filter_upwards [ball_mem_nhds (0 : ComplexModel d) hδ] with s hs z hz
    apply hballs z hz
    simpa only [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hs
  have hf : ∀ᶠ s in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (restrictParam K hF) s :=
    hnear.mono fun _ hs => differentiableAt_restrictParam K hO hF hs
  have hg : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun s => F (s,z)) s := by
    filter_upwards [hnear] with s hs
    exact ((hF (s,z) (hs z z.property)).differentiableAt (hO.mem_nhds (hs z z.property))).comp s
      (differentiableAt_id.prodMk (differentiableAt_const z.1))
  let L := (ContinuousMap.evalCLM ℂ z).comp (holSubalgebra K).toSubmodule.subtypeL
  have he : HolGerm.mk (L ∘ restrictParam K hF)
      (hf.mono fun _ h => L.differentiableAt.comp _ h) = HolGerm.mk (fun s => F (s,z)) hg := by
    apply HolGerm.mk_eq_mk_iff.mpr
    filter_upwards [hnear] with s hs
    exact restrictParam_apply K hF hs z
  refine ⟨hf,hg,?_⟩
  have hs := scalar_germ_eq_coefficient_jet b d q φ hφ (restrictParam K hF) hf L
  rw [he] at hs
  refine hs.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  congr 1

end Hironaka.Analytic.Unibranch.HironakaG10JointSourceJet
