import Hironaka.Analytic.Unibranch.HironakaG10JointSourceJet
import Hironaka.Analytic.Unibranch.HironakaG10CoefficientHolomorphicExtension

/-! # Actual holomorphic Artinian family on the larger box interior -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatPolydiscParametric
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceJet
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientHolomorphicExtension

/-- The actual finite-parameter family constructed from the Banach jet of the
original jointly holomorphic family on the larger compact set. -/
noncomputable def sourceParameterExtension
    {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    {K : Set X} [CompactSpace K] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Q)
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    {O : Set (ComplexModel d × X)} {F : ComplexModel d × X → ℂ}
    (hF : DifferentiableOn ℂ F O) : X → Q :=
  coefficientExtension (K := K) b
    (parameterTensorEquiv (E := holSubalgebra K) b (banachJet d q φ (restrictParam K hF)))

/-- The source-constructed parameter family is holomorphic on the actual
open interior of the larger compact set. -/
theorem differentiableOn_sourceParameterExtension
    {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    {K : Set X} [CompactSpace K] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Q)
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    {O : Set (ComplexModel d × X)} {F : ComplexModel d × X → ℂ}
    (hF : DifferentiableOn ℂ F O) :
    DifferentiableOn ℂ (sourceParameterExtension (K := K) b d q φ hF) (interior K) :=
  differentiableOn_coefficientExtension (K := K) b _

/-- At every point of the larger compact set, the reconstructed parameter
value is the quotient image of the corresponding original parameter germ. -/
theorem sourceParameterExtension_eq_original
    {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    {K : Set X} [CompactSpace K] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) (d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    {O : Set (ComplexModel d × X)} (hO : IsOpen O)
    {F : ComplexModel d × X → ℂ} (hF : DifferentiableOn ℂ F O)
    (hK : ∀ z ∈ K, (0,z) ∈ O) (z : K) :
    ∃ hg : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun s => F (s,z)) s,
      sourceParameterExtension (K := K) b d q φ hF z = φ (HolGerm.mk (fun s => F (s,z)) hg) := by
  obtain ⟨hf,hg,h⟩ := joint_source_germ_eq_coefficient_jet b d q φ hφ hO hF hK z
  refine ⟨hg,?_⟩
  rw [sourceParameterExtension, coefficientExtension_apply]
  exact h.symm

/-- Every residue map compatible with the original germ evaluation sends the
constructed family to the actual initial fibre matrix entry. -/
theorem sourceParameterExtension_residue
    {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    {K : Set X} [CompactSpace K] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) (d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (ε : Q →ₐ[ℂ] ℂ) (hε : ∀ g, ε (φ g) = HolGerm.eval g)
    {O : Set (ComplexModel d × X)} (hO : IsOpen O)
    {F : ComplexModel d × X → ℂ} (hF : DifferentiableOn ℂ F O)
    (hK : ∀ z ∈ K, (0,z) ∈ O) (z : K) :
    ε (sourceParameterExtension (K := K) b d q φ hF z) = F (0,z) := by
  obtain ⟨hg,hgerm⟩ := sourceParameterExtension_eq_original b d q φ hφ hO hF hK z
  rw [hgerm, hε, HolGerm.eval_mk]

end Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension
