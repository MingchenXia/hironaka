import Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension

/-! # The actual finite-parameter matrix on the source tube -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
open Hironaka Hironaka
  Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterExtension

/-- The actual matrix obtained entrywise from the source family and its
Banach-space parameter jets on the larger compact box. -/
noncomputable def sourceParameterMatrix
    {Q X ι a r : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    {K : Set X} [CompactSpace K] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) (d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    {O : Set (ComplexModel d × X)} {F : a → r → ComplexModel d × X → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O) : a → r → X → Q :=
  fun i j => sourceParameterExtension (K := K) b d q φ (hF i j)

/-- The source-constructed matrix has the actual holomorphy and residue
properties required on any smaller privileged box inside the larger one. -/
theorem sourceParameterMatrix_holomorphic_residue
    {Q X ι a r : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    {K : Set X} [CompactSpace K] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) (d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (ε : Q →ₐ[ℂ] ℂ) (hε : ∀ g, ε (φ g) = HolGerm.eval g)
    {O : Set (ComplexModel d × X)} (hO : IsOpen O)
    {F : a → r → ComplexModel d × X → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK : ∀ z ∈ K, (0,z) ∈ O) :
    (∀ i j, DifferentiableOn ℂ (sourceParameterMatrix (K := K) b d q φ hF i j)
      (interior K)) ∧
    (∀ x ∈ interior K, ∀ i j, ε (sourceParameterMatrix (K := K) b d q φ hF i j x) =
      F i j (0,x)) := by
  constructor
  · intro i j
    exact differentiableOn_sourceParameterExtension (K := K) b d q φ (hF i j)
  · intro x hx i j
    exact sourceParameterExtension_residue b d q φ hφ ε hε hO (hF i j) hK
      ⟨x, interior_subset hx⟩

/-- Each entry retains the whole original parameter germ at every point of
the larger box, including points of its boundary. -/
theorem sourceParameterMatrix_eq_original
    {Q X ι a r : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    {K : Set X} [CompactSpace K] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) (d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    {O : Set (ComplexModel d × X)} (hO : IsOpen O)
    {F : a → r → ComplexModel d × X → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK : ∀ z ∈ K, (0,z) ∈ O) (z : K) (i : a) (j : r) :
    ∃ hg : ∀ᶠ s in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun s => F i j (s,z)) s,
      sourceParameterMatrix (K := K) b d q φ hF i j z =
        φ (HolGerm.mk (fun s => F i j (s,z)) hg) :=
  sourceParameterExtension_eq_original b d q φ hφ hO (hF i j) hK z

end Hironaka.Analytic.Unibranch.HironakaG10JointSourceParameterMatrix
