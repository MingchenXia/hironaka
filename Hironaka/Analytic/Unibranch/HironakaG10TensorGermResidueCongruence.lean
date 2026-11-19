import Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift

/-! Actual entrywise holomorphic residue agreement is congruence of the
whole tensor germ modulo the entire residue ideal multiple. -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10TensorGermResidueCongruence
open Hironaka OkaRelationSheaf OkaGermBridge
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
noncomputable section
local instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] :
    Algebra ℂ (HolGerm X) := (HolGerm.constHom : ℂ →+* HolGerm X).toAlgebra

theorem tensorGermAt_sub_reference_mem_residue_ideal
    {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ) {z : X} {F : X → Q} {f₀ : X → ℂ}
    (hF : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ F x) (hf₀ : HolAt f₀ z)
    (hres : ∀ᶠ x in 𝓝 z, ε (F x) = f₀ x) :
    tensorGermAt b z F - (1 : Q) ⊗ₜ[ℂ] germAt z f₀ ∈
      RingHom.ker ε.toRingHom • (⊤ : Submodule Q (Q ⊗[ℂ] HolGerm X)) := by
  apply (residueTensor_eq_zero_iff_mem_ideal_smul ε _).mp
  rw [map_sub, residueTensor_tensorGermAt b ε hF, residueTensor_tmul, map_one, one_smul]
  rw [(germAt_eq_germAt_iff (holomorphic_residue ε hF) hf₀).mpr hres, sub_self]
end
end Hironaka.Analytic.Unibranch.HironakaG10TensorGermResidueCongruence
