import Hironaka.Resolution.HironakaG10LocFrischLocus
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10NearbyCorrectedComparison
open Hironaka.HironakaG10FlatResolutionStart
  Hironaka.HironakaG10FlatPolydiscAlgebra
  Hironaka.HironakaG10LocDirectPersistence
  Hironaka.HironakaG10LocProductExact
  Hironaka.HironakaG10LocFrischLocus
noncomputable section
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

theorem corrected_relation_opA_invertible_near_origin
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {a b c : ℕ}
    {Fm : Y → Fin a → Fin b → R} {s₀ : Y} {V : Set Y} (hs₀V : s₀ ∈ V)
    (hF : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ Fm s) {g₀ : Fin b → Fin c → R}
    (hex : DirectExact g₀ (Fm s₀))
    {R₀ : (Fin b → R) →L[ℂ] (Fin c → R)}
    (hR : ∀ e, matrixOperator g₀ (R₀ (matrixOperator g₀ e)) = matrixOperator g₀ e)
    {S₀ : (Fin a → R) →L[ℂ] (Fin b → R)}
    (hS : ∀ x, matrixOperator (Fm s₀) (S₀ (matrixOperator (Fm s₀) x)) = matrixOperator (Fm s₀) x) :
    ∀ᶠ s in 𝓝 s₀, (opA ((matrixOperator g₀).comp R₀) R₀
      (matrixOperator (kerFamily Fm g₀ R₀ S₀ s₀ s))).IsInvertible := by
  have hk := kerFamily_spec hs₀V hF hex hR hS
  have hG : ContinuousAt (fun s => matrixOperator (kerFamily Fm g₀ R₀ S₀ s₀ s)) s₀ :=
    (matrixOperatorCLM (R := R) (p := Fin c) (q := Fin b)).continuous.continuousAt.comp
      hk.2.1.self_of_nhds.continuousAt
  have hA : ContinuousAt (fun s => opA ((matrixOperator g₀).comp R₀) R₀
      (matrixOperator (kerFamily Fm g₀ R₀ S₀ s₀ s))) s₀ :=
    (continuousAt_const.clm_comp (hG.clm_comp continuousAt_const)).add continuousAt_const
  exact hA (show {L : (Fin b → R) →L[ℂ] (Fin b → R) | L.IsInvertible} ∈
      𝓝 (opA ((matrixOperator g₀).comp R₀) R₀
        (matrixOperator (kerFamily Fm g₀ R₀ S₀ s₀ s₀))) by
    rw [hk.2.2.2, opA_self hR]
    exact isInvertible_mem_nhds_id)
end
end Hironaka.Analytic.Unibranch.HironakaG10NearbyCorrectedComparison
