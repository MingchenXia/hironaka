import Hironaka.Resolution.HironakaG10LocFrischLocus
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
open Filter Set
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10SchurSupportDirectExact
open Hironaka Hironaka
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus HironakaG10FlatGeneralizedInverse

/-- On a single nearby support point, the SAME kernel family is directly exact. -/
theorem kernel_family_directExact_on_nearby_schur_support
    {R Y : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {a b c : ℕ}
    (Fm : Y → Fin a → Fin b → R) (s₀ : Y) (g₀ : Fin b → Fin c → R)
    (hFm : ∀ᶠ s in 𝓝 s₀, DifferentiableAt ℂ Fm s)
    (hex : DirectExact g₀ (Fm s₀))
    (R₀ : (Fin b → R) →L[ℂ] (Fin c → R))
    (hR : ∀ e, matrixOperator g₀ (R₀ (matrixOperator g₀ e)) = matrixOperator g₀ e)
    (S₀ : (Fin a → R) →L[ℂ] (Fin b → R))
    (hS : ∀ e, matrixOperator (Fm s₀) (S₀ (matrixOperator (Fm s₀) e)) = matrixOperator (Fm s₀) e) :
    ∀ᶠ s in 𝓝 s₀,
      (opC ((matrixOperator g₀).comp R₀) ((matrixOperator (Fm s₀)).comp S₀) S₀
        (matrixOperator (Fm s))).IsInvertible →
      schurOp ((matrixOperator g₀).comp R₀) ((matrixOperator (Fm s₀)).comp S₀) S₀
        (matrixOperator (Fm s)) = 0 →
      DirectExact (kerFamily Fm g₀ R₀ S₀ s₀ s) (Fm s) := by
  obtain ⟨_,hG,hGT,hG0⟩ := kerFamily_spec (show s₀ ∈ (Set.univ : Set Y) from trivial) hFm hex hR hS
  let G := kerFamily Fm g₀ R₀ S₀ s₀
  have hgo : ContinuousAt (fun s => matrixOperator (G s)) s₀ :=
    (matrixOperatorCLM (R := R) (p := Fin c) (q := Fin b)).continuous.continuousAt.comp hG.self_of_nhds.continuousAt
  have hfo : ContinuousAt (fun s => matrixOperator (Fm s)) s₀ :=
    (matrixOperatorCLM (R := R) (p := Fin b) (q := Fin a)).continuous.continuousAt.comp hFm.self_of_nhds.continuousAt
  have hR' : ∀ e, matrixOperator (G s₀) (R₀ (matrixOperator (G s₀) e)) = matrixOperator (G s₀) e := by
    simpa only [G,hG0] using hR
  have hex' : ∀ x, matrixOperator (Fm s₀) x = 0 → ∃ e, matrixOperator (G s₀) e = x := by
    simpa only [G,hG0] using hex.exact
  have hc₀ : ∀ e, matrixOperator (Fm s₀) (matrixOperator (G s₀) e) = 0 := by
    simpa only [G,hG0] using matrixOperator_comp_apply g₀ (Fm s₀) hex.comp
  filter_upwards [eventually_directExact3 hgo hfo hR' hS hex' hc₀] with s hs hC hT
  have hcomp : ∀ i k, ∑ j, Fm s i j * G s j k = 0 := hGT s ⟨trivial,hC,hT⟩
  obtain ⟨he,⟨R',hR'⟩,⟨S',hS'⟩⟩ := hs (matrixOperator_comp_apply (G s) (Fm s) hcomp)
  exact ⟨hcomp,he,closedComplemented_ker_of_generalizedInverse _ S' hS',
    closedComplemented_range_of_generalizedInverse _ S' hS',
    closedComplemented_ker_of_generalizedInverse _ R' hR'⟩
end Hironaka.Analytic.Unibranch.HironakaG10SchurSupportDirectExact
