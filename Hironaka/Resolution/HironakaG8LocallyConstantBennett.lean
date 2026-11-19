import Hironaka.Resolution.HironakaStageCenters
import Hironaka.Resolution.HironakaActualHSConstantCentreBennett
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport
import Hironaka.Resolution.HironakaAdmissibleCalculus
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8LocallyConstantBennett
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupRestrictOpen HironakaEmbeddedAnalytic
  HironakaHolomorphicJetChartInvariance HironakaActualVanishingIntrinsicHSTransport
  HironakaActualHSConstantCentreBennett HironakaActualBlowupOffCentreIntrinsicHS
  HironakaBaseChange AnalyticSubsetPreimage HironakaStageCenters

/-- Bennett nonincrease needs only local HS constancy on the actual centre;
different connected centre components may carry different profiles. -/
theorem locally_constant_centre_bennett {n : ℕ} {X Y : CMfd.{0} n}
    {C W : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W)
    (hLocal : ∀ x ∈ C, ∃ O : Opens X, x ∈ O ∧
      ∀ u ∈ C, u ∈ O → ∀ v ∈ C, v ∈ O → ∀ ℓ,
        hilbertSamuelAt (vanishingIdeal (n := n) W) u ℓ =
          hilbertSamuelAt (vanishingIdeal (n := n) W) v ℓ) :
    ∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := n) W) (π z) ℓ := by
  intro z ℓ
  by_cases hz : π z ∈ C
  · obtain ⟨O,hzO,hConst⟩ := hLocal (π z) hz
    let V : Opens Y := ⟨π ⁻¹' (O : Set X), O.isOpen.preimage hπ.contMDiff.continuous⟩
    let r : V → O := fun p => ⟨π p.val,p.property⟩
    let z' : V := ⟨z,hzO⟩
    have hr : IsBlowupAlong n ((Subtype.val : O → X) ⁻¹' C) r :=
      isBlowupAlong_restrict hπ O V.isOpen
    have hCO : IsClosedSubmanifold n ((Subtype.val : O → X) ⁻¹' C) :=
      isClosedSubmanifold_preimage_val hπ.1 O
    have hWO : IsComplexAnalyticSubset (n := n) ((Subtype.val : O → X) ⁻¹' W) :=
      isComplexAnalyticSubset_preimage contMDiff_subtype_val hW
    have hConstO : ∀ u ∈ ((Subtype.val : O → X) ⁻¹' C),
        ∀ v ∈ ((Subtype.val : O → X) ⁻¹' C), ∀ ℓ,
          hilbertSamuelAt (vanishingIdeal (n := n) ((Subtype.val : O → X) ⁻¹' W)) u ℓ =
            hilbertSamuelAt (vanishingIdeal (n := n) ((Subtype.val : O → X) ⁻¹' W)) v ℓ := by
      intro u hu v hv j
      rw [hilbertSamuelAt_vanishing_actual_open_any,hilbertSamuelAt_vanishing_actual_open_any]
      exact hConst u hu u.property v hv v.property j
    have hb := hilbertSamuelAt_actual_hs_constant_smooth_centre_blowup_le hr hCO hWO hConstO z' ℓ
    have hst := strictTransform_preimage_eq hπ.contMDiff hr.contMDiff
      (isOpenHoloEmbedding_val O) (isOpenHoloEmbedding_val V) (fun _ => rfl) W
    rw [hst,hilbertSamuelAt_vanishing_actual_open_any,hilbertSamuelAt_vanishing_actual_open_any] at hb
    exact hb
  · exact (hilbertSamuelAt_actual_strict_blowup_off_centre hπ hW z hz ℓ).le

/-- Locally HS-constant centres give pointwise nonincrease along the same
actual finite tower, including all exceptional points. -/
theorem locally_constant_tower_bennett {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => ∀ x ∈ C, ∃ O : Opens _, x ∈ O ∧
        ∀ u ∈ C, u ∈ O → ∀ v ∈ C, v ∈ O → ∀ ℓ,
          hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) u ℓ =
            hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) v ℓ) T →
      ∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (T.proj z) ℓ
  | _, .refl, _, z, ℓ => by
      simp only [BlowupTower.proj_refl, strictTransform, preimage_id, exceptionalLocus_id,
        sdiff_empty, hW.isClosed.closure_eq, id_eq]
      exact le_rfl
  | _, .step T C π hπ, hs, z, ℓ => by
      have hcurrent := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform
        T.isBlowupSequence hW
      have hone := locally_constant_centre_bennett hπ hcurrent hs.2 z ℓ
      rw [BlowupTower.proj_step, StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff]
      exact hone.trans (locally_constant_tower_bennett W hW T hs.1 (π z) ℓ)
end
end Hironaka.HironakaG8LocallyConstantBennett
