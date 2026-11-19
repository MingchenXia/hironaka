import Hironaka.Resolution.HironakaUniformHistoricalSuccessorOriginalRegular
import Hironaka.Resolution.HironakaActualHSConstantCentreBennett
import Hironaka.Resolution.HironakaActualWholeAmbientHSSuperlevel
import Hironaka.Resolution.HironakaResolutionSpaceSingular

/-! The SAME actual HS-constant singular history derives pointwise Bennett
and the compact ORIGINAL footprint of its persistent singular maximum.
No chartwise CAN compatibility, global clearing block or H12 termination
packet is assumed or claimed. Blueprint FIRST:
`hironaka-uniform-historical-successor-compact-footprint.tex`. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaUniformHistoricalSuccessorCompactFootprint
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualHistoricalNativeGivenTower HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaActualHSConstantCentreBennett
  HironakaActualWholeAmbientHSSuperlevel HironakaResolutionSpaceSingular
  HironakaHolomorphicJetChartInvariance BlowupTowers BlowupTowerTransforms
variable {n : ℕ} {X : CMfd.{0} n}

/-- Actual constant whole-HS centres derive EVERY-order Bennett along the
SAME whole actual history, including its literal empty steps. -/
theorem actual_hs_constant_history_pointwise_bound (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => ∀ x ∈ C, ∀ y ∈ C, ∀ ell,
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) x ell =
          hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) y ell) T →
      ∀ z ell, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z ell ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (T.proj z) ell
  | _, .refl, _, z, ell => by
      simp only [BlowupTower.proj_refl, strictTransform, preimage_id, exceptionalLocus_id,
        sdiff_empty, hW.isClosed.closure_eq, id_eq]
      exact le_rfl
  | _, .step T C π hπ, hConst, z, ell => by
      have hCurrent := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform
        T.isBlowupSequence hW
      have hOne := hilbertSamuelAt_actual_hs_constant_smooth_centre_blowup_le
        hπ hπ.1 hCurrent hConst.2 z ell
      rw [BlowupTower.proj_step,
        StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff]
      exact hOne.trans (actual_hs_constant_history_pointwise_bound W hW T hConst.1 (π z) ell)

/-- Original singular maximality, true current singular centres and their
actual HS constancy derive the persistent whole stratum's compact ORIGINAL
footprint, without a whole-W maximum or any common regular dimension. -/
theorem actual_persistent_singular_maximum_compact_footprint
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (a : X) (ha : a ∈ singularSet (n := n) W)
    (hMax : ∀ x ∈ singularSet (n := n) W,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) x) ≤
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) a))
    {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hStage : ActualHistoricalNativeTowerCentres W T)
    (hConst : StageCentres (fun P C => ∀ x ∈ C, ∀ y ∈ C, ∀ ell,
      hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) x ell =
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) y ell) T) :
    let h0 := hilbertSamuelAt (vanishingIdeal (n := n) W) a
    let WT := strictTransform n T.proj W
    let D0 := singularSet (n := n) W ∩
      actualWholeAmbientHSSuperlevel (vanishingIdeal (n := n) W) h0
    let DT := singularSet (n := n) WT ∩
      actualWholeAmbientHSSuperlevel (vanishingIdeal (n := n) WT) h0
    (∀ z ell, hilbertSamuelAt (vanishingIdeal (n := n) WT) z ell ≤
      hilbertSamuelAt (vanishingIdeal (n := n) W) (T.proj z) ell) ∧
    (∀ z ∈ singularSet (n := n) WT,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n) WT) z) ≤ toLex h0) ∧
    a ∈ D0 ∧ D0 = {x | x ∈ singularSet (n := n) W ∧
      ∀ ell, hilbertSamuelAt (vanishingIdeal (n := n) W) x ell = h0 ell} ∧
    IsComplexAnalyticSubset (n := n) D0 ∧ IsCompact D0 ∧
    DT = {z | z ∈ singularSet (n := n) WT ∧
      ∀ ell, hilbertSamuelAt (vanishingIdeal (n := n) WT) z ell = h0 ell} ∧
    IsComplexAnalyticSubset (n := n) DT ∧ IsCompact DT ∧ DT ⊆ T.proj ⁻¹' D0 := by
  let h0 := hilbertSamuelAt (vanishingIdeal (n := n) W) a
  let WT := strictTransform n T.proj W
  let D0 := singularSet (n := n) W ∩
    actualWholeAmbientHSSuperlevel (vanishingIdeal (n := n) W) h0
  let DT := singularSet (n := n) WT ∩
    actualWholeAmbientHSSuperlevel (vanishingIdeal (n := n) WT) h0
  have hBound := actual_hs_constant_history_pointwise_bound W hW T hConst
  obtain ⟨_hAvoid, _hIso, hProper, hCurrent, _hCurrentK, hSing, _hStop⟩ :=
    actual_singular_history_original_regular_protection W hW T hStage
  have hUpper (z : Y) (hz : z ∈ singularSet (n := n) WT) :
      toLex (hilbertSamuelAt (vanishingIdeal (n := n) WT) z) ≤ toLex h0 :=
    (Pi.toLex_monotone (hBound z)).trans (hMax (T.proj z) (hSing hz))
  have hD0Eq : D0 = {x | x ∈ singularSet (n := n) W ∧
      ∀ ell, hilbertSamuelAt (vanishingIdeal (n := n) W) x ell = h0 ell} := by
    ext x
    constructor
    · intro hx
      have heq := le_antisymm (hMax x hx.1) (Pi.toLex_monotone hx.2)
      exact ⟨hx.1, fun ell => congrFun (congrArg ofLex heq) ell⟩
    · rintro ⟨hx, heq⟩
      exact ⟨hx, fun ell => (heq ell).ge⟩
  have hDTEq : DT = {z | z ∈ singularSet (n := n) WT ∧
      ∀ ell, hilbertSamuelAt (vanishingIdeal (n := n) WT) z ell = h0 ell} := by
    ext z
    constructor
    · intro hz
      have heq := le_antisymm (hUpper z hz.1) (Pi.toLex_monotone hz.2)
      exact ⟨hz.1, fun ell => congrFun (congrArg ofLex heq) ell⟩
    · rintro ⟨hz, heq⟩
      exact ⟨hz, fun ell => (heq ell).ge⟩
  have hD0A : IsComplexAnalyticSubset (n := n) D0 :=
    (isComplexAnalyticSubset_singularSet hW).inter
      (isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel _
        (CartanIrreducible.cartanCoherence W hW) h0)
  have hD0K : IsCompact D0 := hK.of_isClosed_subset hD0A.isClosed
    (fun _ hx => singularSet_subset W hx.1)
  have hDTA : IsComplexAnalyticSubset (n := n) DT :=
    (isComplexAnalyticSubset_singularSet hCurrent).inter
      (isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel _
        (CartanIrreducible.cartanCoherence WT hCurrent) h0)
  have hFootprint : DT ⊆ T.proj ⁻¹' D0 := by
    intro z hz
    exact ⟨hSing hz.1, fun ell => (hz.2 ell).trans (hBound z ell)⟩
  have hDTK : IsCompact DT :=
    (hProper.isCompact_preimage hD0K).of_isClosed_subset hDTA.isClosed hFootprint
  exact ⟨hBound, hUpper, ⟨ha, fun _ => le_rfl⟩, hD0Eq, hD0A, hD0K,
    hDTEq, hDTA, hDTK, hFootprint⟩

end
end Hironaka.HironakaUniformHistoricalSuccessorCompactFootprint
