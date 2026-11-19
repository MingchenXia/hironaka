import Hironaka.Resolution.HironakaG34SurfaceProtection

/-! # The sharp cleanup in every dimension `≤ 3`, unconditional (dispatch)

Lane G34 (run 0080, round 6).  Blueprint: `hironaka-g34-resume-sharp-cleanup-low-dim.tex`.

* `exists_actual_sharp_cleanup_dim_zero`: `W` pure of dimension `0`: the original sharp bad locus is empty
  (held `originalSharpBadLocus_eq_empty_of_regular_zero`) and the empty tower is a sharp cleanup.
* `exists_actual_sharp_cleanup_dim_le_three`: for `W` pure of dimension `m ≤ 3` the sharp cleanup exists
  (dimension `0`: empty tower; `1`, `2`, `3`: `exists_actual_sharp_cleanup_dim_one/_two/_three`). -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34SharpCleanupLowDim
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HomogenizedGlueingTower RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Points**: for `W` pure of dimension `0` the empty tower is a sharp cleanup. -/
theorem exists_actual_sharp_cleanup_dim_zero {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x 0) :
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  have hBad := HironakaG4GeneralSharpBadLocus.originalSharpBadLocus_eq_empty_of_regular_zero
    hW hE hdense hRegW
  refine ⟨X, .refl, trivial, trivial, trivial, trivial, hW, hE, ?_, ?_, ?_⟩
  · change HasNormalCrossings n W E
    intro x hx
    by_contra hnot
    have hmem : x ∈ originalSharpBadLocus (n := n) W E := ⟨hx, hnot⟩
    rw [hBad] at hmem
    exact hmem
  · change IsProperMap (id : X → X)
    exact isProperMap_id
  · change IsIsomorphismOver n (id : X → X) (originalSharpBadLocus (n := n) W E)ᶜ
    refine ⟨?_, ?_⟩
    · simpa using (bijOn_id (originalSharpBadLocus (n := n) W E)ᶜ)
    · rw [exceptionalLocus_id]
      exact disjoint_empty _

/-- **Every dimension `≤ 3`, unconditional**: the sharp cleanup of every `(W, E)` with `W` a closed
submanifold pure of dimension `m ≤ 3`, `E` simple normal crossings, `W` dense off `E`, compact original
sharp bad locus. -/
theorem exists_actual_sharp_cleanup_dim_le_three
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (m : ℕ) (hm : m ≤ 3)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  interval_cases m
  · exact exists_actual_sharp_cleanup_dim_zero hW hE hdense hRegW
  · exact HironakaG34DriverBaseCases.exists_actual_sharp_cleanup_dim_one hn hW hE hdense hRegW hK
  · exact HironakaG34SurfaceSharpCleanup.exists_actual_sharp_cleanup_dim_two hn hW hE hdense hRegW hK
  · exact HironakaG34SurfaceProtection.exists_actual_sharp_cleanup_dim_three hn hW hE hdense hRegW hK

end
end Hironaka.HironakaG34SharpCleanupLowDim
