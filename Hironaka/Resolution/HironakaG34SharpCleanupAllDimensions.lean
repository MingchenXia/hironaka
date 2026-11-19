import Hironaka.Resolution.HironakaG34EquivariantSharpCleanup

/-!
# The sharp cleanup and the certified lower cleanups in every dimension, from the consumption (fifteenth brick)

Lane G34 (run 0080, round 10).  Blueprint: `hironaka-g34-resume-sharp-cleanup-all-dimensions.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §3, §8.

Read-outs of `HironakaG34EquivariantSharpCleanup` in the form of the held consumers: from the consumption
(`EquivariantLowerProtection W E d` for every lower dimension `d ≥ 3`; a named statement, NOT an axiom), the hypothesis
`CertifiedLowerCleanupsExist W E d` of the held route-(L) drivers (`HironakaG34LowerCleanupLift`,
`HironakaG34FoldRecords.exists_actual_sharp_cleanup_records`) holds in EVERY dimension, and the sharp cleanup exists for
every carrier pure of any dimension (the statement shape of `HironakaG34SharpCleanupLowDim.exists_actual_sharp_cleanup_dim_le_three`).

## Main results

* `equivariantLowerProtection_of_protection`: the consumption in every lower dimension `≥ 1` (`1`, `2` proved);
* `equivariantCertifiedLowerCleanupsExist_of_protection_all`, **`certifiedLowerCleanupsExist_of_protection_all`**;
* **`exists_actual_sharp_cleanup_of_protection`**.

New file; no existing statement changed; no sorry; no axiom.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34SharpCleanupAllDimensions
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase RestrictEmptyTower HomogenizedGlueingTower
  HironakaG34LowerCleanupLift HironakaG34DriverEquivariance HironakaG34EquivariantSharpCleanup

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The consumption in every lower dimension `≥ 1`**, from the consumption in lower dimension `≥ 3` (dimensions `1`, `2`
proved). -/
theorem equivariantLowerProtection_of_protection (hn : 0 < n)
    (hProt : ∀ d : ℕ, 3 ≤ d → ∀ {X : CMfd.{u} n} {W : Set X} {E : List (Set X)}, IsClosedSubmanifold n W →
      IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E, H) → EquivariantLowerProtection W E d)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ) (hd : 1 ≤ d) :
    EquivariantLowerProtection W E d := by
  rcases (show d = 1 ∨ d = 2 ∨ 3 ≤ d by omega) with h | h | h
  · subst h
    exact equivariantLowerProtection_one hn hW hE hdense
  · subst h
    exact equivariantLowerProtection_two hn hW hE hdense
  · exact hProt d h hW hE hdense

/-- **Equivariant certified lower cleanups in every dimension**, from the consumption in lower dimension `≥ 3`. -/
theorem equivariantCertifiedLowerCleanupsExist_of_protection_all (hn : 0 < n)
    (hProt : ∀ d : ℕ, 3 ≤ d → ∀ {X : CMfd.{u} n} {W : Set X} {E : List (Set X)}, IsClosedSubmanifold n W →
      IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E, H) → EquivariantLowerProtection W E d)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (hK : IsCompact (originalSharpBadLocus (n := n) W E)) (d : ℕ) :
    EquivariantCertifiedLowerCleanupsExist W E d := by
  rcases d with _ | d
  · exact equivariantCertifiedLowerCleanupsExist_zero hn hW hE hdense
  · exact equivariantCertifiedLowerCleanupsExist_of_protection hn hW hE hdense hK (d + 1)
      (equivariantSharpCleanupsExist_of_protection hn hProt (d + 1))
      (equivariantLowerProtection_of_protection hn hProt hW hE hdense (d + 1) (by omega))

/-- **The hypothesis of the held route-(L) drivers in every dimension**: `CertifiedLowerCleanupsExist W E d` for every
`d`, from the consumption in lower dimension `≥ 3`. -/
theorem certifiedLowerCleanupsExist_of_protection_all (hn : 0 < n)
    (hProt : ∀ d : ℕ, 3 ≤ d → ∀ {X : CMfd.{u} n} {W : Set X} {E : List (Set X)}, IsClosedSubmanifold n W →
      IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E, H) → EquivariantLowerProtection W E d)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (hK : IsCompact (originalSharpBadLocus (n := n) W E)) (d : ℕ) :
    CertifiedLowerCleanupsExist W E d :=
  certifiedLowerCleanupsExist_of_equivariant
    (equivariantCertifiedLowerCleanupsExist_of_protection_all hn hProt hW hE hdense hK d)

/-- **The sharp cleanup for a carrier pure of ANY dimension `m`**, from the consumption in lower dimension `≥ 3` (the
statement shape of `HironakaG34SharpCleanupLowDim.exists_actual_sharp_cleanup_dim_le_three`). -/
theorem exists_actual_sharp_cleanup_of_protection (hn : 0 < n)
    (hProt : ∀ d : ℕ, 3 ≤ d → ∀ {X : CMfd.{u} n} {W : Set X} {E : List (Set X)}, IsClosedSubmanifold n W →
      IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E, H) → EquivariantLowerProtection W E d)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (m : ℕ) (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x m)
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
  obtain ⟨Y, U, -, h⟩ := equivariantSharpCleanupsExist_of_protection hn hProt m X W E hW hE hdense hRegW hK
  exact ⟨Y, U, h⟩

end
end Hironaka.HironakaG34SharpCleanupAllDimensions
