import Hironaka.Resolution.HironakaG34GammaCertifiedLift
import Hironaka.Resolution.HironakaG4GeneralSharpBadLocus

/-! # Base cases of the terminating sharp driver (route (L)): no rows, curves

Lane G34 (run 0080, round 5).  Blueprint: `hironaka-g34-resume-driver-base-cases.tex`.

The driver of `HironakaG34LowerCleanupLift` is conditional on `CertifiedLowerCleanupsExist W E d`.
Two cases need no hypothesis:

* `certifiedLowerCleanupsExist_nil`: no rows (`E = []`), vacuous.
* `certifiedLowerCleanupsExist_zero`: `W` pure of dimension `1` (`d = 0`).  Every lower problem
  `(S_j, F_j)` at a lower entry has a carrier pure of dimension `0` (held `sharp_bad_native_domain`),
  so its sharp bad locus is empty (held `originalSharpBadLocus_eq_empty_of_regular_zero`) and the EMPTY
  tower is a certified lower cleanup (the certificate is vacuous).
* `exists_actual_sharp_cleanup_dim_one`: hence the driver (carrier phase per row, empty lower phase, then
  K3) gives the sharp cleanup of every `(W, E)` with `W` pure of dimension `1`, unconditionally.

At the lower entry the true distinct defect is empty, yet a row need not be prepared (its lower sharp bad
locus `B_j` can be nonempty: the model of `G4K1B-CONTROL-FLOW.md` §7): defect-empty alone is not
preparedness; preparedness of row `j` comes from the lower phase (`actual_lower_cleanup_row_prepared`). -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34DriverBaseCases
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms NormalCrossings NormalCrossingsComparison
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG34PreparedRowEmptyTail RestrictEmptyTower
  HomogenizedGlueingTower HironakaG4RecordedTowerResidualCompatibility
  HironakaG34LowerCleanupLift

variable {n : ℕ} {X : CMfd.{u} n}

/-- **No rows**: the residual statement is vacuous. -/
theorem certifiedLowerCleanupsExist_nil (W : Set X) (d : ℕ) :
    CertifiedLowerCleanupsExist W ([] : List (Set X)) d := by
  intro Y T _ _ _ _ _ _ P _ j _
  exact j.elim0

/-- **Curves**: when the carrier is pure of dimension `1`, every lower problem at a lower entry is
zero-dimensional, its sharp bad locus is empty, and the empty tower is a certified lower cleanup. -/
theorem certifiedLowerCleanupsExist_zero (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) :
    CertifiedLowerCleanupsExist W E 0 := by
  intro Y T hT hFull _hSharp hOrd hReg hDistinct P _hP j _hj
  obtain ⟨hL, hLreg, hLF, -, -⟩ :=
    HironakaActualSharpBadMaximumProcessedSlice.sharp_bad_native_domain
      hn hW hE hdense T hT hFull hOrd 0 hReg hDistinct j
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hFj : IsSNCDivisor n ((E.map (strictAlong T)).eraseIdx j.val ++
      (geoTransformAlong (geometricTemplate W []) T).E) :=
    isSNCDivisor_of_sublist hRec.2.1
      ((List.eraseIdx_sublist (E.map (strictAlong T)) j.val).append (List.Sublist.refl _))
  have hBad := HironakaG4GeneralSharpBadLocus.originalSharpBadLocus_eq_empty_of_regular_zero
    hL hFj hLF hLreg
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  refine ⟨Y, .refl, trivial, trivial, ?_, ?_, trivial⟩
  · change HasNormalCrossings n
      ((chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
      ((E.map (strictAlong T)).eraseIdx j.val ++ (geoTransformAlong (geometricTemplate W []) T).E)
    rw [hNj]
    intro x hx
    by_contra hnot
    have hmem : x ∈ originalSharpBadLocus (n := n)
        ((geoTransformAlong (geometricTemplate W []) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
        ((E.map (strictAlong T)).eraseIdx j.val ++
          (geoTransformAlong (geometricTemplate W []) T).E) := ⟨hx, hnot⟩
    rw [hBad] at hmem
    exact hmem
  · show ((chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus) ⊆
      closure (((chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus) \
          (⋃ D ∈ (E.map (strictAlong T)).eraseIdx j.val ++
            (geoTransformAlong (geometricTemplate W []) T).E, D))
    rw [hNj]
    exact hLF

/-- **The sharp cleanup of every `(W, E)` with `W` pure of dimension `1`**, by the terminating driver
(one carrier phase per row, empty lower phases, then K3), with no hypothesis beyond the static ones. -/
theorem exists_actual_sharp_cleanup_dim_one
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x 1)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ :=
  exists_actual_sharp_cleanup_of_certified_lower_cleanups hn hW hE hdense 0 hRegW hK
    (certifiedLowerCleanupsExist_zero hn hW hE hdense)

end
end Hironaka.HironakaG34DriverBaseCases
