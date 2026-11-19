import Hironaka.Resolution.HironakaG34SharpCleanupLowDim

/-! # The G4K2D field matrix: every ordinary input of the processed contract from the constructed fold

Lane G34 (run 0080, round 7).  Blueprint: `hironaka-g34-resume-field-matrix.tex`.

The held processed sharp cleanup `HironakaActualProcessedSharpCleanup.exists_actual_processed_sharp_cleanup`
(the "processed" contract) and its all-dimension wrapper
`HironakaActualOriginalProcessedSharpCleanupAllDimensions.exists_actual_original_processed_sharp_cleanup_all_dimensions`
take, besides the static data (`hW`, `hE`, `hdense`, `hK`), a prefix `T` with the fields

| field | contract hypothesis | producer here |
|---|---|---|
| both tests | `hT`, `hFull` | the fold (`exists_actual_fold_records`) |
| current sharp centres | `hSharp` | the fold |
| residual order `≤ 1` | `hOrd` | `ActualRowPrepared.1` of every row (`joint_preparation_fields`) |
| actual NC of every support | `hNC` | `ActualRowPrepared.2.1` |
| density of every support | `hDenseS` | `ActualRowPrepared.2.2` |
| processed-row control | `hPrepared` (`IsPreparedResidualSNCAt`) | held `actual_original_processed_joint_preparedness` |
| factorization `I = D·J`, `J` = nonmonomial part, clocks | (records consumed by the contract's readback) | held `actual_original_tower_parts_and_clocks` (`PrefixRecords`) |

* `joint_preparation_fields`: from a two-test prefix at which every row is prepared, every field above.
* `exists_actual_processed_contract_from_fold`: the fold, all fields at its end, and the processed contract applied on the
  SAME history with its whole output (conditional on `CertifiedLowerCleanupsExist W E d`).
* `mother_contracts_from_fields`: the same fields fed literally into the two mother contracts
  (positive-dimensional "processed122" `exists_actual_original_processed_sharp_cleanup` and all-dimension
  "all-n303" `exists_actual_original_processed_sharp_cleanup_all_dimensions`), whole outputs returned.
* `exists_actual_processed_contract_from_fold_dim_le_three`: unconditional for `W` pure of dimension `1 ≤ m ≤ 3`. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34FieldMatrix
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms NormalCrossings NormalCrossingsComparison
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG34PreparedRowEmptyTail
  HomogenizedGlueingTower HironakaG4RecordedTowerResidualCompatibility
  HironakaG34LowerCleanupLift RestrictEmptyTower HironakaG34FoldRecords
  HironakaActualProcessedMaskFiniteBlock HironakaG4MonomialFamilyInvariant
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong
  HironakaG4PreparedCentreCoordinates

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **Every ordinary input field at a jointly prepared prefix.**  At a two-test prefix `T` at which every
original row is prepared: residual order `≤ 1`, normal crossings and density of every support (the
contract's `hOrd`, `hNC`, `hDenseS`), the processed-row control `IsPreparedResidualSNCAt` at every point
of the carrier (`hPrepared`), and the whole factorization/clock records `PrefixRecords`. -/
theorem joint_preparation_fields (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hAll : ∀ i : Fin E.length, ActualRowPrepared W E i T) :
    (∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N, ∀ i : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1) ∧
    (∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E)) ∧
    (∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E, H)) ∧
    (let A := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N, IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x) ∧
    PrefixRecords W E T := by
  have hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N, ∀ i : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1 := by
    intro x hx i
    have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
    change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N =
      (geoTransformAlong (geometricTemplate W []) T).N at hNi
    have h := (hAll i).1
    rw [hNi] at h
    exact h x hx
  refine ⟨hOrd, fun i => (hAll i).2.1, fun i => (hAll i).2.2, ?_, ?_⟩
  · exact HironakaActualOriginalProcessedJointPreparedness.actual_original_processed_joint_preparedness
      hn hW hE hdense T hT hFull hOrd (fun i => (hAll i).2.1) (fun i => (hAll i).2.2)
  · exact HironakaActualOriginalProcessedSharpCleanup.actual_original_tower_parts_and_clocks
      hn hW hE hdense T hT hFull

/-- **The two mother contracts on the SAME constructed history** (G4K2D, literal form): at the end prefix
`T` of the fold, the fields derived by `joint_preparation_fields` are exactly the ordinary inputs of the
positive-dimensional processed contract `exists_actual_original_processed_sharp_cleanup` ("processed122") and
of the all-dimension contract `exists_actual_original_processed_sharp_cleanup_all_dimensions` ("all-n303");
both are applied here and their whole outputs returned. -/
theorem mother_contracts_from_fields (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hAll : ∀ i : Fin E.length, ActualRowPrepared W E i T) :
    (∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      let U := T.append R
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      (∀ x ∈ A.N, tauD (factorMatrix W E U x) = 0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ ∧
      ∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head U k)) ∧
    (∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      let U := T.append R
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      (∀ x ∈ A.N, tauD (factorMatrix W E U x) = 0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ ∧
      ∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head U k)) := by
  obtain ⟨hOrd, hNC, hDenseS, -, -⟩ := joint_preparation_fields hn hW hE hdense T hT hFull hAll
  exact ⟨HironakaActualOriginalProcessedSharpCleanup.exists_actual_original_processed_sharp_cleanup
      hn hW hE hdense T hT hFull hSharp hK hOrd hNC hDenseS,
    HironakaActualOriginalProcessedSharpCleanupAllDimensions.exists_actual_original_processed_sharp_cleanup_all_dimensions
      hW hE hdense T hT hFull hSharp hK hOrd hNC hDenseS⟩

/-- **The G4K2D producer** (conditional on the route-(L) named statement): the fold over the ORIGINAL rows
(history chosen internally, persistent preparedness, records at every head), EVERY ordinary input field of
the processed contract at its end, and the processed contract applied on the SAME history with its whole
output. -/
theorem exists_actual_processed_contract_from_fold
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hIH : CertifiedLowerCleanupsExist W E d) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      (∀ i : Fin E.length, ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y') (R : BlowupTower Y' Y),
        T'.append R = T ∧ PreparedAlong W E i T' R) ∧
      (∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head T k)) ∧
      (∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N, ∀ i : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1) ∧
      (∀ i : Fin E.length,
        let A := geoTransformAlong (geometricTemplate W []) T
        let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
        HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E)) ∧
      (∀ i : Fin E.length,
        let A := geoTransformAlong (geometricTemplate W []) T
        let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
        S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E, H)) ∧
      (let A := geoTransformAlong (geometricTemplate W []) T
        ∀ x ∈ A.N, IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x) ∧
      PrefixRecords W E T ∧
      ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
        let U := T.append R
        let A := geoTransformAlong (geometricTemplate W []) U
        let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        CentresOver (originalSharpBadLocus (n := n) W E) U ∧
        (∀ x ∈ A.N, tauD (factorMatrix W E U x) = 0) ∧
        IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
        IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  obtain ⟨Y, T, hT, hFull, hSharp, hAlong, hRec⟩ :=
    exists_actual_fold_records hn hW hE hdense d hRegW hK hIH
  have hAll : ∀ i : Fin E.length, ActualRowPrepared W E i T := by
    intro i
    obtain ⟨Y', T', R, hEq, hAl⟩ := hAlong i
    have h := hAl.last
    rw [hEq] at h
    exact h
  obtain ⟨hOrd, hNC, hDenseS, hPrepared, hRecT⟩ :=
    joint_preparation_fields hn hW hE hdense T hT hFull hAll
  obtain ⟨Z, R, hOut⟩ := HironakaActualProcessedSharpCleanup.exists_actual_processed_sharp_cleanup
    hn hW hE hdense T hT hFull hSharp hK hOrd hNC hDenseS hPrepared
  exact ⟨Y, T, hT, hFull, hSharp, hAlong, hRec, hOrd, hNC, hDenseS, hPrepared, hRecT, Z, R, hOut⟩

/-- **The G4K2D producer, unconditional in dimensions `1 ≤ m ≤ 3`.** -/
theorem exists_actual_processed_contract_from_fold_dim_le_three
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 3)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      (∀ i : Fin E.length, ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y') (R : BlowupTower Y' Y),
        T'.append R = T ∧ PreparedAlong W E i T' R) ∧
      (∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head T k)) ∧
      (∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N, ∀ i : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1) ∧
      (∀ i : Fin E.length,
        let A := geoTransformAlong (geometricTemplate W []) T
        let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
        HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E)) ∧
      (∀ i : Fin E.length,
        let A := geoTransformAlong (geometricTemplate W []) T
        let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
        S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E, H)) ∧
      (let A := geoTransformAlong (geometricTemplate W []) T
        ∀ x ∈ A.N, IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x) ∧
      PrefixRecords W E T ∧
      ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
        let U := T.append R
        let A := geoTransformAlong (geometricTemplate W []) U
        let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        CentresOver (originalSharpBadLocus (n := n) W E) U ∧
        (∀ x ∈ A.N, tauD (factorMatrix W E U x) = 0) ∧
        IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
        IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
  have hd : d ≤ 2 := by omega
  have hIH : CertifiedLowerCleanupsExist W E d := by
    interval_cases d
    · exact HironakaG34DriverBaseCases.certifiedLowerCleanupsExist_zero hn hW hE hdense
    · exact HironakaG34SurfaceSharpCleanup.certifiedLowerCleanupsExist_one hn hW hE hdense hK
    · exact HironakaG34SurfaceProtection.certifiedLowerCleanupsExist_two hn hW hE hdense hK
  exact exists_actual_processed_contract_from_fold hn hW hE hdense d hRegW hK hIH

end
end Hironaka.HironakaG34FieldMatrix
