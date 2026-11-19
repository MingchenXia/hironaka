import Hironaka.Resolution.HironakaG34SurfaceSharpCleanup

/-! # The row fold with persistent preparedness and per-prefix records; K3 with full readback (G4K2C, G4K4A)

Lane G34 (run 0080, round 6).  Blueprint: `hironaka-g34-resume-fold-records.tex`.

The route-(L) driver of `HironakaG34LowerCleanupLift` returned only "every row prepared at the end of the
fold" and dropped part of the K3 output.  Here the same fold is restated with everything it carries:

* `PreparedAlong W E i T R`: row `i` is prepared at `T` and at every stage `T·R'` of the tail `R` (no
  reset: the rows are the chronological records of the ORIGINAL members along the SAME appended
  history).  `PreparedAlong.last`, `PreparedAlong.append`.
* `preparedAlong_of_centresAvoid` (carrier phase: literally empty near the prepared support, stage by
  stage), `preparedAlong_of_protectedTail` (certified lower cleanup, stage by stage).
* `PrefixRecords W E P`: the whole original I/D/strict-J record and the old/born/empty clocks at the
  prefix `P` (the conclusion of the held `actual_original_tower_parts_and_clocks`);
  `prefixRecords_head` (every literal head of a two-test tower carries them).
* `exists_actual_row_step_along`: one row (carrier phase, one certified lower cleanup) with persistent
  preparedness of the earlier rows.
* `exists_actual_fold_records` (G4K2C shape): the fold over the ORIGINAL rows, choosing its history
  internally from `refl`: both tests, current sharp centres, for each row a stage after which it is
  prepared at EVERY stage, and the records at every literal head.
* `exists_actual_sharp_cleanup_records` (G4K4A shape): K3 appended on the SAME history, with the full
  K3 output (zero `tauD`, full NC endpoint, the records at every head of the final tower).
* `exists_actual_sharp_cleanup_records_dim_one`, `exists_actual_sharp_cleanup_records_dim_two`:
  unconditional for `W` pure of dimension `1` or `2`. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34FoldRecords
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms NormalCrossings NormalCrossingsComparison
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG34PreparedRowEmptyTail
  HomogenizedGlueingTower HironakaG4RecordedTowerResidualCompatibility
  HironakaG34LowerCleanupLift RestrictEmptyTower
  HironakaActualProcessedMaskFiniteBlock HironakaG4MonomialFamilyInvariant
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **Persistent preparedness**: row `i` is prepared at `T` and at every stage `T·R'` of the tail `R`. -/
def PreparedAlong (W : Set X) (E : List (Set X)) (i : Fin E.length) (T : BlowupTower X Y) :
    {Q : CMfd.{u} n} → BlowupTower Y Q → Prop
  | _, .refl => ActualRowPrepared W E i T
  | _, .step R C π hπ => PreparedAlong W E i T R ∧ ActualRowPrepared W E i (T.append (.step R C π hπ))

/-- Persistent preparedness gives preparedness at the end. -/
theorem PreparedAlong.last {W : Set X} {E : List (Set X)} {i : Fin E.length} {T : BlowupTower X Y} :
    ∀ {Q : CMfd.{u} n} {R : BlowupTower Y Q}, PreparedAlong W E i T R →
      ActualRowPrepared W E i (T.append R)
  | _, .refl, h => h
  | _, .step _ _ _ _, h => h.2

/-- Persistent preparedness composes along concatenated tails. -/
theorem PreparedAlong.append {W : Set X} {E : List (Set X)} {i : Fin E.length}
    {T : BlowupTower X Y} {Q₁ : CMfd.{u} n} {R₁ : BlowupTower Y Q₁}
    (h₁ : PreparedAlong W E i T R₁) :
    ∀ {Q₂ : CMfd.{u} n} (R₂ : BlowupTower Q₁ Q₂), PreparedAlong W E i (T.append R₁) R₂ →
      PreparedAlong W E i T (R₁.append R₂)
  | _, .refl, _ => h₁
  | _, .step R₂ C π hπ, h₂ => by
      show PreparedAlong W E i T (R₁.append R₂) ∧
        ActualRowPrepared W E i (T.append (.step (R₁.append R₂) C π hπ))
      refine ⟨PreparedAlong.append h₁ R₂ h₂.1, ?_⟩
      have h := h₂.2
      rw [BlowupTower.append_assoc T R₁ (.step R₂ C π hπ)] at h
      exact h

/-- **The carrier phase keeps a prepared row prepared at every stage** (literally empty near the
prepared support: held `actual_prepared_row_empty_tail` at each stage). -/
theorem preparedAlong_of_centresAvoid
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (i : Fin E.length)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hPrep : ActualRowPrepared W E i T) (U : Opens Y)
    (hSU : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus ⊆ U) :
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      IsGeoTestTower (geometricTemplate W []) (T.append R) → CentresAvoid U R →
      PreparedAlong W E i T R
  | _, .refl, _, _ => hPrep
  | _, .step R C π hπ, hTR, hAv => by
      have hTR' : IsGeoTestTower (geometricTemplate W []) (.step (T.append R) C π hπ) := hTR
      obtain ⟨hT0, -⟩ := (isGeoTestTower_step_iff _ (T.append R) C π hπ).mp hTR'
      refine ⟨preparedAlong_of_centresAvoid hn hW hE hdense i T hT hFull hPrep U hSU R hT0 hAv.1, ?_⟩
      exact (actual_prepared_row_empty_tail hn hW hE hdense i T hT hFull hPrep U hSU
        (.step R C π hπ) hTR ((isEmptyTower_restrict_iff U _).mpr hAv)).1

/-- **A protected tail keeps the prepared rows prepared at every stage.** -/
theorem preparedAlong_of_protectedTail
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (P : Finset (Fin E.length))
    (T : BlowupTower X Y) (hP : ∀ i ∈ P, ActualRowPrepared W E i T) (i : Fin E.length)
    (hi : i ∈ P) :
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      IsGeoTestTower (geometricTemplate W []) (T.append R) →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R) →
      ProtectedTail W E P T R → PreparedAlong W E i T R
  | _, .refl, _, _, _ => hP i hi
  | _, .step R C π hπ, hTR, hFR, hProt => by
      have hTR' : IsGeoTestTower (geometricTemplate W []) (.step (T.append R) C π hπ) := hTR
      have hFR' : IsGeoTestTower (geometricTemplate (univ : Set X) E)
        (.step (T.append R) C π hπ) := hFR
      obtain ⟨hT0, -⟩ := (isGeoTestTower_step_iff _ (T.append R) C π hπ).mp hTR'
      obtain ⟨hF0, -⟩ := (isGeoTestTower_step_iff _ (T.append R) C π hπ).mp hFR'
      exact ⟨preparedAlong_of_protectedTail hn hW hE hdense P T hP i hi R hT0 hF0 hProt.1,
        actual_rows_prepared_of_protected_tail hn hW hE hdense P T hP (.step R C π hπ) hTR hFR
          hProt i hi⟩

/-- **The whole original records at a prefix `P`**: ordered boundary `old ++ born`, one born slot per
blowup (empty steps included), and for every original row the whole I/D/strict-J dictionary (the
conclusion of the held `actual_original_tower_parts_and_clocks`). -/
def PrefixRecords (W : Set X) (E : List (Set X)) (P : BlowupTower X Y) : Prop :=
  let A := geoTransformAlong (geometricTemplate W []) P
  let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) P).E
  F = E.map (strictAlong P) ++ A.E ∧ A.E.length = P.length ∧
    F.length = E.length + P.length ∧
    ∀ i : Fin E.length,
      let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong P (E.get i)))
      let D := monomialPartAlong n A.N I A.E
      let J := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) P
      J.N = A.N ∧ J.E = A.E ∧ J.d = 0 ∧ J.IsWellFormed ∧
        I.IsCoherent ∧ D.IsCoherent ∧
        nonmonomialPartAlong n A.N I A.E = J.ideal ∧
        I = restrictOn n A.N (D.mul J.ideal)

/-- **Every literal head of a two-test tower carries the whole records.** -/
theorem prefixRecords_head (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) (k : ℕ) :
    PrefixRecords W E (BlowupTowerSplit.head T k) :=
  HironakaActualOriginalProcessedSharpCleanup.actual_original_tower_parts_and_clocks hn hW hE hdense
    (BlowupTowerSplit.head T k)
    ((BlowupTowerSplit.isGeoTestTower_iff_head_tail (geometricTemplate W []) T k).mp hT).1
    ((BlowupTowerSplit.isGeoTestTower_iff_head_tail (geometricTemplate (univ : Set X) E) T k).mp
      hFull).1

/-- **One row of the driver with persistent preparedness**: carrier phase, then one certified lower
cleanup; the rows of `P` are prepared at every stage of the appended tail, row `j` at its end. -/
theorem exists_actual_row_step_along
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hIH : CertifiedLowerCleanupsExist W E d)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P, ActualRowPrepared W E i T)
    (j : Fin E.length) (hj : j ∉ P) :
    ∃ (Q : CMfd.{u} n) (V : BlowupTower Y Q),
      IsGeoTestTower (geometricTemplate W []) (T.append V) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append V) ∧
      CurrentSharpCentres W E (T.append V) ∧
      (∀ i ∈ P, PreparedAlong W E i T V) ∧ ActualRowPrepared W E j (T.append V) := by
  obtain ⟨Z, Q, hTQ, hFullTQ, hSharpTQ, _hOver, hEmpty, hRows, hProt⟩ :=
    HironakaG34DefectEmptyOrder.exists_actual_carrier_phase_protected hn hW hE hdense d hRegW hK
      T hT hFull hSharp
  have hAlongQ : ∀ i ∈ P, PreparedAlong W E i T Q := by
    intro i hi
    obtain ⟨U, hSU, hEmptyU⟩ := hProt i (hP i hi).1 (hP i hi).2.1 (hP i hi).2.2
    exact preparedAlong_of_centresAvoid hn hW hE hdense i T hT hFull (hP i hi) U hSU Q hTQ
      ((isEmptyTower_restrict_iff U Q).mp hEmptyU)
  have hPQ : ∀ i ∈ P, ActualRowPrepared W E i (T.append Q) := fun i hi => (hAlongQ i hi).last
  have hRegQ := HironakaG34CarrierPureDimension.actual_carrier_regularAtDim hW d hRegW
    (T.append Q) hTQ
  obtain ⟨Q', R, hR⟩ := hIH (T.append Q) hTQ hFullTQ hSharpTQ hRows hRegQ hEmpty P hPQ j hj
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j))
    (T.append Q)).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).N =
    (geoTransformAlong (geometricTemplate W []) (T.append Q)).N at hNj
  have hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).ideal y ≤ 1 := by
    rw [hNj]
    exact fun y hy => hRows y hy j
  obtain ⟨hTR, hFullR, hSharpR, hAll⟩ := actual_row_step_of_certified_lower_cleanup hn hW hE hdense
    (T.append Q) hTQ hFullTQ hSharpTQ P hPQ j hOrdj R hR
  have hAlongR : ∀ i ∈ P, PreparedAlong W E i (T.append Q) R := by
    intro i hi
    obtain ⟨hLT, -, -, -, hProtR⟩ := hR
    exact preparedAlong_of_protectedTail hn hW hE hdense P (T.append Q) hPQ i hi R hTR hFullR hProtR
  have hAssoc := BlowupTower.append_assoc T Q R
  refine ⟨Q', Q.append R, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hAssoc]; exact hTR
  · rw [← hAssoc]; exact hFullR
  · rw [← hAssoc]; exact hSharpR
  · intro i hi
    exact (hAlongQ i hi).append R (hAlongR i hi)
  · rw [← hAssoc]; exact hAll j (Finset.mem_insert_self j P)

/-- **The fold over the ORIGINAL rows with persistent preparedness and per-prefix records** (G4K2C
shape).  The history is chosen internally from `refl`; for every original row there is a stage after
which it is prepared at EVERY stage (`PreparedAlong`), and every literal head carries the whole
records. -/
theorem exists_actual_fold_records
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
      ∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head T k) := by
  have key : ∀ P : Finset (Fin E.length), ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      ∀ i ∈ P, ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y') (R : BlowupTower Y' Y),
        T'.append R = T ∧ PreparedAlong W E i T' R := by
    intro P
    induction P using Finset.induction_on with
    | empty =>
      exact ⟨X, .refl, trivial, trivial, trivial, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert j P hj ih =>
      obtain ⟨Y, T, hT, hFull, hSharp, hP⟩ := ih
      have hPrep : ∀ i ∈ P, ActualRowPrepared W E i T := by
        intro i hi
        obtain ⟨Y', T', R, hEq, hAl⟩ := hP i hi
        have h := hAl.last
        rw [hEq] at h
        exact h
      obtain ⟨Q, V, hTV, hFullV, hSharpV, hAlong, hjV⟩ :=
        exists_actual_row_step_along hn hW hE hdense d hRegW hK hIH T hT hFull hSharp P hPrep j hj
      refine ⟨Q, T.append V, hTV, hFullV, hSharpV, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hiP
      · exact ⟨Q, T.append V, .refl, rfl, hjV⟩
      · obtain ⟨Y', T', R, hEq, hAl⟩ := hP i hiP
        have hV := hAlong i hiP
        rw [← hEq] at hV
        refine ⟨Y', T', R.append V, ?_, hAl.append V hV⟩
        rw [← BlowupTower.append_assoc, hEq]
  obtain ⟨Y, T, hT, hFull, hSharp, hAll⟩ := key Finset.univ
  exact ⟨Y, T, hT, hFull, hSharp, fun i => hAll i (Finset.mem_univ i),
    prefixRecords_head hn hW hE hdense T hT hFull⟩

/-- **K3 appended on the SAME history, full readback** (G4K4A shape): the fold of
`exists_actual_fold_records` followed by the held all-dimension K3 cleanup, with its whole output. -/
theorem exists_actual_sharp_cleanup_records
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
        IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ ∧
        ∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head U k) := by
  obtain ⟨Y, T, hT, hFull, hSharp, hAlong, hRec⟩ :=
    exists_actual_fold_records hn hW hE hdense d hRegW hK hIH
  have hAll : ∀ i : Fin E.length, ActualRowPrepared W E i T := by
    intro i
    obtain ⟨Y', T', R, hEq, hAl⟩ := hAlong i
    have h := hAl.last
    rw [hEq] at h
    exact h
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
  obtain ⟨Z, R, hTR, hFullR, hSharpR, hOverR, hZero, hN, hF, hNC, hProper, hIso, hHeads⟩ :=
    HironakaActualOriginalProcessedSharpCleanupAllDimensions.exists_actual_original_processed_sharp_cleanup_all_dimensions
      hW hE hdense T hT hFull hSharp hK hOrd (fun i => (hAll i).2.1) (fun i => (hAll i).2.2)
  exact ⟨Y, T, hT, hFull, hSharp, hAlong, hRec, Z, R, hTR, hFullR, hSharpR, hOverR, hZero, hN, hF,
    hNC, hProper, hIso, hHeads⟩

/-- **Curves, with full records**: unconditional for `W` pure of dimension `1`. -/
theorem exists_actual_sharp_cleanup_records_dim_one
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x 1)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      (∀ i : Fin E.length, ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y') (R : BlowupTower Y' Y),
        T'.append R = T ∧ PreparedAlong W E i T' R) ∧
      (∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head T k)) ∧
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
        IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ ∧
        ∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head U k) :=
  exists_actual_sharp_cleanup_records hn hW hE hdense 0 hRegW hK
    (HironakaG34DriverBaseCases.certifiedLowerCleanupsExist_zero hn hW hE hdense)

/-- **Surfaces, with full records**: unconditional for `W` pure of dimension `2`. -/
theorem exists_actual_sharp_cleanup_records_dim_two
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x 2)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      (∀ i : Fin E.length, ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y') (R : BlowupTower Y' Y),
        T'.append R = T ∧ PreparedAlong W E i T' R) ∧
      (∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head T k)) ∧
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
        IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ ∧
        ∀ k : ℕ, PrefixRecords W E (BlowupTowerSplit.head U k) :=
  exists_actual_sharp_cleanup_records hn hW hE hdense 1 hRegW hK
    (HironakaG34SurfaceSharpCleanup.certifiedLowerCleanupsExist_one hn hW hE hdense hK)

end
end Hironaka.HironakaG34FoldRecords
