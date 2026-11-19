import Hironaka.Resolution.HironakaG34LowerCleanupLift
import Hironaka.Resolution.HironakaG34CarrierPhaseEquivariance
import Hironaka.Resolution.HironakaG34ProcessedCleanupEquivariance
import Hironaka.Resolution.HironakaG4RetainedLowerEquivariance

/-!
# The route-(L) driver with an equivariance conclusion (thirteenth brick of EQ_d)

Lane G34 (run 0080, round 10).  Blueprint: `hironaka-g34-resume-driver-equivariance.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §1 (row "lower cleanups"), §2(c)(iv).

The sharp driver of `HironakaG34LowerCleanupLift` (per row: the protected carrier phase, then ONE certified lower cleanup
of the lower problem `(Z_j, F_j) = (S_j, F_j)`; then K3) is re-run with the equivariant phases: the carrier phase of
`HironakaG34CarrierPhaseEquivariance`, lower cleanups that are equivariant for their own (lower) data, and K3 of
`HironakaG34ProcessedCleanupEquivariance`.  The new ingredient is the LIFT: along an equivariant prefix `T` the lift `χ` of a
data-preserving biholomorphism preserves the lower data `(Z_j, F_j)` (the lower carrier `S_j = N_T ∩ Z(J_j)` is cut out
by the canonical residual `J_j`, which is natural: `HironakaG34JointMaskEquivariance.pullback_residual`), so a lower tower
equivariant for `(Z_j, F_j)` appended to `T` is equivariant for `(W, E)`.

## Main results

* `residual_zeroLocus_preserved`: along an equivariant prefix the lift preserves the zero locus of every chronological
  residual row;
* **`isEquivariant_append_lower`**: an equivariant prefix followed by a tower equivariant for the lower data of a row is
  equivariant;
* `EquivariantCertifiedLowerCleanupsExist W E d` (the residual of route (L) with equivariant lower cleanups; a named
  statement, NOT assumed anywhere as an axiom), `certifiedLowerCleanupsExist_of_equivariant`;
* `exists_actual_row_step_equivariant`, `exists_actual_prefix_all_rows_prepared_equivariant`,
  **`exists_actual_sharp_cleanup_of_equivariant_certified_lower_cleanups`**: the terminating driver, with an equivariant
  output.

New file; no existing statement changed; no named input (the named statement is a hypothesis of the conditional driver,
exactly like the held `CertifiedLowerCleanupsExist`).  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34DriverEquivariance
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold NormalCrossings
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG34PreparedRowEmptyTail RestrictEmptyTower
  HomogenizedGlueingTower HironakaSharpActualChronologicalStrictStep
  HironakaG4RecordedTowerResidualCompatibility DivisorExponentAlong NormalCrossingsComparison
  BlowupTowerIsomorphism MarkedIdealBiholomorphism HironakaG4PreparedCentreCoordinates
  HironakaG34MaskFoldEquivariance HironakaG34LowerCleanupLift MonomialPartAlong RestrictedIdealExtension
open HironakaG4RetainedLowerEquivariance HironakaG4OrderedRetainedDefectTrace
  HironakaActualRetainedBornResidualSeed HironakaG4ResidualInductionInputs
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-! ### The lift of the lower data -/

section Lift

/-- **The zero locus of a chronological residual row is preserved along an equivariant prefix**: if `φ : U ≅ U'`
preserves `W` and every member of `E`, and `T` (both geometric tests) has `T|_U ≅ T|_{U'}` over `φ` with last-stage map
`χ`, then `χ` preserves the zero locus of the chronological residual of every original member. -/
theorem residual_zeroLocus_preserved (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) (j : Fin E.length) {U U' : Opens X}
    (φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U')
    (hφW : ∀ p : U, ((φ p : U') : X) ∈ W ↔ (p : X) ∈ W)
    (hφE : ∀ H ∈ E, ∀ p : U, ((φ p : U') : X) ∈ H ↔ (p : X) ∈ H)
    {χ : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U')} (hχ : IsTowerIso φ (restrict U T) (restrict U' T) χ) :
    ∀ p : openPreimage T U,
      ((χ p : openPreimage T U') : Y) ∈
          (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus ↔
        (p : Y) ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus := by
  let B := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  have hFull' : IsGeoTestTower (geometricTemplate (univ : Set X) (E ++ [])) T := by
    rw [List.append_nil]
    exact hFull
  obtain ⟨hcN, hcH⟩ := HironakaG34MaskStepEquivariance.current_data_preserved φ (old := E) (born := []) hW hφW
    (fun H hH p => hφE H (by rwa [List.append_nil] at hH) p) T hT hFull' hχ
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  let oj : Fin old.length := ⟨j.val, by simp [old]⟩
  have hGet : old.get oj = strictAlong T (E.get j) := by simp [old, oj]
  have hJ : nonmonomialPartAlong n B.N (restrictOn n B.N (vanishingIdeal (n := n) (old.get oj))) B.E =
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal := by
    rw [hGet]
    exact (hRec.2.2.2.2 j).2.2.1
  let f₁ : CMfd.of (n := n) (openPreimage T U) → Y := fun p => ((χ p : openPreimage T U') : Y)
  have hf₁ : HironakaBaseChange.IsOpenHoloEmbedding n f₁ := ⟨openPreimage T U', χ, fun _ => rfl⟩
  let f₂ : CMfd.of (n := n) (openPreimage T U) → Y := Subtype.val
  have hf₂ : HironakaBaseChange.IsOpenHoloEmbedding n f₂ :=
    HironakaBaseChange.isOpenHoloEmbedding_val (n := n) (openPreimage T U)
  have hNN : f₁ ⁻¹' B.N = f₂ ⁻¹' B.N := Set.ext fun p => hcN p
  have hHH : f₁ ⁻¹' old.get oj = f₂ ⁻¹' old.get oj :=
    Set.ext fun p => hcH _ (List.mem_append_left _ (List.get_mem old oj)) p
  have hBB : B.E.map (f₁ ⁻¹' ·) = B.E.map (f₂ ⁻¹' ·) :=
    List.map_congr_left fun H hH => Set.ext fun p => hcH H (List.mem_append_right _ hH) p
  have hz := HironakaG34JointMaskEquivariance.retained_residual_zeroLocus_preimage_eq_of_compatible_open_embeddings
    hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1 oj hf₁ hf₂ hNN hHH hBB
  change f₁ ⁻¹' (nonmonomialPartAlong n B.N
    (restrictOn n B.N (vanishingIdeal (n := n) (old.get oj))) B.E).zeroLocus =
      f₂ ⁻¹' (nonmonomialPartAlong n B.N
        (restrictOn n B.N (vanishingIdeal (n := n) (old.get oj))) B.E).zeroLocus at hz
  rw [hJ] at hz
  intro p
  exact Set.ext_iff.mp hz p

/-- **An equivariant prefix followed by a tower equivariant for the lower data of a row is equivariant**: if `T` (both
geometric tests) is equivariant for `(W, E)` and `R` is equivariant for the lower problem `(Z_j, F_j)` of row `j` at `T`
(`Z_j = S_j` the support of the chronological residual of row `j`, `F_j` the current boundary without the strict transform
of `E_j`), then `T R` is equivariant for `(W, E)`. -/
theorem isEquivariant_append_lower (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (j : Fin E.length) (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) (hEqT : IsEquivariant W E T)
    {Q : CMfd.{u} n} (R : BlowupTower Y Q)
    (hEqR : IsEquivariant ((chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
      ((E.map (strictAlong T)).eraseIdx j.val ++ (geoTransformAlong (geometricTemplate W []) T).E) R) :
    IsEquivariant W E (T.append R) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let O := E.map (strictAlong T)
  let j' : Fin O.length := Fin.cast (List.length_map _).symm j
  have hFull' : IsGeoTestTower (geometricTemplate (univ : Set X) (E ++ [])) T := by
    simpa only [List.append_nil] using hFull
  have hEqT' : IsEquivariant W (E ++ []) T := by
    simpa only [List.append_nil] using hEqT
  have hDense' : W ⊆ closure (W \ ⋃ H ∈ E ++ ([] : List (Set X)),H) := by
    simpa only [List.append_nil] using hdense
  have g : NativeRetainedGeometry W E [] :=
    ⟨hW,by simpa only [List.append_nil] using hE,isTransverse_nil_of_isClosedSubmanifold hW,hDense'⟩
  have hS : A.N ∩ (oldResidualPart A.N O A.E j').zeroLocus =
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus := by
    change (retainedResidualMarked A.N O A.E j').N ∩
      (retainedResidualMarked A.N O A.E j').ideal.zeroLocus = _
    have hSeed : retainedResidualMarked A.N O A.E j' =
        chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T :=
      retained_seed_eq_original_chronological hn hW hE hdense T hT hFull j
    rw [hSeed]
  have hLower : IsEquivariant (A.N ∩ (oldResidualPart A.N O A.E j').zeroLocus)
      (remainingBoundary O A.E j') R := by
    rw [hS]
    exact hEqR
  simpa only [List.append_nil] using
    isEquivariant_append_retained_selected_lower hn g j T hT hFull' hEqT' R hLower

end Lift

/-! ### The driver -/

section Driver

/-- **The residual of route (L) with equivariant lower cleanups** (a named statement, NOT assumed anywhere as an axiom): as
`CertifiedLowerCleanupsExist W E d`, with the certified lower cleanup of row `j` moreover equivariant for its own lower data
`(Z_j, F_j)`.  It follows from EQ_d for the lower problems together with the consumption of the route note (§3). -/
def EquivariantCertifiedLowerCleanupsExist (W : Set X) (E : List (Set X)) (d : ℕ) : Prop :=
  ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    IsGeoTestTower (geometricTemplate W []) T →
    IsGeoTestTower (geometricTemplate (univ : Set X) E) T →
    CurrentSharpCentres W E T →
    (∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N, ∀ a : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1) →
    (∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N x (d+1)) →
    chronologicalDistinctDefect W E T = ∅ →
    ∀ (P : Finset (Fin E.length)), (∀ i ∈ P, ActualRowPrepared W E i T) →
    ∀ j : Fin E.length, j ∉ P →
    ∃ (Q : CMfd.{u} n) (R : BlowupTower Y Q), CertifiedLowerCleanup W E P j T R ∧
      IsEquivariant ((chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
        ((E.map (strictAlong T)).eraseIdx j.val ++ (geoTransformAlong (geometricTemplate W []) T).E) R

/-- Forgetting the equivariance. -/
theorem certifiedLowerCleanupsExist_of_equivariant {W : Set X} {E : List (Set X)} {d : ℕ}
    (h : EquivariantCertifiedLowerCleanupsExist W E d) : CertifiedLowerCleanupsExist W E d := by
  intro Y T hT hFull hSharp hOrd hReg hDistinct P hP j hj
  obtain ⟨Q, R, hR, -⟩ := h T hT hFull hSharp hOrd hReg hDistinct P hP j hj
  exact ⟨Q, R, hR⟩

/-- **One full row of the driver, equivariantly**: the equivariant protected carrier phase, then one equivariant
certified lower cleanup; an equivariant prefix gives an equivariant result. -/
theorem exists_actual_row_step_equivariant
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hIH : EquivariantCertifiedLowerCleanupsExist W E d)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P, ActualRowPrepared W E i T)
    (j : Fin E.length) (hj : j ∉ P) :
    ∃ (Q : CMfd.{u} n) (T' : BlowupTower X Q),
      IsGeoTestTower (geometricTemplate W []) T' ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T' ∧
      CurrentSharpCentres W E T' ∧
      (∀ i ∈ insert j P, ActualRowPrepared W E i T') ∧
      (IsEquivariant W E T → IsEquivariant W E T') := by
  obtain ⟨Z, Q, hTQ, hFullTQ, hSharpTQ, _hOver, hEmpty, hRows, hEqQ, hProt⟩ :=
    HironakaG34CarrierPhaseEquivariance.exists_actual_carrier_phase_protected_equivariant hn hW hE hdense d hRegW hK
      T hT hFull hSharp
  have hPQ : ∀ i ∈ P, ActualRowPrepared W E i (T.append Q) := by
    intro i hi
    obtain ⟨U, hSU, hEmptyU⟩ := hProt i (hP i hi).1 (hP i hi).2.1 (hP i hi).2.2
    exact (actual_prepared_row_empty_tail hn hW hE hdense i T hT hFull (hP i hi) U hSU Q hTQ
      hEmptyU).1
  have hRegQ := HironakaG34CarrierPureDimension.actual_carrier_regularAtDim hW d hRegW
    (T.append Q) hTQ
  obtain ⟨Q', R, hR, hEqR⟩ := hIH (T.append Q) hTQ hFullTQ hSharpTQ hRows hRegQ hEmpty P hPQ j hj
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j))
    (T.append Q)).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).N =
    (geoTransformAlong (geometricTemplate W []) (T.append Q)).N at hNj
  have hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).ideal y ≤ 1 := by
    rw [hNj]
    exact fun y hy => hRows y hy j
  obtain ⟨h1, h2, h3, h4⟩ := actual_row_step_of_certified_lower_cleanup hn hW hE hdense
    (T.append Q) hTQ hFullTQ hSharpTQ P hPQ j hOrdj R hR
  exact ⟨Q', (T.append Q).append R, h1, h2, h3, h4,
    fun hEqT => isEquivariant_append_lower hn hW hE hdense j (T.append Q) hTQ hFullTQ (hEqQ hEqT) R hEqR⟩

/-- **The fold over the rows, equivariantly**: an equivariant actual prefix with current sharp centres at which every row
is prepared. -/
theorem exists_actual_prefix_all_rows_prepared_equivariant
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hIH : EquivariantCertifiedLowerCleanupsExist W E d) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      (∀ i : Fin E.length, ActualRowPrepared W E i T) ∧
      IsEquivariant W E T := by
  have key : ∀ P : Finset (Fin E.length), ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      (∀ i ∈ P, ActualRowPrepared W E i T) ∧
      IsEquivariant W E T := by
    intro P
    induction P using Finset.induction_on with
    | empty =>
      exact ⟨X, .refl, trivial, trivial, trivial, fun i hi => absurd hi (Finset.notMem_empty i),
        isEquivariant_refl W E⟩
    | insert j P hj ih =>
      obtain ⟨Y, T, hT, hFull, hSharp, hP, hEq⟩ := ih
      obtain ⟨Q, T', h1, h2, h3, h4, h5⟩ :=
        exists_actual_row_step_equivariant hn hW hE hdense d hRegW hK hIH T hT hFull hSharp P hP j hj
      exact ⟨Q, T', h1, h2, h3, h4, h5 hEq⟩
  obtain ⟨Y, T, hT, hFull, hSharp, hP, hEq⟩ := key Finset.univ
  exact ⟨Y, T, hT, hFull, hSharp, fun i => hP i (Finset.mem_univ i), hEq⟩

/-- **The sharp cleanup of `(W, E)` from equivariant certified lower cleanups, equivariantly** (route (L), terminating):
the conclusions of `HironakaG34LowerCleanupLift.exists_actual_sharp_cleanup_of_certified_lower_cleanups`, and the
cleanup is equivariant for `(W, E)`. -/
theorem exists_actual_sharp_cleanup_of_equivariant_certified_lower_cleanups
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hIH : EquivariantCertifiedLowerCleanupsExist W E d) :
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      IsEquivariant W E U ∧
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  obtain ⟨Y, T, hT, hFull, hSharp, hAll, hEqT⟩ :=
    exists_actual_prefix_all_rows_prepared_equivariant hn hW hE hdense d hRegW hK hIH
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
  obtain ⟨Z, R, hEqR, hTR, hFullR, hSharpR, hOverR, -, hN, hF, hNC, hProper, hIso, -⟩ :=
    HironakaG34ProcessedCleanupEquivariance.exists_actual_original_processed_sharp_cleanup_all_dimensions_equivariant
      hW hE hdense T hT hFull hSharp hK hOrd (fun i => (hAll i).2.1) (fun i => (hAll i).2.2)
  exact ⟨Z, T.append R, hEqR hEqT, hTR, hFullR, hSharpR, hOverR, hN, hF, hNC, hProper, hIso⟩

end Driver

end
end Hironaka.HironakaG34DriverEquivariance
