import Hironaka.Resolution.HironakaG4OriginalUnitStepProtection
import Hironaka.Resolution.HironakaG4OriginalGammaFamilyProtection
import Hironaka.Resolution.HironakaG34SharpCleanupAllDimensions

/-! Original-row protection in both source monomial regimes.
The native zero-mark lower sharp tail supplies the exact all-dimensional
protection consumption, and hence the compact sharp cleanup.
Blueprint: hironaka-g4-original-mixed-tail-protection.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OriginalMixedTailProtection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaG34MaskFoldEquivariance HironakaG34EquivariantLiftAction
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualCurveGlobalBoundaryCoordinates
  HironakaG4PreparedCentreCoordinates HironakaG4RecordedTowerResidualCompatibility
  HironakaActualProtectedOtherRowLocalStep HironakaG4ActualWindowProtection
  HironakaG4OriginalUnitStepProtection HironakaG4OriginalGammaFamilyProtection
  HironakaG4ProtectedResidualEndpoint
  HironakaG34LowerCleanupLift HironakaG34PreparedRowEmptyTail HironakaG34EquivariantSharpCleanup
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  MonomialPartAlong NonmonomialTransformAlong DivisorExponentAlong MemberInterLocusAlong
  RestrictEmptyTower

variable {n : ℕ} {X Y Z Q : CMfd.{u} n}

/-- An actual equivariant lower step protects a native prepared retained
row at a source nonunit point. The actual lower mark is arbitrary. -/
theorem native_prepared_row_nonunit_step_certificate_with_window
    (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born,D))
    (i j : Fin old.length) (hne : j ≠ i)
    (hOrd : ∀ y ∈ N, ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ 1)
    (hNC : HasNormalCrossings n (N ∩ (oldResidualPart N old born i).zeroLocus)
      (old.eraseIdx i.val ++ born))
    (hDenseS : N ∩ (oldResidualPart N old born i).zeroLocus ⊆
      closure ((N ∩ (oldResidualPart N old born i).zeroLocus) \ ⋃ D ∈ old.eraseIdx i.val ++ born,D))
    (P : MarkedIdeal n X) (hPclosed : IsClosed P.N)
    (hPcarrier : P.N = N ∩ (oldResidualPart N old born j).zeroLocus)
    (R : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step R C π hπ))
    (V : Opens X) (extra : List (Set X)) (hExtra : ∀ K ∈ extra, (V : Set X) ⊆ K)
    (hEq : IsEquivariant P.N (extra ++ (old ++ born)) (.step R C π hπ))
    (x : Y) (hxC : x ∈ C) (hxV : R.proj x ∈ V)
    (hxi : R.proj x ∈ N ∩ (oldResidualPart N old born i).zeroLocus)
    (hGamma : ¬ (oldMonomialPart N old born i).mem (R.proj x) 1) :
    let S := N ∩ (oldResidualPart N old born i).zeroLocus
    ProtectedWindowAt (strictAlong R N) (strictAlong R S)
      ((old.eraseIdx i.val ++ born).map (strictAlong R) ++
        (geoTransformAlong (geometricTemplate N []) R).E) C x := by
  have hPN : P.N ⊆ N := by rw [hPcarrier]; exact inter_subset_left
  have hxP' : x ∈ strictAlong R P.N := by
    simpa only [N_geoTransformAlong] using hTest.2.subset_N hxC
  have hxP := MemberInterTowerAlong.strictAlong_subset_preimage R hPclosed hxP'
  obtain ⟨U,hxU,hUV,Haux,hEF,hTF,hSlice,hRes⟩ :=
    native_prepared_source_slice_window hn hN hFull hTr hDense i hOrd hNC hDenseS hxi V hxV
  have hxAux : (⟨R.proj x,hxU⟩ : U) ∈ Haux :=
    ((Set.ext_iff.mp hSlice ⟨R.proj x,hxU⟩).mp hxi).2
  have hLocal : ∀ᶠ y in 𝓝 (R.proj x), y ∈ P.N ↔ y ∈ N ∩ old.get j := by
    rw [hPcarrier]
    exact (retained_prepared_other_row_trace_near hn hN hFull hTr hDense i j hne
      hxi hNC hDenseS).mono (fun _ hy => hy.2.2)
  exact actual_window_parts_protect_equivariant_step_with_window hn P N _ P.N old born hPN hN
    hFull hTr hDense i j hne U Haux hEF hTF hSlice hRes R C π hπ hTest
    extra (fun K hK y hy => hExtra K hK (hUV hy)) hEq x hxC hxU hxi.1 hxAux hxP hLocal hGamma

/-- An actual equivariant lower step protects the original prepared row at
a point with nonunit source monomial part. Only closedness of the lower
carrier is needed; its mark and ideal are unrestricted. -/
theorem original_prepared_row_nonunit_step_certificate_with_window
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i j : Fin E.length) (hne : j ≠ i) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (P : MarkedIdeal n Y) (hPclosed : IsClosed P.N)
    (hPcarrier : P.N = (geoTransformAlong (geometricTemplate W []) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
    (R : BlowupTower Y Z) (C : Set Z) (π : Q → Z) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step R C π hπ))
    (V : Opens Y) (extra : List (Set Y)) (hExtra : ∀ K ∈ extra, (V : Set Y) ⊆ K)
    (hEq : IsEquivariant P.N (extra ++ ((E.map (strictAlong T)) ++
      (geoTransformAlong (geometricTemplate W []) T).E)) (.step R C π hπ))
    (x : Z) (hxC : x ∈ C) (hxV : R.proj x ∈ V)
    (hxi : R.proj x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (hGamma : let A := geoTransformAlong (geometricTemplate W []) T
      let old := E.map (strictAlong T)
      let oi : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
      ¬ (oldMonomialPart A.N old A.E oi).mem (R.proj x) 1) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
    let K := geometricTemplate A.N []
    ProtectedWindowAt (strictAlong R A.N) (strictAlong R Si)
      (((E.map (strictAlong T)).eraseIdx i.val ++ A.E).map (strictAlong R) ++
        (geoTransformAlong K R).E) C x := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun a : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let o : Fin E.length → Fin old.length := fun a => ⟨a.val,by simpa only [old,List.length_map] using a.isLt⟩
  have hGet (a : Fin E.length) : old.get (o a) = strictAlong T (E.get a) := by simp [old,o]
  have hNe : o j ≠ o i := fun he => hne (Fin.ext (congrArg (fun a : Fin old.length => a.val) he))
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N = A.N at hNi
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hJ (a : Fin E.length) : oldResidualPart A.N old A.E (o a) = J a := by
    simpa only [oldResidualPart,oldTraceIdeal,hGet] using (hRecorded.2.2.2.2 a).2.2.1
  have hOrd' : ∀ y ∈ A.N, ordinaryTraceOrder A.N (oldResidualPart A.N old A.E (o i)) y ≤ 1 := by
    rw [hJ i,←hNi]
    exact hOrd
  have hNC' : HasNormalCrossings n (A.N ∩ (oldResidualPart A.N old A.E (o i)).zeroLocus)
      (old.eraseIdx (o i).val ++ A.E) := by rw [hJ i]; exact hNC
  have hD' : A.N ∩ (oldResidualPart A.N old A.E (o i)).zeroLocus ⊆
      closure ((A.N ∩ (oldResidualPart A.N old A.E (o i)).zeroLocus) \
        ⋃ D ∈ old.eraseIdx (o i).val ++ A.E,D) := by rw [hJ i]; exact hDenseS
  have hXi : R.proj x ∈ A.N ∩ (oldResidualPart A.N old A.E (o i)).zeroLocus := by
    rw [hJ i,←hNi]
    exact hxi
  have hPcarrier' : P.N = A.N ∩ (oldResidualPart A.N old A.E (o j)).zeroLocus := by
    rw [hJ j]
    exact hPcarrier
  have hCert := native_prepared_row_nonunit_step_certificate_with_window hn hRecorded.1
    hRecorded.2.1 hRecorded.2.2.1 hRecorded.2.2.2.1 (o i) (o j) hNe hOrd' hNC' hD'
    P hPclosed hPcarrier' R C π hπ hTest V extra hExtra hEq x hxC hxV hXi hGamma
  change ProtectedWindowAt (strictAlong R A.N) (strictAlong R (A.N ∩ (oldResidualPart A.N old A.E (o i)).zeroLocus))
    ((old.eraseIdx (o i).val ++ A.E).map (strictAlong R) ++
      (geoTransformAlong (geometricTemplate A.N []) R).E) C x at hCert
  rw [hJ i] at hCert
  exact hCert

/-- Mixed nonunit protection with the full ordered actual boundary equivariance. -/
theorem original_prepared_row_nonunit_step_certificate
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i j : Fin E.length) (hne : j ≠ i) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (P : MarkedIdeal n Y) (hPclosed : IsClosed P.N)
    (hPcarrier : P.N = (geoTransformAlong (geometricTemplate W []) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
    (R : BlowupTower Y Z) (C : Set Z) (π : Q → Z) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step R C π hπ))
    (hEq : IsEquivariant P.N ((E.map (strictAlong T)) ++ (geoTransformAlong (geometricTemplate W []) T).E)
      (.step R C π hπ))
    (x : Z) (hxC : x ∈ C)
    (hxi : R.proj x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (hGamma : let A := geoTransformAlong (geometricTemplate W []) T
      let old := E.map (strictAlong T)
      let oi : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
      ¬ (oldMonomialPart A.N old A.E oi).mem (R.proj x) 1) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
    let K := geometricTemplate A.N []
    ProtectedWindowAt (strictAlong R A.N) (strictAlong R Si)
      (((E.map (strictAlong T)).eraseIdx i.val ++ A.E).map (strictAlong R) ++
        (geoTransformAlong K R).E) C x :=
  original_prepared_row_nonunit_step_certificate_with_window hn hW hE hdense i j hne T hT hFull hOrd hNC hDenseS
    P hPclosed hPcarrier R C π hπ hTest ⊤ [] (by simp) hEq x hxC (by trivial) hxi hGamma


private theorem remaining_boundary_along (W : Set X) (E : List (Set X))
    (i : Fin E.length) (T : BlowupTower X Y) (R : BlowupTower Y Z) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let K := geometricTemplate A.N []
    ((E.map (strictAlong T)).eraseIdx i.val ++ A.E).map (strictAlong R) ++
        (geoTransformAlong K R).E =
      (E.map (strictAlong (T.append R))).eraseIdx i.val ++
        (geoTransformAlong (geometricTemplate W []) (T.append R)).E := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let K := geometricTemplate A.N []
  have hOld : (E.map (strictAlong T)).map (strictAlong R) = E.map (strictAlong (T.append R)) := by
    rw [List.map_map]
    exact congrArg (fun f : Set X → Set Z => E.map f) (funext fun H => (strictAlong_append T H R).symm)
  have hBorn : (geoTransformAlong (geometricTemplate W []) (T.append R)).E =
      A.E.map (strictAlong R) ++ (geoTransformAlong K R).E := by
    rw [geoTransformAlong_append]
    exact boundary_geoTransformAlong_decomposition A K rfl R
  calc
    _ = ((E.map (strictAlong T)).eraseIdx i.val).map (strictAlong R) ++
        (A.E.map (strictAlong R) ++ (geoTransformAlong K R).E) := by
      rw [List.map_append,List.append_assoc]
    _ = (E.map (strictAlong (T.append R))).eraseIdx i.val ++
        (A.E.map (strictAlong R) ++ (geoTransformAlong K R).E) := by
      rw [←List.eraseIdx_map,hOld]
    _ = _ := by rw [←hBorn]

/-- Every equivariant lower/full test tail protects the original prepared
row, with arbitrary lower mark and no monomial ideal inclusion premise. -/
theorem original_mixed_tail_protects_prepared_row_with_window
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i j : Fin E.length) (hne : j ≠ i) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hPrep : ActualRowPrepared W E i T)
    (P : MarkedIdeal n Y) (hPclosed : IsClosed P.N)
    (hPcarrier : P.N = (geoTransformAlong (geometricTemplate W []) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
    (V : Opens Y) (extra : List (Set Y)) (hExtra : ∀ K ∈ extra, (V : Set Y) ⊆ K) :
    ∀ {Z : CMfd.{u} n} (R : BlowupTower Y Z),
      IsGeoTestTower P R →
      CentresOver (V : Set Y) R →
      IsEquivariant P.N (extra ++ ((E.map (strictAlong T)) ++
        (geoTransformAlong (geometricTemplate W []) T).E)) R →
      IsGeoTestTower (geometricTemplate W []) (T.append R) →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R) →
      ActualRowPrepared W E i (T.append R) ∧
      ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus =
        strictAlong R ((geoTransformAlong (geometricTemplate W []) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)) ∧
      ProtectedTail W E {i} T R := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N = A.N at hNi
  have hOrdA : ∀ y ∈ A.N, ordinaryTraceOrder A.N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1 := by
    simpa only [hNi] using hPrep.1
  have hSiClosed : IsClosed Si :=
    (HironakaG4ProtectedResidualEndpoint.actual_original_selected_endpoint_protection hn hW hE hdense i T hT hFull hOrdA hPrep.2.1 hPrep.2.2).1.1
  intro Z R
  induction R with
  | refl =>
    intro _ _ _ _ _
    exact ⟨hPrep,rfl,trivial⟩
  | @step Z Q R C π hπ ih =>
    intro hTest hOver hEq hUpper hAmbient
    have hUpper0 : IsGeoTestTower (geometricTemplate W []) (T.append R) := hUpper.1
    have hAmbient0 : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R) := hAmbient.1
    obtain ⟨hPrev,hSlice,hTail⟩ := ih hTest.1 hOver.1 (IsEquivariant.of_step hEq) hUpper0 hAmbient0
    have hNcur : (geoTransformAlong (geometricTemplate W []) (T.append R)).N = strictAlong R A.N := by
      rw [geoTransformAlong_append,N_geoTransformAlong]
    have hBoundary := remaining_boundary_along W E i T R
    have hCN : C ⊆ (geoTransformAlong (geometricTemplate W []) (T.append R)).N := hUpper.2.subset_N
    have hCert : ∀ x ∈ C ∩ ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus),
        ProtectedWindowAt (geoTransformAlong (geometricTemplate W []) (T.append R)).N
          ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus)
          ((E.map (strictAlong (T.append R))).eraseIdx i.val ++
            (geoTransformAlong (geometricTemplate W []) (T.append R)).E) C x := by
      intro x hx
      have hxStrict : x ∈ strictAlong R Si := by rw [←hSlice]; exact hx.2
      have hxSi : R.proj x ∈ Si := MemberInterTowerAlong.strictAlong_subset_preimage R hSiClosed hxStrict
      have hxPStrict : x ∈ strictAlong R P.N := by
        have hp := hTest.2.subset_N hx.1
        simpa only [N_geoTransformAlong] using hp
      have hxP : R.proj x ∈ P.N :=
        MemberInterTowerAlong.strictAlong_subset_preimage R hPclosed hxPStrict
      have hxi : R.proj x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus := by
        simpa only [hNi] using hxSi
      let old := E.map (strictAlong T)
      let oi : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
      have hc : let K := geometricTemplate A.N []
          ProtectedWindowAt (strictAlong R A.N) (strictAlong R Si)
            (((E.map (strictAlong T)).eraseIdx i.val ++ A.E).map (strictAlong R) ++
              (geoTransformAlong K R).E) C x := by
        by_cases hunit : (oldMonomialPart A.N old A.E oi).mem (R.proj x) 1
        · let B := geoTransformAlong (geometricTemplate (univ : Set X) E) T
          have hBE : B.E = E.map (strictAlong T) ++ A.E :=
            boundary_geoTransformAlong_decomposition (geometricTemplate (univ : Set X) E)
              (geometricTemplate W []) rfl T
          have hB : IsGeoTestTower B (.step R C π hπ) :=
            ((isGeoTestTower_append_iff (geometricTemplate (univ : Set X) E) T
              (.step R C π hπ)).mp hAmbient).2
          exact original_prepared_row_unit_step_certificate hn hW hE hdense i T hT hFull
            hPrep.1 hPrep.2.1 hPrep.2.2 P B
            (by rw [hPcarrier]; exact inter_subset_left) hBE R C π hπ hTest hB x hxi hunit
        · exact original_prepared_row_nonunit_step_certificate_with_window hn hW hE hdense i j hne T hT hFull
            hPrep.1 hPrep.2.1 hPrep.2.2 P hPclosed hPcarrier R C π hπ hTest V extra hExtra hEq
            x hx.1 (hOver.2 hx.1) hxi hunit
      dsimp only at hc hBoundary
      rw [←hNcur,←hSlice,hBoundary] at hc
      exact hc
    obtain ⟨hNext,hSliceNext⟩ := actual_row_prepared_step_of_certificate hn hW hE hdense i
      (T.append R) hUpper0 hAmbient0 hPrev C hCN π hπ hCert
    refine ⟨hNext, ?_, ⟨hTail, ?_⟩⟩
    · change ((geoTransformAlong (geometricTemplate W []) (.step (T.append R) C π hπ)).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step (T.append R) C π hπ)).ideal.zeroLocus) =
          geoStrictTransform π C (strictAlong R Si)
      rw [hSliceNext,hSlice]
    · intro k hk x hx
      have hk' : k = i := by simpa only [Finset.mem_singleton] using hk
      subst k
      exact hCert x hx

/-- Every equivariant lower test tail protects the original prepared row under the actual boundary symmetries. -/
theorem original_mixed_tail_protects_prepared_row
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i j : Fin E.length) (hne : j ≠ i) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hPrep : ActualRowPrepared W E i T)
    (P : MarkedIdeal n Y) (hPclosed : IsClosed P.N)
    (hPcarrier : P.N = (geoTransformAlong (geometricTemplate W []) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus) :
    ∀ {Z : CMfd.{u} n} (R : BlowupTower Y Z),
      IsGeoTestTower P R →
      IsEquivariant P.N ((E.map (strictAlong T)) ++ (geoTransformAlong (geometricTemplate W []) T).E) R →
      IsGeoTestTower (geometricTemplate W []) (T.append R) →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R) →
      ActualRowPrepared W E i (T.append R) ∧
      ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus =
        strictAlong R ((geoTransformAlong (geometricTemplate W []) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)) ∧
      ProtectedTail W E {i} T R := by
  intro Z R hTest hEq hUpper hAmbient
  have allCentresOverUniv : ∀ {M : CMfd.{u} n} (S : BlowupTower Y M),
      CentresOver (Set.univ : Set Y) S := by
    intro M S
    induction S with
    | refl => trivial
    | step S C π hπ ih => exact ⟨ih, fun _ _ => trivial⟩
  exact original_mixed_tail_protects_prepared_row_with_window hn hW hE hdense
    i j hne T hT hFull hPrep P hPclosed hPcarrier ⊤ [] (by simp)
    R hTest (allCentresOverUniv R) hEq hUpper hAmbient

/-- The native two-test lower sharp tail supplies the exact protection
consumption in every lower dimension. No preselected protected history,
monomial ideal inclusion or mark-one input is assumed. -/
theorem equivariantLowerProtection_all_dimensions (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ) :
    EquivariantLowerProtection W E d := by
  intro Y T hT hFull _hSharp hOrd _hReg _hDistinct I hI j hj Q R hR
  obtain ⟨h1,h2,_hLowerSharp,hEq⟩ := hR
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N =
    (geoTransformAlong (geometricTemplate W []) T).N at hNj
  have hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1 := by
    rw [hNj]
    exact fun y hy => hOrd y hy j
  let Zj := (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
    (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let Fj := old.eraseIdx j.val ++ A.E
  have hLT : IsGeoTestTower (geometricTemplate Zj Fj) R :=
    HironakaG34LowerTemplateBridge.lowerTemplate_test_of_two_tests Zj Fj R h1 h2
  obtain ⟨hZj,_hWhole,hTails⟩ :=
    HironakaG4OriginalSelectedLowerBoundaryHistory.actual_original_selected_lower_boundary_history
      hn hW hE hdense j T hT hFull hOrdj
  obtain ⟨hUpper,hAmbient,-⟩ := hTails R hLT
  have hEqFull : IsEquivariant Zj (old ++ A.E) R := by
    intro U U' φ hN hD
    apply hEq U U' φ hN
    intro H hH
    exact hD H (((List.eraseIdx_sublist old j.val).append (List.Sublist.refl A.E)).subset hH)
  have hEach : ∀ i ∈ I, ProtectedTail W E {i} T R := by
    intro i hi
    have hne : j ≠ i := fun h => hj (h ▸ hi)
    have hCarrier : (geometricTemplate Zj []).N = A.N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus := by
      change Zj = _
      exact congrArg (fun N : Set Y => N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus) hNj
    exact (original_mixed_tail_protects_prepared_row hn hW hE hdense i j hne T hT hFull
      (hI i hi) (geometricTemplate Zj []) hZj.1 hCarrier R h1 hEqFull hUpper hAmbient).2.2
  exact gammaProtectedTail_of_protectedTail R
    (protectedTail_of_singletons W E I T R hEach)

/-- An unconditional finite actual sharp cleanup for every pure smooth
carrier dimension when the original sharp bad locus is compact. -/
theorem exists_actual_compact_sharp_cleanup (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (m : ℕ) (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    (hK : IsCompact (HironakaSharpOriginalMultiBoundaryBadLocus.originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      HironakaG4CompactWholeMonomialMaskPhase.CurrentSharpCentres W E U ∧
      RestrictEmptyTower.CentresOver
        (HironakaSharpOriginalMultiBoundaryBadLocus.originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj
        (HironakaSharpOriginalMultiBoundaryBadLocus.originalSharpBadLocus (n := n) W E)ᶜ := by
  exact HironakaG34SharpCleanupAllDimensions.exists_actual_sharp_cleanup_of_protection hn
    (fun d _hd _X _W _E hW hE hdense => equivariantLowerProtection_all_dimensions hn hW hE hdense d)
    hW hE hdense m hRegW hK

end
end Hironaka.HironakaG4OriginalMixedTailProtection
