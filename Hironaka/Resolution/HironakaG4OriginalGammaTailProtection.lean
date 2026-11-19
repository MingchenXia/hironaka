import Hironaka.Resolution.HironakaG4OriginalGammaStepProtection

/-! Induction of the original-row Gamma certificate along an actual tail. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OriginalGammaTailProtection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaG34MaskFoldEquivariance HironakaG34EquivariantLiftAction
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualCurveGlobalBoundaryCoordinates
  HironakaG4PreparedCentreCoordinates HironakaG4ProtectedResidualEndpoint
  HironakaG4OriginalGammaStepProtection HironakaG34LowerCleanupLift HironakaG34PreparedRowEmptyTail
  MemberInterLocusAlong
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan

variable {n : ℕ} {X Y Z : CMfd.{u} n}

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

/-- Under marked-one equivariant lower testness and inclusion of the selected
recorded monomial ideal, every prefix protects the original prepared row,
whose support remains its actual strict transform. -/
theorem original_gamma_tail_protects_prepared_row
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i j : Fin E.length) (hne : j ≠ i) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hPrep : ActualRowPrepared W E i T)
    (P : MarkedIdeal n Y) (hP : P.IsWellFormed) (hmark : P.d = 1)
    (hPcarrier : P.N = (geoTransformAlong (geometricTemplate W []) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
    (hle : let A := geoTransformAlong (geometricTemplate W []) T
      let old := E.map (strictAlong T)
      let oi : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
      ∀ y ∈ (A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus) ∩ P.N,
        ∀ g, (oldMonomialPart A.N old A.E oi).mem y g → P.ideal.mem y g) :
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
  let A := geoTransformAlong (geometricTemplate W []) T
  let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N = A.N at hNi
  have hOrdA : ∀ y ∈ A.N, ordinaryTraceOrder A.N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1 := by
    simpa only [hNi] using hPrep.1
  have hSiClosed : IsClosed Si :=
    (actual_original_selected_endpoint_protection hn hW hE hdense i T hT hFull hOrdA hPrep.2.1 hPrep.2.2).1.1
  intro Z R
  induction R with
  | refl =>
    intro _ _ _ _
    exact ⟨hPrep,rfl,trivial⟩
  | @step Z Q R C π hπ ih =>
    intro hTest hEq hUpper hAmbient
    have hUpper0 : IsGeoTestTower (geometricTemplate W []) (T.append R) := hUpper.1
    have hAmbient0 : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R) := hAmbient.1
    obtain ⟨hPrev,hSlice,hTail⟩ := ih hTest.1 (IsEquivariant.of_step hEq) hUpper0 hAmbient0
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
        MemberInterTowerAlong.strictAlong_subset_preimage R hP.isClosedSubmanifold_N.1 hxPStrict
      have hxi : R.proj x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus := by
        simpa only [hNi] using hxSi
      have hc := original_prepared_row_gamma_step_certificate hn hW hE hdense i j hne T hT hFull
        hPrep.1 hPrep.2.1 hPrep.2.2 P hP hmark hPcarrier R C π hπ hTest hEq x hx.1 hxi
        (fun g hg => hle _ ⟨hxSi,hxP⟩ g hg)
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

end
end Hironaka.HironakaG4OriginalGammaTailProtection
