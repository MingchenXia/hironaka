import Hironaka.Resolution.HironakaG4ActualWindowProtection
import Hironaka.Resolution.HironakaG4ProjectedLocalNonunit
import Hironaka.Resolution.HironakaActualProtectedOtherRowLocalStep

/-! Protection of a processed original row during an actual lower Gamma step. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OriginalGammaStepProtection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaG34MaskFoldEquivariance HironakaSharpActualFiniteChronologicalHistory
  HironakaG4PreparedCentreCoordinates HironakaG4RecordedTowerResidualCompatibility
  HironakaActualProtectedOtherRowLocalStep HironakaG4ProjectedLocalNonunit
  HironakaG4ActualWindowProtection HironakaG34LowerCleanupLift
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  MonomialPartAlong NonmonomialTransformAlong DivisorExponentAlong

variable {n : ℕ} {X Y Z Q : CMfd.{u} n}

/-- Under the original prepared-row hypotheses, an actual equivariant
marked-one lower step protects that row at a centre point whose projection
lies in its prepared support, provided the selected recorded monomial germ
is included in the lower ideal germ. -/
theorem original_prepared_row_gamma_step_certificate
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
    (P : MarkedIdeal n Y) (hP : P.IsWellFormed) (hmark : P.d = 1)
    (hPcarrier : P.N = (geoTransformAlong (geometricTemplate W []) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
    (R : BlowupTower Y Z) (C : Set Z) (π : Q → Z) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step R C π hπ))
    (hEq : IsEquivariant P.N ((E.map (strictAlong T)) ++ (geoTransformAlong (geometricTemplate W []) T).E)
      (.step R C π hπ))
    (x : Z) (hxC : x ∈ C)
    (hxi : R.proj x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (hIncl : let A := geoTransformAlong (geometricTemplate W []) T
      let old := E.map (strictAlong T)
      let oi : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
      ∀ g, (oldMonomialPart A.N old A.E oi).mem (R.proj x) g → P.ideal.mem (R.proj x) g) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
    let K := geometricTemplate A.N []
    ProtectedWindowAt (strictAlong R A.N) (strictAlong R Si)
      (((E.map (strictAlong T)).eraseIdx i.val ++ A.E).map (strictAlong R) ++
        (geoTransformAlong K R).E) C x := by
  dsimp only
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let born := A.E
  let J := fun h : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal
  let Si := A.N ∩ (J i).zeroLocus
  let Sj := A.N ∩ (J j).zeroLocus
  let oi : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
  let oj : Fin old.length := ⟨j.val,by simpa only [old,List.length_map] using j.isLt⟩
  have hGeti : old.get oi = strictAlong T (E.get i) := by simp [old,oi]
  have hGetj : old.get oj = strictAlong T (E.get j) := by simp [old,oj]
  have hne' : oj ≠ oi := by
    intro he
    have hv := congrArg Fin.val he
    change j.val = i.val at hv
    exact hne (Fin.ext hv)
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N = A.N at hNi
  have hxSi : R.proj x ∈ Si := by simpa only [hNi] using hxi
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hPN : P.N ⊆ A.N := by rw [hPcarrier]; exact inter_subset_left
  have hxP' : x ∈ strictAlong R P.N := by
    have hc := hTest.2.subset_N hxC
    simpa only [N_geoTransformAlong] using hc
  have hxP : R.proj x ∈ P.N := MemberInterTowerAlong.strictAlong_subset_preimage R hP.isClosedSubmanifold_N.1 hxP'
  have hxSj : R.proj x ∈ Sj := by simpa only [hPcarrier] using hxP
  obtain ⟨U,hxU,_hU,Haux,hEF,hTF,hSlice,hWhole,hOther⟩ :=
    protected_slice_window hn hW hE hdense i T hT hFull hOrd hNC hDenseS hxi ⊤ (by trivial)
  have hxAux : (⟨R.proj x,hxU⟩ : U) ∈ Haux :=
    ((Set.ext_iff.mp hSlice ⟨R.proj x,hxU⟩).mp hxSi).2
  have hJ : oldResidualPart A.N old born oi = J i := by
    simpa only [oldResidualPart,oldTraceIdeal,hGeti] using (hRecorded.2.2.2.2 i).2.2.1
  have hRes : GermIdeal.pullback (m := n) (Subtype.val : U → Y) (oldResidualPart A.N old born oi) =
      vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' Si) := by
    rw [hJ]
    exact hWhole
  have hWlocal : ∀ᶠ y in 𝓝 (R.proj x), y ∈ P.N ↔ y ∈ A.N ∩ old.get oj := by
    filter_upwards [U.isOpen.mem_nhds hxU] with y hyU
    have hh := Set.ext_iff.mp (hOther j hne).2 ⟨y,hyU⟩
    change (y ∈ A.N ∩ (J j).zeroLocus ↔ y ∈ A.N ∩ strictAlong T (E.get j)) at hh
    rw [hPcarrier,hGetj]
    exact hh
  have hGamma : ¬ (oldMonomialPart A.N old born oi).mem (R.proj x) 1 :=
    projected_centre_nonunit_of_local_inclusion P hP hmark _ R C π hπ hTest hxC hIncl
  have hEq' : IsEquivariant P.N (old ++ born) (.step R C π hπ) := hEq
  have hEF' : IsSNCDivisor n (Haux :: (old.eraseIdx oi.val ++ born).map ((Subtype.val : U → Y) ⁻¹' ·)) := hEF
  have hTF' : IsTransverse n ((Subtype.val : U → Y) ⁻¹' A.N)
      (Haux :: (old.eraseIdx oi.val ++ born).map ((Subtype.val : U → Y) ⁻¹' ·)) := hTF
  exact actual_window_parts_protect_equivariant_step hn P A.N Si P.N old born hPN hRecorded.1
    hRecorded.2.1 hRecorded.2.2.1 hRecorded.2.2.2.1 oi oj hne' U Haux hEF' hTF' hSlice hRes
    R C π hπ hTest hEq' x hxC hxU hxSi.1 hxAux hxP hWlocal hGamma

end
end Hironaka.HironakaG4OriginalGammaStepProtection
