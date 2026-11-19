import Hironaka.Resolution.HironakaG4MixedOldResidualStep
import Hironaka.Resolution.HironakaSharpActualChronologicalResidualDictionary
import Hironaka.Resolution.HironakaSharpActualCurveWholeBoundaryTransversality
import Mathlib.Topology.Baire.Lemmas

set_option autoImplicit false

/-! Actual canonical whole residuals equal the SAME original chronological
ideals on one genuine recorded geometric tower. No future comparison packet.
Source-first chapter: hironaka-g4-recorded-tower-residual-compatibility.tex. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RecordedTowerResidualCompatibility
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison MonomialPartAlong DivisorExponentAlong
  RelativePrincipalizationSpan RestrictedIdealExtension NonmonomialTransformAlong
  HironakaG4MixedOldResidualStep HironakaG4PreparedCentreCoordinates
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalResidualDictionary
  HironakaSharpActualCurveWholeBoundaryTransversality
  HironakaSharpActualMixedCentreWholeStrictTraceGeometry
  HironakaSharpActualFirstAmbientStrictExponent
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalMemberProduct
  IdealWeightPowers InvertibleIdealQuotient

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem dense_diff_list_of_member_density {N : Set X} (L : List (Set X))
    (hclosed : ∀ H ∈ L,IsClosed H) (hdense : ∀ H ∈ L,N ⊆ closure (N \ H)) :
    N ⊆ closure (N \ ⋃ H ∈ L,H) := by
  let F : Fin L.length → Set N := fun i => {x | (x : X) ∉ L.get i}
  have hOpen : ∀ i,IsOpen (F i) := fun i =>
    (hclosed _ (List.get_mem L i)).isOpen_compl.preimage continuous_subtype_val
  have hDense : ∀ i,Dense (F i) := by
    intro i
    apply Subtype.dense_iff.mpr
    have hImg : (Subtype.val : N → X) '' F i=N \ L.get i := by
      ext x
      simp only [mem_image,Set.mem_sdiff,F,mem_ofPred_eq]
      exact ⟨fun ⟨q,hq,hqeq⟩ => hqeq ▸ ⟨q.property,hq⟩,
        fun hx => ⟨⟨x,hx.1⟩,hx.2,rfl⟩⟩
    rw [hImg]
    exact hdense _ (List.get_mem L i)
  have hAll : Dense (⋂ i,F i) := by
    have hs := (Set.finite_range F).dense_sInter
      (by rintro _ ⟨i,rfl⟩; exact hOpen i)
      (by rintro _ ⟨i,rfl⟩; exact hDense i)
    simpa only [sInter_range] using hs
  have hImg : (Subtype.val : N → X) '' (⋂ i,F i)=N \ ⋃ H ∈ L,H := by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩
      refine ⟨q.property,?_⟩
      rintro hUnion
      obtain ⟨H,hHL,hqH⟩ := mem_iUnion₂.mp hUnion
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hHL
      exact (mem_iInter.mp hq i) (hi ▸ hqH)
    · intro hx
      refine ⟨⟨x,hx.1⟩,mem_iInter.mpr (fun i => ?_),rfl⟩
      exact fun hi => hx.2 (mem_iUnion₂.mpr ⟨L.get i,List.get_mem L i,hi⟩)
  rw [←hImg]
  exact Subtype.dense_iff.mp hAll

private theorem recorded_geometry {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) :
    let A := geoTransformAlong (geometricTemplate W []) T
    IsClosedSubmanifold n A.N ∧ IsSNCDivisor n (E.map (strictAlong T) ++ A.E) ∧
      IsTransverse n A.N A.E := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  have hwF : (geometricTemplate (univ : Set X) E).IsWellFormed :=
    ⟨⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
      isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hSNC := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwF T hFull).isSNCDivisor
  rw [actual_whole_ambient_boundary_ordered_dictionary W E T] at hSNC
  exact ⟨hwT.isClosedSubmanifold_N,hSNC,hwT.isTransverse⟩

private theorem full_density_of_actual_old_nonzero (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (T : BlowupTower X Y)
    (hN : IsClosedSubmanifold n (geoTransformAlong (geometricTemplate W []) T).N)
    (hSNC : IsSNCDivisor n
      (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E))
    (hTr : IsTransverse n (geoTransformAlong (geometricTemplate W []) T).N
      (geoTransformAlong (geometricTemplate W []) T).E)
    (hnz : ∀ i : Fin E.length,∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      IsNonzeroAlongAt (geoTransformAlong (geometricTemplate W []) T).N
        (restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
          (vanishingIdeal (n := n) (strictAlong T (E.get i)))) y) :
    let A := geoTransformAlong (geometricTemplate W []) T
    A.N ⊆ closure (A.N \ ⋃ H ∈ E.map (strictAlong T) ++ A.E,H) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  apply dense_diff_list_of_member_density _ hSNC.1
  intro H hH
  rcases List.mem_append.mp hH with hH | hH
  · obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hH
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH₀
    exact actual_density_of_nonzero_normalized_vanishing (hnz i)
  · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hH
    have hBorn := isSNCDivisor_of_sublist hSNC (List.sublist_append_right _ _)
    have hSingle : IsSNCDivisor n [H] := by
      rw [←hi]
      exact isSNCDivisor_of_sublist hBorn (by simp)
    have hT : IsTransverse n A.N [H] := by
      apply isTransverse_of_forall_mem hTr
      intro K hK
      rw [List.mem_singleton.mp hK]
      exact hH
    have hGeom := actual_normalized_transverse_member_geometry hn hN hSingle hT
    exact actual_density_of_nonzero_normalized_vanishing hGeom.2.1

private theorem recorded_density_and_residuals (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T →
      let A := geoTransformAlong (geometricTemplate W []) T
      A.N ⊆ closure (A.N \ ⋃ H ∈ E.map (strictAlong T) ++ A.E,H) ∧
        ∀ i : Fin E.length,
          let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))
          I.IsCoherent ∧ (∀ y ∈ A.N,IsNonzeroAlongAt A.N I y) ∧
            nonmonomialPartAlong n A.N I A.E=
              (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  | _,.refl,_hT,_hFull => by
    refine ⟨?_,fun i => ?_⟩
    · simpa [geometricTemplate,geoTransformAlong,strictAlong] using hdense
    · let I := restrictOn n W (vanishingIdeal (n := n) (E.get i))
      change I.IsCoherent ∧ (∀ y ∈ W,IsNonzeroAlongAt W I y) ∧
        nonmonomialPartAlong n W I []=I
      have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
        (MonomialPart.isClosedSubmanifold_get hn hE i)
      have hcI : I.IsCoherent := isCoherent_restrictOn hcH
        (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)
      have hnzI : ∀ y ∈ W,IsNonzeroAlongAt W I y := by
        intro y hy
        obtain ⟨g,hg,hfreq⟩ := originalMemberIdeal_isNonzeroAlongAt hE hdense (List.get_mem E i) hy
        exact ⟨g,le_restrictOn hcH y g hg,hfreq⟩
      have hDict := original_members_actual_chronological_residual_dictionary
        hn hW hE hdense i (.refl : BlowupTower X X) (by trivial)
      have hNm : nonmonomialPartAlong n W I []=restrictOn n W I := hDict.2.2.1
      have hNorm : restrictOn n W I=I := by
        ext y g
        exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
          fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
      exact ⟨hcI,hnzI,hNm.trans hNorm⟩
  | _,.step T C π hπ,hT,hFull => by
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let A' := geoTransformAlong (geometricTemplate W []) (.step T C π hπ)
    obtain ⟨hDense,hRows⟩ := recorded_density_and_residuals hn hW hE hdense T hT.1 hFull.1
    obtain ⟨hN,hSNC,hTr⟩ := recorded_geometry hW hE T hT.1 hFull.1
    have hCN : C ⊆ A.N := hT.2.subset_N
    have hCNC : HasNormalCrossings n C (old ++ A.E) := by
      rw [←actual_whole_ambient_boundary_ordered_dictionary W E T]
      exact hFull.2.2.2
    have hRowsNew : ∀ i : Fin E.length,
        let I := restrictOn n A'.N
          (vanishingIdeal (n := n) (strictAlong (.step T C π hπ) (E.get i)))
        I.IsCoherent ∧ (∀ y ∈ A'.N,IsNonzeroAlongAt A'.N I y) ∧
          nonmonomialPartAlong n A'.N I A'.E=
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step T C π hπ)).ideal := by
      intro i
      let j : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
      have hGet : old.get j=strictAlong T (E.get i) := by simp [old,j]
      have hStep := actual_mixed_old_residual_step hn hN hSNC hTr hDense j hπ hCN hCNC
      dsimp only at hStep
      simp only [oldResidualPart,oldTraceIdeal] at hStep
      rw [hGet,(hRows i).2.2] at hStep
      have hChronoN := (chronologicalMarked_geometric_fields
        (originalRelativeMemberMarked W (E.get i)) T).1
      change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hChronoN
      have hChronoStep :
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step T C π hπ)).ideal=
            nextRelativeStrict A.N
              (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal C π := by
        change nextRelativeStrict
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal C π=_
        rw [hChronoN]
      rw [hChronoStep]
      exact hStep
    obtain ⟨hN',hSNC',hTr'⟩ := recorded_geometry hW hE (.step T C π hπ) hT hFull
    have hDense' := full_density_of_actual_old_nonzero hn (.step T C π hπ)
      hN' hSNC' hTr' (fun i => (hRowsNew i).2.1)
    exact ⟨hDense',hRowsNew⟩

/-- ONLY original geometry and two actual recorded geometric tests identify
every true canonical residual with the SAME original chronological ideal.
All whole factors, actual nonzero traces and full density are produced. -/
theorem actual_recorded_tower_residual_dictionary (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) :
    let A := geoTransformAlong (geometricTemplate W []) T
    IsClosedSubmanifold n A.N ∧ IsSNCDivisor n (E.map (strictAlong T) ++ A.E) ∧
      IsTransverse n A.N A.E ∧
      A.N ⊆ closure (A.N \ ⋃ H ∈ E.map (strictAlong T) ++ A.E,H) ∧
      ∀ i : Fin E.length,
        let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))
        let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
        I.IsCoherent ∧ (∀ y ∈ A.N,IsNonzeroAlongAt A.N I y) ∧
          nonmonomialPartAlong n A.N I A.E=J ∧
          I=restrictOn n A.N ((monomialPartAlong n A.N I A.E).mul J) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  obtain ⟨hN,hSNC,hTr⟩ := recorded_geometry hW hE T hT hFull
  obtain ⟨hDense,hRows⟩ := recorded_density_and_residuals hn hW hE hdense T hT hFull
  refine ⟨hN,hSNC,hTr,hDense,fun i => ?_⟩
  let I := restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))
  let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  obtain ⟨hcI,hnzI,hNm⟩ := hRows i
  refine ⟨hcI,hnzI,hNm,?_⟩
  have hBorn := isSNCDivisor_of_sublist hSNC (List.sublist_append_right _ _)
  obtain ⟨_hcR,_hcD,_hnzD,_hmD,_hNo,_hnzR,hFactor⟩ := parts_hypotheses hn
    (⟨A.N,A.E,I,0⟩ : MarkedIdeal n Y) ⟨hN,hcI,hBorn,hTr⟩ hnzI
  have hWhole := MarkedIdealOperationsAlong.restrictOn_eq_of_restrictLe hN.1 hFactor.le hFactor.ge
  change restrictOn n A.N I=restrictOn n A.N
    ((nonmonomialPartAlong n A.N I A.E).mul (monomialPartAlong n A.N I A.E)) at hWhole
  rw [hNm,RestrictLeCalculus.mul_comm'] at hWhole
  have hNorm : restrictOn n A.N I=I := by
    ext y g
    exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
      fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
  exact hNorm.symm.trans hWhole

end
end Hironaka.HironakaG4RecordedTowerResidualCompatibility
