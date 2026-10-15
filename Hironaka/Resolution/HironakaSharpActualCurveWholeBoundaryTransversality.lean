/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualOrderOneCurveTransverseCoordinates
import Hironaka.Resolution.HironakaSharpActualCurveTwoPhaseDefectErasure
import Hironaka.Resolution.HironakaSharpActualCurveFullAmbientBoundary

/-! Literal full ordered ambient boundary and actual two-defect curve
geometry. No replacement trace, coordinate, or transversality certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveWholeBoundaryTransversality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualOrderOneCurveTransverseCoordinates HironakaSharpActualCurveTwoPhaseDefectErasure
  HironakaSharpActualCurveFullAmbientBoundary HironakaSharpActualCurveExceptionalDifference
  HironakaSharpActualFirstGoodCurveBase HironakaSharpActualFirstGoodReducedTraces HironakaSharpActualFirstGoodLowerDimension
  HironakaSharpActualChronologicalAmbientTrace HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpActualFiniteMemberProduct HironakaCoherentTransformExtension
  NormalCrossings NormalCrossingsComparison MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedGlueingTower RelativePrincipalizationSpan RestrictedIdealExtension
  DivisorExponentAlong MonomialPartAlong GermIdealOrder IdealWeightPowers
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Literal BOTH ordered recursions retain EVERY original strict position
and append precisely the SAME real accumulated exceptional positions. -/
theorem actual_whole_ambient_boundary_ordered_dictionary (W : Set X) (E : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E=
        E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E
  | _,.refl => by
    change E=E.map (fun H : Set X => H) ++ []
    simp
  | _,.step T C π hπ => by
    change (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]=_
    rw [actual_whole_ambient_boundary_ordered_dictionary W E T,List.map_append,List.map_map,List.append_assoc]
    rfl

/-- Actual original domain-one geometry supplies full ordered SNC BEFORE its
literal dictionary identifies the exact original-strict-plus-exceptional list. -/
theorem original_curve_whole_ambient_boundary_isSNC (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    IsSNCDivisor n (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) := by
  have h := (original_curve_history_full_ambient_boundary hn hW hE hdense hr T hT).2.2
  rw [actual_whole_ambient_boundary_ordered_dictionary W E T] at h
  exact h

/-- Literal Delta cardinality zero, not a supplied full-germ dictionary,
forces EVERY actual ambient I_i germ to equal its independent chronological J_i. -/
theorem actual_empty_difference_member_germ_iff (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (hEmpty : actualAmbientExceptionalDifference W E T=∅)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N) (i : Fin E.length) :
    ∀ g,(restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
      (vanishingIdeal (n := n) (strictAlong T (E.get i)))).mem x g ↔
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.mem x g := by
  by_contra h
  have hi : i ∈ actualAmbientDifferencePositions W E T x := Finset.mem_filter.mpr ⟨Finset.mem_univ i,h⟩
  have hxD : x ∈ actualAmbientExceptionalDifference W E T := ⟨hx,Finset.card_pos.mpr ⟨i,hi⟩⟩
  rw [hEmpty] at hxD
  exact hxD

/-- ONLY original geometry plus TWO literal empty defects construct actual
full germs, contact order one, incidence uniqueness and exceptional avoidance. -/
theorem original_curve_two_empty_defects_member_rigidity (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    (hZ : chronologicalDistinctDefect W E T=∅) (hD : actualAmbientExceptionalDifference W E T=∅)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N) :
    (∀ i : Fin E.length,∀ g,(restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
      (vanishingIdeal (n := n) (strictAlong T (E.get i)))).mem x g ↔
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.mem x g) ∧
    (∀ i : Fin E.length,x ∈ strictAlong T (E.get i) →
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (vanishingIdeal (n := n) (strictAlong T (E.get i))) x=1) ∧
    (∀ i j : Fin E.length,x ∈ strictAlong T (E.get i) → x ∈ strictAlong T (E.get j) → i=j) ∧
    (x ∈ ⋃ D ∈ (geoTransformAlong (geometricTemplate W []) T).E,D →
      ∀ i : Fin E.length,x ∉ strictAlong T (E.get i)) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let J := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hInit : IsInvDomain 1 (originalMemberProductMarked W E 1) :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun y hy => ⟨1,le_rfl,hr y hy⟩,le_rfl,
      fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy⟩
  have hGeom := actual_original_test_history_template _ hInit.isWellFormed T hT
  have hDisc := original_domain_one_test_actual_discrete_centres _ hInit T hT
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hGeom
  have hCoh (i : Fin E.length) : (J i).IsCoherent :=
    (original_members_actual_finite_chronological_geometry hn hW hE hdense i T hGeom).2.2.2.1.isCoherent
  have hMem := actual_empty_difference_member_germ_iff W E T hD hx
  have hGeometry (i : Fin E.length) := by
    have hSingle : IsSNCDivisor n [E.get i] := isSNCDivisor_of_sublist hE (by simp)
    have hDenseI : W ⊆ closure (W \ E.get i) := by
      apply Subset.trans hdense
      apply closure_mono
      exact fun _ hy => ⟨hy.1,fun hi => hy.2 (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hi⟩)⟩
    exact actual_finite_ambient_strict_trace_geometry hn hW hSingle hDenseI T hGeom hDisc
  have hProper (i : Fin E.length) (hi : x ∈ strictAlong T (E.get i)) : i ∈ actualProperPositions J x := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i,?_⟩
    intro hJ1
    have hI1 := (hMem i (1 : Y → ℂ)).mpr hJ1
    exact ((actual_normalized_vanishing_unit_iff ((hGeometry i).1.1 _ (by simp)) hx).mp hI1) hi
  have hxGood : x ∉ chronologicalDistinctDefect W E T := by rw [hZ];simp
  have hRig := original_first_good_factor_rigidity hn hW hE hdense T hGeom hx hxGood
  obtain ⟨O,hO,hTraces⟩ := exists_original_curve_first_good_trace_separation hn hW hE hdense hr T hGeom
  have hxO : x ∈ O := by change x ∈ (O : Set Y);rw [hO];exact hxGood
  let z : O := ⟨x,hxO⟩
  refine ⟨hMem,?_,?_,?_⟩
  · intro i hi
    have hJOrder := hRig.1 i (hProper i hi)
    have hcI := (hGeometry i).2.2.1
    have hIOrder : ordinaryTraceOrder A.N (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) x=
        ordinaryTraceOrder A.N (J i) x := by
      apply NonmonomialOrderLocal.nmOrd_congr
      intro q
      rw [ordGe_ordinaryTraceMarked_eq_cosupport A.N _ hcI,ordGe_ordinaryTraceMarked_eq_cosupport A.N _ (hCoh i)]
      exact ⟨fun hh => ⟨hh.1,fun g hg => hh.2 g ((hMem i g).mpr hg)⟩,
        fun hh => ⟨hh.1,fun g hg => hh.2 g ((hMem i g).mp hg)⟩⟩
    have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn (hGeometry i).1 (0 : Fin [strictAlong T (E.get i)].length))
    have hnzH : ∀ y ∈ A.N,IsNonzeroAlongAt A.N (vanishingIdeal (n := n) (strictAlong T (E.get i))) y :=
      fun _ hy => HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense
        (hGeometry i).1 (hGeometry i).2.1 hy
    exact (ordinaryTraceOrder_restrictOn_eq hwA.isClosedSubmanifold_N hcH hnzH hx).symm.trans (hIOrder.trans hJOrder)
  · intro i j hi hj
    by_contra hne
    have hzi : z ∈ (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T :=
      ⟨hx,(actual_proper_iff_zeroLocus hCoh i x).mp (hProper i hi)⟩
    have hzj : z ∈ (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E j T :=
      ⟨hx,(actual_proper_iff_zeroLocus hCoh j x).mp (hProper j hj)⟩
    exact Set.disjoint_left.mp ((hTraces i).2.2.2 j (Ne.symm hne)) hzi hzj
  · intro hxF i hi
    have hxD : x ∈ actualAmbientExceptionalDifference W E T := by
      rw [original_curve_actual_exceptional_difference_eq hn hW hE hdense hr T hT]
      exact ⟨⟨hx,hxF⟩,mem_iUnion.mpr ⟨i,hi⟩⟩
    rw [hD] at hxD
    exact hxD


private theorem extend_actual_transverse_coordinates_at {N : Set Y} {B L : List (Set Y)} {x : Y}
    (h : ∃ (S₀ : Finset (Fin n)) (S : Fin B.length → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun t : Option (Fin B.length) => t.elim N (fun i => B.get i))
        (fun t => t.elim S₀ S) x ∧
      ∀ i,x ∈ B.get i → (S i).card=1 ∧ Disjoint (S i) S₀)
    (hCover : ∀ H ∈ L,x ∈ H → H ∈ B) :
    ∃ (S₀ : Finset (Fin n)) (S : Fin L.length → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun t : Option (Fin L.length) => t.elim N (fun i => L.get i))
        (fun t => t.elim S₀ S) x ∧
      ∀ i,x ∈ L.get i → (S i).card=1 ∧ Disjoint (S i) S₀ := by
  obtain ⟨S₀,S,⟨Φ,hsrc,h0,hCoords⟩,hS⟩ := h
  have hidx : ∀ (j : Fin L.length),x ∈ L.get j → ∃ i : Fin B.length,B.get i=L.get j :=
    fun j hj => List.mem_iff_get.mp (hCover _ (List.get_mem L j) hj)
  let f (j : Fin L.length) (hj : x ∈ L.get j) := Classical.choose (hidx j hj)
  have hf (j : Fin L.length) (hj : x ∈ L.get j) : B.get (f j hj)=L.get j := Classical.choose_spec (hidx j hj)
  let S' : Fin L.length → Finset (Fin n) := fun j => if hj : x ∈ L.get j then S (f j hj) else ∅
  refine ⟨S₀,S',⟨Φ,hsrc,h0,?_⟩,?_⟩
  · rintro (_ | j) hxi y hy hyΦ
    · exact hCoords none hxi hy hyΦ
    · change x ∈ L.get j at hxi
      change y ∈ L.get j ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S' j)
      dsimp only [S']
      rw [dif_pos hxi]
      have hxb : x ∈ B.get (f j hxi) := by rw [hf j hxi];exact hxi
      have hb := hCoords (some (f j hxi)) hxb hy hyΦ
      simpa only [Option.elim,hf] using hb
  · intro j hj
    dsimp only [S']
    rw [dif_pos hj]
    exact hS (f j hj) (by rw [hf j hj];exact hj)

/-- BOTH actual empty defects supply actual incidence cases BEFORE real
same-chart extension constructs ENTIRE full-boundary transversality. -/
theorem original_curve_two_empty_defects_whole_boundary_transverse (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    (hZ : chronologicalDistinctDefect W E T=∅) (hD : actualAmbientExceptionalDifference W E T=∅) :
    IsTransverse n (geoTransformAlong (geometricTemplate W []) T).N
      (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let L := E.map (strictAlong T) ++ A.E
  have hInit : IsInvDomain 1 (originalMemberProductMarked W E 1) :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hGeom := actual_original_test_history_template _ hInit.isWellFormed T hT
  have hDisc := original_domain_one_test_actual_discrete_centres _ hInit T hT
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hGeom
  have hPure := actual_template_regular_dimension hW 1 hr T hGeom
  intro x hx
  have hData := original_curve_two_empty_defects_member_rigidity hn hW hE hdense hr T hT hZ hD hx
  by_cases hxF : x ∈ ⋃ D ∈ A.E,D
  · apply extend_actual_transverse_coordinates_at (hwA.isTransverse x hx)
    intro H hH hxH
    rcases List.mem_append.mp hH with hOrig | hOld
    · obtain ⟨H0,hH0,rfl⟩ := List.mem_map.mp hOrig
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hH0
      exact False.elim (hData.2.2.2 hxF i (by rw [hi];exact hxH))
    · exact hOld
  · by_cases hxOrig : ∃ i : Fin E.length,x ∈ strictAlong T (E.get i)
    · obtain ⟨i,hxi⟩ := hxOrig
      have hSingle : IsSNCDivisor n [E.get i] := isSNCDivisor_of_sublist hE (by simp)
      have hDenseI : W ⊆ closure (W \ E.get i) := by
        apply Subset.trans hdense
        apply closure_mono
        exact fun _ hy => ⟨hy.1,fun hi => hy.2 (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hi⟩)⟩
      obtain ⟨hHT,hDense,_hcI,_hnzI,_hPr⟩ := actual_finite_ambient_strict_trace_geometry hn hW hSingle hDenseI T hGeom hDisc
      apply extend_actual_transverse_coordinates_at
        (actual_order_one_curve_member_simultaneous_coordinates hn hwA.isClosedSubmanifold_N hHT hDense
          hx hxi (hPure x hx) (hData.2.1 i hxi))
      intro H hH hxH
      rcases List.mem_append.mp hH with hOrig | hOld
      · obtain ⟨H0,hH0,rfl⟩ := List.mem_map.mp hOrig
        obtain ⟨j,hj⟩ := List.mem_iff_get.mp hH0
        have hjx : x ∈ strictAlong T (E.get j) := by rw [hj];exact hxH
        have hji := hData.2.2.1 j i hjx hxi
        apply List.mem_singleton.mpr
        rw [←hj,hji]
      · exact False.elim (hxF (mem_iUnion₂.mpr ⟨H,hOld,hxH⟩))
    · have hNo : ∀ j : Fin L.length,x ∉ L.get j := by
        intro j hxj
        have hH := List.get_mem L j
        rcases List.mem_append.mp hH with hOrig | hOld
        · obtain ⟨H0,hH0,he⟩ := List.mem_map.mp hOrig
          obtain ⟨i,hi⟩ := List.mem_iff_get.mp hH0
          exact hxOrig ⟨i,by rw [hi,he];exact hxj⟩
        · exact hxF (mem_iUnion₂.mpr ⟨L.get j,hOld,hxj⟩)
      refine ⟨Finset.univ.filter (fun j : Fin n => 1≤j.val),fun _ => ∅,
        isCoordinateFamilyAt_of_regularAtDim (hPure x hx) L (fun _ => ∅) hNo,?_⟩
      intro j hj
      exact (hNo j hj).elim

/-- ONLY original data construct the SAME two actual histories BEFORE genuine
full original-strict-plus-exceptional transverse geometry is proved. -/
theorem exists_original_curve_two_phase_whole_boundary_transverse (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P)
    (hK : IsCompact (geoTransformAlong (originalMemberProductMarked W E 1) P).cosupp) :
    ∃ (Y' : CMfd.{u} n) (π : Y' → Y) (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E P) π)
      (Z : CMfd.{u} n) (S : BlowupTower Y' Z),
      let R := (BlowupTower.step P (chronologicalDistinctDefect W E P) π hπ).append S
      IsGeoTestTower (originalMemberProductMarked W E 1) R ∧
      chronologicalDistinctDefect W E R=∅ ∧ actualAmbientExceptionalDifference W E R=∅ ∧
      IsProperMap R.proj ∧ IsInvDomain 1 (geoTransformAlong (originalMemberProductMarked W E 1) R) ∧
      IsSNCDivisor n (E.map (strictAlong R) ++ (geoTransformAlong (geometricTemplate W []) R).E) ∧
      IsTransverse n (geoTransformAlong (geometricTemplate W []) R).N
        (E.map (strictAlong R) ++ (geoTransformAlong (geometricTemplate W []) R).E) := by
  obtain ⟨Y',π,hπ,Z,S,_hSteps,hTest,hFirst,hDelta,hProper,hDom,_hSNC⟩ :=
    exists_original_curve_two_actual_defect_erasure_phases hn hW hE hdense hr P hP hK
  exact ⟨Y',π,hπ,Z,S,hTest,hFirst,hDelta,hProper,hDom,
    original_curve_whole_ambient_boundary_isSNC hn hW hE hdense hr _ hTest,
    original_curve_two_empty_defects_whole_boundary_transverse hn hW hE hdense hr _ hTest hFirst hDelta⟩

end
end Hironaka.HironakaSharpActualCurveWholeBoundaryTransversality
