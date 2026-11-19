import Hironaka.Resolution.HironakaActualOriginalProcessedSharpCleanup
import Hironaka.Resolution.HironakaSharpActualEmptyChronologicalDefect
import Hironaka.Resolution.HironakaSNCSupportedMonomialIdeal
import Hironaka.Resolution.HironakaG4SharpBadFootprint

/-! The original processed sharp endpoint in every ambient dimension.
The zero branch retains every supplied empty step, old position and birth,
with whole I/D/chronological STRICT-J dictionaries on every literal head.
Blueprint FIRST: hironaka-actual-original-processed-sharp-cleanup-all-dimensions.tex.
Arbitrary processed entry, the global driver and full G4 remain separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualOriginalProcessedSharpCleanupAllDimensions
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualEmptyChronologicalDefect
  HironakaActualProcessedMaskFiniteBlock HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpActualCurveWholeBoundaryTransversality HironakaG4SharpBadFootprint
  HironakaSharpOriginalProductTraceOrder
  HironakaG4MonomialFamilyInvariant HironakaSNCSupportedMonomialIdeal
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  IdealWeightPowers InvertibleIdealQuotient DivisorExponentAlong GermIdealOrder MonomialPartAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower HironakaAdmissibleSequence
  HironakaAdmissibleCalculus
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)

private theorem restrict_unit {n : ℕ} {X : CMfd.{u} n} (N : Set X) :
    restrictOn n N (unitIdeal n X)=unitIdeal n X := by
  ext x g
  constructor
  · exact fun hg=>hg.1
  · intro hg
    exact ⟨hg,IsInSpanAt.restrict (isInSpanAt_self hg hg)⟩

private theorem vanishing_empty {n : ℕ} {X : CMfd.{u} n} :
    vanishingIdeal (n:=n) (∅ : Set X)=unitIdeal n X := by
  ext x g
  exact ⟨fun hg=>hg.1,fun hg=>⟨hg,Eventually.of_forall fun _ hx=>hx.elim⟩⟩

section Zero
variable {X Y : CMfd.{u} 0}

private theorem member_empty (E : List (Set X)) (hE : IsSNCDivisor 0 E)
    (i : Fin E.length) : E.get i=∅ :=
  Set.eq_empty_iff_forall_notMem.mpr (fun x=>notMem_member_of_dim_zero E hE i x)

private theorem sharp_bad_empty {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold 0 W) (hE : IsSNCDivisor 0 E) :
    originalSharpBadLocus (n:=0) W E=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨H,hHE,hxH⟩:=Set.mem_iUnion₂.mp (originalSharpBadLocus_subset_boundary hW hx).2
  obtain ⟨i,hi⟩:=List.mem_iff_get.mp hHE
  exact notMem_member_of_dim_zero E hE i x (by simpa only [hi] using hxH)

private theorem empty_of_centres_over_empty :
    ∀ {Y : CMfd.{u} 0} (P : BlowupTower X Y),CentresOver (∅ : Set X) P→IsEmptyTower P
  | _,.refl,_=>trivial
  | _,.step P _C _π _hπ,h=>
    ⟨empty_of_centres_over_empty P h.1,
      Set.eq_empty_iff_forall_notMem.mpr (fun _x hx=>h.2 hx)⟩

private theorem template_well_formed {W : Set X} (hW : IsClosedSubmanifold 0 W) :
    (geometricTemplate W []).IsWellFormed :=
  ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩

private theorem strict_empty :
    ∀ {Y : CMfd.{u} 0} (P : BlowupTower X Y),strictAlong P (∅ : Set X)=∅
  | _,.refl=>rfl
  | _,.step P C π hπ=>by
    change closure (π ⁻¹' (strictAlong P (∅ : Set X)\C))=∅
    rw [strict_empty P]
    simp

-- Only dimension zero and actual EMPTY histories are used here. The held
-- empty-centre whole pullback theorem supplies each genuine STRICT step.
private theorem zero_chronological_member_unit {W H : Set X}
    (hW : IsClosedSubmanifold 0 W) (hH : H=∅) :
    ∀ {Y : CMfd.{u} 0} (P : BlowupTower X Y),IsEmptyTower P→
      (chronologicalMarked (originalRelativeMemberMarked W H) P).ideal=unitIdeal 0 Y
  | _,.refl,_=>by
    change restrictOn 0 W (vanishingIdeal (n:=0) H)=_
    rw [hH,vanishing_empty,restrict_unit]
  | _,.step P C π hπ,hEmpty=>by
    obtain ⟨hP,hC⟩:=hEmpty
    subst C
    have hUnit:=zero_chronological_member_unit hW hH P hP
    have hTest:=isGeoTestTower_of_isEmptyTower (geometricTemplate W []) P hP
    have hWF:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (template_well_formed hW) P hTest
    have hFields:=chronologicalMarked_geometric_fields (originalRelativeMemberMarked W H) P
    have hN : IsClosedSubmanifold 0
        (chronologicalMarked (originalRelativeMemberMarked W H) P).N := by
      rw [hFields.1]
      exact hWF.isClosedSubmanifold_N
    change nextRelativeStrict
      (chronologicalMarked (originalRelativeMemberMarked W H) P).N
      (chronologicalMarked (originalRelativeMemberMarked W H) P).ideal ∅ π=_
    rw [hUnit,nextRelativeStrict_empty hN isCoherent_unitIdeal (restrict_unit _) hπ,
      BlowupExceptionalDivisor.pullback_unitIdeal]

private theorem parts_and_clocks_of_empty {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold 0 W) (hE : IsSNCDivisor 0 E)
    (P : BlowupTower X Y) (hEmpty : IsEmptyTower P) :
    let A:=geoTransformAlong (geometricTemplate W []) P
    let F:=(geoTransformAlong (geometricTemplate (univ : Set X) E) P).E
    F=E.map (strictAlong P)++A.E ∧ A.E.length=P.length ∧
      F.length=E.length+P.length ∧
      ∀i : Fin E.length,
        let I:=restrictOn 0 A.N (vanishingIdeal (n:=0) (strictAlong P (E.get i)))
        let D:=monomialPartAlong 0 A.N I A.E
        let J:=chronologicalMarked (originalRelativeMemberMarked W (E.get i)) P
        J.N=A.N ∧ J.E=A.E ∧ J.d=0 ∧ J.IsWellFormed ∧
          I.IsCoherent ∧ D.IsCoherent ∧
          nonmonomialPartAlong 0 A.N I A.E=J.ideal ∧
          I=restrictOn 0 A.N (D.mul J.ideal) := by
  let A:=geoTransformAlong (geometricTemplate W []) P
  have hTest:=isGeoTestTower_of_isEmptyTower (geometricTemplate W []) P hEmpty
  have hWF:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (template_well_formed hW) P hTest
  have hBoundary:=actual_whole_ambient_boundary_ordered_dictionary W E P
  have hBorn : A.E.length=P.length := by
    simpa only [A,geometricTemplate,List.length_nil,Nat.zero_add] using
      length_E_geoTransformAlong (geometricTemplate W []) P
  refine ⟨hBoundary,hBorn,?_,?_⟩
  · rw [hBoundary,List.length_append,List.length_map,hBorn]
  · intro i
    let I:=restrictOn 0 A.N (vanishingIdeal (n:=0) (strictAlong P (E.get i)))
    let D:=monomialPartAlong 0 A.N I A.E
    let J:=chronologicalMarked (originalRelativeMemberMarked W (E.get i)) P
    have hI : I=unitIdeal 0 Y := by
      dsimp only [I]
      rw [member_empty E hE i,strict_empty P,vanishing_empty,restrict_unit]
    have hD : D=unitIdeal 0 Y := by
      ext x g
      exact ⟨fun hg=>hg.1,fun hg=>⟨hg,fun j _hx hj=>
        False.elim (notMem_member_of_dim_zero A.E hWF.isSNCDivisor j x hj)⟩⟩
    have hJ : J.ideal=unitIdeal 0 Y :=
      zero_chronological_member_unit hW (member_empty E hE i) P hEmpty
    obtain ⟨hJN,hJE⟩:=chronologicalMarked_geometric_fields
      (originalRelativeMemberMarked W (E.get i)) P
    have hJd : J.d=0:=chronologicalMarked_zero_mark
      (originalRelativeMemberMarked W (E.get i)) rfl P
    refine ⟨hJN,hJE,hJd,?_,?_,?_,?_,?_⟩
    · refine ⟨?_,?_,?_,?_⟩
      · rw [hJN];exact hWF.isClosedSubmanifold_N
      · rw [hJ];exact isCoherent_unitIdeal
      · rw [hJE];exact hWF.isSNCDivisor
      · rw [hJN,hJE];exact hWF.isTransverse
    · change I.IsCoherent
      rw [hI];exact isCoherent_unitIdeal
    · change D.IsCoherent
      rw [hD];exact isCoherent_unitIdeal
    · change colonAlong 0 A.N I D=J.ideal
      rw [hI,hD,hJ,colonAlong,restrict_unit,
        BlowupControlledTransform.colon_unitIdeal isCoherent_unitIdeal]
    · change I=restrictOn 0 A.N (D.mul J.ideal)
      rw [hI,hD,hJ,BlowupControlledTransform.unitIdeal_mul isCoherent_unitIdeal,restrict_unit]

private theorem exponent_empty (N : Set Y) (I : GermIdeal 0 Y) (x : Y) :
    divExpAlong 0 N I ∅ x=0 := by
  unfold divExpAlong
  rw [dif_neg]
  rintro ⟨e,he⟩
  apply he
  exact Eventually.of_forall (fun _ _ hy=>hy.elim)

private theorem count_zero {W : Set X} (hW : IsClosedSubmanifold 0 W)
    (E : List (Set X)) (P : BlowupTower X Y) (hEmpty : IsEmptyTower P) (x : Y) :
    tauD (factorMatrix W E P x)=0 := by
  have hTest:=isGeoTestTower_of_isEmptyTower (geometricTemplate W []) P hEmpty
  have hWF:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (template_well_formed hW) P hTest
  have hMatrix : factorMatrix W E P x=(fun _ _=>0) := by
    funext i j
    change divExpAlong 0 _ _ ((geoTransformAlong (geometricTemplate W []) P).E.get j) x=0
    rw [member_empty _ hWF.isSNCDivisor j]
    exact exponent_empty _ _ x
  rw [hMatrix]
  simp [tauD,properRows,rowOrder]

private theorem zero_final_normal_crossings {N : Set Y} {E : List (Set Y)}
    (hN : IsClosedSubmanifold 0 N) (hE : IsSNCDivisor 0 E) : HasNormalCrossings 0 N E := by
  intro x hx
  obtain ⟨k,hreg⟩:=hN.2 x hx
  refine ⟨_,fun _=>∅,isCoordinateFamilyAt_of_regularAtDim hreg E _
    (fun i=>notMem_member_of_dim_zero E hE i x),?_⟩
  intro i hi
  exact False.elim (notMem_member_of_dim_zero E hE i x hi)

/-- The SAME supplied zero-dimensional sharp history already has the full
endpoint, including every original whole record on EVERY literal prefix. -/
theorem zero_current_sharp_endpoint {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold 0 W) (hE : IsSNCDivisor 0 E)
    (T : BlowupTower X Y) (hSharp : CurrentSharpCentres W E T) :
    let A:=geoTransformAlong (geometricTemplate W []) T
    let F:=(geoTransformAlong (geometricTemplate (univ : Set X) E) T).E
    IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      CentresOver (originalSharpBadLocus (n:=0) W E) T ∧
      (∀x∈A.N,tauD (factorMatrix W E T x)=0) ∧
      IsClosedSubmanifold 0 A.N ∧ IsSNCDivisor 0 F ∧ HasNormalCrossings 0 A.N F ∧
      IsProperMap T.proj ∧ IsIsomorphismOver 0 T.proj (originalSharpBadLocus (n:=0) W E)ᶜ ∧
      ∀k : ℕ,
        let P:=BlowupTowerSplit.head T k
        let B:=geoTransformAlong (geometricTemplate W []) P
        let G:=(geoTransformAlong (geometricTemplate (univ : Set X) E) P).E
        G=E.map (strictAlong P)++B.E ∧ B.E.length=P.length ∧ G.length=E.length+P.length ∧
          ∀i : Fin E.length,
            let I:=restrictOn 0 B.N (vanishingIdeal (n:=0) (strictAlong P (E.get i)))
            let D:=monomialPartAlong 0 B.N I B.E
            let J:=chronologicalMarked (originalRelativeMemberMarked W (E.get i)) P
            J.N=B.N ∧ J.E=B.E ∧ J.d=0 ∧ J.IsWellFormed ∧
              I.IsCoherent ∧ D.IsCoherent ∧
              nonmonomialPartAlong 0 B.N I B.E=J.ideal ∧
              I=restrictOn 0 B.N (D.mul J.ideal) := by
  have hOver:=(currentSharpCentres_original_footprint hW.1 hE.1 T hSharp).2
  have hBad:=sharp_bad_empty hW hE
  have hEmpty : IsEmptyTower T:=empty_of_centres_over_empty T (by simpa only [hBad] using hOver)
  have hTest:=isGeoTestTower_of_isEmptyTower (geometricTemplate W []) T hEmpty
  have hFull:=isGeoTestTower_of_isEmptyTower (geometricTemplate (univ : Set X) E) T hEmpty
  have hWF:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (template_well_formed hW) T hTest
  have hBaseFull : (geometricTemplate (univ : Set X) E).IsWellFormed:=
    ⟨isClosedSubmanifold_univ,isCoherent_unitIdeal,hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hWFFull:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hBaseFull T hFull
  have hAdm:=isAdmissibleBlowupSequence_proj (geometricTemplate W [])
    (originalSharpBadLocus (n:=0) W E) T hTest hOver
  refine ⟨hTest,hFull,hSharp,hOver,fun x _=>count_zero hW E T hEmpty x,
    hWF.isClosedSubmanifold_N,hWFFull.isSNCDivisor,
    zero_final_normal_crossings hWF.isClosedSubmanifold_N hWFFull.isSNCDivisor,
    isProperMap_of_isBlowupSequence hAdm.isBlowupSequence,
    HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hAdm,?_⟩
  intro k
  have hHeadOver:=centresOver_head (originalSharpBadLocus (n:=0) W E) T k hOver
  have hHeadEmpty:=empty_of_centres_over_empty (BlowupTowerSplit.head T k)
    (by simpa only [hBad] using hHeadOver)
  exact parts_and_clocks_of_empty hW hE (BlowupTowerSplit.head T k) hHeadEmpty

end Zero

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Original processed cleanup in ALL ambient dimensions. Every actual head
retains whole I/D/STRICT-J, native fields, full ordered E and all birth clocks. -/
theorem exists_actual_original_processed_sharp_cleanup_all_dimensions {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W\⋃H∈E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hK : IsCompact (originalSharpBadLocus (n:=n) W E))
    (hOrd : ∀x∈(geoTransformAlong (geometricTemplate W []) T).N,
      ∀i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x≤1)
    (hNC : ∀i : Fin E.length,
      let A:=geoTransformAlong (geometricTemplate W []) T
      let S:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val++A.E))
    (hDenseS : ∀i : Fin E.length,
      let A:=geoTransformAlong (geometricTemplate W []) T
      let S:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S⊆closure (S\⋃H∈(E.map (strictAlong T)).eraseIdx i.val++A.E,H)) :
    ∃(Z : CMfd.{u} n)(R : BlowupTower Y Z),
      let U:=T.append R
      let A:=geoTransformAlong (geometricTemplate W []) U
      let F:=(geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n:=n) W E) U ∧
      (∀x∈A.N,tauD (factorMatrix W E U x)=0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n:=n) W E)ᶜ ∧
      ∀k : ℕ,
        let P:=BlowupTowerSplit.head U k
        let B:=geoTransformAlong (geometricTemplate W []) P
        let G:=(geoTransformAlong (geometricTemplate (univ : Set X) E) P).E
        G=E.map (strictAlong P)++B.E ∧ B.E.length=P.length ∧ G.length=E.length+P.length ∧
          ∀i : Fin E.length,
            let I:=restrictOn n B.N (vanishingIdeal (n:=n) (strictAlong P (E.get i)))
            let D:=monomialPartAlong n B.N I B.E
            let J:=chronologicalMarked (originalRelativeMemberMarked W (E.get i)) P
            J.N=B.N ∧ J.E=B.E ∧ J.d=0 ∧ J.IsWellFormed ∧
              I.IsCoherent ∧ D.IsCoherent ∧
              nonmonomialPartAlong n B.N I B.E=J.ideal ∧
              I=restrictOn n B.N (D.mul J.ideal) := by
  by_cases hn : 0<n
  · exact HironakaActualOriginalProcessedSharpCleanup.exists_actual_original_processed_sharp_cleanup
      hn hW hE hdense T hT hFull hSharp hK hOrd hNC hDenseS
  · have hn0 : n=0:=Nat.eq_zero_of_not_pos hn
    subst n
    refine ⟨Y,.refl,?_⟩
    exact zero_current_sharp_endpoint hW hE T hSharp

end
end Hironaka.HironakaActualOriginalProcessedSharpCleanupAllDimensions
