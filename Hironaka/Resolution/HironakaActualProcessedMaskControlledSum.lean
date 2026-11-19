import Hironaka.Resolution.HironakaG4ProcessedSupportHighCountStep
import Hironaka.Resolution.HironakaG4ZeroMaskGammaStep

/-! Whole controlled sums of the independently recomputed canonical old factors
at the SAME arbitrary original prefix. Source-first proof:
`hironaka-g4-processed-mask-controlled-sum-20261101.tex`.
Joint sharp termination and the lower-count resolving schedule remain open. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaActualProcessedMaskControlledSum

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  InvertibleIdealQuotient RestrictLeCalculus IdealWeightPowers GermIdealOrder
  NormalCrossings NormalCrossingsComparison MonomialPartAlong DivisorExponentAlong
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant HomogenizedGlueingTower

variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem controlled_normalized (M : MarkedIdeal n X) {C : Set X}
    {π : Y → X} (hπ : IsBlowupAlong n C π) :
    restrictOn n (M.geoTransform C π).N (M.geoTransform C π).ideal =
      (M.geoTransform C π).ideal := by
  have hcDen := GermIdealPullbackCalculus.isCoherent_idealPow
    (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff
      (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)) M.d
  ext z g
  exact HironakaSharpActualControlledRelativeSaturation.restrictOn_colonAlong_mem_iff _ _ _
    (fun _ ha => GermIdeal.IsCoherent.holomorphicAt_mem hcDen ha) g

private theorem monomialPart_eq_of_normalized_monomial (hn : 0 < n)
    {N : Set Y} {E : List (Set Y)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) {G : GermIdeal n Y}
    (hcG : G.IsCoherent) (hmG : IsMonomialAlong n N G E)
    (hNorm : restrictOn n N G=G) : monomialPartAlong n N G E=G := by
  ext z g
  constructor
  · intro hg
    rw [←hNorm]
    by_cases hz : z ∈ N
    · exact ⟨hg.1,hmG z hz g hg⟩
    · exact restrictOn_eq_top_of_disjoint hN.1.isOpen_compl hz (by simp) hg.1
  · exact le_monomialPartAlong hn hE hTr hcG z g

private theorem controlled_canonical_monomial_of_unit_residual (hn : 0 < n)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hnz : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x)
    {C : Set X} (hC : M.IsAdmissibleCentre C)
    (hD : (⟨M.N,M.E,monomialPartAlong n M.N M.ideal M.E,M.d⟩ :
      MarkedIdeal n X).IsAdmissibleCentre C)
    (hUnit : ∀ x ∈ C,(nonmonomialPartAlong n M.N M.ideal M.E).mem x 1)
    {π : Y → X} (hπ : IsBlowupAlong n C π) :
    monomialPartAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal
      (M.geoTransform C π).E =
        ((⟨M.N,M.E,monomialPartAlong n M.N M.ideal M.E,M.d⟩ :
          MarkedIdeal n X).geoTransform C π).ideal := by
  let J := nonmonomialPartAlong n M.N M.ideal M.E
  let D := monomialPartAlong n M.N M.ideal M.E
  let MD : MarkedIdeal n X := ⟨M.N,M.E,D,M.d⟩
  let MJ : MarkedIdeal n X := ⟨M.N,M.E,J,0⟩
  let G := (MD.geoTransform C π).ideal
  obtain ⟨hcJ,hcD,hnzD,hmD,hNo,hnzJ,hEquiv⟩ :=
    NonmonomialTransformAlong.parts_hypotheses hn M hM hnz
  have hJadm : MJ.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hC.2.2⟩
    change C ⊆ cosupport n M.N J 0
    rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcJ hg)]
    exact hC.subset_N
  have hcG : G.IsCoherent :=
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
      (𝔪 := MD) hM.isClosedSubmanifold_N hcD hD hπ
  have hcJT : (MJ.geoTransform C π).ideal.IsCoherent :=
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
      (𝔪 := MJ) hM.isClosedSubmanifold_N hcJ hJadm hπ
  have hBound : ∀ x ∈ C,x ∉ cosupport n M.N J (0+1) := by
    intro x hx hCos
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcJ hg)] at hCos
    exact one_ne_zero (hCos.2 1 (hUnit x hx))
  have hProductAdm := hEquiv.isAdmissibleCentre_iff.mp hC
  obtain ⟨_hcFactor,hLeft,hRight,hPrincipal,hNoT,_hnzT⟩ :=
    NonmonomialStepAlong.step_along (o := 0) (d := M.d) hn hπ
      hM.isClosedSubmanifold_N hM.isSNCDivisor hM.isTransverse hcJ hcD hnzD hmD
      hNo hnzJ hC.2.2 hJadm.2.1 hProductAdm.2.1 hBound
  have hFactor : NonmonomialStepAlong.monomialFactor n π C M.N M.E D 0 M.d=G := by
    unfold NonmonomialStepAlong.monomialFactor
    simp only [Nat.zero_sub,Nat.sub_zero,idealPow_zero]
    exact BlowupControlledTransform.unitIdeal_mul hcG
  rw [hFactor] at hLeft hRight hPrincipal
  have hProductEq := congrArg MarkedIdeal.ideal
    (hEquiv.geoTransform_eq hM.isClosedSubmanifold_N.1 hM.isCoherent
      (isCoherent_mul hcJ hcD) (C := C) hπ.contMDiff)
  rw [←hProductEq] at hLeft hRight
  have hNext := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hM hC hπ
  have hmG : IsMonomialAlong n (M.geoTransform C π).N G (M.geoTransform C π).E :=
    (MonomialCaseAlong.isNonzeroAlongAt_and_isMonomialAlong_of_principal hn
      hNext.isClosedSubmanifold_N hNext.isSNCDivisor hNext.isTransverse hcG
      (fun z hz => (hPrincipal z hz).choose_spec.isPrincipalMonomialAlongAt)).2
  have hCanonical := NonmonomialTransformAlong.monomialPartAlong_eq_of_factor hn
    hNext.isClosedSubmanifold_N hNext.isSNCDivisor hNext.isTransverse
    hcJT hcG hNoT hLeft hRight
  exact hCanonical.trans (monomialPart_eq_of_normalized_monomial hn
    hNext.isClosedSubmanifold_N hNext.isSNCDivisor hNext.isTransverse
    hcG hmG (controlled_normalized MD hπ))

/-- The genuine actual strict old trace has canonical monomial part equal to
the controlled original factor. The residual-unit condition is used at mark
zero, while the actual current trace and factor both retain mark one. -/
theorem actual_controlled_old_monomial_part (hn : 0 < n)
    {N H C : Set X} {B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hH : IsClosedSubmanifold n H)
    (hB : IsSNCDivisor n B) (hTr : IsTransverse n N B)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N
      (restrictOn n N (vanishingIdeal (n := n) H)) x)
    (hI : (⟨N,B,restrictOn n N (vanishingIdeal (n := n) H),1⟩ :
      MarkedIdeal n X).IsAdmissibleCentre C)
    (hD : (⟨N,B,monomialPartAlong n N
      (restrictOn n N (vanishingIdeal (n := n) H)) B,1⟩ :
        MarkedIdeal n X).IsAdmissibleCentre C)
    (hCH : C ⊆ H)
    (hUnit : ∀ x ∈ C,(nonmonomialPartAlong n N
      (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x 1)
    {π : Y → X} (hπ : IsBlowupAlong n C π) :
    monomialPartAlong n (geoStrictTransform π C N)
      (restrictOn n (geoStrictTransform π C N)
        (vanishingIdeal (n := n) (geoStrictTransform π C H)))
      (B.map (geoStrictTransform π C) ++ [π ⁻¹' C]) =
        ((⟨N,B,monomialPartAlong n N
          (restrictOn n N (vanishingIdeal (n := n) H)) B,1⟩ :
            MarkedIdeal n X).geoTransform C π).ideal := by
  let I := restrictOn n N (vanishingIdeal (n := n) H)
  let M : MarkedIdeal n X := ⟨N,B,I,1⟩
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  have hcI : I.IsCoherent := isCoherent_restrictOn_of_isClosedSubmanifold hcH hN
  have hNorm : MarkedIdeal.RestrictEquiv M
      (⟨N,B,vanishingIdeal (n := n) H,1⟩ : MarkedIdeal n X) :=
    ⟨rfl,rfl,rfl,restrictLe_restrictOn,restrictLe_self_restrictOn hcH⟩
  have hWhole : (M.geoTransform C π).ideal=
      restrictOn n (geoStrictTransform π C N)
        (vanishingIdeal (n := n) (geoStrictTransform π C H)) :=
    (congrArg MarkedIdeal.ideal
      (hNorm.geoTransform_eq hN.1 hcI hcH (C := C) hπ.contMDiff)).trans
        (HironakaSharpActualFirstAmbientStrictTraceFactor.actual_first_controlled_ambient_strict_trace
          hN hH hπ hI.subset_N hCH)
  have h := controlled_canonical_monomial_of_unit_residual hn M
    ⟨hN,hcI,hB,hTr⟩ hnz hI hD hUnit hπ
  rw [hWhole] at h
  exact h

/-- The literal mark-one SUM of the actual canonical old factors at the SAME
original prefix. Original old indices, carrier and the full born list come
from T itself, independently of any supplied transformed-record comparison. -/
def processedMaskMarked (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (P : Finset (Fin E.length)) :
    MarkedIdeal n Y :=
  let A := geoTransformAlong (geometricTemplate W []) T
  let D := fun i : Fin E.length => monomialPartAlong n A.N
    (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
  ⟨A.N,A.E,⟨fun x g => IsInSpanAt (n := n)
    (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩,1⟩

/-- Actual recomputation of the SAME current marked SUM commutes with one real
sum-admissible blowup. All unit/disjointness/old-containment premises needed
by row control are derived from the processed original supports and count cap. -/
theorem actual_processed_mask_controlled_record
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hNC : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (P : Finset (Fin E.length)) (hP : 2 ≤ P.card)
    (hBound : let A := geoTransformAlong (geometricTemplate W []) T
      let D := fun i : Fin E.length => monomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
      ∀ x ∈ A.N,tauD (fun i j => divExpAlong n A.N (D i) (A.E.get j) x) ≤ P.card) :
    ResolutionInvariantSpec.IsInvDomain (n+1) (processedMaskMarked W E T P) ∧
      ∀ (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
        (processedMaskMarked W E T P).IsAdmissibleCentre C →
          (processedMaskMarked W E T P).geoTransform C π =
            processedMaskMarked W E (.step T C π hπ) P ∧
          HasNormalCrossings n C (E.map (strictAlong T) ++
            (geoTransformAlong (geometricTemplate W []) T).E) ∧
          C ⊆ HironakaSharpOriginalMultiBoundaryBadLocus.originalSharpBadLocus (n := n)
            (geoTransformAlong (geometricTemplate W []) T).N
            (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) ∧
          (∀ i : Fin E.length,Disjoint C
            ((geoTransformAlong (geometricTemplate W []) T).N ∩
              (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)) ∧
          IsGeoTestTower (geometricTemplate W []) (.step T C π hπ) ∧
          IsGeoTestTower (geometricTemplate (univ : Set X) E) (.step T C π hπ) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let I := fun i : Fin E.length => restrictOn n A.N
    (vanishingIdeal (n := n) (strictAlong T (E.get i)))
  let D := fun i : Fin E.length => monomialPartAlong n A.N (I i) A.E
  let M := processedMaskMarked W E T P
  have hCore := HironakaG4ProcessedSupportHighCountStep.actual_original_high_count_step_geometry
    (Z := Z) hn hW hE hdense T hT hFull hOrd hNC hDenseS P hP hBound
  change ResolutionInvariantSpec.IsInvDomain (n+1) M ∧ _
  refine ⟨hCore.1,?_⟩
  intro C π hπ hAdm
  let T' := BlowupTower.step T C π hπ
  let A' := geoTransformAlong (geometricTemplate W []) T'
  let I' := fun i : Fin E.length => restrictOn n A'.N
    (vanishingIdeal (n := n) (strictAlong T' (E.get i)))
  let D' := fun i : Fin E.length => monomialPartAlong n A'.N (I' i) A'.E
  obtain ⟨hCNC,hSharp,hDisjoint,hCP,_hOutside,hAtC,hTest,hTestFull⟩ :=
    hCore.2 C π hπ hAdm
  have hRecorded := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hNext := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T' hTest hTestFull
  have hBorn : IsSNCDivisor n A.E :=
    isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_right old A.E)
  have hBorn' : IsSNCDivisor n A'.E :=
    isSNCDivisor_of_sublist hNext.2.1 (List.sublist_append_right (E.map (strictAlong T')) A'.E)
  have hParts (i : Fin E.length) := NonmonomialTransformAlong.parts_hypotheses hn
    (⟨A.N,A.E,I i,1⟩ : MarkedIdeal n Y)
    ⟨hRecorded.1,(hRecorded.2.2.2.2 i).1,hBorn,hRecorded.2.2.1⟩
    (hRecorded.2.2.2.2 i).2.1
  have hParts' (i : Fin E.length) := NonmonomialTransformAlong.parts_hypotheses hn
    (⟨A'.N,A'.E,I' i,1⟩ : MarkedIdeal n Z)
    ⟨hNext.1,(hNext.2.2.2.2 i).1,hBorn',hNext.2.2.1⟩
    (hNext.2.2.2.2 i).2.1
  have hcD (i : Fin E.length) : (D i).IsCoherent := (hParts i).2.1
  have hcD' (i : Fin E.length) : (D' i).IsCoherent := (hParts' i).2.1
  have hCN : C ⊆ A.N := hAdm.subset_N
  have hDadm (i : Fin E.length) (hi : i ∈ P) :
      (⟨A.N,A.E,D i,1⟩ : MarkedIdeal n Y).IsAdmissibleCentre C := by
    have hLe : (D i).Le M.ideal := by
      intro x g hg
      change IsInSpanAt (n := n) (fun f => ∃ j ∈ P,(D j).mem x f) x g
      exact isInSpanAt_self ⟨i,hi,hg⟩
        (GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)
    have hCos := cosupport_subset_of_restrictLe
      (restrictLe_of_le (W := A.N) hCore.1.isWellFormed.isCoherent hLe) 1
    exact ⟨hπ.1,fun x hx => hCos (hAdm.2.1 hx),hAdm.2.2⟩
  have hRow (i : Fin E.length) (hi : i ∈ P) :
      D' i=((⟨A.N,A.E,D i,1⟩ : MarkedIdeal n Y).geoTransform C π).ideal := by
    let oi : Fin old.length := ⟨i.val,by simp [old]⟩
    have hGet : old.get oi=strictAlong T (E.get i) := by simp [old,oi]
    have hH : IsClosedSubmanifold n (strictAlong T (E.get i)) := by
      rw [←hGet]
      exact MonomialPart.isClosedSubmanifold_get hn
        (isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_left old A.E)) oi
    have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
    have hIadm : (⟨A.N,A.E,I i,1⟩ : MarkedIdeal n Y).IsAdmissibleCentre C := by
      refine ⟨hπ.1,?_,hAdm.2.2⟩
      intro x hx
      change x ∈ cosupport n A.N (I i) 1
      rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem
        (hRecorded.2.2.2.2 i).1 hg)]
      refine ⟨hCN hx,?_⟩
      apply (HironakaSharpActualTraceIncidence.zeroLocus_restrictOn_iff hcH (hCN hx)).mpr
      rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hH.1]
      exact hCP i hi hx
    have hUnit : ∀ x ∈ C,(nonmonomialPartAlong n A.N (I i) A.E).mem x 1 := by
      intro x hx
      rw [(hRecorded.2.2.2.2 i).2.2.1]
      exact (hAtC x hx).2 i
    exact actual_controlled_old_monomial_part hn hRecorded.1 hH hBorn hRecorded.2.2.1
      (hRecorded.2.2.2.2 i).2.1 hIadm (hDadm i hi) (hCP i hi) hUnit hπ
  have hNormal (i : Fin E.length) : (vanishingIdeal (n := n) A'.N).Le (D' i) := by
    intro x g hg
    refine ⟨hg.1,fun _j _hxN _hxj => ?_⟩
    refine ⟨0,Fin.elim0,Fin.elim0,fun j => j.elim0,fun j => j.elim0,?_⟩
    filter_upwards [hg.2] with z hz hzN
    simpa using hz hzN
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  have hSum := HironakaG4ZeroMaskGammaStep.finite_mask_sum_controlled
    hRecorded.1 D D' hcD hcD' hNormal hπ P hPne hDadm hRow
  have hRecord : M.geoTransform C π=processedMaskMarked W E T' P := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      (𝔪 := M.geoTransform C π) (𝔫 := processedMaskMarked W E T' P) ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · exact hSum.symm
    · rfl
  exact ⟨hRecord,hCNC,hSharp,hDisjoint,hTest,hTestFull⟩

end

end Hironaka.HironakaActualProcessedMaskControlledSum
