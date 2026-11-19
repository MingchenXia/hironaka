import Hironaka.Resolution.HironakaSharpActualFullValueAmbientCentre

/-! Joint original-only finite FIRST histories retain the WHOLE ambient original
boundary and genuine whole strict-trace factor dictionaries. No desired history,
incidence, factor or avoidance certificate is supplied by the final caller.
Full mathematics precedes source in
`hironaka-sharp-incident-ambient-dynamic-prefixes-extension.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalAmbientDynamicGoodPrefixes
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerSplit HomogenizedGlueingTower
  HironakaSharpActualFullValueAmbientCentre HironakaSharpActualIncidentCentreTrace
  HironakaSharpOriginalDynamicGoodPrefixes HironakaSharpActualOriginalDynamicStep
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualDynamicDistinctCentre
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalStrictStep
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualChronologicalNoOldFactor
  HironakaSharpActualTotalAccumulatedResidual HironakaSharpActualTotalNonmonomialTransport
  HironakaSharpActualCompositeTotalResidual HironakaSharpOriginalFirstMemberExceptionalFactor
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaCoherentTransformExtension RelativePrincipalizationSpan RestrictedIdealExtension
  NormalCrossings NormalCrossingsComparison SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder IdealWeightPowers InvertibleIdealQuotient RestrictLeCalculus
  MonomialPartAlong DivisorExponentAlong NonmonomialTransformAlong MarkedIdealOperationsAlong
  RestrictEmptyTower ResolutionDriver CanonicalCentres
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem restrictOn_idempotent (N : Set X) (I : GermIdeal n X) :
    restrictOn n N (restrictOn n N I)=restrictOn n N I := by
  ext x g
  exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun s hs => hs.2) hg.2⟩,
    fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩

private theorem whole_factor_of_residual (hn : 0<n) {N : Set X} {B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hB : IsSNCDivisor n B) (hT : IsTransverse n N B)
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ x∈N,IsNonzeroAlongAt N I x)
    (hNorm : restrictOn n N I=I) (hNm : nonmonomialPartAlong n N I B=J) :
    I=restrictOn n N ((monomialPartAlong n N I B).mul J) := by
  obtain ⟨_hcR,_hcD,_hnzD,_hmD,_hNo,_hnzR,hFactor⟩ := parts_hypotheses hn
    (⟨N,B,I,0⟩ : MarkedIdeal n X) ⟨hN,hI,hB,hT⟩ hnz
  have he := restrictOn_eq_of_restrictLe hN.1 hFactor.le hFactor.ge
  change restrictOn n N I=restrictOn n N ((nonmonomialPartAlong n N I B).mul (monomialPartAlong n N I B)) at he
  rw [hNorm,hNm,RestrictLeCalculus.mul_comm'] at he
  exact he

private theorem ambient_boundary_eq (W : Set X) (E : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E=
        E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E
  | _,.refl => by
    change E=E.map id ++ []
    rw [List.map_id,List.append_nil]
  | _,.step T C π hπ => by
    change (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E.map
      (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]=_
    rw [ambient_boundary_eq W E T,List.map_append,List.append_assoc]
    congr 1
    rw [List.map_map]
    rfl

private theorem ambient_carrier_univ (E : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).N=univ
  | _,.refl => rfl
  | _,.step T C π hπ => by
    change BlowupStrictSubmanifold.geoStrictTransform π C (geoTransformAlong (geometricTemplate (univ : Set X) E) T).N=univ
    rw [ambient_carrier_univ E T,geoStrictTransform_univ hπ]

/-- The actual full ambient test and whole original-indexed trace dictionary.
All entries, including every empty born position, remain literal. -/
def HasAmbientTraceState (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) : Prop :=
  IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
  ∀ i : Fin E.length,
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    let B := (geoTransformAlong (geometricTemplate W []) T).E
    let H := strictAlong T (E.get i)
    let I := restrictOn n N (vanishingIdeal (n := n) H)
    let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    N⊆closure (N \ H) ∧ I.IsCoherent ∧ (∀ x∈N,IsNonzeroAlongAt N I x) ∧
      (∀ x∈N,∃ f : Y → ℂ,HolomorphicAt n f x ∧ ∀ g,I.mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g) ∧
      nonmonomialPartAlong n N I B=J ∧ I=restrictOn n N ((monomialPartAlong n N I B).mul J)

/-- The initial whole state comes only from true original SNC/density geometry. -/
theorem ambient_trace_state_refl (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) : HasAmbientTraceState W E (.refl : BlowupTower X X) := by
  refine ⟨trivial,?_⟩
  intro i
  let I := restrictOn n W (vanishingIdeal (n := n) (E.get i))
  have hg := original_members_actual_finite_chronological_geometry hn hW hE hdense i (.refl : BlowupTower X X) trivial
  have hcI : I.IsCoherent := hg.2.2.2.1.isCoherent
  have hnzI : ∀ x∈W,IsNonzeroAlongAt W I x := hg.2.2.2.2.1
  have hNm : nonmonomialPartAlong n W I []=I := by
    rw [nonmonomialPartAlong_nil_eq_restrictOn]
    exact restrictOn_idempotent _ _
  refine ⟨?_,hcI,hnzI,hg.2.2.2.2.2,hNm,?_⟩
  · exact hdense.trans (closure_mono (by
      rintro x ⟨hx,hout⟩
      exact ⟨hx,fun h => hout (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,h⟩)⟩))
  · exact whole_factor_of_residual hn hW isSNCDivisor_nil
      (isTransverse_nil_of_isClosedSubmanifold hW) hcI hnzI (restrictOn_idempotent _ _) hNm

private theorem ambient_trace_state_step (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hState : HasAmbientTraceState W E T)
    {C : Set Y} {Z : CMfd.{u} n} {π : Z → Y} (hπ : IsBlowupAlong n C π)
    (hCN : C⊆(geoTransformAlong (geometricTemplate W []) T).N)
    (hBornNC : HasNormalCrossings n C (geoTransformAlong (geometricTemplate W []) T).E)
    (hAmbientNC : HasNormalCrossings n C (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E))
    (hLoc : ∀ x∈C,∀ i : Fin E.length,x∈strictAlong T (E.get i) → ∀ᶠ y in 𝓝 x,y∈C → y∈strictAlong T (E.get i)) :
    HasAmbientTraceState W E (.step T C π hπ) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let Q := geometricTemplate (univ : Set X) E
  have hwQ : Q.IsWellFormed :=
    ⟨⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
      isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hwAmb := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwQ T hState.1
  have hAdm : (geoTransformAlong Q T).IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,?_⟩
    · change C⊆cosupport n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal (geoTransformAlong Q T).d
      rw [d_geoTransformAlong]
      change C⊆cosupport n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal 0
      rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hwAmb.isCoherent hg),ambient_carrier_univ E T]
      exact subset_univ C
    · rw [ambient_boundary_eq W E T]
      exact hAmbientNC
  have hAmbNew : IsGeoTestTower Q (.step T C π hπ) := ⟨hState.1,hAdm⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (show (geometricTemplate W []).IsWellFormed from
      ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩) T hT
  have hNextGeom : IsGeoTestTower (geometricTemplate W []) (.step T C π hπ) :=
    ⟨hT,⟨hπ.1,by
      change C⊆cosupport n A.N A.ideal (geoTransformAlong (geometricTemplate W []) T).d
      rw [d_geoTransformAlong]
      change C⊆cosupport n (geoTransformAlong (geometricTemplate W []) T).N
        (geoTransformAlong (geometricTemplate W []) T).ideal 0
      rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hwA.isCoherent hg)]
      exact hCN,hBornNC⟩⟩
  have hwNext := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (show (geometricTemplate W []).IsWellFormed from
      ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩) _ hNextGeom
  have hSNC : IsSNCDivisor n (E.map (strictAlong T) ++ A.E) := by
    rw [←ambient_boundary_eq W E T]
    exact hwAmb.isSNCDivisor
  refine ⟨hAmbNew,?_⟩
  intro i
  let H := strictAlong T (E.get i)
  let I := restrictOn n A.N (vanishingIdeal (n := n) H)
  let J := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  obtain ⟨hDense,hcI,hnzI,_hprI,hNm,_hFactor⟩ := hState.2 i
  have hHS : IsSNCDivisor n [H] := isSNCDivisor_of_sublist hSNC
    (List.singleton_sublist.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨E.get i,List.get_mem E i,rfl⟩)))
  have hLocH : ∀ x∈C,x∈H → ∀ᶠ y in 𝓝 x,y∈C → y∈H := fun x hx => hLoc x hx i
  obtain ⟨hNnew,_hHnew,hcNew,hnzNew,hDenseNew,hPrNew⟩ :=
    incident_centre_whole_strict_trace_geometry hn hwA.isClosedSubmanifold_N hHS hDense hLocH hπ hCN
  have hTrace := incident_centre_accumulated_trace_nonmonomial_eq_total hn hwA.isClosedSubmanifold_N
    hwA.isSNCDivisor hwA.isTransverse hHS hDense hLocH hπ hCN hBornNC
  have hTransport := actual_whole_total_nonmonomial_parts_transport hn hwA.isClosedSubmanifold_N
    hwA.isSNCDivisor hwA.isTransverse hcI hnzI hπ hCN hBornNC
  change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
    (nextTotalMarked A.N I C π).ideal (A.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])=
      nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
        (nextTotalMarked A.N (nonmonomialPartAlong n A.N I A.E) C π).ideal
        (A.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) at hTransport
  rw [hNm] at hTransport
  have hRaw := geoTransform_zeroMark_ideal_eq_restricted_total (⟨A.N,[],I,0⟩ : MarkedIdeal n Y) rfl C π
  change (nextTotalMarked A.N I C π).ideal=restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
    (GermIdeal.pullback (m := n) π I) at hRaw
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hHS (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHc
  have hNormalize : restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
      (GermIdeal.pullback (m := n) π I)=
      restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
        (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)) :=
    actual_normalized_pullback_restrictOn hwA.isClosedSubmanifold_N hNnew.1 hcH hπ.contMDiff
    (fun y hy => BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hwA.isClosedSubmanifold_N.1 hy)
  rw [hRaw,hNormalize] at hTransport
  obtain ⟨hJN,hJE,_hJd,hwJ,hnzJ,hprJ⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  change J.N=A.N at hJN
  change J.E=A.E at hJE
  have hCJ : C⊆J.N := by rw [hJN];exact hCN
  have hNCJ : HasNormalCrossings n C J.E := by rw [hJE];exact hBornNC
  have hNo := original_members_actual_finite_chronological_no_exceptional_factor hn hW hE hdense i T hT
  have hNext := nextTotal_accumulated_nonmonomial_eq_nextStrict hn hwJ.isClosedSubmanifold_N
    hwJ.isSNCDivisor hwJ.isTransverse hwJ.isCoherent hnzJ hprJ hπ hCJ hNCJ hNo
  change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C J.N)
    (nextTotalMarked J.N J.ideal C π).ideal (J.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])=
      nextRelativeStrict J.N J.ideal C π at hNext
  rw [hJN,hJE] at hNext
  have hNmNew : nonmonomialPartAlong n (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N
      (restrictOn n (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N
        (vanishingIdeal (n := n) (strictAlong (.step T C π hπ) (E.get i))))
      (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).E=
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step T C π hπ)).ideal := by
    change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
      (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
        (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H)))
      (A.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])=nextRelativeStrict J.N J.ideal C π
    rw [hJN]
    exact hTrace.2.2.trans (hTransport.trans hNext)
  refine ⟨hDenseNew,hcNew,hnzNew,hPrNew,hNmNew,?_⟩
  exact whole_factor_of_residual hn hwNext.isClosedSubmanifold_N hwNext.isSNCDivisor hwNext.isTransverse
    hcNew hnzNew (restrictOn_idempotent _ _) hNmNew

/-- The joint state extends on the SAME internally chosen genuine FULL maximum,
with actual all-boundary incidence and whole next trace dictionaries produced. -/
theorem exists_joint_dynamic_successor (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hK : IsCompact W) {d : ℕ} (hd : d+1≤n)
    (hr : ∀ x∈W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hTest : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    (hRule : IsDynamicFirstPrefix hn W E T)
    (hOver : CentresOver (originalSharpBadLocus (n := n) W E) T)
    (hState : HasAmbientTraceState W E T) :
    ∃ (C : Set Y) (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower (originalMemberProductMarked W E 1) (.step T C π hπ) ∧
      IsDynamicFirstPrefix hn W E (.step T C π hπ) ∧
      CentresOver (originalSharpBadLocus (n := n) W E) (.step T C π hπ) ∧
      HasAmbientTraceState W E (.step T C π hπ) := by
  have hwM : (originalMemberProductMarked W E 1).IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hGeom := actual_original_test_history_template _ hwM T hTest
  by_cases hZ : chronologicalDistinctDefect W E T=∅
  · let hπ := BlowupExistenceCodimOne.isBlowupAlong_id_empty (n := n) (X := Y)
    have hStateNew := ambient_trace_state_step hn hW hE hdense T hGeom hState hπ (empty_subset _)
      (fun _ hx => hx.elim) (fun _ hx => hx.elim) (fun _ hx => hx.elim)
    exact ⟨∅,Y,id,hπ,⟨hTest,isAdmissibleCentre_empty _⟩,
      ⟨hRule,by simp only [hZ,ite_true]⟩,⟨hOver,empty_subset _⟩,hStateNew⟩
  · obtain ⟨C,_hneC,hCZ,hAdm,_hLevel,hCeq⟩ := exists_original_dynamic_distinct_centre
      hn hW hE hdense hK hd hr T hTest (Set.nonempty_iff_ne_empty.mpr hZ)
    have hFull : ∀ x∈C,∀ y∈C,(invFamily hn (n+1)).inv (currentProductMarked W E T) .refl x=
        (invFamily hn (n+1)).inv (currentProductMarked W E T) .refl y :=
      fun x hx y hy => ((hCeq ▸ hy).2 x (hCeq ▸ hx).1).antisymm ((hCeq ▸ hx).2 y (hCeq ▸ hy).1)
    have hwAmbient := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (show (geometricTemplate (univ : Set X) E).IsWellFormed from
        ⟨⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
          isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩) T hState.1
    have hAmbient : IsSNCDivisor n (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) := by
      rw [←ambient_boundary_eq W E T]
      exact hwAmbient.isSNCDivisor
    have hDense := fun i => (hState.2 i).1
    have hNm := fun i => (hState.2 i).2.2.2.2.1
    have hLoc := full_value_centre_retained_incidence hn hW hE hdense hK hd hr T hGeom hAmbient hDense hNm hCZ hFull
    have hNC := full_value_centre_hasNormalCrossings_ambient hn hW hE hdense hK hd hr T hGeom
      hAmbient hDense hNm hAdm.1 hCZ hFull
    have hDom := originalMemberProductMarked_isInvDomain hn hW hE hd hr hdense le_rfl
    have hDomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom T hTest
    have hThin : interior C=∅ := eq_empty_of_subset_empty
      ((interior_mono hAdm.2.1).trans (ResolutionInvariantDriver.interior_cosupp_eq_empty hDomT).subset)
    obtain ⟨Z,π,hπ⟩ := exists_blowup C hAdm.1 hThin
    have hCN : C⊆(geoTransformAlong (geometricTemplate W []) T).N := fun _ hx => (hCZ hx).1
    have hBN : HasNormalCrossings n C (geoTransformAlong (geometricTemplate W []) T).E := by
      have he := geoTransformAlong_E_eq_of_E_eq (𝔍 := originalMemberProductMarked W E 1)
        (𝔪 := geometricTemplate W []) rfl T
      rw [←he]
      exact hAdm.2.2
    have hNew := ambient_trace_state_step hn hW hE hdense T hGeom hState hπ hCN hBN hNC hLoc
    exact ⟨C,Z,π,hπ,⟨hTest,hAdm⟩,⟨hRule,by simpa only [hZ,ite_false] using hCeq⟩,
      ⟨hOver,hCZ.trans (chronologicalDistinctDefect_subset_originalBad_of_centresOver hn hW hE hdense T hTest hOver)⟩,hNew⟩

/-- ONLY original compact-pure geometry internally constructs every finite
full-ambient FIRST prefix and every whole trace state, preserving all empty years. -/
theorem exists_original_ambient_dynamic_first_prefix (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hK : IsCompact W) {d : ℕ} (hd : d+1≤n)
    (hr : ∀ x∈W,RegularAtDim (n := n) W x (d+1)) (a : ℕ) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),T.length=a ∧
      IsGeoTestTower (originalMemberProductMarked W E 1) T ∧ IsDynamicFirstPrefix hn W E T ∧
      CentresOver (originalSharpBadLocus (n := n) W E) T ∧ HasAmbientTraceState W E T ∧
      IsIsomorphismOver n T.proj (originalGoodLocus (n := n) W E) ∧
      ∀ j,IsGeoTestTower (originalMemberProductMarked W E 1) (head T j) ∧
        IsDynamicFirstPrefix hn W E (head T j) ∧
        CentresOver (originalSharpBadLocus (n := n) W E) (head T j) ∧
        HasAmbientTraceState W E (head T j) ∧
        IsIsomorphismOver n (head T j).proj (originalGoodLocus (n := n) W E) := by
  have hCore : ∀ k : ℕ,∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),T.length=k ∧
      IsGeoTestTower (originalMemberProductMarked W E 1) T ∧ IsDynamicFirstPrefix hn W E T ∧
      CentresOver (originalSharpBadLocus (n := n) W E) T ∧ HasAmbientTraceState W E T ∧
      ∀ j,HasAmbientTraceState W E (head T j) := by
    intro k
    induction k with
    | zero =>
      have hInit := ambient_trace_state_refl hn hW hE hdense
      refine ⟨X,.refl,rfl,trivial,trivial,trivial,hInit,?_⟩
      intro j
      cases j <;> exact hInit
    | succ k ih =>
      obtain ⟨Y,T,hLen,hTest,hRule,hOver,hState,hHeads⟩ := ih
      obtain ⟨C,Z,π,hπ,hNewTest,hNewRule,hNewOver,hNewState⟩ :=
        exists_joint_dynamic_successor hn hW hE hdense hK hd hr T hTest hRule hOver hState
      refine ⟨Z,.step T C π hπ,by simp only [BlowupTower.length_step,hLen],hNewTest,hNewRule,hNewOver,hNewState,?_⟩
      intro j
      cases j with
      | zero => exact hNewState
      | succ j => exact hHeads j
  obtain ⟨Y,T,hLen,hTest,hRule,hOver,hState,hHeads⟩ := hCore a
  have hGood {Z : CMfd.{u} n} (S : BlowupTower X Z)
      (hS : CentresOver (originalSharpBadLocus (n := n) W E) S) :
      IsIsomorphismOver n S.proj (originalGoodLocus (n := n) W E) := by
    simpa only [originalSharpBadLocus_eq_compl_good,compl_compl] using
      isIsomorphismOver_proj_of_centresOver (originalSharpBadLocus (n := n) W E) S hS
  refine ⟨Y,T,hLen,hTest,hRule,hOver,hState,hGood T hOver,?_⟩
  intro j
  have hO := centresOver_head (originalSharpBadLocus (n := n) W E) T j hOver
  exact ⟨((isGeoTestTower_iff_head_tail _ T j).mp hTest).1,
    isDynamicFirstPrefix_head hn W E T hRule j,hO,hHeads j,hGood _ hO⟩

end
end Hironaka.HironakaSharpOriginalAmbientDynamicGoodPrefixes
