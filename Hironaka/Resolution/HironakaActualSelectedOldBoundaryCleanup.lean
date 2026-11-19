import Hironaka.Resolution.HironakaActualSingleOldBoundaryCleanup
import Hironaka.Resolution.HironakaActualFiniteMarkedSumHistories

/-! A genuine selected OLD-row intersection is removed by an internally
constructed finite sum resolution. A maximal original incidence bound
derives full old/born legality; no current comparison is an input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSelectedOldBoundaryCleanup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower MemberInterTowerAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong.MarkedIdeal
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaActualSingleOldBoundaryCleanup
  HironakaActualFiniteMarkedSumHistories HironakaG4IncidentOldBornStratumCentre
  HironakaAdmissibleSequence HironakaAdmissibleCalculus HironakaLocalPrincipalization
  RelativePrincipalizationSpan RestrictedIdealExtension GermIdealOrder CanonicalCentres RestrictEmptyTower
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

def selectedSum (N : Set X) (O B : List (Set X)) (i : Fin O.length) (L : List (Fin O.length)) : MarkedIdeal n X:=
  finiteSum (boundaryRowMarked N B (O.get i)) (L.map fun j=>boundaryRowMarked N B (O.get j))

private theorem selected_fields (N : Set X) (O B : List (Set X)) (i : Fin O.length) (L : List (Fin O.length)) :
    (selectedSum N O B i L).N=N ∧ (selectedSum N O B i L).E=B := by
  cases L <;> exact ⟨rfl,rfl⟩

private theorem list_rows_iff (N : Set X) (O B : List (Set X)) (i : Fin O.length) (L : List (Fin O.length))
    (P : MarkedIdeal n X → Prop) :
    (∀A∈boundaryRowMarked N B (O.get i)::L.map (fun j=>boundaryRowMarked N B (O.get j)),P A) ↔
      ∀j∈i::L,P (boundaryRowMarked N B (O.get j)) := by
  constructor
  · intro h j hj
    rcases List.mem_cons.mp hj with rfl|hj
    · exact h _ (by simp)
    · exact h _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,hj,rfl⟩))
  · intro h A hA
    rcases List.mem_cons.mp hA with rfl|hA
    · exact h i (by simp)
    · obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hA
      exact h j (List.mem_cons_of_mem _ hj)

private theorem old_smooth (hn : 0<n) {O B : List (Set X)} (hE : IsSNCDivisor n (O++B))
    (j : Fin O.length) : IsClosedSubmanifold n (O.get j) :=
  MonomialPart.isClosedSubmanifold_get hn (isSNCDivisor_of_sublist hE (List.sublist_append_left O B)) j

private theorem row_boundary_snc {O B : List (Set X)} (hE : IsSNCDivisor n (O++B)) (j : Fin O.length) :
    IsSNCDivisor n (O.get j::B) := by
  exact isSNCDivisor_of_sublist hE
    ((List.singleton_sublist.mpr (List.get_mem O j)).append (List.Sublist.refl B))

private theorem row_data (hn : 0<n) (N : Set X) {O B : List (Set X)} (hE : IsSNCDivisor n (O++B))
    (i : Fin O.length) (L : List (Fin O.length)) :
    ∀A∈L.map (fun j=>boundaryRowMarked N B (O.get j)),
      A.N=(boundaryRowMarked N B (O.get i)).N ∧ A.E=(boundaryRowMarked N B (O.get i)).E ∧
        A.ideal.IsCoherent ∧ 1≤A.d := by
  intro A hA
  obtain ⟨j,_hj,rfl⟩:=List.mem_map.mp hA
  exact ⟨rfl,rfl,VanishingIdealCoherent.isCoherent_vanishingIdeal (old_smooth hn hE j),le_rfl⟩

private theorem selected_tests (hn : 0<n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O++B))
    (i : Fin O.length) (L : List (Fin O.length)) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    IsGeoTestTower (selectedSum N O B i L) T ↔
      ∀j∈i::L,IsGeoTestTower (boundaryRowMarked N B (O.get j)) T := by
  exact (finiteSum_history _ _ hN
    (VanishingIdealCoherent.isCoherent_vanishingIdeal (old_smooth hn hE i)) le_rfl
    (row_data hn N hE i L) T).1.trans (list_rows_iff N O B i L _)

private theorem selected_cosupp (hn : 0<n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O++B)) (hTrans : IsTransverse n N B)
    (i : Fin O.length) (L : List (Fin O.length)) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (selectedSum N O B i L) T) :
    (geoTransformAlong (selectedSum N O B i L) T).cosupp=
      {y | y∈strictAlong T N ∧ ∀j∈i::L,y∈strictAlong T (O.get j)} := by
  have hEach:=(selected_tests hn hN hE i L T).mp hT
  have hCos:=(finiteSum_history _ _ hN
    (VanishingIdealCoherent.isCoherent_vanishingIdeal (old_smooth hn hE i)) le_rfl
    (row_data hn N hE i L) T).2 hT |>.1
  change (geoTransformAlong (selectedSum N O B i L) T).cosupp=_ at hCos
  have hRowCos (j : Fin O.length) (hj : j∈i::L) :
      (geoTransformAlong (boundaryRowMarked N B (O.get j)) T).cosupp=
        strictAlong T N∩strictAlong T (O.get j) := by
    have hEq:=(actual_single_old_history hn hN (row_boundary_snc hE j) hTrans T (hEach j hj)).2
    have h:=hEq.cosupp_eq.trans (SmoothCentreLocus.cosupport_vanishingIdeal_one
      (isClosed_strictAlong T (old_smooth hn hE j).1))
    rw [N_geoTransformAlong] at h
    exact h
  ext y
  rw [hCos]
  change (∀A∈boundaryRowMarked N B (O.get i)::L.map (fun j=>boundaryRowMarked N B (O.get j)),
    y∈(geoTransformAlong A T).cosupp) ↔ _
  rw [list_rows_iff]
  constructor
  · intro h
    exact ⟨(hRowCos i (by simp) ▸ h i (by simp)).1,fun j hj=>(hRowCos j hj ▸ h j hj).2⟩
  · rintro ⟨hyN,h⟩ j hj
    rw [hRowCos j hj]
    exact ⟨hyN,h j hj⟩

private theorem full_boundary (N : Set X) (O B : List (Set X)) (i : Fin O.length) (L : List (Fin O.length)) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate (univ : Set X) (O++B)) T).E=
        O.map (strictAlong T)++(geoTransformAlong (selectedSum N O B i L) T).E
  | _,.refl => by
    rw [geoTransformAlong_refl,geoTransformAlong_refl,(selected_fields N O B i L).2]
    simp [geometricTemplate,strictAlong]
  | _,.step T C π hπ => by
    change ((geoTransformAlong (geometricTemplate (univ : Set X) (O++B)) T).E.map
      (geoStrictTransform π C) ++ [π ⁻¹' C])=_
    rw [full_boundary N O B i L T,List.map_append,List.append_assoc,List.map_map]
    rfl

private theorem sum_wellformed (hn : 0<n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O++B)) (hTrans : IsTransverse n N B)
    (i : Fin O.length) (L : List (Fin O.length)) : (selectedSum N O B i L).IsWellFormed := by
  have hG:=finiteSum_geometry _ _
    (VanishingIdealCoherent.isCoherent_vanishingIdeal (old_smooth hn hE i)) le_rfl (row_data hn N hE i L)
  refine ⟨?_,hG.2.2.1,?_,?_⟩
  · rw [(selected_fields N O B i L).1];exact hN
  · rw [(selected_fields N O B i L).2]
    exact isSNCDivisor_of_sublist hE (List.sublist_append_right O B)
  · rw [(selected_fields N O B i L).1,(selected_fields N O B i L).2]
    exact hTrans

theorem actual_selected_old_full_history (hn : 0<n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O++B)) (hTrans : IsTransverse n N B)
    (i : Fin O.length) (L : List (Fin O.length))
    (hMax : ∀x∈N,(Finset.univ.filter fun j : Fin O.length=>x∈O.get j).card≤(i::L).toFinset.card) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),IsGeoTestTower (selectedSum N O B i L) T →
      IsGeoTestTower (geometricTemplate (univ : Set X) (O++B)) T ∧
      (geoTransformAlong (selectedSum N O B i L) T).cosupp=
        {y | y∈strictAlong T N ∧ ∀j∈i::L,y∈strictAlong T (O.get j)}
  | _,.refl,hT => ⟨trivial,selected_cosupp hn hN hE hTrans i L .refl hT⟩
  | _,.step T C π hπ,hT => by
    classical
    let Q:=selectedSum N O B i L
    let A:=geoTransformAlong Q T
    obtain ⟨hFull,hCos⟩:=actual_selected_old_full_history hn hN hE hTrans i L hMax T hT.1
    have hWF:=sum_wellformed hn hN hE hTrans i L
    have hwT:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF T hT.1
    have hFullWF : (geometricTemplate (univ : Set X) (O++B)).IsWellFormed:=
      ⟨isClosedSubmanifold_univ,IdealWeightPowers.isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩
    have hSNC:=(MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hFullWF T hFull).isSNCDivisor
    rw [full_boundary N O B i L T] at hSNC
    have hCTrace : ∀x∈C,x∈strictAlong T N ∧ ∀j∈i::L,x∈strictAlong T (O.get j):=
      fun x hx=>(Set.ext_iff.mp hCos x).mp (hT.2.2.1 hx)
    have hIncident (x) (hx : x∈C) :
        ∀j : Fin O.length,x∈strictAlong T (O.get j) → j∈i::L := by
      let I:=Finset.univ.filter fun j : Fin O.length=>x∈strictAlong T (O.get j)
      let I₀:=Finset.univ.filter fun j : Fin O.length=>T.proj x∈O.get j
      have hSub : I⊆I₀:=by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,strictAlong_subset_preimage T (old_smooth hn hE j).1
          (Finset.mem_filter.mp hj).2⟩
      have hSel : (i::L).toFinset⊆I:=by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hCTrace x hx).2 j (List.mem_toFinset.mp hj)⟩
      have hxN : T.proj x∈N:=strictAlong_subset_preimage T hN.1 (hCTrace x hx).1
      have hCard : I.card≤(i::L).toFinset.card:=(Finset.card_le_card hSub).trans (hMax _ hxN)
      have hEq : (i::L).toFinset=I:=Finset.eq_of_subset_of_card_le hSel hCard
      intro j hj
      apply List.mem_toFinset.mp
      rw [hEq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
    have hNC : HasNormalCrossings n C (O.map (strictAlong T)++A.E):=by
      intro x hx
      apply actual_incident_old_normalCrossingsAt hSNC hT.2.2.2 hx
      intro j hj
      let j₀ : Fin O.length:=⟨j.val,by simpa using j.isLt⟩
      have hGet : (O.map (strictAlong T)).get j=strictAlong T (O.get j₀):=by simp [j₀]
      rw [hGet] at hj ⊢
      have hSelected:=hIncident x hx j₀ hj
      exact Eventually.of_forall fun y hy=>(hCTrace y hy).2 j₀ hSelected
    have hFullNext : IsGeoTestTower (geometricTemplate (univ : Set X) (O++B)) (.step T C π hπ):=by
      let G:=geometricTemplate (univ : Set X) (O++B)
      have hG:=pullback_eq_mul_geoTransformAlong (𝔪:=G) rfl IdealWeightPowers.isCoherent_unitIdeal T hFull
      have hd : (geoTransformAlong G T).d=0:=d_geoTransformAlong G T
      have hCosG : (geoTransformAlong G T).cosupp=univ:=by
        change cosupport n (geoTransformAlong G T).N (geoTransformAlong G T).ideal (geoTransformAlong G T).d=univ
        rw [hd,cosupport_zero (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hG.2.1 hg),hG.1]
      refine ⟨hFull,⟨hπ.1,?_,?_⟩⟩
      · rw [hCosG];exact subset_univ C
      · rw [full_boundary N O B i L T]
        exact hNC
    exact ⟨hFullNext,selected_cosupp hn hN hE hTrans i L (.step T C π hπ) hT⟩

theorem exists_actual_selected_old_cleanup (hn : 0<n) {N F : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hComp : IsCompact N)
    (hE : IsSNCDivisor n (O++B)) (hTrans : IsTransverse n N B)
    (i : Fin O.length) (L : List (Fin O.length))
    (hMax : ∀x∈N,(Finset.univ.filter fun j : Fin O.length=>x∈O.get j).card≤(i::L).toFinset.card)
    (hDense : N⊆closure (N \ ⋃H∈O,H))
    (hFoot : {x | x∈N ∧ ∀j∈i::L,x∈O.get j}⊆F) :
    ∃(Y : CMfd.{u} n)(T : BlowupTower X Y),
      IsGeoTestTower (selectedSum N O B i L) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (O++B)) T ∧
      CentresOver {x | x∈N ∧ ∀j∈i::L,x∈O.get j} T ∧
      IsAdmissibleBlowupSequence n X (O++B) F Y T.proj
        (geoTransformAlong (geometricTemplate (univ : Set X) (O++B)) T).E ∧
      IsProperMap T.proj ∧ IsIsomorphismOver n T.proj Fᶜ ∧
      IsClosedSubmanifold n (strictAlong T N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (O++B)) T).E ∧
      IsTransverse n (strictAlong T N) (geoTransformAlong (selectedSum N O B i L) T).E ∧
      {y | y∈strictAlong T N ∧ ∀j∈i::L,y∈strictAlong T (O.get j)}=∅ := by
  let A:=boundaryRowMarked N B (O.get i)
  let Q:=selectedSum N O B i L
  have hw:=sum_wellformed hn hN hE hTrans i L
  have hHead : A.IsWellFormed:=by
    simpa only [selectedSum,finiteSum,List.map_nil] using sum_wellformed hn hN hE hTrans i []
  have hSingle : IsSNCDivisor n [O.get i]:=
    isSNCDivisor_of_sublist
      (isSNCDivisor_of_sublist hE (List.sublist_append_left O B))
      (List.singleton_sublist.mpr (List.get_mem O i))
  have hDenseHead : N⊆closure (N \ O.get i):=hDense.trans (closure_mono (by
    intro x hx
    refine ⟨hx.1,fun hxi=>hx.2 ?_⟩
    exact mem_iUnion.mpr ⟨O.get i,mem_iUnion.mpr ⟨List.get_mem O i,hxi⟩⟩))
  have hNZ : ∀x∈A.N,DivisorExponentAlong.IsNonzeroAlongAt A.N A.ideal x:=fun _ hx=>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hSingle hDenseHead hx
  have hDomHead : IsInvDomain (n+1) A:=⟨hHead,(by
    intro x hx
    obtain ⟨k,hk⟩:=hN.2 x hx
    exact ⟨k,hk.1.trans (Nat.le_succ n),hk⟩),le_rfl,hNZ⟩
  have hDom : IsInvDomain (n+1) Q:=finiteSum_isInvDomain A _ hDomHead (row_data hn N hE i L)
  have hCos : Q.cosupp={x | x∈N ∧ ∀j∈i::L,x∈O.get j}:=by
    simpa only [geoTransformAlong_refl,strictAlong] using selected_cosupp hn hN hE hTrans i L
      (.refl : BlowupTower X X) trivial
  have hClosed : IsClosed Q.cosupp:=GiraudAlong.isClosed_cosupport_along hw.isCoherent hw.isClosedSubmanifold_N _
  have hSub : Q.cosupp⊆N:=by
    rw [←(selected_fields N O B i L).1]
    exact Q.cosupp_subset_N
  have hK : IsCompact Q.cosupp:=hComp.of_isClosed_subset hClosed hSub
  obtain ⟨Y,T,_hCan,hRes⟩:=exists_isGeoResolution_isCanonical_of_isCompact (invFamily hn (n+1)) hDom hK
  obtain ⟨hFull,hCurrent⟩:=actual_selected_old_full_history hn hN hE hTrans i L hMax T hRes.1
  have hOver : CentresOver {x | x∈N ∧ ∀j∈i::L,x∈O.get j} T:=by
    rw [←hCos]
    exact centresOver_cosupp Q hw.isClosedSubmanifold_N hw.isCoherent T hRes.1
  have hSeq:=(isAdmissibleBlowupSequence_proj (geometricTemplate (univ : Set X) (O++B)) _ T hFull hOver).mono hFoot
  have hFullWF : (geometricTemplate (univ : Set X) (O++B)).IsWellFormed:=
    ⟨isClosedSubmanifold_univ,IdealWeightPowers.isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hwFull:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hFullWF T hFull
  have hwT:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hRes.1
  have hNid : (geoTransformAlong Q T).N=strictAlong T N:=by
    rw [N_geoTransformAlong,(selected_fields N O B i L).1]
  refine ⟨Y,T,hRes.1,hFull,hOver,hSeq,isProperMap_of_isBlowupSequence hSeq.isBlowupSequence,
    HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hSeq,?_,hwFull.isSNCDivisor,?_,?_⟩
  · rw [←hNid];exact hwT.isClosedSubmanifold_N
  · rw [←hNid];exact hwT.isTransverse
  · exact hCurrent.symm.trans hRes.2

end
end Hironaka.HironakaActualSelectedOldBoundaryCleanup
