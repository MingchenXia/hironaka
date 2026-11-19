import Hironaka.Resolution.HironakaActualChronologicalDefectMeasure
import Hironaka.Resolution.HironakaSharpActualFirstAmbientStrictTraceFactor
import Hironaka.Resolution.HironakaG4IncidentOldBornStratumCentre

/-! Genuine arbitrary-born cleanup for one distinguished old ambient member.
Full old/born history legality and the whole strict-member controlled-ideal
dictionary are derived. No constant contact or prescribed endpoint is input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSingleOldBoundaryCleanup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualFirstAmbientStrictTraceFactor HironakaG4IncidentOldBornStratumCentre
  HironakaAdmissibleSequence HironakaAdmissibleCalculus RelativePrincipalizationSpan
  RestrictedIdealExtension RestrictedIdealWeight GermIdealOrder CanonicalCentres
  HironakaLocalPrincipalization RestrictEmptyTower
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

def boundaryRowMarked (N : Set X) (B : List (Set X)) (H : Set X) : MarkedIdeal n X:=
  ⟨N,B,vanishingIdeal (n:=n) H,1⟩

private theorem full_boundary_cons (N H : Set X) (B : List (Set X)) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate (univ : Set X) (H::B)) T).E=
        strictAlong T H::(geoTransformAlong (boundaryRowMarked N B H) T).E
  | _,.refl => rfl
  | _,.step T C π hπ => by
    change ((geoTransformAlong (geometricTemplate (univ : Set X) (H::B)) T).E.map
      (geoStrictTransform π C) ++ [π ⁻¹' C])=_
    rw [full_boundary_cons N H B T,List.map_cons,List.cons_append]
    rfl

private theorem source_wellformed (hn : 0<n) {N H : Set X} {B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (H::B))
    (hT : IsTransverse n N B) : (boundaryRowMarked N B H).IsWellFormed := by
  have hH:=MonomialPart.isClosedSubmanifold_get hn hE (0 : Fin (H::B).length)
  exact ⟨hN,VanishingIdealCoherent.isCoherent_vanishingIdeal hH,
    isSNCDivisor_of_sublist hE (show B.Sublist (H::B) from List.tail_sublist (H::B)),hT⟩

private theorem ambient_wellformed {H : Set X} {B : List (Set X)}
    (hE : IsSNCDivisor n (H::B)) : (geometricTemplate (univ : Set X) (H::B)).IsWellFormed:=
  ⟨isClosedSubmanifold_univ,IdealWeightPowers.isCoherent_unitIdeal,hE,
    isTransverse_univ_of_isSNCDivisor hE⟩

theorem actual_single_old_history (hn : 0<n) {N H : Set X} {B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (H::B))
    (hTrans : IsTransverse n N B) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),IsGeoTestTower (boundaryRowMarked N B H) T →
      IsGeoTestTower (geometricTemplate (univ : Set X) (H::B)) T ∧
      RestrictEquiv (geoTransformAlong (boundaryRowMarked N B H) T)
        (⟨(geoTransformAlong (boundaryRowMarked N B H) T).N,
          (geoTransformAlong (boundaryRowMarked N B H) T).E,
          vanishingIdeal (n:=n) (strictAlong T H),1⟩ : MarkedIdeal n Y)
  | _,.refl,_hT => ⟨trivial,RestrictEquiv.refl (source_wellformed hn hN hE hTrans).isCoherent⟩
  | _,.step T C π hπ,hT => by
    let Q:=boundaryRowMarked N B H
    let A:=geoTransformAlong Q T
    let H₀:=strictAlong T H
    let M : MarkedIdeal n _:=⟨A.N,A.E,vanishingIdeal (n:=n) H₀,1⟩
    obtain ⟨hFull,hEq⟩:=actual_single_old_history hn hN hE hTrans T hT.1
    have hw:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (source_wellformed hn hN hE hTrans) T hT.1
    have hSNC:= (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong (ambient_wellformed hE) T hFull).isSNCDivisor
    rw [full_boundary_cons N H B T] at hSNC
    have hH₀ : IsClosedSubmanifold n H₀:=MonomialPart.isClosedSubmanifold_get hn hSNC (0 : Fin (H₀::A.E).length)
    have hModelCo : M.ideal.IsCoherent:=VanishingIdealCoherent.isCoherent_vanishingIdeal hH₀
    have hCModel : C⊆M.cosupp:=fun x hx=>hEq.cosupp_eq ▸ hT.2.2.1 hx
    have hCos : M.cosupp=A.N∩H₀:=SmoothCentreLocus.cosupport_vanishingIdeal_one hH₀.1
    have hCN : C⊆A.N:=fun _ hx=>(hCos ▸ hCModel hx).1
    have hCH : C⊆H₀:=fun _ hx=>(hCos ▸ hCModel hx).2
    have hNC : HasNormalCrossings n C (H₀::A.E) := by
      intro x hx
      apply actual_incident_old_normalCrossingsAt (old:=[H₀]) hSNC hT.2.2.2 hx
      intro i _hi
      have hi0 : i=0:=Fin.ext (by change i.val=0;have hh:=i.isLt;simp only [List.length_singleton] at hh;omega)
      subst i
      exact Eventually.of_forall fun y hy=>hCH hy
    have hFullNext : IsGeoTestTower (geometricTemplate (univ : Set X) (H::B)) (.step T C π hπ):=by
      let L:=geometricTemplate (univ : Set X) (H::B)
      have hL:=pullback_eq_mul_geoTransformAlong (𝔪:=L) rfl IdealWeightPowers.isCoherent_unitIdeal T hFull
      have hd : (geoTransformAlong L T).d=0:=d_geoTransformAlong L T
      have hCosL : (geoTransformAlong L T).cosupp=univ:=by
        change cosupport n (geoTransformAlong L T).N (geoTransformAlong L T).ideal (geoTransformAlong L T).d=univ
        rw [hd,cosupport_zero (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hL.2.1 hg),hL.1]
      refine ⟨hFull,⟨hπ.1,?_,?_⟩⟩
      · rw [hCosL];exact subset_univ C
      · rw [full_boundary_cons N H B T]
        exact hNC
    have hTransform:=hEq.geoTransform_eq hw.isClosedSubmanifold_N.1 hw.isCoherent hModelCo (C:=C) hπ.contMDiff
    have hI : (geoTransformAlong Q (.step T C π hπ)).ideal=
        restrictOn n (geoStrictTransform π C A.N) (vanishingIdeal (n:=n) (geoStrictTransform π C H₀)) := by
      change (A.geoTransform C π).ideal=_
      rw [hTransform]
      exact actual_first_controlled_ambient_strict_trace hw.isClosedSubmanifold_N hH₀ hπ hCN hCH
    have hHnew:=BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hH₀ hCH
    refine ⟨hFullNext,⟨rfl,rfl,?_,?_,?_⟩⟩
    · exact d_geoTransformAlong Q (.step T C π hπ)
    · change RestrictLe (geoStrictTransform π C A.N) (geoTransformAlong Q (.step T C π hπ)).ideal
        (vanishingIdeal (n:=n) (geoStrictTransform π C H₀))
      rw [hI]
      exact restrictLe_restrictOn
    · change RestrictLe (geoStrictTransform π C A.N) (vanishingIdeal (n:=n) (geoStrictTransform π C H₀))
        (geoTransformAlong Q (.step T C π hπ)).ideal
      rw [hI]
      exact restrictLe_self_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal hHnew)

private theorem full_normal_crossings_of_disjoint {Y : CMfd.{u} n} {N H : Set Y} {B : List (Set Y)}
    (hT : IsTransverse n N B) (hDisj : Disjoint N H) : HasNormalCrossings n N (H::B) := by
  intro x hx
  obtain ⟨S₀,S,⟨Φ,ht,h0,hfamily⟩,hcard⟩:=hT x hx
  let S' : Fin (H::B).length → Finset (Fin n):=Fin.cases ∅ S
  refine ⟨S₀,S',⟨Φ,ht,h0,?_⟩,?_⟩
  · rintro (_|i) hi
    · exact hfamily none hi
    · cases i using Fin.cases with
      | zero => exact (Set.disjoint_left.mp hDisj hx hi).elim
      | succ j => exact hfamily (some j) hi
  · intro i hi
    cases i using Fin.cases with
    | zero => exact (Set.disjoint_left.mp hDisj hx hi).elim
    | succ j => exact (hcard j hi).1

theorem exists_actual_single_old_cleanup (hn : 0<n) {N H F : Set X} {B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hComp : IsCompact N)
    (hE : IsSNCDivisor n (H::B)) (hTrans : IsTransverse n N B)
    (hDense : N⊆closure (N \ H)) (hFoot : N∩H⊆F) :
    ∃(Y : CMfd.{u} n)(T : BlowupTower X Y),
      IsGeoTestTower (boundaryRowMarked N B H) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (H::B)) T ∧
      CentresOver (N∩H) T ∧
      IsAdmissibleBlowupSequence n X (H::B) F Y T.proj
        (geoTransformAlong (geometricTemplate (univ : Set X) (H::B)) T).E ∧
      IsProperMap T.proj ∧ IsIsomorphismOver n T.proj Fᶜ ∧
      IsClosedSubmanifold n (strictAlong T N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (H::B)) T).E ∧
      IsTransverse n (strictAlong T N) (geoTransformAlong (boundaryRowMarked N B H) T).E ∧
      strictAlong T N∩strictAlong T H=∅ ∧
      HasNormalCrossings n (strictAlong T N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (H::B)) T).E := by
  let Q:=boundaryRowMarked N B H
  have hw:=source_wellformed hn hN hE hTrans
  have hH : IsClosedSubmanifold n H:=MonomialPart.isClosedSubmanifold_get hn hE (0 : Fin (H::B).length)
  have hSingle : IsSNCDivisor n [H]:=isSNCDivisor_of_sublist hE (by simp)
  have hNZ : ∀x∈N,DivisorExponentAlong.IsNonzeroAlongAt N Q.ideal x:=fun _ hx=>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hSingle hDense hx
  have hDom : IsInvDomain (n+1) Q:=⟨hw,(by
    intro x hx
    obtain ⟨k,hk⟩:=hN.2 x hx
    exact ⟨k,hk.1.trans (Nat.le_succ n),hk⟩),le_rfl,hNZ⟩
  have hCos : Q.cosupp=N∩H:=SmoothCentreLocus.cosupport_vanishingIdeal_one hH.1
  have hK : IsCompact Q.cosupp:=by rw [hCos];exact hComp.inter_right hH.1
  obtain ⟨Y,T,_hCan,hRes⟩:=exists_isGeoResolution_isCanonical_of_isCompact (invFamily hn (n+1)) hDom hK
  obtain ⟨hFull,hEq⟩:=actual_single_old_history hn hN hE hTrans T hRes.1
  have hwT:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hRes.1
  have hwFull:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong (ambient_wellformed hE) T hFull
  have hSNC : IsSNCDivisor n (strictAlong T H::(geoTransformAlong Q T).E):=by
    rw [←full_boundary_cons N H B T]
    exact hwFull.isSNCDivisor
  have hHt : IsClosedSubmanifold n (strictAlong T H):=MonomialPart.isClosedSubmanifold_get hn hSNC (0 : Fin (strictAlong T H::(geoTransformAlong Q T).E).length)
  have hCosT : (geoTransformAlong Q T).cosupp=(geoTransformAlong Q T).N∩strictAlong T H:=
    hEq.cosupp_eq.trans (SmoothCentreLocus.cosupport_vanishingIdeal_one hHt.1)
  have hNid : (geoTransformAlong Q T).N=strictAlong T N:=N_geoTransformAlong Q T
  have hErase : strictAlong T N∩strictAlong T H=∅:=by
    rw [←hNid,←hCosT]
    exact hRes.2
  have hOver : CentresOver (N∩H) T:=by
    rw [←hCos]
    exact centresOver_cosupp Q hN hw.isCoherent T hRes.1
  have hSeq:= (isAdmissibleBlowupSequence_proj (geometricTemplate (univ : Set X) (H::B)) (N∩H) T hFull hOver).mono hFoot
  have hTr : IsTransverse n (strictAlong T N) (geoTransformAlong Q T).E:=by rw [←hNid];exact hwT.isTransverse
  refine ⟨Y,T,hRes.1,hFull,hOver,hSeq,isProperMap_of_isBlowupSequence hSeq.isBlowupSequence,
    HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hSeq,?_,hwFull.isSNCDivisor,hTr,hErase,?_⟩
  · rw [←hNid];exact hwT.isClosedSubmanifold_N
  · rw [full_boundary_cons N H B T]
    exact full_normal_crossings_of_disjoint hTr (Set.disjoint_iff_inter_eq_empty.mpr hErase)

end
end Hironaka.HironakaActualSingleOldBoundaryCleanup
