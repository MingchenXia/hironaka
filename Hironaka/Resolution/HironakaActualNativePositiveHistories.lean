import Hironaka.Resolution.HironakaActualNativeInvariantDomain
import Hironaka.Resolution.HironakaActualNativeSectionStepOneHistory

/-! ORIGINAL positive masks and full lower records/tails for ANY supported
actual native embedding. Generic initial bar naturality is produced from
source geometry, never supplied. Canonicality is a separate recursive goal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativePositiveHistories
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace NormalCrossings NormalCrossingsComparison StepOneValue StepOneValueMasked
  StepOneRegime InvDomainMemberRestriction InvDomainRebase
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionStepOneHistory HironakaActualNativeSectionPositiveMask
  HironakaActualNativeSectionCoefficientRecords HironakaActualNativeSectionPositiveLowerRecords
  HironakaActualRawRecordPullbacks HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceImageTrace RelativePrincipalizationSpan

section History
variable {n k : ℕ} {X : CMfd.{0} n} {hk : k≤n} {W : Set X} {hWc : IsClosed W}
  {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
  (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hMN : M.N⊆W) (hTrans : IsTransverse n W M.E)
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
  (h : Lift hk W hWc hW M.E T V hVc hV Q) (hn : 0<n)

include hM hMN hTrans h hn

/-- Every ORIGINAL generic chronology field, with the missing initial bar
naturality PRODUCED from the source carrier and ideal rather than supplied. -/
theorem original_step_one_chronology :
    let B:=nativePullback hk W hW M
    geoTransformAlong (barMarked B) Q=nativePullback hk V hV (geoTransformAlong (barMarked M) T) ∧
      (origMembers M T).map ((Subtype.val : V→Y) ⁻¹' ·)=origMembers B Q ∧
      (∀p : nativeManifold hk V hV,
        level M T p.val=level B Q p ∧ (IsSpecial M T p.val ↔ IsSpecial B Q p)) ∧
      (∀s (p : nativeManifold hk V hV),stepRegime M s T p.val ↔ stepRegime B s Q p) ∧
      (∀s (p : nativeManifold hk V hV),
        regimeRun (stepRegime M s) T p.val=regimeRun (stepRegime B s) Q p) := by
  have hBar:=nativePullback_barMarked hk hW M hMN
    (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isCoherent hg)
  exact ⟨native_original_bar_records h hn hM.isSNCDivisor hTrans M rfl hMN
      hM.isClosedSubmanifold_N hM.isCoherent hBar,
    native_original_member_prefix h hn hM.isSNCDivisor hTrans M rfl hMN
      hM.isClosedSubmanifold_N hM.isCoherent hBar,
    native_original_level_special h hn hM.isSNCDivisor hTrans M rfl hMN
      hM.isClosedSubmanifold_N hM.isCoherent hBar,
    native_original_step_regime h hn hM.isSNCDivisor hTrans M rfl hMN
      hM.isClosedSubmanifold_N hM.isCoherent hBar,
    native_original_step_regime_run h hn hM.isSNCDivisor hTrans M rfl hMN
      hM.isClosedSubmanifold_N hM.isCoherent hBar⟩

/-- The ORIGINAL positive masks agree under the literal native inclusion,
for arbitrary actual W; interior naturality is derived from actual support. -/
theorem original_positive_mask (p : nativeManifold hk V hV) :
    (Subtype.val : V→Y) ⁻¹' (maskA M T p.val : Set Y)=
      (maskA (nativePullback hk W hW M) Q p : Set (nativeManifold hk V hV)) := by
  let B:=nativePullback hk W hW M
  obtain ⟨_hRec,hOrig,hLS,_hReg,_hRun⟩:=original_step_one_chronology M hM hMN hTrans h hn
  let C : Set Y:={z | ∀H∈origMembers M T,z∈H → p.val∈H}
  let S : Set Y:={z | level M T z=level M T p.val ∧ IsSpecial M T z}
  have hSub : (geoTransformAlong (barMarked M) T).N⊆V:=
    Lift.current_carrier_subset h (barMarked M) hMN
  have hSS : S⊆V:=by
    intro z hz
    rcases hz.2 with hzero|hpos
    · exact hSub ((geoTransformAlong (barMarked M) T).cosupp_subset_N
        (CodimOneSupportAlong.codimOnePartAlong_subset hzero.2))
    · exact hSub ((geoTransformAlong (barMarked M) T).cosupp_subset_N hpos.2.1)
  have hC : IsOpen C:=by
    classical
    let A : Set (Set Y):={H | H∈origMembers M T ∧ p.val∉H}
    have hA : A.Finite:=(List.finite_toSet (origMembers M T)).subset (fun _ hh=>hh.1)
    have hEq : C=⋂H∈A,Hᶜ:=by
      ext z
      simp only [C,A,mem_ofPred_eq,mem_iInter,mem_compl_iff,and_imp]
      constructor
      · intro hz H hH hpH hzH;exact hpH (hz H hH hzH)
      · intro hz H hH hzH
        by_contra hpH
        exact hz H hH hpH hzH
    rw [hEq]
    exact hA.isOpen_biInter fun H hH=>(StepOneLowerDomain.isClosed_of_mem_origMembers M hM.isSNCDivisor.1 T H hH.1).isOpen_compl
  have hSC:=interior_supported_complement V S hSS
  have hPre : (Subtype.val : V→Y) ⁻¹' (C∩Sᶜ)=
      {z | (∀H∈origMembers B Q,z∈H → p∈H) ∧
        ¬(level B Q z=level B Q p ∧ IsSpecial B Q z)}:=by
    ext z
    change ((∀H∈origMembers M T,z.val∈H → p.val∈H) ∧
        ¬(level M T z.val=level M T p.val ∧ IsSpecial M T z.val)) ↔ _
    rw [←hOrig]
    simp only [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,mem_preimage]
    rw [(hLS z).1,(hLS p).1,(hLS z).2]
    rfl
  change (Subtype.val : V→Y) ⁻¹' interior (C∩Sᶜ)=_
  rw [interior_inter,hC.interior_eq,preimage_inter,hSC]
  rw [←(hC.preimage continuous_subtype_val).interior_eq,←interior_inter,←preimage_inter,hPre]
  rfl


/-- Literal inclusion between the two ORIGINAL positive masks on the SAME history. -/
def positiveMaskSection (p : nativeManifold hk V hV) :
    maskA (nativePullback hk W hW M) Q p → maskA M T p.val := fun q=>⟨q.val.val,by
      have hm:=original_positive_mask M hM hMN hTrans h hn p
      have hq : q.val∈(Subtype.val : V→Y) ⁻¹' (maskA M T p.val : Set Y):=by
        rw [hm]
        exact q.property
      exact hq⟩

theorem positiveMaskSection_contMDiff (p : nativeManifold hk V hV) :
    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞
      (positiveMaskSection M hM hMN hTrans h hn p) := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  apply (ContMDiff.subtypeVal_comp_iff (maskA M T p.val) _).mp
  exact (contMDiff_val hk hV).comp contMDiff_subtype_val

private theorem current_selected_record (p : nativeManifold hk V hV) :
    nativePullback hk V hV
      (memberRestrict (geoTransformAlong (barMarked M) T)
        (membersThrough (geoTransformAlong (barMarked M) T).E (origMembers M T) p.val))=
      memberRestrict (geoTransformAlong (barMarked (nativePullback hk W hW M)) Q)
        (membersThrough (geoTransformAlong (barMarked (nativePullback hk W hW M)) Q).E
          (origMembers (nativePullback hk W hW M) Q) p) := by
  let MT:=geoTransformAlong (barMarked M) T
  obtain ⟨hRec,hOrig,_hLS,_hReg,_hRun⟩:=original_step_one_chronology M hM hMN hTrans h hn
  obtain ⟨hEcur,hTcur⟩:=h.geometry hn hM.isSNCDivisor hTrans
  have hEN : MT.E=boundary M.E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=barMarked M) (𝔫:=⟨univ,M.E,IdealWeightPowers.unitIdeal n X,1⟩) rfl T
  rw [←hEN] at hEcur hTcur
  have hMem:=nativePullback_memberRestrict_membersThrough hk hV hn MT
    (Lift.current_carrier_subset h (barMarked M) hMN)
    (holomorphic_geoTransformAlong (barMarked M) (fun _ _ hg=>hg.1) T)
    hEcur hTcur (origMembers M T) (fun _ hH=>List.mem_of_mem_take hH) p
  rw [←hRec,hOrig] at hMem
  exact hMem

/-- ENTIRE ORIGINAL positive lowerMarkedM on arbitrary actual native embeddings.
The original member selection and literal masks are internally produced. -/
theorem original_positive_lower_record (s : ℕ) (p : nativeManifold hk V hV) :
    markedPullback (m:=k) (positiveMaskSection M hM hMN hTrans h hn p)
      (lowerMarkedM M (s+1) T p.val)=
      lowerMarkedM (nativePullback hk W hW M) (s+1) Q p := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let B:=nativePullback hk W hW M
  let OA:=maskA M T p.val
  let OB:=maskA B Q p
  let LA:=memberRestrict (geoTransformAlong (barMarked M) T)
    (membersThrough (geoTransformAlong (barMarked M) T).E (origMembers M T) p.val)
  let LB:=memberRestrict (geoTransformAlong (barMarked B) Q)
    (membersThrough (geoTransformAlong (barMarked B) Q).E (origMembers B Q) p)
  let σ:=positiveMaskSection M hM hMN hTrans h hn p
  have hσ:=positiveMaskSection_contMDiff M hM hMN hTrans h hn p
  have hHol : ∀x g,LA.ideal.mem x g → HolomorphicAt n g x:=fun _ _ hg=>hg.1
  have hDict : nativePullback hk V hV LA=LB:=current_selected_record M hM hMN hTrans h hn p
  have hSquare : markedPullback (m:=k) σ
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : OA→Y) LA)=
      MarkedIdealBiholomorphism.MarkedIdeal.pullback
        (Subtype.val : OB→nativeManifold hk V hV) (nativePullback hk V hV LA) := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · change (LA.E.map ((Subtype.val : OA→Y) ⁻¹' ·)).map (σ ⁻¹' ·)=
        (LA.E.map ((Subtype.val : V→Y) ⁻¹' ·)).map
          ((Subtype.val : OB→nativeManifold hk V hV) ⁻¹' ·)
      simp only [List.map_map]
      rfl
    · change GermIdeal.pullback (m:=k) σ
          (GermIdeal.pullback (m:=n) (Subtype.val : OA→Y) LA.ideal)=
        GermIdeal.pullback (m:=k) (Subtype.val : OB→nativeManifold hk V hV)
          (GermIdeal.pullback (m:=k) (Subtype.val : V→Y) LA.ideal)
      rw [←whole_pullback_comp contMDiff_subtype_val hσ LA.ideal hHol,
        ←whole_pullback_comp (contMDiff_val hk hV) contMDiff_subtype_val LA.ideal hHol]
      rfl
    · rfl
  change markedPullback (m:=k) σ
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : OA→Y) LA)=
    MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : OB→nativeManifold hk V hV) LB
  rw [hSquare,hDict]


section Tail
variable {Z : CMfd.{0} n} {S : BlowupTower Y Z}
  {V' : Set Z} {hV'c : IsClosed V'} {hV' : ∀z∈V',RegularAtDim (n:=n) V' z k}
  {R : BlowupTower (nativeManifold hk V hV) (nativeManifold hk V' hV')}
  (hTail : Lift hk V hVc hV (boundary M.E T) S V' hV'c hV' R)
include hTail

/-- Actual endpoint inclusion on the literal ORIGINAL restricted tails. -/
def positiveEndpointSection (p : nativeManifold hk V hV) :
    openPreimage R (maskA (nativePullback hk W hW M) Q p) → openPreimage S (maskA M T p.val) := fun z=>⟨z.val.val,by
      have hm:=original_positive_mask M hM hMN hTrans h hn p
      have hz : R.proj z.val∈(Subtype.val : V→Y) ⁻¹' (maskA M T p.val : Set Y):=by
        rw [hm]
        exact z.property
      change S.proj z.val.val∈maskA M T p.val
      rw [hTail.square z.val]
      exact hz⟩

theorem positiveEndpointSection_contMDiff (p : nativeManifold hk V hV) :
    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞
      (positiveEndpointSection M hM hMN hTrans h hn hTail p) := by
  let := chartedSpace hk hV'
  have := isComplexManifold_chartedSpace hk hV'
  apply (ContMDiff.subtypeVal_comp_iff (openPreimage S (maskA M T p.val)) _).mp
  exact (contMDiff_val hk hV').comp contMDiff_subtype_val

/-- ENTIRE original positive lower records on SAME genuine restricted native
and ambient tails. All selected original and subsequently born slots remain. -/
theorem original_positive_lower_tail (s : ℕ) (p : nativeManifold hk V hV) :
    geoTransformAlong (lowerMarkedM (nativePullback hk W hW M) (s+1) Q p)
        (restrict (maskA (nativePullback hk W hW M) Q p) R)=
      markedPullback (m:=k) (positiveEndpointSection M hM hMN hTrans h hn hTail p)
        (geoTransformAlong (lowerMarkedM M (s+1) T p.val) (restrict (maskA M T p.val) S)) := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let := chartedSpace hk hV'
  have := isComplexManifold_chartedSpace hk hV'
  let B:=nativePullback hk W hW M
  let MT:=geoTransformAlong (barMarked M) T
  let OA:=maskA M T p.val
  let OB:=maskA B Q p
  let LA:=memberRestrict MT (membersThrough MT.E (origMembers M T) p.val)
  let LB:=memberRestrict (geoTransformAlong (barMarked B) Q)
    (membersThrough (geoTransformAlong (barMarked B) Q).E (origMembers B Q) p)
  let σ:=positiveEndpointSection M hM hMN hTrans h hn hTail p
  have hσ:=positiveEndpointSection_contMDiff M hM hMN hTrans h hn hTail p
  have hDict : nativePullback hk V hV LA=LB:=current_selected_record M hM hMN hTrans h hn p
  obtain ⟨hEcur,hTcur⟩:=h.geometry hn hM.isSNCDivisor hTrans
  have hEN : MT.E=boundary M.E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=barMarked M) (𝔫:=⟨univ,M.E,IdealWeightPowers.unitIdeal n X,1⟩) rfl T
  rw [←hEN] at hEcur hTcur
  have hSub : LA.E.Sublist MT.E:=by
    change (memberRestrict MT (membersThrough MT.E (origMembers M T) p.val)).E.Sublist MT.E
    rw [memberRestrict_membersThrough_E]
    exact List.filter_sublist
  have hSmall:=Lift.forget_boundary hTail (E':=LA.E) (by rw [←hEN];exact hSub)
  have hLN : LA.N⊆V:=fun _ hx=>Lift.current_carrier_subset h (barMarked M) hMN hx.1
  have hLAhol : ∀x g,LA.ideal.mem x g → HolomorphicAt n g x:=fun _ _ hg=>hg.1
  have hLBhol : ∀x g,LB.ideal.mem x g → HolomorphicAt k g x:=fun _ _ hg=>hg.1
  have hRecords:=hSmall.whole_records hn (isSNCDivisor_of_sublist hEcur hSub)
    (isTransverse_of_forall_mem hTcur hSub.subset) LA rfl hLN hLAhol
  rw [hDict] at hRecords
  change geoTransformAlong
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : OB→nativeManifold hk V hV) LB) (restrict OB R)=
    markedPullback (m:=k) σ
      (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : OA→Y) LA) (restrict OA S))
  rw [geoTransformAlong_restrict_of_hhol LB hLBhol OB R,
    geoTransformAlong_restrict_of_hhol LA hLAhol OA S,hRecords]
  have hGhol:=holomorphic_geoTransformAlong LA hLAhol S
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · change (((geoTransformAlong LA S).E.map ((Subtype.val : V'→Z) ⁻¹' ·)).map
      ((Subtype.val : openPreimage R OB→nativeManifold hk V' hV') ⁻¹' ·))=
      ((geoTransformAlong LA S).E.map ((Subtype.val : openPreimage S OA→Z) ⁻¹' ·)).map (σ ⁻¹' ·)
    simp only [List.map_map]
    rfl
  · change GermIdeal.pullback (m:=k) (Subtype.val : openPreimage R OB→nativeManifold hk V' hV')
        (GermIdeal.pullback (m:=k) (Subtype.val : V'→Z) (geoTransformAlong LA S).ideal)=
      GermIdeal.pullback (m:=k) σ
        (GermIdeal.pullback (m:=n) (Subtype.val : openPreimage S OA→Z) (geoTransformAlong LA S).ideal)
    rw [←whole_pullback_comp (contMDiff_val hk hV') contMDiff_subtype_val (geoTransformAlong LA S).ideal hGhol,
      ←whole_pullback_comp contMDiff_subtype_val hσ (geoTransformAlong LA S).ideal hGhol]
    rfl
  · rfl

end Tail

end History

end
end Hironaka.HironakaActualNativePositiveHistories
