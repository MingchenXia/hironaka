import Hironaka.Resolution.HironakaActualNativeSectionPositiveMask
import Hironaka.Resolution.HironakaActualNativeSectionCoefficientRecords
import Hironaka.Invariant.StepOneValueMasked
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace

/-! Entire ORIGINAL positive lower records at every actual native prefix.
The comparison map is the literal inclusion between the original masks.
The original bar record, original-member selection and every retained
ordered old/born boundary position are derived from actual geometry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionPositiveLowerRecords
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace NormalCrossings NormalCrossingsComparison StepOneValue StepOneValueMasked
  InvDomainMemberRestriction InvDomainRebase HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionInitialBar
  HironakaActualNativeSectionStepOneHistory HironakaActualNativeSectionPositiveMask
  HironakaActualNativeSectionCoefficientRecords HironakaActualOpenZeroSectionDifferentials
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
variable {n : ℕ}

/-- The unchanged original adjoining-normal record supported on its zero plane. -/
abbrev sourceRecord (U : Opens (ComplexModel n)) (A : Set U) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U)) (d : ℕ) :
    MarkedIdeal (n+1) (CMfd.of (n:=n+1) (productOpen U)) :=
  ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩

abbrev nativeRecord (U : Opens (ComplexModel n)) (A : Set U) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U)) (d : ℕ) :=
  nativePullback (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)
    (sourceRecord U A E J d)

private theorem zeroPlane_closed (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n:=n) (M:=U))).1


private theorem retained_boundary_sublist {X : CMfd.{0} n}
    (E E' : List (Set X)) (hsub : E'.Sublist E) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),(boundary E' T).Sublist (boundary E T)
  | _,.refl => hsub
  | _,.step T C π _hπ =>
    (List.Sublist.map (BlowupStrictSubmanifold.geoStrictTransform π C)
      (retained_boundary_sublist E E' hsub T)).append (List.Sublist.refl _)

/-- Retaining the exact initial boundary sublist changes no actual centre,
blowup, native strict subset or map. Every subsequently born slot remains. -/
theorem Lift.forget_boundary {k : ℕ} {X : CMfd.{0} n} {hk : k≤n}
    {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    {E E' : List (Set X)} {Y : CMfd.{0} n} {T : BlowupTower X Y}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW E T V hVc hV Q) (hsub : E'.Sublist E) :
    Lift hk W hWc hW E' T V hVc hV Q := by
  induction h with
  | refl => exact Lift.refl
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    exact Lift.step ih D hD hint π hπ
      (hasNormalCrossings_of_forall_mem hNC (retained_boundary_sublist E E' hsub T).subset)

section Original
variable (U : Opens (ComplexModel n)) (A : Set U) (hA : IsClosedSubmanifold n A)
  (E : List (Set U)) (hE : IsSNCDivisor n E)
  (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ)
  {Y : CMfd.{0} (n+1)} {T : BlowupTower (CMfd.of (n:=n+1) (productOpen U)) Y}
  {V : Set Y} {hVc : IsClosed V} {hV : ∀y∈V,RegularAtDim (n:=n+1) V y n}
  {Q : BlowupTower (nativeManifold (Y:=CMfd.of (n:=n+1) (productOpen U))
      (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
    (nativeManifold (Nat.le_succ n) V hV)}
  (h : Lift (Nat.le_succ n) (zeroPlane U) (zeroPlane_closed U) (zeroPlane_regular U)
    (E.map (projection U ⁻¹' ·)) T V hVc hV Q)

include hA hE hJ h

/-- Literal inclusion between the SAME original positive masks. -/
def positiveMaskSection (p : nativeManifold (Nat.le_succ n) V hV) :
    maskA (nativeRecord U A E J d) Q p → maskA (sourceRecord U A E J d) T p.val :=
  fun q => ⟨q.val.val,by
    have hm : (Subtype.val : V→Y) ⁻¹' (maskA (sourceRecord U A E J d) T p.val : Set Y)=
        (maskA (nativeRecord U A E J d) Q p : Set (nativeManifold (Nat.le_succ n) V hV)):=
      actual_section_maskA U A hA E hE J hJ d h p
    have hq : q.val∈(Subtype.val : V→Y) ⁻¹' (maskA (sourceRecord U A E J d) T p.val : Set Y):=by
      rw [hm]
      exact q.property
    exact hq⟩

theorem positiveMaskSection_contMDiff (p : nativeManifold (Nat.le_succ n) V hV) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞
      (positiveMaskSection (U:=U) (A:=A) (hA:=hA) (E:=E) (hE:=hE) (J:=J) (hJ:=hJ) (d:=d) (h:=h) p) := by
  let := chartedSpace (Nat.le_succ n) hV
  have := isComplexManifold_chartedSpace (Nat.le_succ n) hV
  apply (ContMDiff.subtypeVal_comp_iff (maskA (sourceRecord U A E J d) T p.val) _).mp
  exact (contMDiff_val (Nat.le_succ n) hV).comp contMDiff_subtype_val

private theorem current_selected_record (p : nativeManifold (Nat.le_succ n) V hV) :
    nativePullback (Nat.le_succ n) V hV
      (memberRestrict (geoTransformAlong (barMarked (sourceRecord U A E J d)) T)
        (membersThrough (geoTransformAlong (barMarked (sourceRecord U A E J d)) T).E
          (origMembers (sourceRecord U A E J d) T) p.val))=
      memberRestrict (geoTransformAlong (barMarked (nativeRecord U A E J d)) Q)
        (membersThrough (geoTransformAlong (barMarked (nativeRecord U A E J d)) Q).E
          (origMembers (nativeRecord U A E J d) Q) p) := by
  let M := sourceRecord U A E J d
  let B := nativeRecord U A E J d
  let MT := geoTransformAlong (barMarked M) T
  obtain ⟨hRec,hOrig,_hLS,_hReg,_hRun⟩:=
    actual_section_step_one_chronology U A hA E hE J hJ d h
  have hMN : M.N⊆zeroPlane U:=fun _ hx=>⟨mem_univ _,hx.2⟩
  have hE' := HironakaActualSectionBoundaryGeometry.isSNCDivisor_preimage_projection (U:=U) E hE
  have hTrans := HironakaActualSectionBoundaryGeometry.isTransverse_liftedCarrier (U:=U) (univ : Set U) E
    (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE)
  obtain ⟨hEcur,hTcur⟩:=h.geometry (Nat.zero_lt_succ n) hE' hTrans
  have hEN : MT.E=boundary (E.map (projection U ⁻¹' ·)) T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=barMarked M)
      (𝔫:=⟨univ,E.map (projection U ⁻¹' ·),IdealWeightPowers.unitIdeal (n+1) _,1⟩) rfl T
  rw [←hEN] at hEcur hTcur
  have hMem := nativePullback_memberRestrict_membersThrough (Nat.le_succ n) hV
    (Nat.zero_lt_succ n) MT (Lift.current_carrier_subset h (barMarked M) hMN)
    (HironakaActualRawRecordPullbacks.holomorphic_geoTransformAlong (barMarked M)
      (fun _ _ hg=>hg.1) T) hEcur hTcur (origMembers M T)
    (fun _ hH=>List.mem_of_mem_take hH) p
  rw [←hRec,hOrig] at hMem
  exact hMem

/-- Entire ORIGINAL lowerMarkedM at every actual original positive prefix.
No current member, mask or coefficient comparison is an input. -/
theorem actual_section_lowerMarkedM_succ (s : ℕ)
    (p : nativeManifold (Nat.le_succ n) V hV) :
    markedPullback (m:=n) (positiveMaskSection (U:=U) (A:=A) (hA:=hA) (E:=E) (hE:=hE) (J:=J) (hJ:=hJ) (d:=d) (h:=h) p)
      (lowerMarkedM (sourceRecord U A E J d) (s+1) T p.val)=
      lowerMarkedM (nativeRecord U A E J d) (s+1) Q p := by
  let := chartedSpace (Nat.le_succ n) hV
  have := isComplexManifold_chartedSpace (Nat.le_succ n) hV
  let M := sourceRecord U A E J d
  let B := nativeRecord U A E J d
  let OA := maskA M T p.val
  let OB := maskA B Q p
  let LA := memberRestrict (geoTransformAlong (barMarked M) T)
    (membersThrough (geoTransformAlong (barMarked M) T).E (origMembers M T) p.val)
  let LB := memberRestrict (geoTransformAlong (barMarked B) Q)
    (membersThrough (geoTransformAlong (barMarked B) Q).E (origMembers B Q) p)
  let σ := positiveMaskSection (U:=U) (A:=A) (hA:=hA) (E:=E) (hE:=hE) (J:=J) (hJ:=hJ) (d:=d) (h:=h) p
  have hσ := positiveMaskSection_contMDiff U A hA E hE J hJ d h p
  have hHol : ∀x g,LA.ideal.mem x g → HolomorphicAt (n+1) g x:=fun _ _ hg=>hg.1
  have hDict : nativePullback (Nat.le_succ n) V hV LA=LB:=
    current_selected_record U A hA E hE J hJ d h p
  have hSquare : markedPullback (m:=n) σ
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : OA→Y) LA)=
      MarkedIdealBiholomorphism.MarkedIdeal.pullback
        (Subtype.val : OB→nativeManifold (Nat.le_succ n) V hV)
        (nativePullback (Nat.le_succ n) V hV LA) := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · change (LA.E.map ((Subtype.val : OA→Y) ⁻¹' ·)).map (σ ⁻¹' ·)=
        (LA.E.map ((Subtype.val : V→Y) ⁻¹' ·)).map
          ((Subtype.val : OB→nativeManifold (Nat.le_succ n) V hV) ⁻¹' ·)
      simp only [List.map_map]
      rfl
    · change GermIdeal.pullback (m:=n) σ
          (GermIdeal.pullback (m:=n+1) (Subtype.val : OA→Y) LA.ideal)=
        GermIdeal.pullback (m:=n) (Subtype.val : OB→nativeManifold (Nat.le_succ n) V hV)
          (GermIdeal.pullback (m:=n) (Subtype.val : V→Y) LA.ideal)
      rw [←whole_pullback_comp contMDiff_subtype_val hσ LA.ideal hHol,
        ←whole_pullback_comp (contMDiff_val (Nat.le_succ n) hV) contMDiff_subtype_val LA.ideal hHol]
      rfl
    · rfl
  change markedPullback (m:=n) σ
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : OA→Y) LA)=
    MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : OB→nativeManifold (Nat.le_succ n) V hV) LB
  rw [hSquare,hDict]

section Tail
variable {Z : CMfd.{0} (n+1)} {S : BlowupTower Y Z}
  {V' : Set Z} {hV'c : IsClosed V'} {hV' : ∀z∈V',RegularAtDim (n:=n+1) V' z n}
  {R : BlowupTower (nativeManifold (Nat.le_succ n) V hV)
    (nativeManifold (Nat.le_succ n) V' hV')}
  (hTail : Lift (Nat.le_succ n) V hVc hV (boundary (E.map (projection U ⁻¹' ·)) T)
    S V' hV'c hV' R)

include hTail

/-- Literal endpoint inclusion on the two ORIGINAL restricted tails. Its
ambient mask membership follows from the SAME actual tail projection square. -/
def positiveEndpointSection (p : nativeManifold (Nat.le_succ n) V hV) :
    openPreimage R (maskA (nativeRecord U A E J d) Q p) →
      openPreimage S (maskA (sourceRecord U A E J d) T p.val) := fun z=>
  ⟨z.val.val,by
    have hm : (Subtype.val : V→Y) ⁻¹' (maskA (sourceRecord U A E J d) T p.val : Set Y)=
        (maskA (nativeRecord U A E J d) Q p : Set (nativeManifold (Nat.le_succ n) V hV)):=
      actual_section_maskA U A hA E hE J hJ d h p
    have hz : R.proj z.val∈(Subtype.val : V→Y) ⁻¹' (maskA (sourceRecord U A E J d) T p.val : Set Y):=by
      rw [hm]
      exact z.property
    change S.proj z.val.val∈maskA (sourceRecord U A E J d) T p.val
    rw [hTail.square z.val]
    exact hz⟩

theorem positiveEndpointSection_contMDiff (p : nativeManifold (Nat.le_succ n) V hV) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞
      (positiveEndpointSection (U:=U) (A:=A) (hA:=hA) (E:=E) (hE:=hE)
        (J:=J) (hJ:=hJ) (d:=d) (h:=h) (hTail:=hTail) p) := by
  let := chartedSpace (Nat.le_succ n) hV'
  have := isComplexManifold_chartedSpace (Nat.le_succ n) hV'
  apply (ContMDiff.subtypeVal_comp_iff
    (openPreimage S (maskA (sourceRecord U A E J d) T p.val)) _).mp
  exact (contMDiff_val (Nat.le_succ n) hV').comp contMDiff_subtype_val

/-- ENTIRE transformed original positive lowerMarkedM on the SAME genuine
restricted tails. The selected old positions and every retained born slot
are derived, not replaced by a fresh boundary or a supplied record certificate. -/
theorem actual_section_lowerMarkedM_succ_tail (s : ℕ)
    (p : nativeManifold (Nat.le_succ n) V hV) :
    geoTransformAlong (lowerMarkedM (nativeRecord U A E J d) (s+1) Q p)
        (restrict (maskA (nativeRecord U A E J d) Q p) R)=
      markedPullback (m:=n)
        (positiveEndpointSection (U:=U) (A:=A) (hA:=hA) (E:=E) (hE:=hE)
          (J:=J) (hJ:=hJ) (d:=d) (h:=h) (hTail:=hTail) p)
        (geoTransformAlong (lowerMarkedM (sourceRecord U A E J d) (s+1) T p.val)
          (restrict (maskA (sourceRecord U A E J d) T p.val) S)) := by
  let := chartedSpace (Nat.le_succ n) hV
  have := isComplexManifold_chartedSpace (Nat.le_succ n) hV
  let := chartedSpace (Nat.le_succ n) hV'
  have := isComplexManifold_chartedSpace (Nat.le_succ n) hV'
  let M := sourceRecord U A E J d
  let B := nativeRecord U A E J d
  let MT := geoTransformAlong (barMarked M) T
  let OA := maskA M T p.val
  let OB := maskA B Q p
  let LA := memberRestrict MT (membersThrough MT.E (origMembers M T) p.val)
  let LB := memberRestrict (geoTransformAlong (barMarked B) Q)
    (membersThrough (geoTransformAlong (barMarked B) Q).E (origMembers B Q) p)
  let σ := positiveEndpointSection (U:=U) (A:=A) (hA:=hA) (E:=E) (hE:=hE)
    (J:=J) (hJ:=hJ) (d:=d) (h:=h) (hTail:=hTail) p
  have hσ := positiveEndpointSection_contMDiff U A hA E hE J hJ d h hTail p
  have hDict : nativePullback (Nat.le_succ n) V hV LA=LB:=
    current_selected_record U A hA E hE J hJ d h p
  have hMN : M.N⊆zeroPlane U:=fun _ hx=>⟨mem_univ _,hx.2⟩
  have hE' := HironakaActualSectionBoundaryGeometry.isSNCDivisor_preimage_projection (U:=U) E hE
  have hTrans := HironakaActualSectionBoundaryGeometry.isTransverse_liftedCarrier (U:=U) (univ : Set U) E
    (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE)
  obtain ⟨hEcur,hTcur⟩:=h.geometry (Nat.zero_lt_succ n) hE' hTrans
  have hEN : MT.E=boundary (E.map (projection U ⁻¹' ·)) T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=barMarked M)
      (𝔫:=⟨univ,E.map (projection U ⁻¹' ·),IdealWeightPowers.unitIdeal (n+1) _,1⟩) rfl T
  rw [←hEN] at hEcur hTcur
  have hSub : LA.E.Sublist MT.E:=by
    change (memberRestrict MT (membersThrough MT.E (origMembers M T) p.val)).E.Sublist MT.E
    rw [memberRestrict_membersThrough_E]
    exact List.filter_sublist
  have hSmall := Lift.forget_boundary hTail (E':=LA.E) (by rw [←hEN];exact hSub)
  have hLN : LA.N⊆V:=fun _ hx=>
    Lift.current_carrier_subset h (barMarked M) hMN hx.1
  have hLAhol : ∀x g,LA.ideal.mem x g → HolomorphicAt (n+1) g x:=fun _ _ hg=>hg.1
  have hLBhol : ∀x g,LB.ideal.mem x g → HolomorphicAt n g x:=fun _ _ hg=>hg.1
  have hRecords := hSmall.whole_records (Nat.zero_lt_succ n)
    (isSNCDivisor_of_sublist hEcur hSub)
    (isTransverse_of_forall_mem hTcur hSub.subset) LA rfl hLN hLAhol
  rw [hDict] at hRecords
  change geoTransformAlong
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback
        (Subtype.val : OB→nativeManifold (Nat.le_succ n) V hV) LB) (restrict OB R)=
    markedPullback (m:=n) σ
      (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : OA→Y) LA)
        (restrict OA S))
  rw [HironakaActualRawRecordPullbacks.geoTransformAlong_restrict_of_hhol LB hLBhol OB R,
    HironakaActualRawRecordPullbacks.geoTransformAlong_restrict_of_hhol LA hLAhol OA S,hRecords]
  have hGhol := HironakaActualRawRecordPullbacks.holomorphic_geoTransformAlong LA hLAhol S
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · change (((geoTransformAlong LA S).E.map ((Subtype.val : V'→Z) ⁻¹' ·)).map
      ((Subtype.val : openPreimage R OB→nativeManifold (Nat.le_succ n) V' hV') ⁻¹' ·))=
      ((geoTransformAlong LA S).E.map ((Subtype.val : openPreimage S OA→Z) ⁻¹' ·)).map (σ ⁻¹' ·)
    simp only [List.map_map]
    rfl
  · change GermIdeal.pullback (m:=n)
        (Subtype.val : openPreimage R OB→nativeManifold (Nat.le_succ n) V' hV')
        (GermIdeal.pullback (m:=n) (Subtype.val : V'→Z) (geoTransformAlong LA S).ideal)=
      GermIdeal.pullback (m:=n) σ
        (GermIdeal.pullback (m:=n+1) (Subtype.val : openPreimage S OA→Z) (geoTransformAlong LA S).ideal)
    rw [←whole_pullback_comp (contMDiff_val (Nat.le_succ n) hV') contMDiff_subtype_val
        (geoTransformAlong LA S).ideal hGhol,
      ←whole_pullback_comp contMDiff_subtype_val hσ (geoTransformAlong LA S).ideal hGhol]
    rfl
  · rfl

end Tail

end Original
end
end Hironaka.HironakaActualNativeSectionPositiveLowerRecords
