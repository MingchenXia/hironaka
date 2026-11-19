import Hironaka.Resolution.HironakaG4MonomialFamilyInvariant
import Hironaka.Resolution.HironakaG4ProtectedResidualEndpoint
import Hironaka.Resolution.HironakaG4MixedOldResidualStep
import Hironaka.Resolution.HironakaG4EquimultipleRelativeOrder
import Hironaka.Resolution.HironakaG4SmoothSubcarrierResidualStep
import Hironaka.Resolution.HironakaG4IncidentOldBornStratumCentre
import Hironaka.Invariant.MonomialCaseAlong
import Hironaka.Resolution.HironakaG4PreparedCentreCoordinates
import Hironaka.Resolution.FactorizationFromResolution
import Hironaka.Blowup.NormalCrossingsInvariance
import Hironaka.Invariant.MonomialPartEtale

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4ProcessedSupportHighCountStep
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualFiniteChronologicalHistory
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaSharpOriginalMultiBoundaryBadLocus NormalCrossings
  RelativePrincipalizationSpan RestrictedIdealExtension DivisorExponentAlong
  MonomialPartAlong GermIdealOrder MarkedIdeals MarkedIdeals.MarkedIdeal
  MonomialCaseAlong MonomialCase MonomialInvariant InvertibleIdealQuotient
  HironakaSharpNormalCrossingsOpenLocus BlowupFlatCoordinates MarkedIdealOperationsAlong
variable {n : ℕ} {X Y Z : CMfd.{u} n}

private def finiteSum {ι : Type*} (D : ι → GermIdeal n X) (P : Finset ι) : GermIdeal n X :=
  ⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩

private theorem le_finiteSum {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) {P : Finset ι} {i : ι} (hi : i ∈ P) :
    (D i).Le (finiteSum D P) := by
  intro x g hg
  change IsInSpanAt (n := n) (fun f => ∃ j ∈ P,(D j).mem x f) x g
  exact isInSpanAt_self ⟨i,hi,hg⟩ (GermIdeal.IsCoherent.holomorphicAt_mem (hc i) hg)

private theorem coherent_finiteSum {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (P : Finset ι) : (finiteSum D P).IsCoherent := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro x
    refine ⟨univ,isOpen_univ,mem_univ x,0,Fin.elim0,fun i => i.elim0,?_⟩
    intro y _hy g
    change IsInSpanAt (n := n) (fun f => ∃ i ∈ (∅ : Finset ι),(D i).mem y f) y g ↔ _
    constructor
    · exact IsInSpanAt.mono (fun _ ⟨i,hi,_⟩ => (Finset.notMem_empty i hi).elim)
    · exact IsInSpanAt.mono (fun _ ⟨i,_⟩ => i.elim0)
  | insert i P _hi ih =>
    have heq : finiteSum D (insert i P)=sumIdeal (D i) (finiteSum D P) := by
      ext x g
      change IsInSpanAt (n := n) (fun f => ∃ j ∈ insert i P,(D j).mem x f) x g ↔
        IsInSpanAt (n := n) (fun f => (D i).mem x f ∨ (finiteSum D P).mem x f) x g
      constructor
      · apply IsInSpanAt.mono
        rintro f ⟨j,hj,hf⟩
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Or.inl hf
        · exact Or.inr (le_finiteSum D hc hj x f hf)
      · apply IsInSpanAt.trans
        rintro f (hf | hf)
        · exact le_finiteSum D hc (Finset.mem_insert_self i P) x f hf
        · change IsInSpanAt (n := n) (fun f => ∃ j ∈ P,(D j).mem x f) x f at hf
          exact hf.mono (fun _ ⟨j,hj,hg⟩ => ⟨j,Finset.mem_insert_of_mem hj,hg⟩)
    rw [heq]
    exact isCoherent_sumIdeal (hc i) ih

private theorem cosupport_finiteSum_one {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (P : Finset ι) (N : Set X) (x : X) :
    x ∈ cosupport n N (finiteSum D P) 1 ↔
      x ∈ N ∧ ∀ i ∈ P,x ∈ cosupport n N (D i) 1 := by
  have hrow (i : ι) : x ∈ cosupport n N (D i) 1 ↔
      x ∈ N ∧ ∀ g,(D i).mem x g → g x=0 := by
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hc i) hg)]
    rfl
  rw [cosupport_one (𝔞 := finiteSum D P) (fun _ _ hg => hg.1)]
  constructor
  · rintro ⟨hxN,hx⟩
    exact ⟨hxN,fun i hi => (hrow i).mpr ⟨hxN,fun g hg =>
      hx g (le_finiteSum D hc hi x g hg)⟩⟩
  · rintro ⟨hxN,hx⟩
    refine ⟨hxN,?_⟩
    intro g hg
    obtain ⟨_hg,K,s,a,hs,_ha,heq⟩ := hg
    rw [heq.self_of_nhds]
    apply Finset.sum_eq_zero
    intro k _hk
    obtain ⟨i,hi,hsi⟩ := hs k
    rw [((hrow i).mp (hx i hi)).2 _ hsi,mul_zero]

private theorem exponent_zero_of_not_mem {N H : Set X} {I : GermIdeal n X}
    (hc : IsClosed (N ∩ H)) {x : X} (hx : x ∉ H) :
    divExpAlong n N I H x=0 := by
  have hnot : ¬∃ e,¬IsDivNearAlong n N I H (e+1) x := by
    rintro ⟨e,he⟩
    exact he (isDivNearAlong_of_notMem hc (fun h => hx h.2) (e+1))
  unfold divExpAlong
  rw [dif_neg hnot]

private theorem row_cosupport_iff (hn : 0<n) {N : Set X}
    {B : List (Set X)} {D : GermIdeal n X} (hN : IsClosedSubmanifold n N)
    (hB : IsSNCDivisor n B) (hTr : IsTransverse n N B) (hc : D.IsCoherent)
    (hne : ∀ y ∈ N,IsNonzeroAlongAt N D y) (hm : IsMonomialAlong n N D B)
    {x : X} (hx : x ∈ N) :
    x ∈ cosupport n N D 1 ↔ 0<∑ j : Fin B.length,divExpAlong n N D (B.get j) x := by
  rw [mem_cosupport_iff_of_isMonomialAlong hn hN hB hTr hc hne hm 1 hx]
  have hsum : (∑ i ∈ memberIdx B x,expDataAlong n N D B x i)=
      ∑ j : Fin B.length,divExpAlong n N D (B.get j) x := by
    rw [memberIdx,Finset.sum_map]
    simp only [Fin.valEmbedding_apply,expDataAlong,Fin.eta]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [dif_pos j.isLt]
    change (if x ∈ B.get j then divExpAlong n N D (B.get j) x else 0)=
      divExpAlong n N D (B.get j) x
    by_cases hxj : x ∈ B.get j
    · simp only [if_pos hxj]
    · simp only [if_neg hxj]
      exact (exponent_zero_of_not_mem (hN.1.inter (hB.1 _ (List.get_mem B j))) hxj).symm
  rw [hsum]
  omega


private theorem finiteSum_domain_and_cosupport {ι : Type*} [Fintype ι]
    (hn : 0<n) {N : Set X} {B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hB : IsSNCDivisor n B) (hTr : IsTransverse n N B)
    (D : ι → GermIdeal n X) (hc : ∀ i,(D i).IsCoherent)
    (hne : ∀ i,∀ x ∈ N,IsNonzeroAlongAt N (D i) x)
    (hm : ∀ i,IsMonomialAlong n N (D i) B)
    (P : Finset ι) (hP : P.Nonempty) :
    let M : MarkedIdeal n X := ⟨N,B,finiteSum D P,1⟩
    ResolutionInvariantSpec.IsInvDomain (n+1) M ∧
      ∀ x,x ∈ M.cosupp ↔ x ∈ N ∧ P ⊆ properRows
        (fun i j => divExpAlong n N (D i) (B.get j) x) := by
  let I := finiteSum D P
  let M : MarkedIdeal n X := ⟨N,B,I,1⟩
  have hcI : I.IsCoherent := coherent_finiteSum D hc P
  have hnzI : ∀ x ∈ N,IsNonzeroAlongAt N I x := by
    obtain ⟨i0,hi0⟩ := hP
    intro x hx
    obtain ⟨g,hg,hfreq⟩ := hne i0 x hx
    exact ⟨g,le_finiteSum D hc hi0 x g hg,hfreq⟩
  refine ⟨⟨⟨hN,hcI,hB,hTr⟩,?_,Nat.le_refl 1,hnzI⟩,?_⟩
  · intro x hx
    obtain ⟨k,hk⟩ := hN.2 x hx
    exact ⟨k,hk.1.trans (Nat.le_succ n),hk⟩
  · intro x
    change x ∈ cosupport n N (finiteSum D P) 1 ↔ _
    rw [cosupport_finiteSum_one D hc P N x]
    constructor
    · rintro ⟨hx,hall⟩
      refine ⟨hx,fun i hi => ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (row_cosupport_iff hn hN hB hTr (hc i) (hne i) (hm i) hx).mp (hall i hi)⟩
    · rintro ⟨hx,hall⟩
      refine ⟨hx,fun i hi => ?_⟩
      exact (row_cosupport_iff hn hN hB hTr (hc i) (hne i) (hm i) hx).mpr
        (Finset.mem_filter.mp (hall hi)).2

/-- Public name for the existing literal finite local-span ideal. -/
def nativeFiniteSum {ι : Type*} (D : ι → GermIdeal n X) (P : Finset ι) : GermIdeal n X :=
  finiteSum D P

/-- Public factor of the existing finite-SUM domain and actual cosupport dictionary. -/
theorem nativeFiniteSum_domain_and_cosupport {ι : Type*} [Fintype ι]
    (hn : 0<n) {N : Set X} {B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hB : IsSNCDivisor n B) (hTr : IsTransverse n N B)
    (D : ι → GermIdeal n X) (hc : ∀ i,(D i).IsCoherent)
    (hne : ∀ i,∀ x ∈ N,IsNonzeroAlongAt N (D i) x)
    (hm : ∀ i,IsMonomialAlong n N (D i) B)
    (P : Finset ι) (hP : P.Nonempty) :
    let M : MarkedIdeal n X := ⟨N,B,nativeFiniteSum D P,1⟩
    ResolutionInvariantSpec.IsInvDomain (n+1) M ∧
      ∀ x,x ∈ M.cosupp ↔ x ∈ N ∧ P ⊆ properRows
        (fun i j => divExpAlong n N (D i) (B.get j) x) :=
  finiteSum_domain_and_cosupport hn hN hB hTr D hc hne hm P hP

private theorem active_row_sharp_bad (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hFull : IsSNCDivisor n (old ++ born))
    (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (i : Fin old.length) {x : X} (hx : x ∈ N)
    (hNot : ¬(oldMonomialPart N old born i).mem x (1 : X → ℂ)) :
    x ∈ originalSharpBadLocus (n := n) N (old ++ born) := by
  let oi : Fin (old ++ born).length := ⟨i.val,by simp only [List.length_append];omega⟩
  let bornIndex : Fin born.length → Fin (old ++ born).length :=
    fun j => ⟨old.length+j.val,by simp only [List.length_append];omega⟩
  let L : List (Fin (old ++ born).length) := List.ofFn bornIndex
  have hOld : (old ++ born).get oi=old.get i := by simp [oi,List.get_eq_getElem]
  have hBorn (j) : (old ++ born).get (bornIndex j)=born.get j := by
    simp [bornIndex,List.get_eq_getElem]
  have hLmap : L.map (old ++ born).get=born := by
    rw [show L=List.ofFn bornIndex from rfl,List.map_ofFn]
    convert List.ofFn_get born using 1
    congr 1
    funext j
    exact hBorn j
  have hApart : ∀ j ∈ L,oi ≠ j := by
    intro j hj
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hj
    intro heq
    have hv := congrArg Fin.val heq
    dsimp [oi,bornIndex] at hv
    omega
  apply HironakaG4ActiveMonomialSharpBad.active_old_monomial_subset_originalSharpBadLocus
    hn hN hFull hDense oi L hApart
  refine ⟨hx,?_⟩
  simpa only [hOld,hLmap,oldMonomialPart,oldTraceIdeal] using hNot

private theorem factor_one_mem {N : Set X} {I D J : GermIdeal n X} {x : X}
    (hFactor : I=restrictOn n N (D.mul J))
    (hD : D.mem x (1 : X → ℂ)) (hJ : J.mem x (1 : X → ℂ)) :
    I.mem x (1 : X → ℂ) := by
  rw [hFactor]
  refine ⟨holomorphicAt_const 1,IsInSpanAt.restrict ?_⟩
  apply isInSpanAt_self ?_ (holomorphicAt_const 1)
  change IsInSpanAt (n := n) (fun f => ∃ a b,D.mem x a ∧ J.mem x b ∧ f=a*b) x (1 : X → ℂ)
  exact isInSpanAt_self ⟨1,1,hD,hJ,by ext y;simp⟩ (holomorphicAt_const 1)

private theorem relativeStrict_disjoint_vanishing (hn : 0<n) {N S C : Set X}
    (hS : IsClosed S) (hSN : S ⊆ N) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hCS : Disjoint C S) :
    HironakaSharpActualChronologicalStrictStep.nextRelativeStrict N
      (vanishingIdeal (n := n) S) C π=vanishingIdeal (n := n) (π ⁻¹' S) := by
  have hSub : π ⁻¹' S ⊆ BlowupStrictSubmanifold.geoStrictTransform π C N := by
    intro z hz
    exact subset_closure ⟨hSN hz,fun hzC => Set.disjoint_left.mp hCS hzC hz⟩
  have hDense : π ⁻¹' S ⊆ closure ((π ⁻¹' S) \ π ⁻¹' C) := by
    intro z hz
    exact subset_closure ⟨hz,fun hzC => Set.disjoint_left.mp hCS hzC hz⟩
  change HironakaSharpOriginalFirstMemberRelativeStrict.relativeExceptionalSaturation
    (BlowupStrictSubmanifold.geoStrictTransform π C N)
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) S)) (π ⁻¹' C)=_
  rw [FactorizationFromResolution.pullback_vanishingIdeal_eq_of_disjoint hπ hS hCS]
  exact HironakaG4SmoothSubcarrierResidualStep.relativeExceptionalSaturation_vanishingIdeal_eq
    hn (BlowupSNCTransform.isSNCDivisor_preimage_centre hπ) hSub hDense

private theorem dense_after_disjoint {S C : Set X} {F : List (Set X)}
    (hClosed : ∀ H ∈ F,IsClosed H) (hDense : S ⊆ closure (S \ ⋃ H ∈ F,H))
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCS : Disjoint C S) :
    π ⁻¹' S ⊆ closure ((π ⁻¹' S) \ ⋃ H ∈
      F.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C],H) := by
  obtain ⟨s,hs,hsπ,hsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  let U : Opens X := ⟨Cᶜ,hπ.1.1.isOpen_compl⟩
  intro z hz
  have hzC : π z ∈ Cᶜ := fun hzC => Set.disjoint_left.mp hCS hzC hz
  let x : U := ⟨π z,hzC⟩
  have hx : x ∈ closure ((Subtype.val : U → X) ⁻¹' (S \ ⋃ H ∈ F,H)) := by
    have hEq := U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (S \ ⋃ H ∈ F,H)
    exact (Set.ext_iff.mp hEq x).mp (hDense hz)
  apply mem_closure_iff.mpr
  intro O hOo hzO
  have hxO : x ∈ s ⁻¹' O := by
    change s ⟨π z,hzC⟩ ∈ O
    rw [hsec z hzC]
    exact hzO
  obtain ⟨y,hyO,hyGood⟩ := mem_closure_iff.mp hx _ (hOo.preimage hs.continuous) hxO
  have hsy : π (s y)=(y : X) := congrFun hsπ y
  refine ⟨s y,hyO,⟨?_,?_⟩⟩
  · change π (s y) ∈ S
    rw [hsy]
    exact hyGood.1
  · intro hyUnion
    obtain ⟨H,hHF,hyH⟩ := mem_iUnion₂.mp hyUnion
    rcases List.mem_append.mp hHF with hOld | hNew
    · obtain ⟨K,hKF,rfl⟩ := List.mem_map.mp hOld
      have hyK := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
        hπ.contMDiff.continuous (hClosed K hKF) hyH
      change π (s y) ∈ K at hyK
      rw [hsy] at hyK
      exact hyGood.2 (mem_iUnion₂.mpr ⟨K,hKF,hyK⟩)
    · rw [List.mem_singleton.mp hNew] at hyH
      change π (s y) ∈ C at hyH
      rw [hsy] at hyH
      exact y.property hyH

private theorem nc_after_disjoint {S C : Set X} {F : List (Set X)}
    (hClosed : ∀ H ∈ F,IsClosed H) (hNC : HasNormalCrossings n S F)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCS : Disjoint C S) :
    HasNormalCrossings n (π ⁻¹' S)
      (F.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  let G := F.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
  intro z hz
  have hzC : π z ∉ C := fun hzC => Set.disjoint_left.mp hCS hzC hz
  obtain ⟨S₀,Q,hFrame,hCard⟩ := hNC (π z) hz
  let idx : Fin G.length → Option (Fin F.length) := fun j =>
    if hj : j.val<F.length then some ⟨j.val,hj⟩ else none
  let A : Option (Fin G.length) → Set X :=
    fun o => o.elim S (fun j => (idx j).elim ∅ F.get)
  let R : Fin G.length → Finset (Fin n) := fun j => (idx j).elim ∅ Q
  have hExpanded : IsCoordinateFamilyAt n A (fun o => o.elim S₀ R) (π z) := by
    obtain ⟨Φ,hsrc,h0,hFlat⟩ := hFrame
    refine ⟨Φ,hsrc,h0,?_⟩
    rintro (_ | j) hj y hy hyΦ
    · exact hFlat none hj hy hyΦ
    · cases hIdx : idx j with
      | none => simp [A,hIdx] at hj
      | some i =>
        change (y ∈ (idx j).elim ∅ F.get ↔ _) at ⊢
        simp only [hIdx,Option.elim,R]
        exact hFlat (some i) (by simpa [A,hIdx] using hj) hy hyΦ
  have hGet (j : Fin G.length) : G.get j=(idx j).elim (π ⁻¹' C)
      (fun i => BlowupStrictSubmanifold.geoStrictTransform π C (F.get i)) := by
    by_cases hj : j.val<F.length
    · simp [G,idx,hj,List.get_eq_getElem]
    · have hval : j.val=F.length := by
        have hlt := j.isLt
        simp only [G,List.length_append,List.length_map,List.length_singleton] at hlt
        omega
      simp [G,idx,hval,List.get_eq_getElem]
  have hO : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
  have hFamily : IsCoordinateFamilyAt n
      (fun o : Option (Fin G.length) => o.elim (π ⁻¹' S) G.get)
      (fun o => o.elim S₀ R) z := by
    apply NormalCrossingsInvariance.isCoordinateFamilyAt_of_preimage hπ.contMDiff
      (fun he => hzC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ he)) hO hzC ?_ hExpanded
    rintro (_ | j) y hy
    · rfl
    · change y ∈ G.get j ↔ π y ∈ (idx j).elim ∅ F.get
      rw [hGet]
      cases hIdx : idx j with
      | none =>
          simp only [Option.elim,mem_preimage,mem_empty_iff_false,iff_false]
          exact hy
      | some i =>
          exact BlowupStrictSubmanifold.mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous (hClosed _ (List.get_mem F i)) hy
  refine ⟨S₀,R,hFamily,?_⟩
  intro j hj
  rw [hGet] at hj
  cases hIdx : idx j with
  | none => exact (hzC (by simpa [hIdx] using hj)).elim
  | some i =>
    have hi : π z ∈ F.get i := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
      hπ.contMDiff.continuous (hClosed _ (List.get_mem F i)) (by simpa [hIdx] using hj)
    simpa [R,hIdx] using hCard i hi

theorem exponent_zero_of_one_mem {N H : Set Y} {I : GermIdeal n Y} {x : Y}
    (hClosed : IsClosed (N ∩ H)) (hOne : I.mem x (1 : Y → ℂ)) :
    divExpAlong n N I H x=0 := by
  by_cases hx : x ∈ N ∩ H
  · have hNot : ¬IsDivNearAlong n N I H 1 x := by
      intro hDiv
      have hVan := (hDiv.self_of_nhds hx.1 hx.2).2 (1 : Y → ℂ) hOne
      exact one_ne_zero ((vanishesToOrderOn_one_iff hx.1 (holomorphicAt_const 1)).mp hVan)
    have hFin : ∃ e,¬IsDivNearAlong n N I H (e+1) x := ⟨0,hNot⟩
    rw [divExpAlong,dif_pos hFin]
    exact (Nat.find_eq_zero hFin).mpr hNot
  · have hInf : ¬∃ e,¬IsDivNearAlong n N I H (e+1) x := by
      rintro ⟨e,he⟩
      exact he (isDivNearAlong_of_notMem hClosed hx (e+1))
    rw [divExpAlong,dif_neg hInf]

theorem actual_processed_original_high_count_unit_window
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
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H)) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let J := fun i : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    let D := fun i : Fin E.length => monomialPartAlong n A.N
      (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
    let a := fun x i j => divExpAlong n A.N (D i) (A.E.get j) x
    ∀ x ∈ A.N,2 ≤ tauD (a x) → ∃ U : Opens Y,x ∈ U ∧
      ∀ y ∈ U,∀ i : Fin E.length,(J i).mem y (1 : Y → ℂ) := by

  let A := geoTransformAlong (geometricTemplate W []) T
  let J := fun i : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let D := fun i : Fin E.length => monomialPartAlong n A.N
    (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
  let a := fun x i j => divExpAlong n A.N (D i) (A.E.get j) x
  have hProtect (i : Fin E.length) :=
    HironakaG4ProtectedResidualEndpoint.actual_original_selected_endpoint_protection
      hn hW hE hdense i T hT hFull (fun x hx => hOrd x hx i) (hNC i) (hDenseS i)
  have hcJ (i : Fin E.length) : (J i).IsCoherent := by
    rw [show J i=vanishingIdeal (n := n) (A.N ∩ (J i).zeroLocus) from (hProtect i).2.1]
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal (hProtect i).1
  have hRecorded := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  change ∀ x ∈ A.N,2 ≤ tauD (a x) → ∃ U : Opens Y,x ∈ U ∧
    ∀ y ∈ U,∀ i : Fin E.length,(J i).mem y (1 : Y → ℂ)
  intro x hx hHigh
  have hOne (i : Fin E.length) : (J i).mem x (1 : Y → ℂ) := by
    by_contra hNot
    have hxS : x ∈ A.N ∩ (J i).zeroLocus := by
      refine ⟨hx,?_⟩
      apply (HironakaSharpActualChronologicalDistinctDefect.actual_proper_iff_zeroLocus hcJ i x).mp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,hNot⟩
    have hSub : properRows (a x) ⊆ {i} := by
      intro h hh
      by_cases hhi : h=i
      · exact Finset.mem_singleton.mpr hhi
      · exfalso
        have hD : (D h).mem x (1 : Y → ℂ) :=
          ((hProtect i).2.2.2.1 h hhi x hxS).self_of_nhds.1
        have hZero (j : Fin A.E.length) : a x h j=0 :=
          exponent_zero_of_one_mem
            (hRecorded.1.1.inter (hRecorded.2.1.1 _
              (List.mem_append_right (E.map (strictAlong T)) (List.get_mem A.E j)))) hD
        have hPos := (Finset.mem_filter.mp hh).2
        change 0 < ∑ j,a x h j at hPos
        simp only [hZero,Finset.sum_const_zero] at hPos
        omega
    have hLow : tauD (a x) ≤ 1 := by
      exact (Finset.card_le_card hSub).trans (by simp)
    omega
  have hAll : ∀ᶠ y in 𝓝 x,∀ i : Fin E.length,(J i).mem y (1 : Y → ℂ) :=
    Filter.eventually_all.mpr (fun i => HadamardBridge.eventually_mem_of_isCoherent (hcJ i) (hOne i))
  obtain ⟨U,hU,hUo,hxU⟩ := mem_nhds_iff.mp hAll
  exact ⟨⟨U,hUo⟩,hxU,fun y hy => hU hy⟩

private theorem original_high_count_step_geometry
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
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun i : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    let S := fun i : Fin E.length => A.N ∩ (J i).zeroLocus
    let D := fun i : Fin E.length => monomialPartAlong n A.N
      (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
    let sumP : GermIdeal n Y := ⟨fun x g =>
      IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n Y := ⟨A.N,A.E,sumP,1⟩
    let a := fun x i j => divExpAlong n A.N (D i) (A.E.get j) x
    ResolutionInvariantSpec.IsInvDomain (n+1) M ∧
      ∀ (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),M.IsAdmissibleCentre C →
        HasNormalCrossings n C (old ++ A.E) ∧
        C ⊆ originalSharpBadLocus (n := n) A.N (old ++ A.E) ∧
        (∀ i : Fin E.length,Disjoint C (S i)) ∧
        (∀ i ∈ P,C ⊆ strictAlong T (E.get i)) ∧
        (∀ i : Fin E.length,i ∉ P → Disjoint C (strictAlong T (E.get i))) ∧
        (∀ x ∈ C,properRows (a x)=P ∧ ∀ i : Fin E.length,(J i).mem x 1) ∧
        IsGeoTestTower (geometricTemplate W []) (BlowupTower.step T C π hπ) ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) (BlowupTower.step T C π hπ) := by
  classical
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun i : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let S := fun i : Fin E.length => A.N ∩ (J i).zeroLocus
  let I := fun i : Fin E.length => restrictOn n A.N
    (vanishingIdeal (n := n) (strictAlong T (E.get i)))
  let D := fun i : Fin E.length => monomialPartAlong n A.N (I i) A.E
  let a := fun x i j => divExpAlong n A.N (D i) (A.E.get j) x
  let M : MarkedIdeal n Y := ⟨A.N,A.E,finiteSum D P,1⟩
  have hRecorded := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n A.N := hRecorded.1
  have hFullE : IsSNCDivisor n (old ++ A.E) := hRecorded.2.1
  have hBorn : IsSNCDivisor n A.E :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist hFullE (List.sublist_append_right old A.E)
  have hTr : IsTransverse n A.N A.E := hRecorded.2.2.1
  have hDenseFull : A.N ⊆ closure (A.N \ ⋃ H ∈ old ++ A.E,H) := hRecorded.2.2.2.1
  let o : Fin E.length → Fin old.length := fun i => ⟨i.val,by simp [old]⟩
  have hGet (i : Fin E.length) : old.get (o i)=strictAlong T (E.get i) := by simp [old,o]
  have hParts (i : Fin E.length) := actual_old_parts_geometry hn hN hFullE hTr hDenseFull (o i)
  have hcD (i : Fin E.length) : (D i).IsCoherent := by
    simpa only [oldMonomialPart,oldTraceIdeal,hGet] using (hParts i).2.2.2.2.1
  have hnzD (i : Fin E.length) : ∀ x ∈ A.N,IsNonzeroAlongAt A.N (D i) x := by
    simpa only [oldMonomialPart,oldTraceIdeal,hGet] using (hParts i).2.2.2.2.2.1
  have hmD (i : Fin E.length) : IsMonomialAlong n A.N (D i) A.E := by
    simpa only [oldMonomialPart,oldTraceIdeal,hGet] using (hParts i).2.2.2.2.2.2.1
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  have hSum := finiteSum_domain_and_cosupport hn hN hBorn hTr D hcD hnzD hmD P hPne
  change ResolutionInvariantSpec.IsInvDomain (n+1) M ∧ _
  refine ⟨hSum.1,?_⟩
  intro C π hπ hC
  have hCN : C ⊆ A.N := hC.subset_N
  have hProper (x : Y) (hx : x ∈ C) : properRows (a x)=P :=
    (Finset.eq_of_subset_of_card_le ((hSum.2 x).mp (hC.2.1 hx)).2 (hBound x (hCN hx))).symm
  have hUnit (x : Y) (hx : x ∈ C) (i : Fin E.length) : (J i).mem x 1 := by
    have hHigh : 2 ≤ tauD (a x) := by
      change 2 ≤ (properRows (a x)).card
      rw [hProper x hx]
      exact hP
    obtain ⟨U,hxU,hU⟩ := actual_processed_original_high_count_unit_window hn hW hE hdense
      T hT hFull hOrd hNC hDenseS x (hCN hx) hHigh
    exact hU x hxU i
  have hDisjoint (i : Fin E.length) : Disjoint C (S i) := by
    apply Set.disjoint_left.mpr
    intro x hxC hxS
    exact one_ne_zero (hxS.2 1 (hUnit x hxC i))
  have hNotD (i : Fin E.length) (hi : i ∈ P) (x : Y) (hx : x ∈ C) : ¬(D i).mem x 1 := by
    have hPi : i ∈ properRows (a x) := by rw [hProper x hx];exact hi
    have hCos := (row_cosupport_iff hn hN hBorn hTr (hcD i) (hnzD i) (hmD i) (hCN hx)).mpr
      (Finset.mem_filter.mp hPi).2
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)] at hCos
    exact fun hOne => one_ne_zero (hCos.2 1 hOne)
  have hDunit (i : Fin E.length) (hi : i ∉ P) (x : Y) (hx : x ∈ C) : (D i).mem x 1 := by
    by_contra hNot
    have hCos : x ∈ cosupport n A.N (D i) 1 := by
      rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)]
      refine ⟨hCN hx,fun g hg => ?_⟩
      by_contra hne
      exact hNot (CompanionReduction.one_mem_of_apply_ne_zero (hcD i) hg hne)
    have hPos := (row_cosupport_iff hn hN hBorn hTr (hcD i) (hnzD i) (hmD i) (hCN hx)).mp hCos
    apply hi
    rw [←hProper x hx]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,hPos⟩
  have hH (i : Fin E.length) : IsClosedSubmanifold n (strictAlong T (E.get i)) := by
    have hOld := NormalCrossingsComparison.isSNCDivisor_of_sublist hFullE (List.sublist_append_left old A.E)
    rw [←hGet i]
    exact MonomialPart.isClosedSubmanifold_get hn hOld (o i)
  have hCP (i : Fin E.length) (hi : i ∈ P) : C ⊆ strictAlong T (E.get i) := by
    intro x hx
    by_contra hnot
    have hIone : (I i).mem x 1 :=
      (HironakaSharpActualCurveExceptionalDifference.actual_normalized_vanishing_unit_iff (hH i).1 (hCN hx)).mpr hnot
    exact hNotD i hi x hx
      (le_monomialPartAlong hn hBorn hTr (hRecorded.2.2.2.2 i).1 x 1 hIone)
  have hOutside (i : Fin E.length) (hi : i ∉ P) : Disjoint C (strictAlong T (E.get i)) := by
    apply Set.disjoint_left.mpr
    intro x hxC hxH
    have hFactor : I i=restrictOn n A.N ((D i).mul (J i)) := (hRecorded.2.2.2.2 i).2.2.2
    have hIone := factor_one_mem hFactor (hDunit i hi x hxC) (hUnit x hxC i)
    exact ((HironakaSharpActualCurveExceptionalDifference.actual_normalized_vanishing_unit_iff
      (hH i).1 (hCN hxC)).mp hIone) hxH
  have hCNC : HasNormalCrossings n C (old ++ A.E) := by
    intro x hx
    apply HironakaG4IncidentOldBornStratumCentre.actual_incident_old_normalCrossingsAt hFullE hC.2.2 hx
    intro j hj
    let i : Fin E.length := ⟨j.val,by simpa [old] using j.isLt⟩
    have hji : old.get j=strictAlong T (E.get i) := by simp [old,i]
    by_cases hi : i ∈ P
    · exact Eventually.of_forall (fun y hy => by rw [hji];exact hCP i hi hy)
    · exact (Set.disjoint_left.mp (hOutside i hi) hx (hji ▸ hj)).elim
  have hSharp : C ⊆ originalSharpBadLocus (n := n) A.N (old ++ A.E) := by
    obtain ⟨i0,hi0⟩ := hPne
    intro x hx
    apply active_row_sharp_bad hn hN hFullE hDenseFull (o i0) (hCN hx)
    simpa only [oldMonomialPart,oldTraceIdeal,hGet] using hNotD i0 hi0 x hx
  have hTest : IsGeoTestTower (geometricTemplate W []) (.step T C π hπ) := by
    have hw0 : (geometricTemplate W []).IsWellFormed :=
      ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,NormalCrossings.isSNCDivisor_nil,
        NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hT
    refine ⟨hT,⟨hπ.1,?_,hC.2.2⟩⟩
    change C ⊆ cosupport n _ _ (geoTransformAlong (geometricTemplate W []) T).d
    rw [d_geoTransformAlong,show (geometricTemplate W []).d=0 from rfl,
      cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hw.isCoherent hg)]
    exact hCN
  have hTestFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) (.step T C π hπ) := by
    let L := geometricTemplate (univ : Set X) E
    have hL := pullback_eq_mul_geoTransformAlong
      (𝔪 := L) rfl IdealWeightPowers.isCoherent_unitIdeal T hFull
    have hd : (geoTransformAlong L T).d=0 := d_geoTransformAlong L T
    have hCos : (geoTransformAlong L T).cosupp=univ := by
      change cosupport n (geoTransformAlong L T).N (geoTransformAlong L T).ideal
        (geoTransformAlong L T).d=univ
      rw [hd,cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hL.2.1 hg),hL.1]
    refine ⟨hFull,⟨hπ.1,?_,?_⟩⟩
    · rw [hCos]
      exact subset_univ C
    · rw [HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T]
      exact hCNC
  exact ⟨hCNC,hSharp,hDisjoint,hCP,hOutside,fun x hx => ⟨hProper x hx,hUnit x hx⟩,hTest,hTestFull⟩

private def PreparedFamilyAt {ι : Type*} (N : Set X) (R : ι → Set X) (x : X) : Prop :=
  ∃ (Q : Finset (Fin n)) (p : ι → Fin n),
    IsCoordinateFamilyAt n (fun o : Option ι => o.elim N R)
      (fun o => o.elim Q (fun i => Q ∪ {p i})) x ∧
    (∀ i,x ∈ R i → p i ∉ Q) ∧ Set.InjOn p {i | x ∈ R i}

private theorem preparedFamilyAt_pullback_partial {ι κ : Type*} (hn : 0<n)
    {N : Set X} {R : ι → Set X} {N' : Set Y} {R' : κ → Set Y}
    {g : Y → X} (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {z : Y} (hzE : z ∉ exceptionalLocus n g) {O : Set Y}
    (hO : IsOpen O) (hzO : z ∈ O) (f : κ → Option ι)
    (hInject : ∀ a b i,f a=some i → f b=some i → a=b)
    (hN : ∀ y ∈ O,y ∈ N' ↔ g y ∈ N)
    (hR : ∀ a,∀ y ∈ O,y ∈ R' a ↔ ∃ i,f a=some i ∧ g y ∈ R i)
    (hP : PreparedFamilyAt N R (g z)) : PreparedFamilyAt N' R' z := by
  obtain ⟨Q,p,hFrame,hFree,hInj⟩ := hP
  let p' : κ → Fin n := fun a => (f a).elim ⟨0,hn⟩ p
  let A : Option κ → Set X := fun o => o.elim N (fun a => (f a).elim ∅ R)
  have hExpanded : IsCoordinateFamilyAt n A
      (fun o => o.elim Q (fun a => Q ∪ {p' a})) (g z) := by
    obtain ⟨Φ,hsrc,h0,hFlat⟩ := hFrame
    refine ⟨Φ,hsrc,h0,?_⟩
    rintro (_ | a) ha y hy hyΦ
    · exact hFlat none ha hy hyΦ
    · cases hfa : f a with
      | none => simp [A,hfa] at ha
      | some i =>
        simpa [A,p',hfa] using hFlat (some i) (by simpa [A,hfa] using ha) hy hyΦ
  have hTarget : IsCoordinateFamilyAt n
      (fun o : Option κ => o.elim N' R')
      (fun o => o.elim Q (fun a => Q ∪ {p' a})) z := by
    apply NormalCrossingsInvariance.isCoordinateFamilyAt_of_preimage hg hzE hO hzO ?_ hExpanded
    rintro (_ | a) y hy
    · exact hN y hy
    · change y ∈ R' a ↔ g y ∈ (f a).elim ∅ R
      rw [hR a y hy]
      cases hfa : f a <;> simp
  have hLift (a : κ) (ha : z ∈ R' a) :
      ∃ i,f a=some i ∧ g z ∈ R i ∧ p' a=p i := by
    obtain ⟨i,hfi,hi⟩ := (hR a z hzO).mp ha
    exact ⟨i,hfi,hi,by simp [p',hfi]⟩
  refine ⟨Q,p',hTarget,?_,?_⟩
  · intro a ha
    obtain ⟨i,_hfi,hi,hp⟩ := hLift a ha
    rw [hp]
    exact hFree i hi
  · intro a ha b hb heq
    obtain ⟨i,hfi,hi,hpi⟩ := hLift a ha
    obtain ⟨j,hfj,hj,hpj⟩ := hLift b hb
    have hij : i=j := hInj hi hj (hpi.symm.trans (heq.trans hpj))
    apply hInject a b i hfi
    rw [hij]
    exact hfj

private theorem pullback_one_mem {L K : Type u} [TopologicalSpace L]
    [ChartedSpace (ComplexModel n) L] [IsComplexManifold n L]
    [TopologicalSpace K] [ChartedSpace (ComplexModel n) K] [IsComplexManifold n K]
    {I : GermIdeal n L} {φ : K → L} {z : K}
    (hOne : I.mem (φ z) (1 : L → ℂ)) :
    (GermIdeal.pullback (m := n) φ I).mem z (1 : K → ℂ) := by
  exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨1,hOne,rfl⟩ (holomorphicAt_const 1))

private theorem monomial_unit_off_centre {N H C : Set X} {B : List (Set X)}
    (hN : IsClosed N) (hH : IsClosed H) (hB : ∀ K ∈ B,IsClosed K)
    {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hcD : (monomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C N)
      (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
      (B.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])).IsCoherent)
    {z : Y} (hzC : π z ∉ C)
    (hOne : (monomialPartAlong n N (vanishingIdeal (n := n) H) B).mem (π z) 1) :
    (monomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C N)
      (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
      (B.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])).mem z 1 := by
  let U : Opens X := ⟨Cᶜ,hπ.1.1.isOpen_compl⟩
  let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → U := fun q => ⟨π q.val,q.property⟩
  let NU : Set U := (Subtype.val : U → X) ⁻¹' N
  let HU : Set U := (Subtype.val : U → X) ⁻¹' H
  let BU : List (Set U) := B.map ((Subtype.val : U → X) ⁻¹' ·)
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let H' := BlowupStrictSubmanifold.geoStrictTransform π C H
  let B' := B.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
  let D := monomialPartAlong n N (vanishingIdeal (n := n) H) B
  let D' := monomialPartAlong n N' (vanishingIdeal (n := n) H') B'
  let DU := monomialPartAlong n NU (vanishingIdeal (n := n) HU) BU
  let zv : V := ⟨z,hzC⟩
  have hCU : ((Subtype.val : U → X) ⁻¹' C : Set U)=∅ := by
    ext q
    simp only [mem_preimage,mem_empty_iff_false,iff_false]
    exact q.property
  have hr : IsBlowupAlong n (∅ : Set U) ρ := by
    have hr := BlowupRestrictOpen.isBlowupAlong_restrict hπ U V.isOpen
    rw [hCU] at hr
    exact hr
  have hloc := ContactCanonicalAlong.exists_isLocalInverseAt_of_isBlowupAlong_empty hr
  have hSource : GermIdeal.pullback (m := n) (Subtype.val : U → X) D=DU := by
    rw [show D=monomialPartAlong n N (vanishingIdeal (n := n) H) B from rfl,
      MonomialPartEtale.pullback_monomialPartAlong
        (φ := (Subtype.val : U → X)) (N := N) (𝔞 := vanishingIdeal (n := n) H) (E := B)
        (fun y : U => ⟨DerivativeIdealAlongEtale.openInv U y,
          DerivativeIdealAlongEtale.isLocalInverseAt_val U y⟩) (fun _ _ hg => hg.1),
      SmoothCentreHomogeneity.pullback_val_vanishingIdeal U H]
  have hNU : (Subtype.val : V → Y) ⁻¹' N'=ρ ⁻¹' NU := by
    ext q
    exact BlowupStrictSubmanifold.mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hN q.property
  have hHU : (Subtype.val : V → Y) ⁻¹' H'=ρ ⁻¹' HU := by
    ext q
    exact BlowupStrictSubmanifold.mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hH q.property
  have hBU : B'.map ((Subtype.val : V → Y) ⁻¹' ·)=BU.map (ρ ⁻¹' ·) ++ [∅] := by
    have hMaps : B.map (fun K => (Subtype.val : V → Y) ⁻¹'
        BlowupStrictSubmanifold.geoStrictTransform π C K)=
        B.map (fun K => ρ ⁻¹' ((Subtype.val : U → X) ⁻¹' K)) := by
      apply List.map_congr_left
      intro K hK
      ext q
      exact BlowupStrictSubmanifold.mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous (hB K hK) q.property
    have hEmpty : ((Subtype.val : V → Y) ⁻¹' (π ⁻¹' C) : Set V)=∅ := by
      ext q
      simp only [mem_preimage,mem_empty_iff_false,iff_false]
      exact q.property
    simpa only [B',BU,List.map_append,List.map_singleton,List.map_map,Function.comp_def,hEmpty] using
      congrArg (fun L : List (Set V) => L ++ [∅]) hMaps
  have hRaw : GermIdeal.pullback (m := n) ρ (vanishingIdeal (n := n) HU)=
      vanishingIdeal (n := n) (ρ ⁻¹' HU) :=
    FactorizationFromResolution.pullback_vanishingIdeal_eq_of_disjoint hr
      (hH.preimage continuous_subtype_val)
      (Set.disjoint_left.mpr (fun _ hEmpty _ => hEmpty.elim))
  have hTarget : GermIdeal.pullback (m := n) (Subtype.val : V → Y) D'=
      GermIdeal.pullback (m := n) ρ DU := by
    rw [show D'=monomialPartAlong n N' (vanishingIdeal (n := n) H') B' from rfl,
      MonomialPartEtale.pullback_monomialPartAlong
        (φ := (Subtype.val : V → Y)) (N := N') (𝔞 := vanishingIdeal (n := n) H') (E := B')
        (fun y : V => ⟨DerivativeIdealAlongEtale.openInv V y,
          DerivativeIdealAlongEtale.isLocalInverseAt_val V y⟩) (fun _ _ hg => hg.1),
      SmoothCentreHomogeneity.pullback_val_vanishingIdeal V H',hNU,hHU,hBU,
      MonomialPartEtale.monomialPartAlong_append_empty,←hRaw]
    exact (MonomialPartEtale.pullback_monomialPartAlong (φ := ρ) (N := NU)
      (𝔞 := vanishingIdeal (n := n) HU) (E := BU) hloc (fun _ _ hg => hg.1)).symm
  have hOneU : DU.mem (ρ zv) 1 := by
    rw [←hSource]
    exact pullback_one_mem (φ := (Subtype.val : U → X)) (z := ρ zv) hOne
  have hTargetOne : (GermIdeal.pullback (m := n) (Subtype.val : V → Y) D').mem zv 1 := by
    rw [hTarget]
    exact pullback_one_mem (φ := ρ) (z := zv) hOneU
  exact (MonomialPartEtale.mem_pullback_iff_of_local hcD
    (DerivativeIdealAlongEtale.isLocalInverseAt_val V zv)).mp hTargetOne

private theorem prepared_when_residuals_absent (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (hBorn : IsSNCDivisor n born) (hTr : IsTransverse n N born)
    {x : X} (hx : x ∈ N)
    (hAbsent : ∀ i : Fin old.length,x ∉ preparedSupport N old born (Sum.inl i)) :
    IsPreparedResidualSNCAt N old born x := by
  obtain ⟨Q,s,hFrame,hFree,hInj⟩ := actual_trace_family_frame hn hBorn hTr hx
  let p : Fin old.length ⊕ Fin born.length → Fin n := Sum.elim (fun _ => ⟨0,hn⟩) s
  refine ⟨Q,p,?_,?_,?_⟩
  · obtain ⟨Φ,hsrc,h0,hFlat⟩ := hFrame
    refine ⟨Φ,hsrc,h0,?_⟩
    rintro (_ | (i | j)) hi y hy hyΦ
    · exact hFlat none hi hy hyΦ
    · exact (hAbsent i hi).elim
    · exact hFlat (some j) hi hy hyΦ
  · rintro (i | j) hi
    · exact (hAbsent i hi).elim
    · exact hFree j hi
  · rintro (i | j) hi (k | l) hk heq
    · exact (hAbsent i hi).elim
    · exact (hAbsent i hi).elim
    · exact (hAbsent k hk).elim
    · exact congrArg Sum.inr (hInj hi hk heq)

private theorem prepared_off_centre {N C : Set X} {old born : List (Set X)}
    (hN : IsClosed N) (hBorn : ∀ H ∈ born,IsClosed H)
    {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hSupports : let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
      let old' := old.map (BlowupStrictSubmanifold.geoStrictTransform π C)
      let born' := born.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
      ∀ i : Fin old'.length,
        preparedSupport N' old' born' (Sum.inl i)=π ⁻¹'
          preparedSupport N old born (Sum.inl ⟨i.val,by simpa [old'] using i.isLt⟩))
    (hn : 0<n) {z : Y} (hzC : π z ∉ C)
    (hP : IsPreparedResidualSNCAt N old born (π z)) :
    IsPreparedResidualSNCAt (BlowupStrictSubmanifold.geoStrictTransform π C N)
      (old.map (BlowupStrictSubmanifold.geoStrictTransform π C))
      (born.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) z := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let old' := old.map (BlowupStrictSubmanifold.geoStrictTransform π C)
  let born' := born.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
  let o : Fin old'.length → Fin old.length := fun i => ⟨i.val,by simpa [old'] using i.isLt⟩
  let f : Fin old'.length ⊕ Fin born'.length → Option (Fin old.length ⊕ Fin born.length) :=
    Sum.elim (fun i => some (Sum.inl (o i)))
      (fun j => if hj : j.val<born.length then some (Sum.inr ⟨j.val,hj⟩) else none)
  have hInject : ∀ a b i,f a=some i → f b=some i → a=b := by
    rintro (i | j) (k | l) a ha hb
    · have heq := ha.trans hb.symm
      simp only [f,Sum.elim_inl,Option.some.injEq,Sum.inl.injEq] at heq
      have hv : i.val=k.val := congrArg (fun a : Fin old.length => a.val) heq
      exact congrArg Sum.inl (Fin.ext hv)
    · have heq := ha.trans hb.symm
      by_cases hl : l.val<born.length <;> simp [f,hl] at heq
    · have heq := ha.trans hb.symm
      by_cases hj : j.val<born.length <;> simp [f,hj] at heq
    · by_cases hj : j.val<born.length
      · by_cases hl : l.val<born.length
        · have heq := ha.trans hb.symm
          simp only [f,Sum.elim_inr,dif_pos hj,dif_pos hl,Option.some.injEq,Sum.inr.injEq] at heq
          have hv : j.val=l.val := congrArg (fun a : Fin born.length => a.val) heq
          exact congrArg Sum.inr (Fin.ext hv)
        · simp [f,hl] at hb
      · simp [f,hj] at ha
  have hGet (j : Fin born'.length) : born'.get j=
      if hj : j.val<born.length then
        BlowupStrictSubmanifold.geoStrictTransform π C (born.get ⟨j.val,hj⟩) else π ⁻¹' C := by
    by_cases hj : j.val<born.length
    · simp [born',hj,List.get_eq_getElem]
    · have hv : j.val=born.length := by
        have hlt := j.isLt
        simp only [born',List.length_append,List.length_map,List.length_singleton] at hlt
        omega
      simp [born',hv,List.get_eq_getElem]
  have hCarrier (y : Y) (hy : π y ∉ C) : y ∈ N' ↔ π y ∈ N :=
    BlowupStrictSubmanifold.mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hN hy
  change PreparedFamilyAt N' (preparedSupport N' old' born') z
  apply preparedFamilyAt_pullback_partial hn hπ.contMDiff
    (fun he => hzC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ he))
    (hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous) hzC f hInject hCarrier ?_ hP
  rintro (i | j) y hy
  · rw [hSupports i]
    simp [f,o]
  · change (y ∈ N' ∧ y ∈ born'.get j) ↔ _
    rw [hGet]
    by_cases hj : j.val<born.length
    · simp only [dif_pos hj,f,Sum.elim_inr,Option.some.injEq]
      have hEq := and_congr (hCarrier y hy)
        (BlowupStrictSubmanifold.mem_geoStrictTransform_iff_of_notMem
          hπ.contMDiff.continuous (hBorn _ (List.get_mem born ⟨j.val,hj⟩)) hy)
      constructor
      · intro hySet
        exact ⟨Sum.inr ⟨j.val,hj⟩,rfl,hEq.mp hySet⟩
      · rintro ⟨i,rfl,hySet⟩
        exact hEq.mpr hySet
    · simp only [dif_neg hj,mem_preimage]
      constructor
      · rintro ⟨_hyN,hyC⟩
        exact (hy hyC).elim
      · rintro ⟨i,hfi,_hi⟩
        simp [f,hj] at hfi

private theorem ordinaryOrder_zero_of_one_mem {N : Set Y} {I : GermIdeal n Y}
    (hcI : I.IsCoherent) {x : Y} (hOne : I.mem x (1 : Y → ℂ)) :
    ordinaryTraceOrder N I x=0 := by
  have hNot : x ∉ cosupport n N I 1 := by
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcI hg)]
    exact fun h => one_ne_zero (h.2 1 hOne)
  have hNot' : x ∉ NonmonomialOrderLocal.ordGe (ordinaryTraceMarked N I) (0+1) := by
    rwa [HironakaSharpOriginalProductTraceOrder.ordGe_ordinaryTraceMarked_eq_cosupport N I hcI]
  exact Nat.eq_zero_of_le_zero (NonmonomialOrderLocal.nmOrd_le_of_notMem hNot')

private theorem original_processed_row_after (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ (geoTransformAlong (geometricTemplate W []) T).N)
    (hUnit : ∀ x ∈ C,(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.mem x 1)
    (hTest : IsGeoTestTower (geometricTemplate W []) (.step T C π hπ))
    (hTestFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) (.step T C π hπ)) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
    let T' := BlowupTower.step T C π hπ
    let A' := geoTransformAlong (geometricTemplate W []) T'
    let old' := E.map (strictAlong T')
    IsClosedSubmanifold n (π ⁻¹' S) ∧
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').ideal=
        vanishingIdeal (n := n) (π ⁻¹' S) ∧
      nonmonomialPartAlong n A'.N
        (restrictOn n A'.N (vanishingIdeal (n := n) (strictAlong T' (E.get i)))) A'.E=
        vanishingIdeal (n := n) (π ⁻¹' S) ∧
      HasNormalCrossings n (π ⁻¹' S) (old'.eraseIdx i.val ++ A'.E) ∧
      (π ⁻¹' S ⊆ closure ((π ⁻¹' S) \ ⋃ H ∈ old'.eraseIdx i.val ++ A'.E,H)) ∧
      ∀ z ∈ A'.N,ordinaryTraceOrder A'.N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').ideal z ≤ 1 := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let S := A.N ∩ J.zeroLocus
  let F := (E.map (strictAlong T)).eraseIdx i.val ++ A.E
  let T' := BlowupTower.step T C π hπ
  let A' := geoTransformAlong (geometricTemplate W []) T'
  let old' := E.map (strictAlong T')
  have hProtect := HironakaG4ProtectedResidualEndpoint.actual_original_selected_endpoint_protection
    hn hW hE hdense i T hT hFull hOrd hNC hDenseS
  have hDisjoint : Disjoint C S := Set.disjoint_left.mpr (fun x hxC hxS =>
    one_ne_zero (hxS.2 1 (hUnit x hxC)))
  have hRecorded := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hNext := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T' hTest hTestFull
  obtain ⟨hNi,_hEi,_hdi,hwi,hnzi,hpri⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hNi
  rw [hNi] at hnzi hpri
  have hWhole : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').ideal=
      vanishingIdeal (n := n) (π ⁻¹' S) := by
    change HironakaSharpActualChronologicalStrictStep.nextRelativeStrict
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N J C π=_
    rw [hNi,show J=vanishingIdeal (n := n) S from hProtect.2.1]
    exact relativeStrict_disjoint_vanishing hn hProtect.1.1 inter_subset_left hπ hDisjoint
  have hOrder : ∀ z ∈ A'.N,ordinaryTraceOrder A'.N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').ideal z ≤ 1 := by
    intro z hz
    have hLoc (x : Y) (hx : x ∈ C) : ∀ᶠ y in 𝓝 x,y ∈ C →
        ordinaryTraceOrder A.N J y=ordinaryTraceOrder A.N J x := by
      exact Eventually.of_forall (fun y hy =>
        (ordinaryOrder_zero_of_one_mem hwi.isCoherent (hUnit y hy)).trans
          (ordinaryOrder_zero_of_one_mem hwi.isCoherent (hUnit x hx)).symm)
    have hLe := HironakaG4EquimultipleRelativeOrder.nextRelativeStrict_order_le_of_locally_constant_on_centre
      hn hRecorded.1 hwi.isCoherent hnzi hpri hπ hCN hLoc hz
    have hzN := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hRecorded.1.1 hz
    change ordinaryTraceOrder _ (HironakaSharpActualChronologicalStrictStep.nextRelativeStrict _ J C π) z ≤ _
    rw [hNi]
    exact hLe.trans (hOrd (π z) hzN)
  have hSub : π ⁻¹' S ⊆ A'.N := by
    intro z hz
    exact subset_closure ⟨hz.1,fun hzC => Set.disjoint_left.mp hDisjoint hzC hz⟩
  have hClosed : IsClosed (π ⁻¹' S) := hProtect.1.1.preimage hπ.contMDiff.continuous
  have hSupport : A'.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').ideal.zeroLocus=π ⁻¹' S := by
    rw [hWhole,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hClosed]
    exact inter_eq_right.mpr hSub
  obtain ⟨hNi',_hEi',_hdi',_hwi',_hnzi',_hpri'⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense i T' hTest
  have hSmooth : IsClosedSubmanifold n (π ⁻¹' S) := by
    have ho : ∀ z ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').N,
        ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').ideal z ≤ 1 := by
      rw [hNi']
      exact hOrder
    have hSm := (HironakaG4OriginalSelectedResidualTail.actual_original_selected_residual_tail
      hn hW hE hdense i T' hTest ho).1
    rw [hNi',hSupport] at hSm
    exact hSm
  have hFsub : F.Sublist (E.map (strictAlong T) ++ A.E) :=
    (List.eraseIdx_sublist _ i.val).append (List.Sublist.refl A.E)
  have hClosedF : ∀ H ∈ F,IsClosed H := fun H hH => hRecorded.2.1.1 H (hFsub.subset hH)
  have hMap : F.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]=
      old'.eraseIdx i.val ++ A'.E := by
    simp only [F,old',List.map_append,←List.eraseIdx_map,List.map_map,List.append_assoc]
    rfl
  have hNC' := nc_after_disjoint hClosedF hNC hπ hDisjoint
  rw [hMap] at hNC'
  have hDense' := dense_after_disjoint hClosedF hDenseS hπ hDisjoint
  rw [hMap] at hDense'
  exact ⟨hSmooth,hWhole,(hNext.2.2.2.2 i).2.2.1.trans hWhole,hNC',hDense',hOrder⟩

/-- Every actual sum-admissible high-count step preserves the genuine processed
current supports and global order/count caps, on the SAME original labels. -/
theorem actual_processed_original_high_count_step
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
    (hPrepared : let A := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x)
    (P : Finset (Fin E.length)) (hP : 2 ≤ P.card)
    (hBound : let A := geoTransformAlong (geometricTemplate W []) T
      let D := fun i : Fin E.length => monomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
      ∀ x ∈ A.N,tauD (fun i j => divExpAlong n A.N (D i) (A.E.get j) x) ≤ P.card) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun i : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    let S := fun i : Fin E.length => A.N ∩ (J i).zeroLocus
    let D := fun i : Fin E.length => monomialPartAlong n A.N
      (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
    let sumP : GermIdeal n Y := ⟨fun x g =>
      IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n Y := ⟨A.N,A.E,sumP,1⟩
    let a := fun x i j => divExpAlong n A.N (D i) (A.E.get j) x
    ResolutionInvariantSpec.IsInvDomain (n+1) M ∧
      ∀ (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),M.IsAdmissibleCentre C →
        let T' := BlowupTower.step T C π hπ
        let A' := geoTransformAlong (geometricTemplate W []) T'
        let old' := E.map (strictAlong T')
        let D' := fun i : Fin E.length => monomialPartAlong n A'.N
          (restrictOn n A'.N (vanishingIdeal (n := n) (strictAlong T' (E.get i)))) A'.E
        let a' := fun z i j => divExpAlong n A'.N (D' i) (A'.E.get j) z
        HasNormalCrossings n C (old ++ A.E) ∧
        C ⊆ originalSharpBadLocus (n := n) A.N (old ++ A.E) ∧
        (∀ i : Fin E.length,Disjoint C (S i)) ∧
        IsGeoTestTower (geometricTemplate W []) T' ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) T' ∧
        (∀ i : Fin E.length,
          IsClosedSubmanifold n (π ⁻¹' S i) ∧
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').ideal =
            vanishingIdeal (n := n) (π ⁻¹' S i) ∧
          nonmonomialPartAlong n A'.N
            (restrictOn n A'.N (vanishingIdeal (n := n) (strictAlong T' (E.get i)))) A'.E =
            vanishingIdeal (n := n) (π ⁻¹' S i) ∧
          HasNormalCrossings n (π ⁻¹' S i) (old'.eraseIdx i.val ++ A'.E) ∧
          π ⁻¹' S i ⊆ closure ((π ⁻¹' S i) \ ⋃ H ∈ old'.eraseIdx i.val ++ A'.E,H)) ∧
        (∀ z ∈ A'.N,∀ i : Fin E.length,ordinaryTraceOrder A'.N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').ideal z ≤ 1) ∧
        (∀ z ∈ A'.N,properRows (a' z) ⊆ properRows (a (π z)) ∧ tauD (a' z) ≤ P.card) ∧
        ∀ z ∈ A'.N,IsPreparedResidualSNCAt A'.N old' A'.E z := by
  classical
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun i : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let S := fun i : Fin E.length => A.N ∩ (J i).zeroLocus
  let I := fun i : Fin E.length => restrictOn n A.N
    (vanishingIdeal (n := n) (strictAlong T (E.get i)))
  let D := fun i : Fin E.length => monomialPartAlong n A.N (I i) A.E
  let M : MarkedIdeal n Y := ⟨A.N,A.E,finiteSum D P,1⟩
  let a := fun x i j => divExpAlong n A.N (D i) (A.E.get j) x
  have hCore := original_high_count_step_geometry (Z := Z) hn hW hE hdense T hT hFull hOrd hNC hDenseS P hP hBound
  change ResolutionInvariantSpec.IsInvDomain (n+1) M ∧ _
  refine ⟨hCore.1,?_⟩
  intro C π hπ hAdm
  let T' := BlowupTower.step T C π hπ
  let A' := geoTransformAlong (geometricTemplate W []) T'
  let old' := E.map (strictAlong T')
  let D' := fun i : Fin E.length => monomialPartAlong n A'.N
    (restrictOn n A'.N (vanishingIdeal (n := n) (strictAlong T' (E.get i)))) A'.E
  let a' := fun z i j => divExpAlong n A'.N (D' i) (A'.E.get j) z
  obtain ⟨hCNC,hSharp,hDisjoint,_hCP,hOutside,hAtC,hTest,hTestFull⟩ := hCore.2 C π hπ hAdm
  have hCN : C ⊆ A.N := hAdm.subset_N
  have hRecorded := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hNext := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T' hTest hTestFull
  have hBorn : IsSNCDivisor n A.E := NormalCrossingsComparison.isSNCDivisor_of_sublist
    hRecorded.2.1 (List.sublist_append_right old A.E)
  have hBorn' : IsSNCDivisor n A'.E := NormalCrossingsComparison.isSNCDivisor_of_sublist
    hNext.2.1 (List.sublist_append_right old' A'.E)
  have hRows (i : Fin E.length) := original_processed_row_after hn hW hE hdense i T hT hFull
    (fun x hx => hOrd x hx i) (hNC i) (hDenseS i) hπ hCN
    (fun x hx => (hAtC x hx).2 i) hTest hTestFull
  have hImage {z : Z} (hz : z ∈ A'.N) : π z ∈ A.N :=
    BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hRecorded.1.1 hz
  let o : Fin E.length → Fin old.length := fun i => ⟨i.val,by simp [old]⟩
  let o' : Fin E.length → Fin old'.length := fun i => ⟨i.val,by simp [old']⟩
  have hGet (i : Fin E.length) : old.get (o i)=strictAlong T (E.get i) := by simp [old,o]
  have hGet' (i : Fin E.length) : old'.get (o' i)=strictAlong T' (E.get i) := by simp [old',o']
  have hParts (i : Fin E.length) := actual_old_parts_geometry hn hRecorded.1 hRecorded.2.1
    hRecorded.2.2.1 hRecorded.2.2.2.1 (o i)
  have hParts' (i : Fin E.length) := actual_old_parts_geometry hn hNext.1 hNext.2.1
    hNext.2.2.1 hNext.2.2.2.1 (o' i)
  have hcD (i : Fin E.length) : (D i).IsCoherent := by
    simpa [oldMonomialPart,oldTraceIdeal,old,o,D,I,A] using (hParts i).2.2.2.2.1
  have hnzD (i : Fin E.length) : ∀ x ∈ A.N,IsNonzeroAlongAt A.N (D i) x := by
    simpa [oldMonomialPart,oldTraceIdeal,old,o,D,I,A] using (hParts i).2.2.2.2.2.1
  have hmD (i : Fin E.length) : IsMonomialAlong n A.N (D i) A.E := by
    simpa [oldMonomialPart,oldTraceIdeal,old,o,D,I,A] using (hParts i).2.2.2.2.2.2.1
  have hcD' (i : Fin E.length) : (D' i).IsCoherent := by
    simpa [oldMonomialPart,oldTraceIdeal,old',o',D',A'] using (hParts' i).2.2.2.2.1
  have hH (i : Fin E.length) : IsClosedSubmanifold n (strictAlong T (E.get i)) := by
    rw [←hGet i]
    exact MonomialPart.isClosedSubmanifold_get hn
      (NormalCrossingsComparison.isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_left old A.E)) (o i)
  have hH' (i : Fin E.length) : IsClosedSubmanifold n (strictAlong T' (E.get i)) := by
    rw [←hGet' i]
    exact MonomialPart.isClosedSubmanifold_get hn
      (NormalCrossingsComparison.isSNCDivisor_of_sublist hNext.2.1 (List.sublist_append_left old' A'.E)) (o' i)
  have hInactiveUnit (i : Fin E.length) {x : Y} (hx : x ∈ A.N)
      (hi : i ∉ properRows (a x)) : (D i).mem x 1 := by
    by_contra hNot
    have hCos : x ∈ cosupport n A.N (D i) 1 := by
      rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)]
      refine ⟨hx,fun g hg => ?_⟩
      by_contra hne
      exact hNot (CompanionReduction.one_mem_of_apply_ne_zero (hcD i) hg hne)
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      (row_cosupport_iff hn hRecorded.1 hBorn hRecorded.2.2.1
        (hcD i) (hnzD i) (hmD i) hx).mp hCos⟩)
  have hActive (z : Z) (hz : z ∈ A'.N) : properRows (a' z) ⊆ properRows (a (π z)) := by
    intro i hi
    by_contra hNot
    have hTargetUnit : (D' i).mem z 1 := by
      by_cases hzC : π z ∈ C
      · have hiP : i ∉ P := by
          rw [←(hAtC (π z) hzC).1]
          exact hNot
        have hzH : z ∉ strictAlong T' (E.get i) := by
          intro hzH
          have hxH := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
            hπ.contMDiff.continuous (hH i).1 hzH
          exact Set.disjoint_left.mp (hOutside i hiP) hzC hxH
        have hIone : (restrictOn n A'.N (vanishingIdeal (n := n) (strictAlong T' (E.get i)))).mem z 1 :=
          (HironakaSharpActualCurveExceptionalDifference.actual_normalized_vanishing_unit_iff (hH' i).1 hz).mpr hzH
        exact le_monomialPartAlong hn hBorn' hNext.2.2.1 (hNext.2.2.2.2 i).1 z 1 hIone
      · have hNorm : D i=monomialPartAlong n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i))) A.E :=
          MonomialPartEtale.monomialPartAlong_congr restrictLe_restrictOn
            (restrictLe_self_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal (hH i)))
        have hNorm' : D' i=monomialPartAlong n A'.N (vanishingIdeal (n := n) (strictAlong T' (E.get i))) A'.E :=
          MonomialPartEtale.monomialPartAlong_congr restrictLe_restrictOn
            (restrictLe_self_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal (hH' i)))
        have hcRaw : (monomialPartAlong n A'.N
            (vanishingIdeal (n := n) (strictAlong T' (E.get i))) A'.E).IsCoherent := by
          rw [←hNorm']
          exact hcD' i
        have hSourceOne : (monomialPartAlong n A.N
            (vanishingIdeal (n := n) (strictAlong T (E.get i))) A.E).mem (π z) 1 := by
          rw [←hNorm]
          exact hInactiveUnit i (hImage hz) hNot
        have hNew := monomial_unit_off_centre hRecorded.1.1 (hH i).1 hBorn.1 hπ hcRaw hzC hSourceOne
        change (monomialPartAlong n A'.N (vanishingIdeal (n := n) (strictAlong T' (E.get i))) A'.E).mem z 1 at hNew
        rw [←hNorm'] at hNew
        exact hNew
    have hZero (j : Fin A'.E.length) : a' z i j=0 :=
      exponent_zero_of_one_mem (hNext.1.1.inter (hBorn'.1 _ (List.get_mem A'.E j))) hTargetUnit
    have hPos := (Finset.mem_filter.mp hi).2
    change 0 < ∑ j,a' z i j at hPos
    simp only [hZero,Finset.sum_const_zero] at hPos
    omega
  have hSourceSupport (j : Fin old.length) :
      preparedSupport A.N old A.E (Sum.inl j)=S ⟨j.val,by simpa only [old,List.length_map] using j.isLt⟩ := by
    let i : Fin E.length := ⟨j.val,by simpa only [old,List.length_map] using j.isLt⟩
    have hji : old.get j=strictAlong T (E.get i) := by simp [old,i]
    change A.N ∩ (nonmonomialPartAlong n A.N
      (restrictOn n A.N (vanishingIdeal (n := n) (old.get j))) A.E).zeroLocus=S i
    rw [hji,(hRecorded.2.2.2.2 i).2.2.1]
  have hTargetSupport (j : Fin old'.length) :
      preparedSupport A'.N old' A'.E (Sum.inl j)=π ⁻¹' S ⟨j.val,by simpa only [old',List.length_map] using j.isLt⟩ := by
    let i : Fin E.length := ⟨j.val,by simpa only [old',List.length_map] using j.isLt⟩
    have hji : old'.get j=strictAlong T' (E.get i) := by simp [old',i]
    change A'.N ∩ (nonmonomialPartAlong n A'.N
      (restrictOn n A'.N (vanishingIdeal (n := n) (old'.get j))) A'.E).zeroLocus=π ⁻¹' S i
    rw [hji,(hRows i).2.2.1,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hRows i).1.1]
    apply inter_eq_right.mpr
    intro y hy
    exact subset_closure ⟨hy.1,fun hyC => Set.disjoint_left.mp (hDisjoint i) hyC hy⟩
  have hPreparedNext : ∀ z ∈ A'.N,IsPreparedResidualSNCAt A'.N old' A'.E z := by
    intro z hz
    by_cases hzC : π z ∈ C
    · apply prepared_when_residuals_absent hn hBorn' hNext.2.2.1 hz
      intro j hj
      rw [hTargetSupport j] at hj
      exact Set.disjoint_left.mp (hDisjoint _) hzC hj
    · have hOldMap : old'=old.map (BlowupStrictSubmanifold.geoStrictTransform π C) := by
        simp only [old',old,List.map_map]
        rfl
      have hSuppMap : ∀ j : Fin (old.map (BlowupStrictSubmanifold.geoStrictTransform π C)).length,
          preparedSupport A'.N (old.map (BlowupStrictSubmanifold.geoStrictTransform π C)) A'.E (Sum.inl j)=
            π ⁻¹' S ⟨j.val,by simpa only [List.length_map,old,List.length_map] using j.isLt⟩ := by
        intro j
        let i : Fin E.length := ⟨j.val,by simpa only [List.length_map,old,List.length_map] using j.isLt⟩
        have hji : (old.map (BlowupStrictSubmanifold.geoStrictTransform π C)).get j=
            strictAlong T' (E.get i) := by
          simp [old,i,List.get_eq_getElem]
          rfl
        change A'.N ∩ (nonmonomialPartAlong n A'.N
          (restrictOn n A'.N (vanishingIdeal (n := n)
            ((old.map (BlowupStrictSubmanifold.geoStrictTransform π C)).get j))) A'.E).zeroLocus=π ⁻¹' S i
        rw [hji,(hRows i).2.2.1,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hRows i).1.1]
        apply inter_eq_right.mpr
        intro y hy
        exact subset_closure ⟨hy.1,fun hyC => Set.disjoint_left.mp (hDisjoint i) hyC hy⟩
      have hSupports : let N' := BlowupStrictSubmanifold.geoStrictTransform π C A.N
          let old' := old.map (BlowupStrictSubmanifold.geoStrictTransform π C)
          let born' := A.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
          ∀ i : Fin old'.length,
            preparedSupport N' old' born' (Sum.inl i)=π ⁻¹'
              preparedSupport A.N old A.E (Sum.inl ⟨i.val,by simpa [old'] using i.isLt⟩) := by
        change ∀ j : Fin (old.map (BlowupStrictSubmanifold.geoStrictTransform π C)).length,
          preparedSupport A'.N (old.map (BlowupStrictSubmanifold.geoStrictTransform π C)) A'.E (Sum.inl j)=
            π ⁻¹' preparedSupport A.N old A.E (Sum.inl ⟨j.val,by simpa only [List.length_map] using j.isLt⟩)
        intro j
        rw [hSuppMap j,hSourceSupport]
      have hResult := prepared_off_centre hRecorded.1.1 hBorn.1 hπ hSupports hn hzC
        (hPrepared (π z) (hImage hz))
      rw [hOldMap]
      exact hResult
  refine ⟨hCNC,hSharp,hDisjoint,hTest,hTestFull,?_,?_,?_,hPreparedNext⟩
  · intro i
    exact ⟨(hRows i).1,(hRows i).2.1,(hRows i).2.2.1,(hRows i).2.2.2.1,(hRows i).2.2.2.2.1⟩
  · intro z hz i
    exact (hRows i).2.2.2.2.2 z hz
  · intro z hz
    exact ⟨hActive z hz,(Finset.card_le_card (hActive z hz)).trans (hBound (π z) (hImage hz))⟩

end
end Hironaka.HironakaG4ProcessedSupportHighCountStep


/-! Public access to the existing private proof; no strengthened statement. -/
namespace Hironaka.HironakaG4ProcessedSupportHighCountStep

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualFiniteChronologicalHistory
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaSharpOriginalMultiBoundaryBadLocus NormalCrossings
  RelativePrincipalizationSpan RestrictedIdealExtension DivisorExponentAlong
  MonomialPartAlong GermIdealOrder MarkedIdeals MarkedIdeals.MarkedIdeal
  MonomialCaseAlong MonomialCase MonomialInvariant InvertibleIdealQuotient
  HironakaSharpNormalCrossingsOpenLocus BlowupFlatCoordinates MarkedIdealOperationsAlong
variable {n : ℕ} {X Y Z : CMfd.{u} n}

theorem actual_original_high_count_step_geometry
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
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let J := fun i : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    let S := fun i : Fin E.length => A.N ∩ (J i).zeroLocus
    let D := fun i : Fin E.length => monomialPartAlong n A.N
      (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
    let sumP : GermIdeal n Y := ⟨fun x g =>
      IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n Y := ⟨A.N,A.E,sumP,1⟩
    let a := fun x i j => divExpAlong n A.N (D i) (A.E.get j) x
    ResolutionInvariantSpec.IsInvDomain (n+1) M ∧
      ∀ (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),M.IsAdmissibleCentre C →
        HasNormalCrossings n C (old ++ A.E) ∧
        C ⊆ originalSharpBadLocus (n := n) A.N (old ++ A.E) ∧
        (∀ i : Fin E.length,Disjoint C (S i)) ∧
        (∀ i ∈ P,C ⊆ strictAlong T (E.get i)) ∧
        (∀ i : Fin E.length,i ∉ P → Disjoint C (strictAlong T (E.get i))) ∧
        (∀ x ∈ C,properRows (a x)=P ∧ ∀ i : Fin E.length,(J i).mem x 1) ∧
        IsGeoTestTower (geometricTemplate W []) (BlowupTower.step T C π hπ) ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) (BlowupTower.step T C π hπ) :=
  original_high_count_step_geometry (Z := Z) hn hW hE hdense T hT hFull hOrd hNC hDenseS P hP hBound

end
end Hironaka.HironakaG4ProcessedSupportHighCountStep
