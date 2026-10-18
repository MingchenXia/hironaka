/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCoherentCompanionCountOpenNaturality
/-! Actual selected smooth component and coefficient codimension-one ideals
present the SAME whole original masked StepOne special-reset thresholds.
Source-first complete blueprint precedes code. Full arbitrary recursive lower
and higher-special semicoherent comparison / global scheduler remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCoherentSpecialResetIdeal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaOriginalCoherentHistoryYearIdeal HironakaOriginalCoherentCompanionCountIdeal
  HironakaOriginalStepOneHistoryYearAnalytic HironakaStepOneSpecialAnalyticLoci
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  NormalCrossings SimultaneousNormalCrossings BoundaryCount RestrictedIdealExtension
  IdealWeightPowers HomogenizedIdealAlong StepOneValue StepOneLowerDomain CodimOneSupportAlong
  HironakaStepOneMemberLowerExtension CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y : CMfd.{u} n}

private theorem hol_of_coherent {I : GermIdeal n X} (h : I.IsCoherent) :
    ∀ x g,I.mem x g → HolomorphicAt n g x :=
  fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h hg

private theorem zeroLocus_sumIdeal {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    (sumIdeal I J).zeroLocus = I.zeroLocus ∩ J.zeroLocus := by
  ext x
  constructor
  · intro hx
    exact ⟨fun g hg => hx g (le_sumIdeal_left hI x g hg),fun g hg => hx g (le_sumIdeal_right hJ x g hg)⟩
  · rintro ⟨hxI,hxJ⟩ g hg
    obtain ⟨_,N,s,a,hs,_,he⟩ := hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _hi
    rcases hs i with hi | hi
    · rw [hxI _ hi,mul_zero]
    · rw [hxJ _ hi,mul_zero]

private theorem mem_product_zeroLocus (L : List (GermIdeal n X))
    (hL : ∀ I ∈ L,I.IsCoherent) (x : X) :
    x ∈ (idealListProduct L).zeroLocus ↔ ∃ I ∈ L,x ∈ I.zeroLocus := by
  induction L with
  | nil =>
    constructor
    · intro hx
      exact False.elim (one_ne_zero (hx (fun _ => 1) (holomorphicAt_const 1)))
    · rintro ⟨I,hI,_⟩
      simp at hI
  | cons I L ih =>
    rw [idealListProduct,HironakaEffectiveDivisorSum.zeroLocus_mul_eq_union
      (hL I (List.mem_cons_self)) (isCoherent_idealListProduct L (fun J hJ => hL J (List.mem_cons_of_mem I hJ)))]
    constructor
    · rintro (hx | hx)
      · exact ⟨I,List.mem_cons_self,hx⟩
      · obtain ⟨J,hJ,hxJ⟩ := (ih (fun J hJ => hL J (List.mem_cons_of_mem I hJ))).mp hx
        exact ⟨J,List.mem_cons_of_mem I hJ,hxJ⟩
    · rintro ⟨J,hJ,hxJ⟩
      rcases List.mem_cons.mp hJ with rfl | hJ
      · exact Or.inl hxJ
      · exact Or.inr ((ih (fun J hJ => hL J (List.mem_cons_of_mem I hJ))).mpr ⟨J,hJ,hxJ⟩)

/-- Actual selected global components of EVERY indexed SNC intersection, with true finite ideal product. -/
def memberInterComponentIdeal (N : Set X) (E : List (Set X)) (A : Set X) : GermIdeal n X :=
  idealListProduct ((Finset.univ : Finset (Finset (Fin E.length))).toList.map
    (fun S => vanishingIdeal (n := n) (selectedComponents (n := n) (N ∩ memberInter E S) A)))

private theorem member_component_factors_coherent (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (htr : IsTransverse n N E) (A : Set X) :
    ∀ I ∈ (Finset.univ : Finset (Finset (Fin E.length))).toList.map
      (fun S => vanishingIdeal (n := n) (selectedComponents (n := n) (N ∩ memberInter E S) A)),I.IsCoherent := by
  intro I hI
  obtain ⟨S,_hS,rfl⟩ := List.mem_map.mp hI
  exact VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_selectedComponents
    (MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hN.1 hE htr S) A)

/-- TRUE original SNC geometry constructs coherence before any desired member-locus dictionary. -/
theorem isCoherent_memberInterComponentIdeal (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (htr : IsTransverse n N E) (A : Set X) :
    (memberInterComponentIdeal N E A).IsCoherent :=
  isCoherent_idealListProduct _ (member_component_factors_coherent hn hN hE htr A)

/-- The actual component product cuts out the SAME original whole member-intersection locus. -/
theorem zeroLocus_memberInterComponentIdeal (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (htr : IsTransverse n N E)
    {A : Set X} (hA : IsComplexAnalyticSubset (n := n) A) (hAN : A ⊆ N) :
    (memberInterComponentIdeal N E A).zeroLocus = MemberInterLocusAlong.memberInterLocus N E A := by
  rw [memberInterLocus_eq_componentUnion hn N hN E hE htr hA hAN]
  ext x
  rw [memberInterComponentIdeal,mem_product_zeroLocus _ (member_component_factors_coherent hn hN hE htr A) x]
  constructor
  · rintro ⟨I,hI,hx⟩
    obtain ⟨S,_hS,rfl⟩ := List.mem_map.mp hI
    rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (isClosedSubmanifold_selectedComponents
      (MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hN.1 hE htr S) A).1] at hx
    exact mem_iUnion.mpr ⟨S,hx⟩
  · intro hx
    obtain ⟨S,hS⟩ := mem_iUnion.mp hx
    refine ⟨_,List.mem_map.mpr ⟨S,Finset.mem_toList.mpr (Finset.mem_univ S),rfl⟩,?_⟩
    rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (isClosedSubmanifold_selectedComponents
      (MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hN.1 hE htr S) A).1]
    exact hS

/-- SAME actual original coefficient cosupport and indexed original level defining factors. -/
def stepOneLevelBaselineIdeal (m : MarkedIdeal n X) (T : BlowupTower X Y) (s : ℕ) : GermIdeal n Y :=
  let J := geoTransformAlong (barMarked m) T
  sumIdeal (carrierOrderIdeal J.N J.ideal J.d) (indexedBoundaryCountIdeal (origMembers m T) s)

private theorem actual_coefficient_geometry (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T) :
    (geoTransformAlong (barMarked m) T).IsWellFormed ∧
      1 ≤ (geoTransformAlong (barMarked m) T).d ∧
      IsMaximalOrderAlong (geoTransformAlong (barMarked m) T).N
        (geoTransformAlong (barMarked m) T).ideal (geoTransformAlong (barMarked m) T).d ∧
      IsSNCDivisor n (origMembers m T) ∧
      IsTransverse n (geoTransformAlong (barMarked m) T).N (origMembers m T) ∧
      (geoTransformAlong (barMarked m) T).cosupp = (geoTransformAlong m T).cosupp := by
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) (invFamily hn k) m h hmax hn T hc
  have hm := isWellFormed_barMarked m h.isWellFormed
  have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hm T hb.1
  refine ⟨hw,?_,isMaximalOrderAlong_geoTransformAlong hm.isClosedSubmanifold_N hm.isCoherent
    (isMaximalOrderAlong_barMarked m h.isWellFormed h.one_le_d hmax) T hb.1,
    NormalCrossingsComparison.isSNCDivisor_of_sublist hw.isSNCDivisor (List.take_sublist _ _),
    NormalCrossingsComparison.isTransverse_of_forall_mem hw.isTransverse (fun H hH => List.take_subset _ _ hH),hb.2.2⟩
  rw [d_geoTransformAlong]
  exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _

/-- Original-only maximal order and canonical history construct the WHOLE genuine baseline dictionary. -/
theorem original_stepOneLevelBaselineIdeal_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T) (s : ℕ) :
    (stepOneLevelBaselineIdeal m T s).IsCoherent ∧
      (stepOneLevelBaselineIdeal m T s).zeroLocus = {y | y ∈ (geoTransformAlong m T).cosupp ∧ s ≤ level m T y} := by
  obtain ⟨hw,_hd,_hmax,hE,_htr,hEq⟩ := actual_coefficient_geometry hn m h hmax T hc
  have hA := isCoherent_carrierOrderIdeal hw.isClosedSubmanifold_N hw.isCoherent (geoTransformAlong (barMarked m) T).d
  have hB := isCoherent_indexedBoundaryCountIdeal hn hE s
  refine ⟨isCoherent_sumIdeal hA hB,?_⟩
  rw [stepOneLevelBaselineIdeal,zeroLocus_sumIdeal hA hB,
    zeroLocus_carrierOrderIdeal hw.isClosedSubmanifold_N hw.isCoherent,
    zeroLocus_indexedBoundaryCountIdeal hn hE s]
  change (geoTransformAlong (barMarked m) T).cosupp ∩ {y | s ≤ level m T y} = _
  rw [hEq]
  rfl

/-- Actual whole higher-level baseline, codimension-one and selected-member equations. -/
def stepOneSpecialResetIdeal (m : MarkedIdeal n X) (T : BlowupTower X Y) : ℕ → GermIdeal n Y
  | 0 => (stepOneLevelBaselineIdeal m T 1).mul
      (vanishingIdeal (n := n) (codimOnePartAlong (geoTransformAlong (barMarked m) T).N
        (geoTransformAlong (barMarked m) T).ideal (geoTransformAlong (barMarked m) T).d))
  | s+1 => (stepOneLevelBaselineIdeal m T (s+2)).mul
      (sumIdeal (memberInterComponentIdeal (geoTransformAlong (barMarked m) T).N (origMembers m T)
        (geoTransformAlong (barMarked m) T).cosupp) (indexedBoundaryCountIdeal (origMembers m T) (s+1)))

/-- ONLY genuine original inputs supply whole coherence and BOTH exact actual special-reset branches. -/
theorem original_stepOneSpecialResetIdeal_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T) (s : ℕ) :
    (stepOneSpecialResetIdeal m T s).IsCoherent ∧
      (stepOneSpecialResetIdeal m T s).zeroLocus = stepOneSpecialResetLocus m T s := by
  obtain ⟨hw,hd,hmaxT,hE,htr,hEq⟩ := actual_coefficient_geometry hn m h hmax T hc
  have hA := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hw.isCoherent hw.isClosedSubmanifold_N hd
  cases s with
  | zero =>
    have hZ := isClosedSubmanifold_codimOnePartAlong hw.isCoherent hw.isClosedSubmanifold_N hd hmaxT
    have hZI := VanishingIdealCoherent.isCoherent_vanishingIdeal hZ
    obtain ⟨hB,hBeq⟩ := original_stepOneLevelBaselineIdeal_dictionary hn m h hmax T hc 1
    refine ⟨isCoherent_mul hB hZI,?_⟩
    rw [stepOneSpecialResetIdeal,HironakaEffectiveDivisorSum.zeroLocus_mul_eq_union hB hZI,
      hBeq,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hZ.1]
    ext y
    constructor
    · rintro (⟨hy,hpos⟩ | hz)
      · exact ⟨hy,Or.inl hpos⟩
      · have hy : y ∈ (geoTransformAlong m T).cosupp := hEq ▸ codimOnePartAlong_subset hz
        refine ⟨hy,?_⟩
        by_cases hzero : level m T y=0
        · exact Or.inr ⟨hzero.symm,Or.inl ⟨hzero,hz⟩⟩
        · exact Or.inl (Nat.pos_of_ne_zero hzero)
    · rintro ⟨hy,hpos | ⟨he,hsp⟩⟩
      · exact Or.inl ⟨hy,hpos⟩
      · rcases hsp with ⟨_hzero,hz⟩ | ⟨hpositive,_hl⟩
        · exact Or.inr hz
        · omega
  | succ s =>
    obtain ⟨hB,hBeq⟩ := original_stepOneLevelBaselineIdeal_dictionary hn m h hmax T hc (s+2)
    have hM := isCoherent_memberInterComponentIdeal hn hw.isClosedSubmanifold_N hE htr (geoTransformAlong (barMarked m) T).cosupp
    have hC := isCoherent_indexedBoundaryCountIdeal hn hE (s+1)
    refine ⟨isCoherent_mul hB (isCoherent_sumIdeal hM hC),?_⟩
    rw [stepOneSpecialResetIdeal,HironakaEffectiveDivisorSum.zeroLocus_mul_eq_union hB (isCoherent_sumIdeal hM hC),
      hBeq,zeroLocus_sumIdeal hM hC,zeroLocus_memberInterComponentIdeal (A := (geoTransformAlong (barMarked m) T).cosupp) hn hw.isClosedSubmanifold_N hE htr
        hA (geoTransformAlong (barMarked m) T).cosupp_subset_N,zeroLocus_indexedBoundaryCountIdeal hn hE (s+1)]
    ext y
    constructor
    · rintro (⟨hy,hpos⟩ | ⟨hl,hle⟩)
      · exact ⟨hy,Or.inl (by omega)⟩
      · have hy : y ∈ (geoTransformAlong m T).cosupp := hEq ▸ hl.1
        refine ⟨hy,?_⟩
        change s+1 ≤ level m T y at hle
        rcases hle.lt_or_eq with hlt | he
        · exact Or.inl hlt
        · exact Or.inr ⟨he,Or.inr ⟨by omega,hl⟩⟩
    · rintro ⟨hy,hpos | ⟨he,hsp⟩⟩
      · exact Or.inl ⟨hy,by omega⟩
      · rcases hsp with ⟨hzero,_hz⟩ | ⟨_hpositive,hl⟩
        · omega
        · exact Or.inr ⟨hl,by change s+1 ≤ level m T y; omega⟩


/-- The SAME actual coherent reset equations present the literal ENTIRE original masked top threshold. -/
theorem original_stepOneSpecialResetIdeal_top_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T) (s : ℕ) :
    (stepOneSpecialResetIdeal m T s).IsCoherent ∧
      (stepOneSpecialResetIdeal m T s).zeroLocus =
        {y | y ∈ (geoTransformAlong m T).cosupp ∧
          toLex (s,(⊤ : WithTop (ValTy k))) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m T y} := by
  obtain ⟨hI,hZ⟩ := original_stepOneSpecialResetIdeal_dictionary hn m h hmax T hc s
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) (invFamily hn k) m h hmax hn T hc
  refine ⟨hI,?_⟩
  rw [hZ]
  ext y
  constructor
  · rintro ⟨hy,hr⟩
    have hybar : y ∈ (geoTransformAlong (barMarked m) T).cosupp := by rwa [hb.2.2]
    exact ⟨hy,(stepOneInvM_top_threshold_iff (invFamily hn k) hn m h.isWellFormed h.one_le_d hmax T hb.1 hybar s).mpr hr⟩
  · rintro ⟨hy,hv⟩
    have hybar : y ∈ (geoTransformAlong (barMarked m) T).cosupp := by rwa [hb.2.2]
    exact ⟨hy,(stepOneInvM_top_threshold_iff (invFamily hn k) hn m h.isWellFormed h.one_le_d hmax T hb.1 hybar s).mp hv⟩

/-- Actual finite coherent functions give BOTH nearby ideal-span and literal whole reset-zero directions. -/
theorem exists_original_stepOneSpecialResetIdeal_generators (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T)
    (s : ℕ) (x : Y) :
    ∃ U : Set Y,IsOpen U ∧ x ∈ U ∧ ∃ (N : ℕ) (a : Fin N → Y → ℂ),
      (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (a i) U) ∧
      (∀ y ∈ U,∀ g,(stepOneSpecialResetIdeal m T s).mem y g ↔ IsInSpanAt (n := n) (· ∈ range a) y g) ∧
      ∀ y ∈ U,y ∈ stepOneSpecialResetLocus m T s ↔ ∀ i,a i y=0 := by
  obtain ⟨hI,hZ⟩ := original_stepOneSpecialResetIdeal_dictionary hn m h hmax T hc s
  obtain ⟨U,hU,hxU,N,a,ha,hgen⟩ := hI x
  refine ⟨U,hU,hxU,N,a,ha,hgen,?_⟩
  intro y hy
  rw [← hZ]
  constructor
  · intro hz i
    have hol : HolomorphicAt n (a i) y := eventually_of_mem (hU.mem_nhds hy)
      (fun z hz => (ha i z hz).mdifferentiableAt (hU.mem_nhds hz))
    apply hz (a i)
    apply (hgen y hy (a i)).mpr
    exact isInSpanAt_of_eq_mul ⟨i,rfl⟩ hol (holomorphicAt_const 1)
      (Eventually.of_forall fun z => (one_mul (a i z)).symm)
  · intro hz g hg
    obtain ⟨_,M,t,b,ht,_,he⟩ := (hgen y hy g).mp hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _hi
    obtain ⟨j,hj⟩ := ht i
    rw [← hj,hz j,mul_zero]

private theorem interior_original_cosupp_eq_empty {m : MarkedIdeal n Y} (h : IsInvDomain k m) :
    interior m.cosupp = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨g,hg,hfreq⟩ := h.isNonzeroAlongAt x (m.cosupp_subset_N (interior_subset hx))
  have hmem := HomogenizedGlueing.eventually_mem h.isWellFormed.isCoherent hg
  obtain ⟨z,⟨hzN,hzg⟩,hzgmem,hzO⟩ := (hfreq.and_eventually (hmem.and (isOpen_interior.mem_nhds hx))).exists
  have hzcs := interior_subset hzO
  have hhol := hol_of_coherent h.isWellFormed.isCoherent z g hzgmem
  exact hzg ((GermIdealOrder.vanishesToOrderOn_one_iff hzN hhol).mp ((hzcs.2 g hzgmem).mono h.one_le_d))

/-- WHOLE ambient carrier, SAME current original SNC list and true actual special-reset ideal, mark one. -/
def stepOneSpecialResetMarked (m : MarkedIdeal n X) (T : BlowupTower X Y) (s : ℕ) : MarkedIdeal n Y :=
  ⟨univ,(geoTransformAlong m T).E,stepOneSpecialResetIdeal m T s,1⟩

/-- Original inputs internally construct actual nonzero and every SAME-boundary ambient marked-domain field. -/
theorem original_stepOneSpecialResetMarked_isInvDomain (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (hmax : IsMaximalOrderAlong m.N m.ideal m.d)
    (T : BlowupTower X Y) (hc : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) m) T) (s : ℕ) :
    IsInvDomain n (stepOneSpecialResetMarked m T s) := by
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1) (invFamily hn k) m h hmax hn T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hb.2.1
  obtain ⟨hI,hZ⟩ := original_stepOneSpecialResetIdeal_dictionary hn m h hmax T hc s
  have hi : interior (stepOneSpecialResetIdeal m T s).zeroLocus = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hm := interior_mono (show (stepOneSpecialResetIdeal m T s).zeroLocus ⊆ (geoTransformAlong m T).cosupp from
      fun z hz => (hZ ▸ hz).1) hy
    rw [interior_original_cosupp_eq_empty hd] at hm
    exact hm
  have hN : IsClosedSubmanifold n (univ : Set Y) :=
    ⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
  refine ⟨⟨hN,hI,hd.isWellFormed.isSNCDivisor,isTransverse_univ_of_isSNCDivisor hd.isWellFormed.isSNCDivisor⟩,
    (fun x _ => ⟨n,le_rfl,AnalyticIrreducibleComponents.regularAtDim_univ x⟩),le_rfl,?_⟩
  intro x hx
  apply isNonzeroAlongAt_of_thin_cosupport (d := 1) hI
  · intro O hO hOA
    change O ∩ univ ⊆ GermIdealOrder.cosupport n univ (stepOneSpecialResetIdeal m T s) 1 at hOA
    change O ∩ univ = ∅
    rw [inter_univ] at hOA ⊢
    rw [GermIdealOrder.cosupport_one (hol_of_coherent hI),univ_inter] at hOA
    have hsub : O ⊆ interior (stepOneSpecialResetIdeal m T s).zeroLocus := by
      rw [← hO.interior_eq]
      exact interior_mono hOA
    rw [hi] at hsub
    exact eq_empty_iff_forall_notMem.mpr (fun y hy => hsub hy)
  · exact hx

end
end Hironaka.HironakaOriginalCoherentSpecialResetIdeal
