/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneSeqLowerValueExact
import Hironaka.Resolution.HironakaStepOneMemberHeadIncidence
import Hironaka.Resolution.HironakaStepOneMemberMaskedMonomialValues

/-! # Original positive lower values across actual reference masks

Genuine finite head/selection configurations internally produce reference
points and actual canonical masked lower records. Whole head incidence,
true intermediate global components, and both positive/zero component-own
lower value dictionaries give one analytic dimension-zero exception. Outside
it the ORIGINAL Seq lowerValue and entire Step1 value agree across different
actual basepoints on every genuine curve component. The original Gen3
consumer constructs the actual companion/canonical tail/curve internally.
No caller mask, lower canonicality, family or value certificate is used.
Original Step1 level-zero contact and whole General3/G3 remain OPEN.
Blueprint: hironaka-step-one-member-across-mask-values-extension.tex.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneMemberAcrossMaskValues
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  StepOneValue StepOneLowerDomain StepOneRegime HomogenizedIdealAlong InvDomainMemberRestriction
  MarkedIdealBiholomorphism GlobalComponents RegularLocusComponent AnalyticDimensionBasics
  HironakaStepOneMemberHeadIncidence HironakaStepOneMemberLowerExtension
  HironakaStepOneMemberTailExtension HironakaStepOneMemberLowerOrderPredicates
  HironakaStepOneMemberCompanionMaskedPositiveValues HironakaStepOneMemberMaskedMonomialValues
  HironakaStepOneMemberCompanionPositiveSpecialLoci HironakaStepOneMemberCompanionHistoryExtension
  HironakaCurveAnalyticPredicates HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaCoherentTransformExtension CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem mem_globalComponents_of_subset {Z A B : Set Y}
    (hZ : IsComplexAnalyticSubset (n := n) Z)
    (hB : B ∈ globalComponents (n := n) Z) (hBA : B ⊆ A) (hAZ : A ⊆ Z) :
    B ∈ globalComponents (n := n) A := by
  obtain ⟨c, ⟨k, hc⟩, rfl⟩ := hB
  let C := component (n := n) Z c
  have hreg : ∀ y ∈ C, RegularAtDim (n := n) A y k := by
    intro y hy
    obtain ⟨W, hW, hyW, hWC⟩ := exists_open_inter_subset_component hc hy
    apply RegularPointDimension.regularAtDim_of_inter_eq hW hyW ?_
      (regularAtDim_of_mem_component hc hy)
    exact Subset.antisymm (fun z hz => ⟨hBA (subset_closure (hWC hz)), hz.2⟩)
      (fun z hz => ⟨hAZ hz.1, hz.2⟩)
  have hcA := hreg c (mem_component_self hc)
  have hCD : C ⊆ component (n := n) A c :=
    subset_component_of_isPreconnected isPreconnected_connectedComponentIn
      (fun y hy => ⟨k, hreg y hy⟩) ⟨c, mem_component_self hc, mem_component_self hcA⟩
  have hBa := isComplexAnalyticSubset_closure_component hZ hc
  obtain ⟨W, hW, hcW, hWC⟩ := exists_open_inter_subset_component hc (mem_component_self hc)
  have hDB : component (n := n) A c ⊆ closure C :=
    component_subset_of_isOpen hBa hW ⟨c, hcW, mem_component_self hcA⟩
      (fun y hy => subset_closure (hWC ⟨hAZ (component_subset A c hy.2), hy.1⟩))
  have he : closure C = closure (component (n := n) A c) :=
    (closure_mono hCD).antisymm (closure_minimal hDB isClosed_closure)
  rw [he]
  exact closure_component_mem_globalComponents hcA

private theorem incidence_of_membersThrough_eq (m : MarkedIdeal n X) (T : BlowupTower X Y)
    (p q : Y)
    (hS : membersThrough (geoTransformAlong (barMarked m) T).E (origMembers m T) p =
      membersThrough (geoTransformAlong (barMarked m) T).E (origMembers m T) q) :
    ∀ W ∈ origMembers m T, p ∈ W ↔ q ∈ W := by
  intro W hW
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_of_mem_take hW)
  have hm : i ∈ membersThrough (geoTransformAlong (barMarked m) T).E (origMembers m T) p ↔
      i ∈ membersThrough (geoTransformAlong (barMarked m) T).E (origMembers m T) q := by rw [hS]
  simpa only [mem_membersThrough, hi, and_iff_right hW] using hm

private theorem level_eq_of_membersThrough_eq (m : MarkedIdeal n X) (T : BlowupTower X Y)
    (p q : Y)
    (hS : membersThrough (geoTransformAlong (barMarked m) T).E (origMembers m T) p =
      membersThrough (geoTransformAlong (barMarked m) T).E (origMembers m T) q) :
    level m T p = level m T q := by
  classical
  unfold level BoundaryCount.boundaryCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact incidence_of_membersThrough_eq m T p q hS _ (List.get_mem _ i)

theorem maskA_eq_of_membersThrough_eq (m : MarkedIdeal n X) (T : BlowupTower X Y)
    (p q : Y)
    (hS : membersThrough (geoTransformAlong (barMarked m) T).E (origMembers m T) p =
      membersThrough (geoTransformAlong (barMarked m) T).E (origMembers m T) q) :
    maskA m T p = maskA m T q := by
  have hc := incidence_of_membersThrough_eq m T p q hS
  have hl := level_eq_of_membersThrough_eq m T p q hS
  apply Opens.ext
  change interior {z | _} = interior {z | _}
  congr 1
  ext z
  simp only [mem_ofPred_eq, hl]
  constructor
  · rintro ⟨h, hns⟩
    exact ⟨fun W hW hzW => (hc W hW).mp (h W hW hzW), hns⟩
  · rintro ⟨h, hns⟩
    exact ⟨fun W hW hzW => (hc W hW).mpr (h W hW hzW), hns⟩

def positiveAcrossMaskValues (hn : 0 < n) (m : MarkedIdeal n X) (T : BlowupTower X Y)
    (Z E : Set Y) : Prop :=
  ∀ B ∈ globalComponents (n := n) Z, ∀ p ∈ B \ E, ∀ q ∈ B \ E,
    ¬ IsSpecial m T p → ¬ IsSpecial m T q → 1 ≤ level m T p → 1 ≤ level m T q →
    let rp := regimeRun (stepRegime m (level m T p)) T p
    let rq := regimeRun (stepRegime m (level m T q)) T q
    Seq.StepOneValue.lowerValue (invFamily hn 2) m (level m T p) (head T rp) (tail T rp) p =
      Seq.StepOneValue.lowerValue (invFamily hn 2) m (level m T q) (head T rq) (tail T rq) q ∧
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m T p =
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) m T q ∧
    ∀ α : WithTop (ValTy 2),
      (α ≤ Seq.StepOneValue.lowerValue (invFamily hn 2) m (level m T p) (head T rp) (tail T rp) p ↔
       α ≤ Seq.StepOneValue.lowerValue (invFamily hn 2) m (level m T q) (head T rq) (tail T rq) q)

private theorem positive_original_lower_data (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hnsp : ¬ IsSpecial K R p)
    (s : ℕ) (hs : level K R p = s+1) :
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    p₀ ∈ maskA K H p₀ ∧ IsInvDomain 2 (lowerMarked K (s+1) H p₀) ∧
      IsCanonical (lowerMarked K (s+1) H p₀) ((invFamily hn 2).inv (lowerMarked K (s+1) H p₀))
        (restrict (maskA K H p₀) Q) ∧
      (∀ z : openPreimage Q (maskA K H p₀),
        z ∈ (geoTransformAlong (lowerMarked K (s+1) H p₀) (restrict (maskA K H p₀) Q)).cosupp ↔
          (z : Y) ∈ (geoTransformAlong K R).cosupp ∧ level K R (z : Y) = s+1) ∧
      ∀ z : openPreimage Q (maskA K H p₀),
        z ∈ (geoTransformAlong (lowerMarked K (s+1) H p₀) (restrict (maskA K H p₀) Q)).cosupp →
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R (z : Y) =
          toLex (s+1, ((invFamily hn 2).inv (lowerMarked K (s+1) H p₀)
            (restrict (maskA K H p₀) Q) z : WithTop (ValTy 2))) := by
  dsimp only
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  let P : ℕ → Prop := fun a =>
    p₀ ∈ lowerMask K a H p₀ ∧ IsInvDomain 2 (StepOneValueMasked.lowerMarkedM K a H p₀) ∧
      IsCanonical (StepOneValueMasked.lowerMarkedM K a H p₀)
        ((invFamily hn 2).inv (StepOneValueMasked.lowerMarkedM K a H p₀))
        (restrict (lowerMask K a H p₀) Q) ∧
      (∀ z : openPreimage Q (lowerMask K a H p₀),
        z ∈ (geoTransformAlong (StepOneValueMasked.lowerMarkedM K a H p₀)
          (restrict (lowerMask K a H p₀) Q)).cosupp ↔
          (z : Y) ∈ (geoTransformAlong K R).cosupp ∧ level K R (z : Y) = a) ∧
      ∀ z : openPreimage Q (lowerMask K a H p₀),
        z ∈ (geoTransformAlong (StepOneValueMasked.lowerMarkedM K a H p₀)
          (restrict (lowerMask K a H p₀) Q)).cosupp →
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R (z : Y) =
          toLex (a, ((invFamily hn 2).inv (StepOneValueMasked.lowerMarkedM K a H p₀)
            (restrict (lowerMask K a H p₀) Q) z : WithTop (ValTy 2)))
  obtain ⟨hmask, hdom, hcanL, hdict⟩ :=
    HironakaDimensionThreeStepOneLowerAnalyticLoci.actual_lower_domain_and_cosupport_dictionary
      hn K hK hmax R hcan p hp hnsp
  have hd : P (level K R p) := ⟨hmask, hdom, hcanL, hdict,
    fun z hz => HironakaDimensionThreeStepOneLowerAnalyticLoci.stepOneInvM_eq_actual_fixed_lower
      hn K hK hmax R hcan p hp hnsp z hz⟩
  exact Eq.mp (congrArg P hs) hd

private theorem exists_analytic_dimzero_fixed_member_values (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (U : Opens X)
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S))
      ((invFamily hn 2).inv (MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S))) (restrict U T))
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdim : DimLE (n := n) Z 1)
    (hZN : Z ⊆ (geoTransformAlong (memberRemainderMarked m S) T).N) :
    let L : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S)
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ z : openPreimage T U, (z : Y) ∈ B \ E →
        z ∈ (geoTransformAlong L (restrict U T)).cosupp →
        ∀ w : openPreimage T U, (w : Y) ∈ B \ E → w ∈ (geoTransformAlong L (restrict U T)).cosupp →
          (invFamily hn 2).inv L (restrict U T) z = (invFamily hn 2).inv L (restrict U T) w := by
  dsimp only
  obtain ⟨Ep, hEp, hdEp, hEpZ, hhist, hpvals⟩ :=
    exists_analytic_dimzero_member_masked_positive_values hn m h S hS T hT U hcan hZ hdim hZN
  obtain ⟨Ez, hEz, hdEz, hEzZ, _, hzvals⟩ :=
    exists_analytic_dimzero_member_masked_monomial_values hn m h S hS T hT U hZ hdim hZN
  obtain ⟨hE, hdE⟩ := analytic_dimzero_union hEp hdEp hEz hdEz
  refine ⟨Ep ∪ Ez, hE, hdE, union_subset hEpZ hEzZ, ?_⟩
  intro B hB z hz hzcs w hw hwcs
  obtain ⟨q, hatt, hmin, _, _, _⟩ := hhist B hB
  by_cases hq : q = 0
  · subst q
    exact ((hzvals B hB hatt).2 z ⟨hz.1, fun hh => hz.2 (Or.inr hh)⟩ hzcs
      w ⟨hw.1, fun hh => hw.2 (Or.inr hh)⟩ hwcs).1
  · exact ((hpvals B hB q hatt hmin (Nat.one_le_iff_ne_zero.mpr hq)).2
      z ⟨hz.1, fun hh => hz.2 (Or.inl hh)⟩ hzcs
      w ⟨hw.1, fun hh => hw.2 (Or.inl hh)⟩ hwcs).1

private theorem exists_analytic_dimzero_reference_values (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hnsp : ¬ IsSpecial K R p)
    (hpos : 1 ≤ level K R p) {Z : Set Y}
    (hZ : IsComplexAnalyticSubset (n := n) Z) (hdZ : DimLE (n := n) Z 1)
    (hZA : Z ⊆ (geoTransformAlong K R).cosupp) :
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let U := maskA K H (Q.proj p)
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ z ∈ B \ E, ∀ w ∈ B \ E,
        Q.proj z ∈ U → Q.proj w ∈ U →
        level K R z = level K R p → level K R w = level K R p →
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R z =
            Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R w := by
  dsimp only
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hpos)
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  let J := geoTransformAlong (barMarked K) H
  let S := membersThrough J.E (origMembers K H) p₀
  let I := memberRemainderMarked J S
  let U := maskA K H p₀
  let L : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → (split R r).1) I
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail (barMarked K) R r).mp hb.1
  have hpbar : p ∈ (geoTransformAlong (barMarked K) R).cosupp := by rw [hb.2.2]; exact hp
  have hreg := (StepOneValueMasked.stepRegime_and_mem_cosupp_head K hK.isWellFormed R hb.1 hpbar hnsp).1
  have hl : level K H p₀ = s+1 := hreg.1.trans hs
  have hdJ := InvDomainTowerAlong.isInvDomain_geoTransformAlong (isInvDomain_barMarked K hK) H hhead
  have hE₀ : ∀ W ∈ origMembers K H, W ∈ J.E := fun W hW => List.mem_of_mem_take hW
  have hS : S.Nonempty := membersThrough_nonempty hE₀ (by change 1 ≤ level K H p₀; rw [hl]; omega)
  obtain ⟨hdI, hid⟩ := memberLowerExtension_tail_domain_and_mask_identity hn K hK H hhead p₀ hl Q htail
  have hinit : L = lowerMarked K (s+1) H p₀ :=
    pullback_memberLowerExtension_eq_lowerMarked_succ hn K hK.isWellFormed H hhead p₀ hl
  obtain ⟨_hmask, _hdL, hcanL, hdict, hfixed⟩ := positive_original_lower_data hn K hK hmax R hcan p hp hnsp s hs
  have hcanL' : IsCanonical L ((invFamily hn 2).inv L) (restrict U Q) := by rw [hinit]; exact hcanL
  let A : Set Y := Z ∩ (geoTransformAlong I Q).N
  have hA : IsComplexAnalyticSubset (n := n) A := hZ.inter
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hdI.isWellFormed.isClosedSubmanifold_N)
  have hdA : DimLE (n := n) A 1 := DimensionMonotone.DimLE.anti hZ inter_subset_left hdZ
  obtain ⟨Ev, hEv, hdEv, hEvA, hvalues⟩ := exists_analytic_dimzero_fixed_member_values
    hn J hdJ S hS Q htail U hcanL' hA hdA inter_subset_right
  obtain ⟨Ea, hEa, hdEa, hEaZ, hAdict⟩ := exists_analytic_dimzero_predicate_exception hZ hdZ
    (fun _ : Unit => A) (fun _ => hA)
  obtain ⟨hE, hdE⟩ := analytic_dimzero_union hEa hdEa hEv hdEv
  refine ⟨Ea ∪ Ev, hE, hdE, union_subset hEaZ (hEvA.trans inter_subset_left), ?_⟩
  intro B hB z hz w hw hzU hwU hlz hlw
  let zu : openPreimage Q U := ⟨z, hzU⟩
  let wu : openPreimage Q U := ⟨w, hwU⟩
  have hzcs : zu ∈ (geoTransformAlong (lowerMarked K (s+1) H p₀) (restrict U Q)).cosupp :=
    (hdict zu).mpr ⟨hZA (subset_of_mem_globalComponents hZ hB hz.1), hlz.trans hs⟩
  have hwcs : wu ∈ (geoTransformAlong (lowerMarked K (s+1) H p₀) (restrict U Q)).cosupp :=
    (hdict wu).mpr ⟨hZA (subset_of_mem_globalComponents hZ hB hw.1), hlw.trans hs⟩
  have hzN : z ∈ (geoTransformAlong I Q).N := by
    rw [hid] at hzcs
    exact hzcs.1
  have hzA : z ∈ A := ⟨subset_of_mem_globalComponents hZ hB hz.1, hzN⟩
  have hBA : B ⊆ A := (hAdict B hB z ⟨hz.1, fun h => hz.2 (Or.inl h)⟩ ()).mp hzA
  have hBAcomp := mem_globalComponents_of_subset hZ hB hBA inter_subset_left
  have hzL : zu ∈ (geoTransformAlong L (restrict U Q)).cosupp := by rw [hinit]; exact hzcs
  have hwL : wu ∈ (geoTransformAlong L (restrict U Q)).cosupp := by rw [hinit]; exact hwcs
  have heq := hvalues B hBAcomp zu ⟨hz.1, fun h => hz.2 (Or.inr h)⟩ hzL
    wu ⟨hw.1, fun h => hw.2 (Or.inr h)⟩ hwL
  change (invFamily hn 2).inv L (restrict U Q) zu = (invFamily hn 2).inv L (restrict U Q) wu at heq
  rw [hinit] at heq
  rw [hfixed zu hzcs, hfixed wu hwcs, heq]

private theorem actual_selection_reference_facts (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (p z : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hnsp : ¬ IsSpecial K R p)
    (hz : z ∈ (geoTransformAlong K R).cosupp) (hzns : ¬ IsSpecial K R z) (hzpos : 1 ≤ level K R z)
    (hr : regimeRun (stepRegime K (level K R z)) R z = regimeRun (stepRegime K (level K R p)) R p)
    (hS : membersThrough (geoTransformAlong (barMarked K) (head R (regimeRun (stepRegime K (level K R p)) R p))).E
        (origMembers K (head R (regimeRun (stepRegime K (level K R p)) R p)))
        ((tail R (regimeRun (stepRegime K (level K R p)) R p)).proj z) =
      membersThrough (geoTransformAlong (barMarked K) (head R (regimeRun (stepRegime K (level K R p)) R p))).E
        (origMembers K (head R (regimeRun (stepRegime K (level K R p)) R p)))
        ((tail R (regimeRun (stepRegime K (level K R p)) R p)).proj p)) :
    level K R z = level K R p ∧
      (tail R (regimeRun (stepRegime K (level K R p)) R p)).proj z ∈
        maskA K (head R (regimeRun (stepRegime K (level K R p)) R p))
          ((tail R (regimeRun (stepRegime K (level K R p)) R p)).proj p) := by
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
  have hpbar : p ∈ (geoTransformAlong (barMarked K) R).cosupp := by rw [hb.2.2]; exact hp
  have hzbar : z ∈ (geoTransformAlong (barMarked K) R).cosupp := by rw [hb.2.2]; exact hz
  have hpreg := (StepOneValueMasked.stepRegime_and_mem_cosupp_head K hK.isWellFormed R hb.1 hpbar hnsp).1
  have hzreg := (StepOneValueMasked.stepRegime_and_mem_cosupp_head K hK.isWellFormed R hb.1 hzbar hzns).1
  rw [hr] at hzreg
  have hl := level_eq_of_membersThrough_eq K _ _ _ hS
  have heq := hzreg.1.symm.trans (hl.trans hpreg.1)
  refine ⟨heq, ?_⟩
  have hhead := ((isGeoTestTower_iff_head_tail (barMarked K) R
    (regimeRun (stepRegime K (level K R p)) R p)).mp hb.1).1
  have hzmask := mem_maskA K hK.isWellFormed hK.one_le_d hn _ hhead
    (hzreg.1 ▸ hzpos) hzreg.2
  rwa [maskA_eq_of_membersThrough_eq K _ _ _ hS] at hzmask

private theorem stepOneInvM_eq_original_positive_lower (hn : 0 < n)
    (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y)
    (hns : ¬ IsSpecial K R p) (hpos : 1 ≤ level K R p) :
    let r := regimeRun (stepRegime K (level K R p)) R p
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R p =
      toLex (level K R p, Seq.StepOneValue.lowerValue (invFamily hn 2) K (level K R p)
        (head R r) (tail R r) p) := by
  dsimp only
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_neg hns]
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hpos)
  rw [hs]
  rfl

theorem exists_analytic_dimzero_across_mask_values (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdZ : DimLE (n := n) Z 1)
    (hZA : Z ⊆ (geoTransformAlong K R).cosupp) :
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      positiveAcrossMaskValues hn K R Z E := by
  classical
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
  have hZbar : Z ⊆ (geoTransformAlong (barMarked K) R).cosupp := by rw [hb.2.2]; exact hZA
  obtain ⟨Eh, hEh, hdEh, hEhZ, _, hhist⟩ := exists_analytic_dimzero_head_incidence_history_exception
    hn K hK.isWellFormed hK.one_le_d hmax R hb.1 hZ hdZ hZbar
  let C := (r : Fin (R.length+1)) × Finset (Fin (geoTransformAlong (barMarked K) (head R r)).E.length)
  let P : C → Prop := fun c => ∃ p : Y,
    p ∈ (geoTransformAlong K R).cosupp ∧ ¬ IsSpecial K R p ∧ 1 ≤ level K R p ∧
      regimeRun (stepRegime K (level K R p)) R p = c.1 ∧
      membersThrough (geoTransformAlong (barMarked K) (head R c.1)).E (origMembers K (head R c.1))
        ((tail R c.1).proj p) = c.2
  let J := {c : C // P c}
  have hp : ∀ c : J, ∃ p : Y,
    p ∈ (geoTransformAlong K R).cosupp ∧ ¬ IsSpecial K R p ∧ 1 ≤ level K R p ∧
      regimeRun (stepRegime K (level K R p)) R p = c.1.1 ∧
      membersThrough (geoTransformAlong (barMarked K) (head R c.1.1)).E (origMembers K (head R c.1.1))
        ((tail R c.1.1).proj p) = c.1.2 := fun c => c.2
  choose p hpcs hpns hppos hpr hpS using hp
  have hex : ∀ c : J, ∃ E : Set Y,
    IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ z ∈ B \ E, ∀ w ∈ B \ E,
        (tail R (regimeRun (stepRegime K (level K R (p c))) R (p c))).proj z ∈
          maskA K (head R (regimeRun (stepRegime K (level K R (p c))) R (p c)))
            ((tail R (regimeRun (stepRegime K (level K R (p c))) R (p c))).proj (p c)) →
        (tail R (regimeRun (stepRegime K (level K R (p c))) R (p c))).proj w ∈
          maskA K (head R (regimeRun (stepRegime K (level K R (p c))) R (p c)))
            ((tail R (regimeRun (stepRegime K (level K R (p c))) R (p c))).proj (p c)) →
        level K R z = level K R (p c) → level K R w = level K R (p c) →
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R z =
            Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K R w :=
    fun c => exists_analytic_dimzero_reference_values hn K hK hmax R hcan (p c) (hpcs c) (hpns c)
      (hppos c) hZ hdZ hZA
  choose D hD hdD hDZ hvalues using hex
  let Eu : Set Y := ⋃ c ∈ (Finset.univ : Finset J), D c
  obtain ⟨hEu, hdEu⟩ := analytic_dimzero_finset_union Finset.univ D (fun c _ => hD c) (fun c _ => hdD c)
  have hEuZ : Eu ⊆ Z := by
    intro z hz
    obtain ⟨c, _, hzc⟩ := mem_iUnion₂.mp hz
    exact hDZ c hzc
  obtain ⟨hE, hdE⟩ := analytic_dimzero_union hEh hdEh hEu hdEu
  refine ⟨Eh ∪ Eu, hE, hdE, union_subset hEhZ hEuZ, ?_⟩
  intro B hB z hz w hw hzns hwns hzpos hwpos
  have hzEh : z ∈ B \ Eh := ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
  have hwEh : w ∈ B \ Eh := ⟨hw.1, fun h => hw.2 (Or.inl h)⟩
  obtain ⟨_hlzw, hrzw, hinc⟩ := hhist B hB z hzEh w hwEh
  let rz : Fin (R.length+1) := ⟨regimeRun (stepRegime K (level K R z)) R z,
    by have hh := regimeRun_le_length (stepRegime K (level K R z)) R z; omega⟩
  let Sz := membersThrough (geoTransformAlong (barMarked K) (head R rz)).E
    (origMembers K (head R rz)) ((tail R rz).proj z)
  let c : C := ⟨rz, Sz⟩
  have hzcs := hZA (subset_of_mem_globalComponents hZ hB hz.1)
  have hwcs := hZA (subset_of_mem_globalComponents hZ hB hw.1)
  have hPc : P c := ⟨z, hzcs, hzns, hzpos, rfl, rfl⟩
  let i : J := ⟨c, hPc⟩
  have hzr : regimeRun (stepRegime K (level K R z)) R z =
      regimeRun (stepRegime K (level K R (p i))) R (p i) := (hpr i).symm
  have hwr : regimeRun (stepRegime K (level K R w)) R w =
      regimeRun (stepRegime K (level K R (p i))) R (p i) := hrzw.symm.trans hzr
  have hSzref : membersThrough (geoTransformAlong (barMarked K)
      (head R (regimeRun (stepRegime K (level K R (p i))) R (p i)))).E
      (origMembers K (head R (regimeRun (stepRegime K (level K R (p i))) R (p i))))
      ((tail R (regimeRun (stepRegime K (level K R (p i))) R (p i))).proj z) =
      membersThrough (geoTransformAlong (barMarked K)
      (head R (regimeRun (stepRegime K (level K R (p i))) R (p i)))).E
      (origMembers K (head R (regimeRun (stepRegime K (level K R (p i))) R (p i))))
      ((tail R (regimeRun (stepRegime K (level K R (p i))) R (p i))).proj (p i)) := by
    rw [hpr i]
    exact (hpS i).symm
  have hSwref : membersThrough (geoTransformAlong (barMarked K)
      (head R (regimeRun (stepRegime K (level K R (p i))) R (p i)))).E
      (origMembers K (head R (regimeRun (stepRegime K (level K R (p i))) R (p i))))
      ((tail R (regimeRun (stepRegime K (level K R (p i))) R (p i))).proj w) =
      membersThrough (geoTransformAlong (barMarked K)
      (head R (regimeRun (stepRegime K (level K R (p i))) R (p i)))).E
      (origMembers K (head R (regimeRun (stepRegime K (level K R (p i))) R (p i))))
      ((tail R (regimeRun (stepRegime K (level K R (p i))) R (p i))).proj (p i)) := by
    rw [hpr i]
    exact ((hinc rz).2.2.1).symm.trans (hpS i).symm
  obtain ⟨hlz, hzU⟩ := actual_selection_reference_facts hn K hK hmax R hcan (p i) z
    (hpcs i) (hpns i) hzcs hzns hzpos hzr hSzref
  obtain ⟨hlw, hwU⟩ := actual_selection_reference_facts hn K hK hmax R hcan (p i) w
    (hpcs i) (hpns i) hwcs hwns hwpos hwr hSwref
  have hzD : z ∈ B \ D i := ⟨hz.1, fun h => hz.2 (Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, h⟩))⟩
  have hwD : w ∈ B \ D i := ⟨hw.1, fun h => hw.2 (Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, h⟩))⟩
  have hv := hvalues i B hB z hzD w hwD hzU hwU hlz hlw
  have hvo := hv
  rw [stepOneInvM_eq_original_positive_lower hn K R z hzns hzpos,
    stepOneInvM_eq_original_positive_lower hn K R w hwns hwpos] at hvo
  have hlo := congrArg (fun v : ℕ ×ₗ WithTop (ValTy 2) => (ofLex v).2) hvo
  change Seq.StepOneValue.lowerValue (invFamily hn 2) K (level K R z)
      (head R (regimeRun (stepRegime K (level K R z)) R z))
      (tail R (regimeRun (stepRegime K (level K R z)) R z)) z =
    Seq.StepOneValue.lowerValue (invFamily hn 2) K (level K R w)
      (head R (regimeRun (stepRegime K (level K R w)) R w))
      (tail R (regimeRun (stepRegime K (level K R w)) R w)) w at hlo
  exact ⟨hlo, hv, fun α => by rw [hlo]⟩

open HironakaGeneralThreeNonspecialAnalyticLoci HironakaDimensionThreeStepOneCurveEnvelope

theorem exists_actual_general_three_companion_across_mask_values (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x) :
    let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
    let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
      (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
    ∃ Z : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) Z ∧
      DimLE (n := n) Z 1 ∧ Z ⊆ (geoTransformAlong K R).cosupp ∧
      (∀ p ∈ (geoTransformAlong K R).cosupp, ¬ IsSpecial K R p → p ∈ Z) ∧
      ∃ E : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) E ∧
        DimLE (n := n) E 0 ∧ E ⊆ Z ∧ positiveAcrossMaskValues hn K R Z E := by
  dsimp only
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  obtain ⟨Z, hZ, hdZ, hZA, hnsp⟩ := exists_actual_companion_dimone_nonspecial_envelope hn m h T hcan x hx hq
  obtain ⟨E, hE, hdE, hEZ, hvalues⟩ := exists_analytic_dimzero_across_mask_values
    (X := CMfd.of (n := n) (maskAt m T x)) (Y := CMfd.of (n := n) (patchAt m T x))
    hn (companionAt m T x) hK hmax (companionTailAt m T x) hcanK hZ hdZ hZA
  exact ⟨Z, hZ, hdZ, hZA, hnsp, E, hE, hdE, hEZ, hvalues⟩

end
end Hironaka.HironakaStepOneMemberAcrossMaskValues
