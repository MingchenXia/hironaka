/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneMemberCompanionMaskedPositiveValues
import Hironaka.Invariant.MonomialInvariantFunctorialAlong

/-! # Actual zero-order member values and both original masked alternatives

True finite current-boundary incidence and connected regular-component closure
internally produce constant actual along-exponents and an analytic discrete
monomial history exception. Whole actual member controlled identities identify
the SAME original masked General2 zero-order value with the whole gamma.
The original General3 consumer returns both positive and zero alternatives on
one genuine curve, plus its FULL original lower marked identity. Whole member
candidate testness, canonicality, maximum order and finite spectrum are never
inputs. Original level-zero contact, across-mask gluing and whole G3 remain
open. Blueprint: hironaka-step-one-member-masked-monomial-values-extension.tex.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneMemberMaskedMonomialValues
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  HironakaStepOneMemberLowerOrderPredicates HironakaStepOneMemberCompanionHistoryExtension
  HironakaStepOneMemberCompanionPositiveSpecialLoci HironakaStepOneMemberCompanionMaskedPositiveValues
  MarkedIdealBiholomorphism CanonicalCentres HironakaDimensionTwoStepOneAnalyticSuperlevels
  InvDomainMemberRestriction NonmonomialOrderLocal AnalyticDimensionBasics GlobalComponents
  HironakaCurveAnalyticPredicates NormalCrossings GeneralValue BoundaryCount
  DivisorExponentAlong MonomialCase MonomialCaseAlong MonomialInvariant MonomialStepAlong MonomialInvariantFunctorialAlong
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem isPreconnected_of_mem_globalComponents {A B : Set X}
    (hB : B ∈ globalComponents (n := n) A) : IsPreconnected B := by
  obtain ⟨c, _, rfl⟩ := hB
  exact isPreconnected_connectedComponentIn.closure

theorem divExpAlong_eq_on_globalComponent_of_subset (hn : 0 < n)
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed)
    (hne : ∀ x ∈ J.N, IsNonzeroAlongAt J.N J.ideal x)
    {Z B : Set X} (hZ : IsComplexAnalyticSubset (n := n) Z) (hZN : Z ⊆ J.N)
    (hB : B ∈ globalComponents (n := n) Z) (i : Fin J.E.length) (hBi : B ⊆ J.E.get i)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) :
    divExpAlong n J.N J.ideal (J.E.get i) x = divExpAlong n J.N J.ideal (J.E.get i) y := by
  have hBN : B ⊆ J.N := (subset_of_mem_globalComponents hZ hB).trans hZN
  apply (isPreconnected_of_mem_globalComponents hB).constant ?_ hx hy
  intro z hz
  have hev := eventually_divExpAlong_get_eq hn hJ.isClosedSubmanifold_N hJ.isSNCDivisor hJ.isTransverse
    hJ.isCoherent hne i (hBN hz) (hBi hz)
  have heq : (fun w => divExpAlong n J.N J.ideal (J.E.get i) w) =ᶠ[𝓝[B] z]
      (fun _ => divExpAlong n J.N J.ideal (J.E.get i) z) := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwB
    exact hw (hBN hwB) (hBi hwB)
  exact continuousWithinAt_const.congr_of_eventuallyEq heq rfl

theorem exists_analytic_dimzero_component_monomial_history (hn : 0 < n)
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed)
    (hne : ∀ x ∈ J.N, IsNonzeroAlongAt J.N J.ideal x)
    {Z : Set X} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdim : DimLE (n := n) Z 1)
    (hZN : Z ⊆ J.N) :
    ∃ E : Set X, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ x ∈ B \ E, ∀ y ∈ B \ E,
        gammaAlong n J.N J.ideal J.E J.d x = gammaAlong n J.N J.ideal J.E J.d y := by
  classical
  obtain ⟨E, hE, hdE, hEZ, hdict⟩ := exists_analytic_dimzero_predicate_exception hZ hdim
    (fun i : Fin J.E.length => J.E.get i)
    (fun i => AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (MonomialPart.isClosedSubmanifold_get hn hJ.isSNCDivisor i))
  refine ⟨E, hE, hdE, hEZ, ?_⟩
  intro B hB x hx y hy
  have hidx : memberIdx J.E x = memberIdx J.E y := by
    ext a
    simp only [mem_memberIdx]
    constructor
    · rintro ⟨ha, hxa⟩
      exact ⟨ha, (hdict B hB y hy ⟨a, ha⟩).mpr ((hdict B hB x hx ⟨a, ha⟩).mp hxa)⟩
    · rintro ⟨ha, hya⟩
      exact ⟨ha, (hdict B hB x hx ⟨a, ha⟩).mpr ((hdict B hB y hy ⟨a, ha⟩).mp hya)⟩
  unfold gammaAlong
  rw [hidx]
  apply inv_congr
  intro a ha
  obtain ⟨hlt, hya⟩ := (mem_memberIdx J.E).mp ha
  have hBi : B ⊆ J.E.get ⟨a, hlt⟩ := (hdict B hB y hy ⟨a, hlt⟩).mp hya
  simp only [expDataAlong, dif_pos hlt]
  exact divExpAlong_eq_on_globalComponent_of_subset hn J hJ hne hZ hZN hB ⟨a, hlt⟩ hBi hx.1 hy.1


def memberMaskedMonomialValues (hn : 0 < n) (m : MarkedIdeal n X)
    (S : Finset (Fin m.E.length)) (T : BlowupTower X Y) (U : Opens X) (Z E : Set Y) : Prop :=
  let I := memberRemainderMarked m S
  let L : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) I
  ∀ B ∈ globalComponents (n := n) Z,
    (∃ x ∈ B, nmOrd (geoTransformAlong I T) x = 0) →
    (∀ z : openPreimage T U, (z : Y) ∈ B \ E → z ∈ (geoTransformAlong L (restrict U T)).cosupp →
      (invFamily hn 2).inv L (restrict U T) z = toLex (0, toLex (Sum.inl (towerInvAlong I T (z : Y))))) ∧
    ∀ z : openPreimage T U, (z : Y) ∈ B \ E → z ∈ (geoTransformAlong L (restrict U T)).cosupp →
      ∀ w : openPreimage T U, (w : Y) ∈ B \ E → w ∈ (geoTransformAlong L (restrict U T)).cosupp →
        (invFamily hn 2).inv L (restrict U T) z = (invFamily hn 2).inv L (restrict U T) w ∧
          ∀ β : ValTy 2, (β ≤ (invFamily hn 2).inv L (restrict U T) z ↔
            β ≤ (invFamily hn 2).inv L (restrict U T) w)

private theorem positiveHistory_mono (m : MarkedIdeal n X)
    (S : Finset (Fin m.E.length)) (T : BlowupTower X Y) (Z E F : Set Y)
    (h : memberCompanionPositiveHistory m S T Z E) (hEF : E ⊆ F) :
    memberCompanionPositiveHistory m S T Z F := by
  intro B hB
  obtain ⟨q, hatt, hmin, hord, hrun, hpos⟩ := h B hB
  have hm : B \ F ⊆ B \ E := fun x hx => ⟨hx.1, fun he => hx.2 (hEF he)⟩
  exact ⟨q, hatt, hmin, fun x hx => hord x (hm hx),
    fun x hx y hy => hrun x (hm hx) y (hm hy),
    fun hq x hx y hy => hpos hq x (hm hx) y (hm hy)⟩

theorem exists_analytic_dimzero_member_masked_monomial_values (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (U : Opens X)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdim : DimLE (n := n) Z 1)
    (hsub : Z ⊆ (geoTransformAlong (memberRemainderMarked m S) T).N) :
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      memberCompanionPositiveHistory m S T Z E ∧ memberMaskedMonomialValues hn m S T U Z E := by
  dsimp only [memberMaskedMonomialValues]
  let I := memberRemainderMarked m S
  let L : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → X) I
  let J := geoTransformAlong I T
  let TU := restrict U T
  have hdJ := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS T hT
  have hmaskEq := geoTransformAlong_restrict_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS U T hT
  obtain ⟨Em, hEm, hdEm, hEmZ, hγ⟩ := exists_analytic_dimzero_component_monomial_history
    hn J hdJ.isWellFormed hdJ.isNonzeroAlongAt hZ hdim hsub
  obtain ⟨Eo, hEo, hdEo, hEoZ, hhist⟩ := exists_analytic_dimzero_member_companion_positive_history
    hn m h S hS T hT hZ hdim hsub
  obtain ⟨hE, hdE⟩ := analytic_dimzero_union hEm hdEm hEo hdEo
  let E := Em ∪ Eo
  refine ⟨E, hE, hdE, union_subset hEmZ hEoZ, positiveHistory_mono m S T Z Eo E hhist subset_union_right, ?_⟩
  intro B hB hatt0
  obtain ⟨q, _, hmin, hord, _, _⟩ := hhist B hB
  have hq : q = 0 := by
    obtain ⟨x, hx, hx0⟩ := hatt0
    have hq0 := hmin x hx
    rw [hx0] at hq0
    exact Nat.eq_zero_of_le_zero hq0
  subst q
  have hval : ∀ z : openPreimage T U, (z : Y) ∈ B \ E → z ∈ (geoTransformAlong L TU).cosupp →
      (invFamily hn 2).inv L TU z = toLex (0, toLex (Sum.inl (towerInvAlong I T (z : Y)))) := by
    intro z hz _hzcs
    have hz0 : nmOrd (geoTransformAlong L TU) z = 0 := by
      rw [hmaskEq]
      exact (nmOrd_pullback_val hn hdJ.isWellFormed hdJ.isNonzeroAlongAt _ z).trans
        (hord z ⟨hz.1, fun hh => hz.2 (Or.inr hh)⟩)
    have hγz : towerInvAlong L TU z = towerInvAlong I T (z : Y) := by
      unfold towerInvAlong
      rw [hmaskEq]
      exact gammaAlong_pullback_val J
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdJ.isWellFormed.isCoherent hg)
        (openPreimage T U) z J.d
    let lower := fun {V : CMfd.{u} n} (a : MarkedIdeal n V) {W : CMfd.{u} n}
      (R : BlowupTower V W) (p : W) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) a R p
    change genInv lower L TU z = _
    rw [genInv_of_nmOrd_eq_zero lower L TU hz0]
    exact congrArg (fun v => toLex (0, toLex (Sum.inl v))) hγz
  refine ⟨hval, ?_⟩
  intro z hz hzcs w hw hwcs
  have heq : (invFamily hn 2).inv L TU z = (invFamily hn 2).inv L TU w := by
    rw [hval z hz hzcs, hval w hw hwcs]
    exact congrArg (fun v => toLex (0, toLex (Sum.inl v)))
      (hγ B hB (z : Y) ⟨hz.1, fun hh => hz.2 (Or.inl hh)⟩ (w : Y) ⟨hw.1, fun hh => hw.2 (Or.inl hh)⟩)
  exact ⟨heq, fun β => by rw [heq]⟩


private theorem positiveValues_mono (hn : 0 < n) (m : MarkedIdeal n X)
    (S : Finset (Fin m.E.length)) (T : BlowupTower X Y) (U : Opens X) (Z E F : Set Y)
    (h : memberMaskedPositiveValues hn m S T U Z E) (hEF : E ⊆ F) :
    memberMaskedPositiveValues hn m S T U Z F := by
  intro B hB q hatt hmin hq
  obtain ⟨hv, heq⟩ := h B hB q hatt hmin hq
  have hm : B \ F ⊆ B \ E := fun x hx => ⟨hx.1, fun he => hx.2 (hEF he)⟩
  exact ⟨fun z hz hzcs => hv z (hm hz) hzcs,
    fun z hz hzcs w hw hwcs => heq z (hm hz) hzcs w (hm hw) hwcs⟩

private theorem monomialValues_mono (hn : 0 < n) (m : MarkedIdeal n X)
    (S : Finset (Fin m.E.length)) (T : BlowupTower X Y) (U : Opens X) (Z E F : Set Y)
    (h : memberMaskedMonomialValues hn m S T U Z E) (hEF : E ⊆ F) :
    memberMaskedMonomialValues hn m S T U Z F := by
  intro B hB hatt0
  obtain ⟨hv, heq⟩ := h B hB hatt0
  have hm : B \ F ⊆ B \ E := fun x hx => ⟨hx.1, fun he => hx.2 (hEF he)⟩
  exact ⟨fun z hz hzcs => hv z (hm hz) hzcs,
    fun z hz hzcs w hw hwcs => heq z (hm hz) hzcs w (hm hw) hwcs⟩

open HironakaGeneralThreeNonspecialAnalyticLoci HironakaCoherentTransformExtension InvDomainCompanion HomogenizedIdealAlong StepOneValue
  StepOneValueMasked StepOneRegime

theorem exists_actual_general_three_member_all_masked_values (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hnsp : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (hpos : 1 ≤ level (companionAt m T x) (companionTailAt m T x) p) :
    let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
    let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
      (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let J₀ := geoTransformAlong (barMarked K) H
    let S := membersThrough J₀.E (origMembers K H) p₀
    let I := memberRemainderMarked J₀ S
    let U := maskA K H p₀
    ∃ s : ℕ, level K R p = s+1 ∧ p₀ ∈ U ∧
      ∃ A E : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) A ∧ DimLE (n := n) A 1 ∧
        A ⊆ (geoTransformAlong I Q).N ∧ p ∈ A ∧
        IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ A ∧
        memberCompanionPositiveHistory J₀ S Q A E ∧
        MarkedIdeal.pullback (Subtype.val : U → (split R r).1) I = lowerMarked K (s+1) H p₀ ∧
        memberMaskedPositiveValues hn J₀ S Q U A E ∧
        memberMaskedMonomialValues hn J₀ S Q U A E := by
  dsimp only
  let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
  let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
    (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  let J₀ := geoTransformAlong (barMarked K) H
  let S := membersThrough J₀.E (origMembers K H) p₀
  let I := memberRemainderMarked J₀ S
  let U := maskA K H p₀
  obtain ⟨s, hs, hmask, A, Ep, hA, hdA, hsubA, hpA, hEp, hdEp, hEpA, hhist, hLinit, hvals⟩ :=
    exists_actual_general_three_member_masked_positive_values hn m h T hcan x hx hq p hp hnsp hpos
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcanK
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail (barMarked K) R r).mp hb.1
  have hpbar : p ∈ (geoTransformAlong (barMarked K) R).cosupp := by rw [hb.2.2]; exact hp
  have hreg := (StepOneValueMasked.stepRegime_and_mem_cosupp_head K hK.isWellFormed R hb.1 hpbar hnsp).1
  have hl : level K H p₀ = s+1 := hreg.1.trans hs
  have hdJ₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong (isInvDomain_barMarked K hK) H hhead
  have hE₀ : ∀ W ∈ origMembers K H, W ∈ J₀.E := fun W hW => List.mem_of_mem_take hW
  have hS : S.Nonempty := membersThrough_nonempty hE₀ (by change 1 ≤ level K H p₀; rw [hl]; omega)
  obtain ⟨Ez, hEz, hdEz, hEzA, _hzhist, hzero⟩ := exists_analytic_dimzero_member_masked_monomial_values
    hn J₀ hdJ₀ S hS Q htail U hA hdA hsubA
  obtain ⟨hE, hdE⟩ := analytic_dimzero_union hEp hdEp hEz hdEz
  let E := Ep ∪ Ez
  exact ⟨s, hs, hmask, A, E, hA, hdA, hsubA, hpA, hE, hdE, union_subset hEpA hEzA,
    positiveHistory_mono J₀ S Q A Ep E hhist subset_union_left, hLinit,
    positiveValues_mono hn J₀ S Q U A Ep E hvals subset_union_left,
    monomialValues_mono hn J₀ S Q U A Ez E hzero subset_union_right⟩

end
end Hironaka.HironakaStepOneMemberMaskedMonomialValues
