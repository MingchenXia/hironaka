/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneCurveHistoryPredicates
import Hironaka.Invariant.MemberRestrictCosupportExact

/-!
# Entire actual positive-level member lower datum and exact literal mask identity

Genuine locally finite unselected components refine the real SNC member
intersection. Actual coherence and thin cosupport internally produce nonzero
along this entire lower carrier; no caller lower domain or nonzero certificate.
The global datum restricts exactly to the original literal positive-level
lowerMarked. Original domain3/constructed invFamily3 canonical inputs produce
this extension at the actual computed regimeRun head and real mask point.
Full controlled tail extension, zero-level contact and whole General3/G3 remain open.
Blueprint: `hironaka-step-one-member-lower-extension.tex`.
-/


set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneMemberLowerExtension
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism CoefficientIdealRestriction
  InvDomainMemberRestriction GermIdealOrder DivisorExponentAlong BoundaryCount GiraudAlong CodimOneSupportAlong
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneSpecialAnalyticLoci
  GlobalComponents RegularLocusComponent AnalyticDimensionBasics
  NormalCrossings HomogenizedIdealAlong StepOneValue StepOneLowerDomain
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka

noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual closed selected components make the genuine remaining carrier locally equal to the original. -/
theorem eventually_mem_remainingComponents_iff {H A : Set X}
    (hH : IsClosedSubmanifold n H) {x : X}
    (hx : x ∈ remainingComponents (n := n) H A) :
    ∀ᶠ y in 𝓝 x, y ∈ remainingComponents (n := n) H A ↔ y ∈ H := by
  rw [remainingComponents_eq_diff_selected hH] at hx ⊢
  filter_upwards [(isClosedSubmanifold_selectedComponents hH A).1.isOpen_compl.mem_nhds hx.2] with y hy
  exact and_iff_left hy

/-- Finite genuine coherent generators and thin actual cosupport internally produce nonzero along. -/
theorem isNonzeroAlongAt_of_thin_cosupport {H : Set X} {I : GermIdeal n X} {d : ℕ}
    (hI : I.IsCoherent)
    (hthin : ∀ O : Set X, IsOpen O → O ∩ H ⊆ cosupport n H I d → O ∩ H = ∅)
    {x : X} (hx : x ∈ H) : IsNonzeroAlongAt H I x := by
  by_contra hnz
  have hz := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt hI hnz
  obtain ⟨O, hOz, hO, hxO⟩ := mem_nhds_iff.mp hz
  have he := hthin O hO (by
    intro z hzz
    exact ⟨hzz.2, fun g hg => ⟨fun _ => 0, zero_mem_idealPow _ z d, hOz hzz.1 g hg⟩⟩)
  have hxOH : x ∈ O ∩ H := ⟨hxO, hx⟩
  rw [he] at hxOH
  exact hxOH

/-- The entire true coefficient/member datum on actual unselected smooth carrier components. -/
def memberRemainderMarked (m : MarkedIdeal n X) (S : Finset (Fin m.E.length)) : MarkedIdeal n X :=
  withN (memberRestrict m S)
    (remainingComponents (n := n) (m.N ∩ memberInter m.E S) m.cosupp)

/-- Use the real head barMarked transform and actual original membersThrough, with no supplied lower datum. -/
def memberLowerExtension (m : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) : MarkedIdeal n Y :=
  memberRemainderMarked (geoTransformAlong (barMarked m) T)
    (membersThrough (geoTransformAlong (barMarked m) T).E (origMembers m T) y)

private theorem cosupp_memberRemainderMarked (m : MarkedIdeal n X)
    (hw : m.IsWellFormed) (hd : 1 ≤ m.d) (S : Finset (Fin m.E.length)) (hn : 0 < n) :
    (memberRemainderMarked m S).cosupp = m.cosupp ∩ (memberRemainderMarked m S).N := by
  let H := m.N ∩ memberInter m.E S
  have hH : IsClosedSubmanifold n H :=
    MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hw.isClosedSubmanifold_N.1 hw.isSNCDivisor hw.isTransverse S
  have hsub : (memberRemainderMarked m S).N ⊆ H := by
    rw [memberRemainderMarked, withN_N, remainingComponents_eq_diff_selected hH]
    exact sdiff_subset
  have hR := cosupp_memberRestrict hw hd S
  ext x
  constructor
  · rintro ⟨hxN, hxord⟩
    have hev := eventually_mem_remainingComponents_iff hH hxN
    have hxH : x ∈ (memberRestrict m S).cosupp := by
      refine ⟨hsub hxN, fun g hg => ?_⟩
      obtain ⟨f, hf, hgf⟩ := hxord g hg
      refine ⟨f, hf, ?_⟩
      filter_upwards [hev, hgf] with z hz hgz hzH
      exact hgz (hz.mpr hzH)
    rw [hR] at hxH
    exact ⟨hxH.1, hxN⟩
  · rintro ⟨hxA, hxN⟩
    have hxH : x ∈ (memberRestrict m S).cosupp := by
      rw [hR]
      exact ⟨hxA, (hsub hxN).2⟩
    exact ⟨hxN, fun g hg => (hxH.2 g hg).mono_set hsub⟩

/-- Genuine SNC dimension drop, local component geometry and actual thin cosupport prove every lower domain field. -/
theorem isInvDomain_memberRemainderMarked (hn : 0 < n) (m : MarkedIdeal n X)
    (hw : m.IsWellFormed) (hd : 1 ≤ m.d) {k : ℕ}
    (hDim : ResolutionInvariantSpec.DimLE n m.N k)
    (S : Finset (Fin m.E.length)) (hS : S.Nonempty) :
    IsInvDomain (k-1) (memberRemainderMarked m S) := by
  let H := m.N ∩ memberInter m.E S
  have hH : IsClosedSubmanifold n H :=
    MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hw.isClosedSubmanifold_N.1 hw.isSNCDivisor hw.isTransverse S
  have hA : IsComplexAnalyticSubset (n := n) m.cosupp :=
    isComplexAnalyticSubset_cosupport_along hw.isCoherent hw.isClosedSubmanifold_N hd
  have hR := isWellFormed_memberRestrict hn hw S
  have hRN := isClosedSubmanifold_remainingComponents hH m.cosupp
  have hsub : (memberRemainderMarked m S).N ⊆ H := by
    rw [memberRemainderMarked, withN_N, remainingComponents_eq_diff_selected hH]
    exact sdiff_subset
  have hdimH := dimLE_memberRestrict hn hw hS hDim
  have hdimR : ResolutionInvariantSpec.DimLE n (memberRemainderMarked m S).N (k-1) := by
    intro x hx
    obtain ⟨j, hxR⟩ := hRN.2 x hx
    obtain ⟨d, hd, hxH⟩ := hdimH x (hsub hx)
    exact ⟨j, (BlowupStrictSubmanifold.le_of_regularAtDim_subset hxR hxH hsub).trans hd, hxR⟩
  have htr : IsTransverse n (memberRemainderMarked m S).N (memberRemainderMarked m S).E := by
    apply CodimOneAdmissibleAlong.isTransverse_of_forall_eventually
    intro x hx
    exact ⟨H, hsub hx, eventually_mem_remainingComponents_iff hH hx, hR.isTransverse⟩
  have hcs := cosupp_memberRemainderMarked m hw hd S hn
  have hthin := thin_inter_remainingComponents hH hA
  refine ⟨⟨hRN, hR.isCoherent, hR.isSNCDivisor, htr⟩, hdimR, one_le_memberRestrict_d m S, ?_⟩
  intro x hx
  apply isNonzeroAlongAt_of_thin_cosupport (d := (memberRemainderMarked m S).d) hR.isCoherent
  · intro O hO hOA
    apply hthin O hO
    change O ∩ (memberRemainderMarked m S).N ⊆ m.cosupp ∩ (memberRemainderMarked m S).N
    rw [← hcs]
    exact hOA
  · exact hx

/-- Original true domain and positive actual indexed count internally construct the entire lower domain. -/
theorem isInvDomain_memberLowerExtension (hn : 0 < n) (m : MarkedIdeal n X)
    {k : ℕ} (h : IsInvDomain k m) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked m) T) (y : Y) (hpos : 1 ≤ level m T y) :
    IsInvDomain (k-1) (memberLowerExtension m T y) := by
  have hJ := isWellFormed_barMarked m h.isWellFormed
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T hT
  have hdT : 1 ≤ (geoTransformAlong (barMarked m) T).d := by
    rw [d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hdimT := InvDomainTowerAlong.dimLE_geoTransformAlong hJ.isClosedSubmanifold_N
    hJ.isCoherent h.dimLE T hT
  have hE₀ : ∀ H ∈ origMembers m T, H ∈ (geoTransformAlong (barMarked m) T).E :=
    fun H hH => List.mem_of_mem_take hH
  have hS := membersThrough_nonempty hE₀ hpos
  exact isInvDomain_memberRemainderMarked hn _ hwT hdT hdimT _ hS

private theorem carrier_memberLowerExtension_on_mask (hn : 0 < n) (m : MarkedIdeal n X)
    (hw : m.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked m) T)
    (y₀ : Y) {s : ℕ} (hl : level m T y₀ = s+1) {z : Y}
    (hz : z ∈ maskA m T y₀) :
    z ∈ (memberLowerExtension m T y₀).N ↔
      z ∈ (memberRestrict (geoTransformAlong (barMarked m) T)
        (membersThrough (geoTransformAlong (barMarked m) T).E (origMembers m T) y₀)).N := by
  classical
  let J := geoTransformAlong (barMarked m) T
  let E₀ := origMembers m T
  let S := membersThrough J.E E₀ y₀
  let H := J.N ∩ memberInter J.E S
  have hJ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong (isWellFormed_barMarked m hw) T hT
  have hH : IsClosedSubmanifold n H :=
    MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hJ.isClosedSubmanifold_N.1 hJ.isSNCDivisor hJ.isTransverse S
  have hE₀ : ∀ H ∈ E₀, H ∈ J.E := fun H hH => List.mem_of_mem_take hH
  have hmem := memberInter_membersThrough hE₀ y₀
  change z ∈ remainingComponents (n := n) H J.cosupp ↔ z ∈ H
  rw [remainingComponents_eq_diff_selected hH]
  refine ⟨fun h => h.1, fun hzH => ⟨hzH, ?_⟩⟩
  intro hzsel
  have hselA : selectedComponents (n := n) H J.cosupp ⊆ J.cosupp := by
    rintro w ⟨B, ⟨_, hBA⟩, hwB⟩
    exact hBA hwB
  have hnotrem : z ∉ remainingComponents (n := n) H J.cosupp := by
    rw [remainingComponents_eq_diff_selected hH]
    exact fun h => h.2 hzsel
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ H → w ∈ J.cosupp := by
    filter_upwards [(isClosedSubmanifold_remainingComponents hH J.cosupp).1.isOpen_compl.mem_nhds hnotrem] with w hw hwH
    apply hselA
    by_contra hnot
    exact hw (by rw [remainingComponents_eq_diff_selected hH]; exact ⟨hwH, hnot⟩)
  have hzS : ∀ H ∈ E₀, y₀ ∈ H → z ∈ H := by
    have ht := hzH.2
    rw [hmem] at ht
    exact ht
  have hinc : ∀ H ∈ E₀, z ∈ H ↔ y₀ ∈ H := fun H hH =>
    ⟨fun hzH => (interior_subset hz).1 H hH hzH, hzS H hH⟩
  have hlev : level m T z = level m T y₀ := MemberInterLocusAlong.boundaryCount_eq_of_forall_iff hinc
  have hzL : z ∈ MemberInterLocusAlong.memberInterLocus J.N E₀ J.cosupp := by
    rw [MemberInterLocusAlong.mem_memberInterLocus_iff]
    refine ⟨hselA hzsel, ?_⟩
    filter_upwards [hnear] with w hw hwN hwE
    apply hw
    refine ⟨hwN, ?_⟩
    rw [hmem]
    exact fun H hH hyH => hwE H hH ((hinc H hH).mpr hyH)
  exact (interior_subset hz).2 ⟨hlev, Or.inr ⟨by rw [hlev, hl]; omega, hzL⟩⟩

/-- Selected actual components would force forbidden same-level member specialness on the literal mask. -/
theorem pullback_memberLowerExtension_eq_lowerMarked_succ (hn : 0 < n) (m : MarkedIdeal n X)
    (hw : m.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked m) T)
    (y : Y) {s : ℕ} (hl : level m T y = s+1) :
    MarkedIdeal.pullback (Subtype.val : maskA m T y → Y) (memberLowerExtension m T y) =
      lowerMarked m (s+1) T y := by
  change MarkedIdeal.pullback (Subtype.val : maskA m T y → Y) (memberLowerExtension m T y) =
    MarkedIdeal.pullback (Subtype.val : maskA m T y → Y)
      (memberRestrict (geoTransformAlong (barMarked m) T)
        (membersThrough (geoTransformAlong (barMarked m) T).E (origMembers m T) y))
  unfold MarkedIdeal.pullback
  congr 1
  ext z
  exact carrier_memberLowerExtension_on_mask hn m hw T hT y hl z.2

open StepOneRegime HironakaGeneralThreeNonspecialAnalyticLoci
open Hironaka.ResolutionInvariantSpec (IsCanonical)

private theorem regime_at_run_start_of_current (P : Regime X) (T : BlowupTower X Y)
    (y : Y) (hy : P T y) :
    P (head T (regimeRun P T y)) ((tail T (regimeRun P T y)).proj y) := by
  by_cases hr : regimeRun P T y = 0
  · rw [hr]
    cases T <;> exact hy
  · exact regime_head_of_le_regimeRun P T y _ (by omega) le_rfl

/-- Original constructed General3 canonical inputs produce the actual run-head lower domain and exact mask identity. -/
theorem exists_actual_companion_member_lower_extension (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((CanonicalCentres.invFamily hn 3).inv m) T)
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
    let p₀ := (tail R r).proj p
    ∃ s : ℕ, level K R p = s+1 ∧ p₀ ∈ maskA K H p₀ ∧
      IsInvDomain 2 (memberLowerExtension K H p₀) ∧
      MarkedIdeal.pullback (Subtype.val : maskA K H p₀ → (split R r).1)
        (memberLowerExtension K H p₀) = lowerMarked K (s+1) H p₀ := by
  dsimp only
  let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
  let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
    (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let p₀ := (tail R r).proj p
  obtain ⟨_, hK, hmax, hcanK, _⟩ :=
    actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (CanonicalCentres.invFamily hn 2)
    K hK hmax hn R hcanK
  have hreg := regime_at_run_start_of_current (stepRegime K (level K R p)) R p ⟨rfl, hnsp⟩
  have hposK : 1 ≤ level K R p := hpos
  obtain ⟨s, hs⟩ : ∃ s : ℕ, level K R p = s+1 := ⟨level K R p - 1, by omega⟩
  have hregS : stepRegime K (s+1) H p₀ := by
    rw [← hs]
    exact hreg
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail (barMarked K) R r).mp hb.1
  have hwhead := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked K hK.isWellFormed) H hhead
  have hphead : p₀ ∈ (geoTransformAlong (barMarked K) H).cosupp := by
    apply proj_mem_cosupp_of_mem_cosupp hwhead.isClosedSubmanifold_N hwhead.isCoherent (tail R r) htail
    rw [← geoTransformAlong_head_tail]
    rw [hb.2.2]
    exact hp
  have hmask := (mem_lowerMask_and_isInvDomain K hK.isWellFormed hK.one_le_d hn hmax hK.dimLE
    H hhead hphead hregS).1
  have hdom := isInvDomain_memberLowerExtension hn K hK H hhead p₀ (by rw [hregS.1]; omega)
  have heq := pullback_memberLowerExtension_eq_lowerMarked_succ hn K hK.isWellFormed H hhead p₀ hregS.1
  exact ⟨s, hs, hmask, hdom, heq⟩

end
end Hironaka.HironakaStepOneMemberLowerExtension
