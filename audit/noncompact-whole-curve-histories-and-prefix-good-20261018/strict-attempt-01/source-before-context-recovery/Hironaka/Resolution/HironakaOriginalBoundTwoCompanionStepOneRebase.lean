/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalBoundTwoStepOneRepresentative
import Hironaka.Resolution.HironakaOriginalBoundTwoStepOneEmptyPrefix
import Hironaka.Resolution.HironakaOriginalFiniteOrderCutMiddleHistory
/-! Concrete original companion geometry and genuine avoided-middle histories
supply changed-reference TESTs and StepOne cuts before every numerical law. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalBoundTwoCompanionStepOneRebase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealEquivalence.MarkedIdeal InvDomainRebase InvDomainTowerAlong InvDomainCompanion
  CompanionRebase CompanionOpen GeneralCompare NonmonomialOrderLocal RestrictEmptyTower
  StepOneLowerDomain HomogenizedIdealAlong NonmonomialOrderRegime NonmonomialOrderTail CanonicalCentres HironakaOriginalFrozenRecursiveLower
  HironakaOriginalFiniteLevelCutLowerTests HironakaOriginalFiniteStepOneCutMaskAvoidance
  HironakaOriginalEmptyPrefixLevelCutTransport HironakaOriginalRelativeIdealLevelCut
  HironakaOriginalBoundTwoStepOneEmptyPrefix HironakaOriginalBoundTwoStepOneRepresentative
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual original geometry constructs the WHOLE comparison and source
coherence. No changed-reference geometry or equality is an input. -/
private theorem actual_geometry (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain 2 M) (q : ℕ) (hq : 1≤q)
    (P : BlowupTower X Y) (hP : IsGeoTestTower M P)
    (hAvoid : CentresAvoid (ordMask M q) P) :
    let W := ordMask M q
    let J := MarkedIdeal.pullback (Subtype.val : W → X) (companionOf n M q)
    let R := restrict W P
    let N := MarkedIdeal.pullback (Subtype.val : openPreimage P W → Y)
      (companionOf n (geoTransformAlong M P) q)
    IsEmptyTower R ∧ IsInvDomain 2 J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsInvDomain 2 (geoTransformAlong J R) ∧
      IsMaximalOrderAlong (geoTransformAlong J R).N (geoTransformAlong J R).ideal
        (geoTransformAlong J R).d ∧
      N.ideal.IsCoherent ∧ RestrictEquiv (geoTransformAlong J R) N ∧ IsInvDomain 2 N := by
  dsimp only
  let W := ordMask M q
  let J := MarkedIdeal.pullback (Subtype.val : W → X) (companionOf n M q)
  let R := restrict W P
  let N := MarkedIdeal.pullback (Subtype.val : openPreimage P W → Y)
    (companionOf n (geoTransformAlong M P) q)
  have he : IsEmptyTower R := (isEmptyTower_restrict_iff W P).mpr hAvoid
  have hJ : IsInvDomain 2 J := isInvDomain_pullback_val_companionAlong hn hM W hq
  have hMax : IsMaximalOrderAlong J.N J.ideal J.d := by
    have h := isMaximalOrderAlong_compAt hn q (.refl : BlowupTower X X) hM
    rw [compAt_eq_pullback hn q .refl hM] at h
    exact h
  have hRt := isGeoTestTower_of_isEmptyTower J R he
  have hBase := isInvDomain_geoTransformAlong hJ R hRt
  have hBaseMax := isMaximalOrderAlong_geoTransformAlong hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hMax R hRt
  have hCurrent := isInvDomain_geoTransformAlong hM P hP
  have hN : IsInvDomain 2 N := isInvDomain_pullback_val_companionAlong hn hCurrent (openPreimage P W) hq
  have hEq := CompanionRebase.restrictEquiv_companionOf_rebase hn hM hq P hP W hAvoid
  exact ⟨he,hJ,hMax,hBase,hBaseMax,hN.isWellFormed.isCoherent,restrictEquiv_symm hEq,hN⟩

/-- Generic actual empty-prefix and relative-ideal composition isolates
only the genuine numerical proof from concrete companion elaboration. -/
private theorem actual_rebase_value (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X)
    (hJ : IsInvDomain 2 J) (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    (P : BlowupTower X Y) (he : IsEmptyTower P) (N : MarkedIdeal n Y)
    (hCN : N.ideal.IsCoherent) (hEq : RestrictEquiv (geoTransformAlong J P) N)
    (S : BlowupTower Y Z) (hS : IsLevelCutTower J (P.append S)) (z : Z)
    (hz : z∈(geoTransformAlong J (P.append S)).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J (P.append S) z=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) N S z := by
  have hPt := isGeoTestTower_of_isEmptyTower J P he
  have hBase := isInvDomain_geoTransformAlong hJ P hPt
  have hBaseMax := isMaximalOrderAlong_geoTransformAlong hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hMax P hPt
  have hLevel := level_cut_tail_of_empty_prefix J hJ.isWellFormed hJ.one_le_d P he S hS
  have hzBase : z∈(geoTransformAlong (geoTransformAlong J P) S).cosupp := by
    simpa only [geoTransformAlong_append] using hz
  exact (step_one_values_empty_prefix hn k J hJ hMax P he S hS z hz).trans
    (step_one_values_of_restrictEquiv hn k (geoTransformAlong J P) N hBase hCN
      hBaseMax hEq S hLevel z hzBase)

/-- The actual earlier level recipe supplies the later companion TEST,
current DOMAIN, ENTIRE cosupport, and unchanged StepOne at EVERY depth. -/
theorem companion_step_one_rebase_values (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain 2 M) (q : ℕ) (hq : 1≤q)
    (P : BlowupTower X Y) (hP : IsGeoTestTower M P)
    (hAvoid : CentresAvoid (ordMask M q) P)
    (S : BlowupTower (CMfd.of (n := n) (openPreimage P (ordMask M q))) Z)
    (hS : IsLevelCutTower (MarkedIdeal.pullback (Subtype.val : ordMask M q → X)
      (companionOf n M q)) ((restrict (ordMask M q) P).append S)) :
    let J := MarkedIdeal.pullback (Subtype.val : ordMask M q → X) (companionOf n M q)
    let N := MarkedIdeal.pullback (Subtype.val : openPreimage P (ordMask M q) → Y)
      (companionOf n (geoTransformAlong M P) q)
    IsInvDomain 2 N ∧ IsGeoTestTower N S ∧ IsInvDomain 2 (geoTransformAlong N S) ∧
      (geoTransformAlong J ((restrict (ordMask M q) P).append S)).cosupp=
        (geoTransformAlong N S).cosupp ∧
      ∀ (k : ℕ) (z : Z),z∈(geoTransformAlong J ((restrict (ordMask M q) P).append S)).cosupp →
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J
          ((restrict (ordMask M q) P).append S) z=
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) N S z := by
  dsimp only
  let J := MarkedIdeal.pullback (Subtype.val : ordMask M q → X) (companionOf n M q)
  let R := restrict (ordMask M q) P
  let N := MarkedIdeal.pullback (Subtype.val : openPreimage P (ordMask M q) → Y)
    (companionOf n (geoTransformAlong M P) q)
  obtain ⟨he,hJ,hMax,hBase,hBaseMax,hCN,hEq,hN⟩ := actual_geometry hn M hM q hq P hP hAvoid
  have hLevel := level_cut_tail_of_empty_prefix J hJ.isWellFormed hJ.one_le_d R he S hS
  have hLevelN := level_cut_of_restrictEquiv (geoTransformAlong J R) N
    hBase.isWellFormed hCN hEq S hLevel
  have hTest := levelCutTower_geoTest N S hLevelN
  have hWhole := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong
    hEq hBase.isWellFormed.isClosedSubmanifold_N.1 hBase.isWellFormed.isCoherent hCN S
  refine ⟨hN,hTest,isInvDomain_geoTransformAlong hN S hTest,?_,?_⟩
  · rw [geoTransformAlong_append]
    exact hWhole.1
  · intro k z hz
    exact actual_rebase_value hn k J hJ hMax R he N hCN hEq S hS z hz

/-- True earlier whole StepOne cuts construct the concrete later companion
cuts, using actual admissibility separately from all numeric comparisons. -/
theorem companion_step_one_rebase_cut (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X)
    (hM : IsInvDomain 2 M) (q : ℕ) (hq : 1≤q)
    (P : BlowupTower X Y) (hP : IsGeoTestTower M P)
    (hAvoid : CentresAvoid (ordMask M q) P)
    (S : BlowupTower (CMfd.of (n := n) (openPreimage P (ordMask M q))) Z)
    (hS : IsStepOneCutTower hn (k+1) (MarkedIdeal.pullback (Subtype.val : ordMask M q → X)
      (companionOf n M q)) ((restrict (ordMask M q) P).append S)) :
    IsStepOneCutTower hn (k+1)
      (MarkedIdeal.pullback (Subtype.val : openPreimage P (ordMask M q) → Y)
        (companionOf n (geoTransformAlong M P) q)) S := by
  let J := MarkedIdeal.pullback (Subtype.val : ordMask M q → X) (companionOf n M q)
  let R := restrict (ordMask M q) P
  let N := MarkedIdeal.pullback (Subtype.val : openPreimage P (ordMask M q) → Y)
    (companionOf n (geoTransformAlong M P) q)
  obtain ⟨he,hJ,hMax,hBase,hBaseMax,hCN,hEq,_hN⟩ := actual_geometry hn M hM q hq P hP hAvoid
  have hTail := step_one_cut_tail_empty_prefix hn k J hJ hMax R he S hS
  exact step_one_cut_of_restrictEquiv hn k (geoTransformAlong J R) N hBase hCN hBaseMax hEq S hTail

end
end Hironaka.HironakaOriginalBoundTwoCompanionStepOneRebase
