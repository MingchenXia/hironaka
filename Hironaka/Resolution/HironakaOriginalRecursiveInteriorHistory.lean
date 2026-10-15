/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalRecursiveBoundaryHistoryMap
import Hironaka.Resolution.HironakaOriginalStepOneCurveHistory
import Hironaka.Resolution.HironakaOriginalOuterShortFamily
/-! Whole original recursive interior identity-empty histories.
The complete five-node mathematical route preceded proofs. The natural-depth
history induction is constructed from genuine original canonical lower data. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalRecursiveInteriorHistory
noncomputable section
open Classical
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  MarkedIdealBiholomorphism BlowupTowerIsomorphism BlowupTowerIsoTail
  HironakaOriginalInteriorEmptyHistory HironakaOriginalCrossingLowerHistory
  HironakaOriginalCanonicalNormalizedLowerTail HironakaOriginalCrossingExactIndex
  HironakaOriginalInvariantEmptyInsertion HironakaOriginalShortUniformIndex
  HironakaOriginalRecursiveBoundaryHistoryMap HironakaOriginalOuterShortFamily
  HironakaOriginalGeneralCrossingHistory HironakaOriginalCrossingValueTransport
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail GeneralValue
  CompanionRebase CompanionReductionAlong
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- The true short future index is INITIAL in the actual canonical lower record;
no assertion that its entire prefix is empty is assumed or needed. -/
private theorem canonical_short_step_map_compatibility (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hshort : regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y<S.length) :
    recursiveStepShift k (M.E.length+H.length)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y)=
      historyStepShift k (M.E.length+H.length)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y) := by
  by_cases hsp : IsSpecial M (H.append S) y
  · unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hsp]
    rfl
  have hfacts := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) M hM hmax hn (H.append S) hcan
  have hbarcos : y∈(geoTransformAlong (barMarked M) (H.append S)).cosupp := hfacts.2.2.symm ▸ hy
  have hsc := (Seq.StepOneBridge.isCanonical_iff (k := k+1)
    (invFamily hn k) M hM hmax hn (H.append S)).mp hcan
  let ℓ := level M (H.append S) y
  let r := regimeRun (stepRegime M ℓ) (H.append S) y
  let K := head (H.append S) r
  let Q := tail (H.append S) r
  let p := Q.proj y
  let U := lowerMask M ℓ K p
  let J := lowerMarkedM M ℓ K p
  let c := M.E.length+H.length-ℓ
  have hd := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical M (k := k+1)
    (invFamily hn k) hM.isWellFormed hM.one_le_d hn hmax hM.dimLE (H.append S)
    hfacts.1 hsc y hbarcos hsp
  change ∃ hp : p∈U, IsInvDomain k J ∧
    IsCanonical J ((invFamily hn k).inv J) (restrict U Q) ∧
      (⟨y,hp⟩ : openPreimage Q U)∈(geoTransformAlong J (restrict U Q)).cosupp at hd
  obtain ⟨hp,hdom,hcanJ,hcosJ⟩ := hd
  have hK := (isGeoTestTower_iff_head_tail (barMarked M) (H.append S) r).mp hfacts.1 |>.1
  have hwhole : K.append Q=H.append S := head_append_tail (H.append S) r
  have hcurrent : stepRegime M ℓ (K.append Q) y := by rw [hwhole];exact ⟨rfl,hsp⟩
  have hreach : Q.length≤regimeRun (stepRegime M ℓ) (K.append Q) y := by
    rw [hwhole]
    change (tail (H.append S) r).length≤r
    rw [length_tail]
    exact Nat.min_le_left _ _
  have hbase := regime_at_base_of_reaching_run (stepRegime M ℓ) K Q y hcurrent hreach
  have hlen := original_lower_boundary_length_actual_level M hM.isWellFormed K hK p
  rw [hbase.1] at hlen
  have hKH : H.length≤K.length := by
    change H.length≤(head (H.append S) r).length
    rw [length_head,BlowupTower.length_append]
    change r<S.length at hshort
    omega
  have hc : c≤J.E.length := by change J.E.length=M.E.length+K.length-ℓ at hlen;dsimp only [c];omega
  have hv := original_canonical_family_initial_boundary_compatibility (X := CMfd.of (n := n) U)
    hn k J hdom (restrict U Q) hcanJ c hc (⟨y,hp⟩ : openPreimage Q U) hcosJ
  have hmasked : WithTop.map (recursiveHistoryShift k c)
      (Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) ℓ K Q y)=
    WithTop.map (shiftFamily k c)
      (Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) ℓ K Q y) := by
    rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
    simp only [WithTop.map_coe]
    exact congrArg (fun v : ValTy k => (v : WithTop (ValTy k))) hv
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_neg hsp]
  simp only [recursiveStepShift,historyStepShift,ofLex_toLex]
  exact congrArg (fun v : WithTop (ValTy k) => toLex (ℓ,v)) hmasked

/-- Actual OLD canonical inputs compute the whole recursive short value at ALL depths and levels. -/
theorem original_recursive_short_step_value (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hshort : regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y<S.length) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y=
      recursiveStepShift k (M.E.length+H.length)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y) := by
  have hbar := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) M hM hmax hn (H.append S) hcan).1
  exact (actual_entire_short_stepOne_value hn k M hM.isWellFormed H S hbar y hshort).trans
    (canonical_short_step_map_compatibility hn k M hM hmax H S hcan y hy hshort).symm

private def FamilyInteriorTransport (hn : 0<n) (k : ℕ) : Prop :=
  ∀ {X A Y : CMfd.{u} n} (M : MarkedIdeal n X), IsInvDomain k M →
    ∀ (H : BlowupTower X A) (S : BlowupTower A Y),
    IsCanonical M ((invFamily hn k).inv M) (H.append S) →
      IsCanonical M ((invFamily hn k).inv M) (interiorEmptyHistory H S) ∧
      ∀ y∈(geoTransformAlong M (H.append S)).cosupp,
        (invFamily hn k).inv M (interiorEmptyHistory H S) y=
          recursiveHistoryShift k (M.E.length+H.length) ((invFamily hn k).inv M (H.append S) y)

/-- The true preceding specific depth IH constructs NEW normalized CAN FIRST. -/
private theorem step_crossing_lower_of_family (hn : 0<n) (k : ℕ)
    (hFamily : FamilyInteriorTransport.{u} hn k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hns : ¬ IsSpecial M (H.append S) y)
    (hreach : S.length≤regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y) :
    let ℓ := level M (H.append S) y
    let r := regimeRun (stepRegime M ℓ) (H.append S) y
    let K := head H (r-S.length)
    let B := tail H (r-S.length)
    let W := lowerMask M ℓ K ((B.append S).proj y)
    let J := lowerMarkedM M ℓ K ((B.append S).proj y)
    ∃ (hp : (B.append S).proj y∈W) (hp' : (interiorEmptyHistory B S).proj y∈W),
      IsInvDomain k J ∧ IsCanonical J ((invFamily hn k).inv J) (restrict W (B.append S)) ∧
      IsCanonical J ((invFamily hn k).inv J) (restrict W (interiorEmptyHistory B S)) ∧
      (⟨y,hp⟩ : openPreimage (B.append S) W)∈(geoTransformAlong J (restrict W (B.append S))).cosupp ∧
      (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) W)∈
        (geoTransformAlong J (restrict W (interiorEmptyHistory B S))).cosupp ∧
      (invFamily hn k).inv J (restrict W (interiorEmptyHistory B S))
          (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) W)=
        recursiveHistoryShift k (J.E.length+B.length)
          ((invFamily hn k).inv J (restrict W (B.append S)) (⟨y,hp⟩ : openPreimage (B.append S) W)) := by
  dsimp only
  let ℓ := level M (H.append S) y
  let r := regimeRun (stepRegime M ℓ) (H.append S) y
  let K := head H (r-S.length)
  let B := tail H (r-S.length)
  let W := lowerMask M ℓ K ((B.append S).proj y)
  let J := lowerMarkedM M ℓ K ((B.append S).proj y)
  let B' := restrict W B
  let S' := restrict (openPreimage B W) S
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞
  let χ := opensCongr (n := n) (openPreimage_append B S W).symm
  have hd := original_canonical_crossing_normalized_lower_data hn k M hM hmax H S hcan y hy hns hreach
  change ∃ hp : (B.append S).proj y∈W,
    IsInvDomain k J ∧ IsCanonical J ((invFamily hn k).inv J) (restrict W (B.append S)) ∧
      IsCanonical J ((invFamily hn k).inv J) (B'.append S') ∧
      (⟨y,hp⟩ : openPreimage (B.append S) W)∈(geoTransformAlong J (restrict W (B.append S))).cosupp ∧
      χ ⟨y,hp⟩∈(geoTransformAlong J (B'.append S')).cosupp ∧
      (invFamily hn k).inv J (B'.append S') (χ ⟨y,hp⟩)=
        (invFamily hn k).inv J (restrict W (B.append S)) (⟨y,hp⟩ : openPreimage (B.append S) W) at hd
  obtain ⟨hp,hdom,hcanL,hcanN,hcosL,hcosN,hvold⟩ := hd
  let p : openPreimage (B.append S) W := ⟨y,hp⟩
  let q := χ p
  have hpull : MarkedIdeal.pullback Φ J=J := ContactCanonicalAlong.pullback_id J hdom.isWellFormed.isCoherent
  have hnew := hFamily (X := CMfd.of (n := n) W) J hdom B' S' hcanN
  have hcanNnew := hnew.1
  have htestN := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn k).isInvValue hdom (B'.append S') hcanN
  have hB' := (isGeoTestTower_append_iff J B' S').mp htestN |>.1
  have hcosNnew : q∈(geoTransformAlong J (interiorEmptyHistory B' S')).cosupp := by
    rw [(geometric_dictionary (X := CMfd.of (n := n) W) J hdom.isWellFormed B' hB' S').2.2.2.1]
    exact hcosN
  have hvNnew := hnew.2 q hcosN
  have hp' : (interiorEmptyHistory B S).proj y∈W := by rw [proj_interiorEmptyHistory];exact hp
  let p' : openPreimage (interiorEmptyHistory B S) W := ⟨y,hp'⟩
  let χ' := opensCongr (n := n) (openPreimage_append
    (B.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S W).symm
  have hpoint : χ' p'=q := by apply Subtype.ext;rfl
  have hi := actual_restricted_empty_history W B S
  have hcanLnew := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
    (X := CMfd.of (n := n) W) (invFamily hn k) hdom Φ hi hcanNnew
  rw [hpull] at hcanLnew
  have htNnew := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn k).isInvValue hdom (interiorEmptyHistory B' S') hcanNnew
  have hcosnew := IsTowerIso.cosupp_geoTransformAlong Φ hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent hi htNnew
  rw [hpull] at hcosnew
  have hcosLnew : p'∈(geoTransformAlong J (restrict W (interiorEmptyHistory B S))).cosupp := by
    rw [hcosnew]
    change χ' p'∈(geoTransformAlong J (interiorEmptyHistory B' S')).cosupp
    rw [hpoint]
    exact hcosNnew
  have hvnew := (invFamily hn k).isInvValue.towerIso Φ J hdom
    (restrict W (interiorEmptyHistory B S)) (interiorEmptyHistory B' S') χ' hi hcanNnew p'
    (by
      change χ' p'∈(geoTransformAlong J (interiorEmptyHistory B' S')).cosupp
      rw [hpoint]
      exact hcosNnew)
  rw [hpull] at hvnew
  change (invFamily hn k).inv J (restrict W (interiorEmptyHistory B S)) p'=
    (invFamily hn k).inv J (interiorEmptyHistory B' S') (χ' p') at hvnew
  rw [hpoint,hvNnew,hvold] at hvnew
  refine ⟨hp,hp',hdom,hcanL,hcanLnew,hcosL,hcosLnew,?_⟩
  simpa only [B',length_restrict] using hvnew

private def splitLowerValue (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X) (s : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) : WithTop (ValTy k) :=
  Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) s v.2.1 v.2.2 y

private def fixedLowerValue (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X) (s : ℕ)
    {D : CMfd.{u} n} (K : BlowupTower X D) (z : D) (Q : BlowupTower D Y) (y : Y) : WithTop (ValTy k) :=
  if h : Q.proj y∈lowerMask M s K z then
    ((invFamily hn k).inv (lowerMarkedM M s K z) (restrict (lowerMask M s K z) Q)
      (⟨y,h⟩ : openPreimage Q (lowerMask M s K z)) : WithTop (ValTy k))
  else ⊤

private theorem step_crossing_value_of_family (hn : 0<n) (k : ℕ)
    (hFamily : FamilyInteriorTransport.{u} hn k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hns : ¬ IsSpecial M (H.append S) y)
    (hreach : S.length≤regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y=
      recursiveStepShift k (M.E.length+H.length)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y) := by
  obtain ⟨hp,hpnew,hdom,hcanL,hcanNew,hcosL,hcosNew,hval⟩ :=
    step_crossing_lower_of_family hn k hFamily M hM hmax H S hcan y hy hns hreach
  have hindex := original_canonical_crossing_lower_index_exact hn k M hM hmax H S hcan y hns hreach
  dsimp only at hindex
  rw [hindex] at hval
  let ℓ := level M (H.append S) y
  let r := regimeRun (stepRegime M ℓ) (H.append S) y
  let K := head H (r-S.length)
  let B := tail H (r-S.length)
  let W := lowerMask M ℓ K ((B.append S).proj y)
  let J := lowerMarkedM M ℓ K ((B.append S).proj y)
  have hbar := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) M hM hmax hn (H.append S) hcan).1
  have hH := (isGeoTestTower_append_iff (barMarked M) H S).mp hbar |>.1
  have hlevel : level M (interiorEmptyHistory H S) y=ℓ := level_dictionary M hM.isWellFormed H hH S y
  have hnewns : ¬ IsSpecial M (interiorEmptyHistory H S) y :=
    fun h => hns ((isSpecial_dictionary M hM.isWellFormed H hH S y).mp h)
  have hc := actual_crossing_selected_splits M hM.isWellFormed H hH S y hns hreach
  rw [hlevel] at hc
  have hcut := hc.2.2
  rw [hc.1] at hcut
  have hpair : Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y=
      pairShift (recursiveHistoryShift k (M.E.length+H.length-ℓ))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns,if_neg hnewns,hlevel,hc.1]
    change toLex (ℓ,splitLowerValue hn k M ℓ (split (interiorEmptyHistory H S) (r+1)) y)=
      pairShift (recursiveHistoryShift k (M.E.length+H.length-ℓ))
        (toLex (ℓ,splitLowerValue hn k M ℓ (split (H.append S) r) y))
    simp only [pairShift,ofLex_toLex]
    apply congrArg (fun v : WithTop (ValTy k) => toLex (ℓ,v))
    rw [hcut,hc.2.1]
    change fixedLowerValue hn k M ℓ K ((interiorEmptyHistory B S).proj y) (interiorEmptyHistory B S) y=
      WithTop.map (recursiveHistoryShift k (M.E.length+H.length-ℓ))
        (fixedLowerValue hn k M ℓ K ((B.append S).proj y) (B.append S) y)
    rw [proj_interiorEmptyHistory]
    unfold fixedLowerValue
    rw [dif_pos hpnew,dif_pos hp]
    exact congrArg (fun v : ValTy k => (v : WithTop (ValTy k))) hval
  have hfst := Seq.StepOneValueMasked.stepOneInvL_fst (invFamily hn k) M (lowerMarkedM M) (H.append S) y
  change (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y)).1=ℓ at hfst
  simpa only [pairShift,recursiveStepShift,hfst] using hpair

private theorem step_entire_value_of_family (hn : 0<n) (k : ℕ)
    (hFamily : FamilyInteriorTransport.{u} hn k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y=
      recursiveStepShift k (M.E.length+H.length)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y) := by
  have hbar := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) M hM hmax hn (H.append S) hcan).1
  have hH := (isGeoTestTower_append_iff (barMarked M) H S).mp hbar |>.1
  by_cases hsp : IsSpecial M (H.append S) y
  · have hspnew := (isSpecial_dictionary M hM.isWellFormed H hH S y).mpr hsp
    have hl := level_dictionary M hM.isWellFormed H hH S y
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hspnew,if_pos hsp]
    simp only [recursiveStepShift,ofLex_toLex,WithTop.map_top,hl]
  by_cases hs : regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y<S.length
  · exact original_recursive_short_step_value hn k M hM hmax H S hcan y hy hs
  · exact step_crossing_value_of_family hn k hFamily M hM hmax H S hcan y hy hsp (le_of_not_gt hs)

private theorem step_maximum_of_family (hn : 0<n) (k : ℕ)
    (hFamily : FamilyInteriorTransport.{u} hn k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S)) :
    ResolutionDriver.maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S))
        (geoTransformAlong M (interiorEmptyHistory H S)).cosupp=
      ResolutionDriver.maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S))
        (geoTransformAlong M (H.append S)).cosupp := by
  have ht := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) M hM hmax hn (H.append S) hcan).2.1
  have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
  have hcos := (geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1
  ext y
  change (y∈(geoTransformAlong M (interiorEmptyHistory H S)).cosupp ∧
    ∀ z∈(geoTransformAlong M (interiorEmptyHistory H S)).cosupp, _ ≤ _) ↔
    (y∈(geoTransformAlong M (H.append S)).cosupp ∧
    ∀ z∈(geoTransformAlong M (H.append S)).cosupp, _ ≤ _)
  rw [hcos]
  have hcompare : ∀ z∈(geoTransformAlong M (H.append S)).cosupp,
      ∀ w∈(geoTransformAlong M (H.append S)).cosupp,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) z≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) w ↔
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) z≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) w := by
    intro z hz w hw
    rw [step_entire_value_of_family hn k hFamily M hM hmax H S hcan z hz,
      step_entire_value_of_family hn k hFamily M hM hmax H S hcan w hw]
    exact (strictMono_recursiveStepShift k (M.E.length+H.length)).le_iff_le
  constructor
  · rintro ⟨hy,hdom⟩
    exact ⟨hy,fun z hz => (hcompare z hz y hy).mp (hdom z hz)⟩
  · rintro ⟨hy,hdom⟩
    exact ⟨hy,fun z hz => (hcompare z hz y hy).mpr (hdom z hz)⟩

private def StepInteriorTransport (hn : 0<n) (k : ℕ) : Prop :=
  ∀ {X A Y : CMfd.{u} n} (M : MarkedIdeal n X), IsInvDomain (k+1) M →
    IsMaximalOrderAlong M.N M.ideal M.d → ∀ (H : BlowupTower X A) (S : BlowupTower A Y),
    IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S) →
      IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (interiorEmptyHistory H S) ∧
      ∀ y∈(geoTransformAlong M (H.append S)).cosupp,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y=
          recursiveStepShift k (M.E.length+H.length)
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y)

private theorem step_history_of_family (hn : 0<n) (k : ℕ)
    (hFamily : FamilyInteriorTransport.{u} hn k) : StepInteriorTransport.{u} hn k := by
  intro D B Z M hM hmax H S hcan
  refine ⟨?_,fun y hy => step_entire_value_of_family hn k hFamily M hM hmax H S hcan y hy⟩
  revert hcan
  induction S with
  | refl =>
    intro hcan
    exact ⟨hcan,Or.inl rfl⟩
  | step S C π hπ ih =>
    intro hcan
    obtain ⟨hc,hC⟩ := hcan
    refine ⟨ih hc,?_⟩
    rcases hC with he | hm
    · exact Or.inl he
    · exact Or.inr (hm.trans (step_maximum_of_family hn k hFamily M hM hmax H S hc).symm)

private def familyInner (hn : 0<n) (k : ℕ) :
    ∀ {D : CMfd.{u} n}, MarkedIdeal n D → ∀ {Z : CMfd.{u} n}, BlowupTower D Z → Z →
      ℕ ×ₗ WithTop (ValTy k) :=
  fun {D} J {Z} Q z => Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) J (Y := Z) Q z

private theorem whole_companion_history_of_step (hn : 0<n) (k : ℕ)
    (hStep : StepInteriorTransport.{u} hn k) {D : CMfd.{u} n}
    (U : Opens D) (J : MarkedIdeal n U) (hdom : IsInvDomain (k+1) J)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (B : BlowupTower D A) (S : BlowupTower A Y)
    (hcan : IsCanonical J (familyInner hn k J) (restrict U (B.append S)))
    (p : openPreimage (B.append S) U)
    (hcos : p∈(geoTransformAlong J (restrict U (B.append S))).cosupp) :
    ∃ hp' : (interiorEmptyHistory B S).proj (p : Y)∈U,
      let p' : openPreimage (interiorEmptyHistory B S) U := ⟨(p : Y),hp'⟩
      IsCanonical J (familyInner hn k J) (restrict U (interiorEmptyHistory B S)) ∧
      p'∈(geoTransformAlong J (restrict U (interiorEmptyHistory B S))).cosupp ∧
      familyInner hn k J (restrict U (interiorEmptyHistory B S)) p'=
        recursiveStepShift k (J.E.length+B.length) (familyInner hn k J (restrict U (B.append S)) p) := by
  dsimp only
  let B' := restrict U B
  let S' := restrict (openPreimage B U) S
  let N := B'.append S'
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞
  let χ := opensCongr (n := n) (openPreimage_append B S U).symm
  let q := χ p
  have hVal := StepOneSeq.isMaxOrderValue_stepOneInvM (k := k+1) (invFamily hn k) hn
  have hpull : MarkedIdeal.pullback Φ J=J := ContactCanonicalAlong.pullback_id J hdom.isWellFormed.isCoherent
  have hpull' : MarkedIdeal.pullback Φ.symm J=J := ContactCanonicalAlong.pullback_id J hdom.isWellFormed.isCoherent
  have hi : IsTowerIso Φ (restrict U (B.append S)) N χ := isTowerIso_restrict_append U B S
  have hcanN := hVal.isCanonical_of_isTowerIso (X := CMfd.of (n := n) U) hdom hmax Φ.symm hi.symm hcan
  rw [hpull'] at hcanN
  have ht := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) J hdom hmax hn (restrict U (B.append S)) hcan).2.1
  have hcN := IsTowerIso.cosupp_geoTransformAlong Φ.symm hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent hi.symm ht
  rw [hpull'] at hcN
  have hq : χ.symm q=p := χ.symm_apply_apply p
  have hqcos : q∈(geoTransformAlong J N).cosupp := by
    rw [hcN]
    change χ.symm q∈(geoTransformAlong J (restrict U (B.append S))).cosupp
    rw [hq]
    exact hcos
  have hvOld := hVal.towerIso Φ.symm J hdom hmax N
    (restrict U (B.append S)) χ.symm hi.symm hcan q (by rw [hq];exact hcos)
  rw [hpull',hq] at hvOld
  have hnew := hStep (X := CMfd.of (n := n) U) J hdom hmax B' S' hcanN
  have hcanNN := hnew.1
  have htN := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) J hdom hmax hn N hcanN).2.1
  have htB := (isGeoTestTower_append_iff J B' S').mp htN |>.1
  have hqcosNN : q∈(geoTransformAlong J (interiorEmptyHistory B' S')).cosupp := by
    rw [(geometric_dictionary (X := CMfd.of (n := n) U) J hdom.isWellFormed B' htB S').2.2.2.1]
    exact hqcos
  have hvNN := hnew.2 q hqcos
  have hp' : (interiorEmptyHistory B S).proj (p : Y)∈U := by
    rw [proj_interiorEmptyHistory]
    exact p.2
  let p' : openPreimage (interiorEmptyHistory B S) U := ⟨(p : Y),hp'⟩
  let χ' := opensCongr (n := n) (openPreimage_append
    (B.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S U).symm
  have hpoint : χ' p'=q := by apply Subtype.ext;rfl
  have hi' := actual_restricted_empty_history U B S
  have hcanL' := hVal.isCanonical_of_isTowerIso (X := CMfd.of (n := n) U) hdom hmax Φ hi' hcanNN
  rw [hpull] at hcanL'
  have htNN := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) J hdom hmax hn (interiorEmptyHistory B' S') hcanNN).2.1
  have hcNew := IsTowerIso.cosupp_geoTransformAlong Φ hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent hi' htNN
  rw [hpull] at hcNew
  have hp'cos : p'∈(geoTransformAlong J (restrict U (interiorEmptyHistory B S))).cosupp := by
    rw [hcNew]
    change χ' p'∈(geoTransformAlong J (interiorEmptyHistory B' S')).cosupp
    rw [hpoint]
    exact hqcosNN
  have hvNew := hVal.towerIso Φ J hdom hmax (restrict U (interiorEmptyHistory B S))
    (interiorEmptyHistory B' S') χ' hi' hcanNN p' (by
      change q∈(geoTransformAlong J (interiorEmptyHistory B' S')).cosupp
      exact hqcosNN)
  rw [hpull] at hvNew
  change familyInner hn k J (restrict U (interiorEmptyHistory B S)) p'=
    familyInner hn k J (interiorEmptyHistory B' S') q at hvNew
  have hiLen : B'.length=B.length := length_restrict U B
  change familyInner hn k J (interiorEmptyHistory B' S') q=
    recursiveStepShift k (J.E.length+B'.length) (familyInner hn k J N q) at hvNN
  change familyInner hn k J N q=familyInner hn k J (restrict U (B.append S)) p at hvOld
  rw [hiLen,hvOld] at hvNN
  exact ⟨hp',hcanL',hp'cos,hvNew.trans hvNN⟩

private theorem companion_boundary_length {D : CMfd.{u} n}
    (M : MarkedIdeal n X) (o : ℕ) (K : BlowupTower X D) :
    (compAt M o K).E.length=M.E.length+K.length := by
  unfold compAt companionOf companionAlong
  split_ifs <;> simp only [MarkedIdealOperationsTransform.MarkedIdeal.add,
    MarkedIdeal.pullback,List.length_map,length_E_geoTransformAlong]

/-- ONLY original full family CAN and the internally supplied specific Step history IH supplies BOTH whole companion histories and complete values. -/
private theorem family_crossing_companion_of_step (hn : 0<n) (k : ℕ)
    (hStep : StepInteriorTransport.{u} hn k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn (k+1)).inv M) (H.append S))
    (o : ℕ) (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hν : nmOrd (geoTransformAlong M (H.append S)) y=o) (ho : 1≤o)
    (hreach : S.length≤regimeRun (OrdRegime M o) (H.append S) y) :
    let r := regimeRun (OrdRegime M o) (H.append S) y
    let K := head H (r-S.length)
    let B := tail H (r-S.length)
    let U := ordMask (geoTransformAlong M K) o
    let J := compAt M o K
    ∃ (hp : (B.append S).proj y∈U) (hp' : (interiorEmptyHistory B S).proj y∈U),
      IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) (restrict U (B.append S)) ∧
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) (restrict U (interiorEmptyHistory B S)) ∧
      (⟨y,hp⟩ : openPreimage (B.append S) U)∈(geoTransformAlong J (restrict U (B.append S))).cosupp ∧
      (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) U)∈
        (geoTransformAlong J (restrict U (interiorEmptyHistory B S))).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J (restrict U (interiorEmptyHistory B S))
          (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) U)=
        recursiveStepShift k (M.E.length+H.length)
          (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J (restrict U (B.append S))
            (⟨y,hp⟩ : openPreimage (B.append S) U)) := by
  dsimp only
  have hd := original_canonical_general_crossing_data hn k M hM H S hcan o y hy hν ho hreach
  let r := regimeRun (OrdRegime M o) (H.append S) y
  let K := head H (r-S.length)
  let B := tail H (r-S.length)
  let U := ordMask (geoTransformAlong M K) o
  let J := compAt M o K
  change ∃ hp : (B.append S).proj y∈U, IsInvDomain (k+1) J ∧
    IsMaximalOrderAlong J.N J.ideal J.d ∧ IsCanonical J (familyInner hn k J) (restrict U (B.append S)) ∧
      (⟨y,hp⟩ : openPreimage (B.append S) U)∈(geoTransformAlong J (restrict U (B.append S))).cosupp at hd
  obtain ⟨hp,hdom,hmax,hcanJ,hcos⟩ := hd
  obtain ⟨hp',hcanJ',hcos',hv⟩ := whole_companion_history_of_step hn k hStep U J hdom hmax
    B S hcanJ (⟨y,hp⟩ : openPreimage (B.append S) U) hcos
  have hj : (compAt M o (head H (regimeRun (OrdRegime M o) (H.append S) y-S.length))).E.length+
      (tail H (regimeRun (OrdRegime M o) (H.append S) y-S.length)).length=M.E.length+H.length := by
    rw [companion_boundary_length,length_head,length_tail]
    omega
  rw [hj] at hv
  exact ⟨hp,hp',hdom,hmax,hcanJ,hcanJ',hcos,hcos',hv⟩


private def familySplitLowerValue (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X) (o : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) :
      WithTop (ℕ ×ₗ WithTop (ValTy k)) := genLowerValue (familyInner hn k) M o v.2.1 v.2.2 y

private def familySplitData (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X) (o : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) : Prop :=
  GenLowerData (familyInner hn k) (k+1) M o v.2.1 v.2.2 y

private theorem actual_short_whole_map_compatibility (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn (k+1)).inv M) (H.append S))
    (o : ℕ) (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hν : nmOrd (geoTransformAlong M (H.append S)) y=o) (ho : o≠0)
    (hs : regimeRun (OrdRegime M o) (H.append S) y<S.length) :
    generalShift (M.E.length+H.length) (recursiveStepShift k (M.E.length+H.length)) ((invFamily hn (k+1)).inv M (H.append S) y)=
      shiftFamily (k+1) (M.E.length+H.length) ((invFamily hn (k+1)).inv M (H.append S) y) := by
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)).isInvValue hM (H.append S) hcan
  have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
  have hc := actual_general_short_splits M hM.isWellFormed H hH S o y hs
  have hdj := actual_general_short_companion_diagram M hM.isWellFormed H hH S o y hs
  let r := regimeRun (OrdRegime M o) (H.append S) y
  let P := head S r
  let Q := tail S r
  let U := ordMask (geoTransformAlong M (H.append P)) o
  let J := compAt M o (H.append P)
  have hd := original_canonical_general_crossing_data hn k M hM (H.append S) BlowupTower.refl
    hcan o y hy hν (by omega) (Nat.zero_le _)
  simp only [BlowupTower.append_refl,BlowupTower.length_refl,Nat.sub_zero] at hd
  change familySplitData hn k M o (split (H.append S) (regimeRun (OrdRegime M o) (H.append S) y)) y at hd
  rw [hc.2.1] at hd
  change ∃ hp : Q.proj y∈U,
    IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsCanonical J (familyInner hn k J) (restrict U Q) ∧
      (⟨y,hp⟩ : openPreimage Q U)∈(geoTransformAlong J (restrict U Q)).cosupp at hd
  obtain ⟨hp,hdom,hmax,hcanJ,hcosJ⟩ := hd
  have hv := original_canonical_step_initial_boundary_compatibility (X := CMfd.of (n := n) U)
    hn k J hdom hmax (restrict U Q) hcanJ (M.E.length+H.length) hdj.2.1
    (⟨y,hp⟩ : openPreimage Q U) hcosJ
  change generalShift (M.E.length+H.length) (recursiveStepShift k (M.E.length+H.length))
      (genInv (familyInner hn k) M (H.append S) y)=
    generalShift (M.E.length+H.length) (pairShift (shiftFamily k 0))
      (genInv (familyInner hn k) M (H.append S) y)
  rw [genInv_of_nmOrd_ne_zero (familyInner hn k) M _ hν ho]
  change generalShift (M.E.length+H.length) (recursiveStepShift k (M.E.length+H.length))
      (toLex (o,toLex (Sum.inr (familySplitLowerValue hn k M o
        (split (H.append S) (regimeRun (OrdRegime M o) (H.append S) y)) y))) : ValTy (k+1))=
    generalShift (M.E.length+H.length) (pairShift (shiftFamily k 0))
      (toLex (o,toLex (Sum.inr (familySplitLowerValue hn k M o
        (split (H.append S) (regimeRun (OrdRegime M o) (H.append S) y)) y))) : ValTy (k+1))
  rw [hc.2.1]
  simp only [generalShift,ofLex_toLex,Sum.map_inr]
  change toLex (o,toLex (Sum.inr (WithTop.map (recursiveStepShift k (M.E.length+H.length))
      (genLowerValue (familyInner hn k) M o (H.append P) Q y))))=
    toLex (o,toLex (Sum.inr (WithTop.map (pairShift (shiftFamily k 0))
      (genLowerValue (familyInner hn k) M o (H.append P) Q y))))
  rw [genLowerValue_eq_of_mem (familyInner hn k) M hp]
  simp only [WithTop.map_coe]
  exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy k) =>
    (toLex (o,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy k))))) : ValTy (k+1))) hv

private theorem family_value_as_genInv (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) :
    (invFamily hn (k+1)).inv M T y=genInv (familyInner hn k) M T y := rfl

private def generic_split_lower {Λ : Type*} [LinearOrder Λ]
    (F : ∀ {D : CMfd.{u} n}, MarkedIdeal n D → ∀ {Z : CMfd.{u} n}, BlowupTower D Z → Z → Λ)
    (M : MarkedIdeal n X) (o : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) : WithTop Λ :=
  genLowerValue F M o v.2.1 v.2.2 y

private theorem generic_monomial_maps {Λ : Type*} [LinearOrder Λ]
    (F : ∀ {D : CMfd.{u} n}, MarkedIdeal n D → ∀ {Z : CMfd.{u} n}, BlowupTower D Z → Z → Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y)
    (h0 : nmOrd (geoTransformAlong M T) y=0) (j : ℕ) (f g : Λ → Λ) :
    generalShift j f (genInv F M T y)=generalShift j g (genInv F M T y) := by
  unfold generalShift genInv genSecond
  rw [h0]
  rfl

private theorem generic_positive_computed_map {Λ : Type*} [LinearOrder Λ]
    (F : ∀ {D : CMfd.{u} n}, MarkedIdeal n D → ∀ {Z : CMfd.{u} n}, BlowupTower D Z → Z → Λ)
    (M : MarkedIdeal n X) (T T' : BlowupTower X Y) (y : Y) (o : ℕ)
    (hν : nmOrd (geoTransformAlong M T) y=o) (hν' : nmOrd (geoTransformAlong M T') y=o)
    (ho : o≠0) (j : ℕ) (f : Λ → Λ)
    (hL : generic_split_lower F M o (split T' (regimeRun (OrdRegime M o) T' y)) y=
      WithTop.map f (generic_split_lower F M o (split T (regimeRun (OrdRegime M o) T y)) y)) :
    genInv F M T' y=generalShift j f (genInv F M T y) := by
  rw [genInv_of_nmOrd_ne_zero F M _ hν' ho,genInv_of_nmOrd_ne_zero F M _ hν ho]
  change toLex (o,toLex (Sum.inr (generic_split_lower F M o
      (split T' (regimeRun (OrdRegime M o) T' y)) y)))=
    generalShift j f (toLex (o,toLex (Sum.inr (generic_split_lower F M o
      (split T (regimeRun (OrdRegime M o) T y)) y))))
  simp only [generalShift,ofLex_toLex,Sum.map_inr]
  exact congrArg (fun v : WithTop Λ => toLex (o,toLex (Sum.inr v))) hL

/-- ENTIRE actual original successor family on ALL original cosupport, no branch/companion/value premise. -/
private theorem family_entire_value_of_step (hn : 0<n) (k : ℕ)
    (hStep : StepInteriorTransport.{u} hn k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn (k+1)).inv M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp) :
    (invFamily hn (k+1)).inv M (interiorEmptyHistory H S) y=
      recursiveHistoryShift (k+1) (M.E.length+H.length) ((invFamily hn (k+1)).inv M (H.append S) y) := by
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)).isInvValue hM (H.append S) hcan
  have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
  by_cases h0 : nmOrd (geoTransformAlong M (H.append S)) y=0
  · rw [HironakaOriginalCurveHistory.original_invFamily_interior_monomial_all_tails hn (k+1) M hM.isWellFormed H hH S y h0,
      family_value_as_genInv hn k]
    exact generic_monomial_maps (familyInner hn k) M (H.append S) y h0 _ _ _
  let o := nmOrd (geoTransformAlong M (H.append S)) y
  by_cases hs : regimeRun (OrdRegime M o) (H.append S) y<S.length
  · exact (actual_entire_outer_short_family_value hn k M hM.isWellFormed H hH S y hs).trans
      (actual_short_whole_map_compatibility hn k M hM H S hcan o y hy rfl h0 hs).symm
  have hreach : S.length≤regimeRun (OrdRegime M o) (H.append S) y := le_of_not_gt hs
  let r := regimeRun (OrdRegime M o) (H.append S) y
  let K := head H (r-S.length)
  let B := tail H (r-S.length)
  let U := ordMask (geoTransformAlong M K) o
  let J := compAt M o K
  have hD := family_crossing_companion_of_step hn k hStep M hM H S hcan o y hy rfl (by omega) hreach
  change ∃ (hp : (B.append S).proj y∈U) (hp' : (interiorEmptyHistory B S).proj y∈U),
    IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsCanonical J (familyInner hn k J) (restrict U (B.append S)) ∧
      IsCanonical J (familyInner hn k J) (restrict U (interiorEmptyHistory B S)) ∧
      (⟨y,hp⟩ : openPreimage (B.append S) U)∈(geoTransformAlong J (restrict U (B.append S))).cosupp ∧
      (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) U)∈
        (geoTransformAlong J (restrict U (interiorEmptyHistory B S))).cosupp ∧
      familyInner hn k J (restrict U (interiorEmptyHistory B S)) (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) U)=
        recursiveStepShift k (M.E.length+H.length)
          (familyInner hn k J (restrict U (B.append S)) (⟨y,hp⟩ : openPreimage (B.append S) U)) at hD
  obtain ⟨hp,hp',_hdom,_hmax,_hcanJ,_hcanJ',_hcos,_hcos',hvJ⟩ := hD
  have hc := actual_general_crossing_splits M hM.isWellFormed H hH S o y hy rfl hreach
  have hv : genLowerValue (familyInner hn k) M o K (interiorEmptyHistory B S) y=
      WithTop.map (recursiveStepShift k (M.E.length+H.length))
        (genLowerValue (familyInner hn k) M o K (B.append S) y) := by
    rw [genLowerValue_eq_of_mem (familyInner hn k) M hp',genLowerValue_eq_of_mem (familyInner hn k) M hp,WithTop.map_coe]
    exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy k) => (v : WithTop (ℕ ×ₗ WithTop (ValTy k)))) hvJ
  have hνnew : nmOrd (geoTransformAlong M (interiorEmptyHistory H S)) y=o :=
    nmOrd_interior_empty_all_tails M hM.isWellFormed H hH S y
  have hnewcut := congrArg (fun v => generic_split_lower (familyInner hn k) M o v y) hc.2.2
  have holdcut := congrArg (fun v => generic_split_lower (familyInner hn k) M o v y) hc.2.1
  have hcomputed : generic_split_lower (familyInner hn k) M o
      (split (interiorEmptyHistory H S) (regimeRun (OrdRegime M o) (interiorEmptyHistory H S) y)) y=
    WithTop.map (recursiveStepShift k (M.E.length+H.length))
      (generic_split_lower (familyInner hn k) M o (split (H.append S) r) y) :=
    hnewcut.trans (hv.trans (congrArg (WithTop.map (recursiveStepShift k (M.E.length+H.length))) holdcut.symm))
  rw [family_value_as_genInv hn k]
  exact generic_positive_computed_map (familyInner hn k) M (H.append S) (interiorEmptyHistory H S) y o
    rfl hνnew h0 (M.E.length+H.length) (recursiveStepShift k (M.E.length+H.length)) hcomputed

/-- A private algebra interface, consumed only with internally proved ACTUAL entire values. -/
private theorem generic_maximum_dictionary {Z Λ : Type*} [LinearOrder Λ]
    (B B' : Set Z) (f f' : Z → Λ) (hB : B'=B) (g : Λ → Λ) (hg : StrictMono g)
    (hValues : ∀ y∈B, f' y=g (f y)) : ResolutionDriver.maxLocus f' B'=ResolutionDriver.maxLocus f B := by
  ext y
  change (y∈B' ∧ ∀ z∈B', f' z≤f' y) ↔ (y∈B ∧ ∀ z∈B, f z≤f y)
  rw [hB]
  have hcompare : ∀ z∈B, ∀ w∈B, (f' z≤f' w ↔ f z≤f w) := by
    intro z hz w hw
    rw [hValues z hz,hValues w hw]
    exact hg.le_iff_le
  constructor
  · rintro ⟨hy,hdom⟩
    exact ⟨hy,fun z hz => (hcompare z hz y hy).mp (hdom z hz)⟩
  · rintro ⟨hy,hdom⟩
    exact ⟨hy,fun z hz => (hcompare z hz y hy).mpr (hdom z hz)⟩

private theorem family_maximum_of_step (hn : 0<n) (k : ℕ)
    (hStep : StepInteriorTransport.{u} hn k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn (k+1)).inv M) (H.append S)) :
    ResolutionDriver.maxLocus ((invFamily hn (k+1)).inv M (interiorEmptyHistory H S))
        (geoTransformAlong M (interiorEmptyHistory H S)).cosupp=
      ResolutionDriver.maxLocus ((invFamily hn (k+1)).inv M (H.append S))
        (geoTransformAlong M (H.append S)).cosupp := by
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)).isInvValue hM (H.append S) hcan
  have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
  exact generic_maximum_dictionary _ _ _ _ (geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1
    (recursiveHistoryShift (k+1) (M.E.length+H.length))
    (strictMono_recursiveHistoryShift (k+1) (M.E.length+H.length))
    (fun y hy => family_entire_value_of_step hn k hStep M hM H S hcan y hy)

/-- The genuine Step depth already constructed supplies successor FAMILY history and all values. -/
private theorem family_history_succ (hn : 0<n) (k : ℕ)
    (hStep : StepInteriorTransport.{u} hn k) : FamilyInteriorTransport.{u} hn (k+1) := by
  intro D B Z M hM H S hcan
  refine ⟨?_,fun y hy => family_entire_value_of_step hn k hStep M hM H S hcan y hy⟩
  revert hcan
  induction S with
  | refl =>
    intro hcan
    exact ⟨hcan,Or.inl rfl⟩
  | step S C π hπ ih =>
    intro hcan
    obtain ⟨hc,hC⟩ := hcan
    refine ⟨ih hc,?_⟩
    rcases hC with he | hm
    · exact Or.inl he
    · exact Or.inr (hm.trans (family_maximum_of_step hn k hStep M hM H S hc).symm)

/-- The REAL depth-zero family is constant; no nonvacuous seed or maximum-existence premise. -/
private theorem family_history_zero (hn : 0<n) : FamilyInteriorTransport.{u} hn 0 := by
  intro D B Z M hM H S hcan
  refine ⟨?_,fun _ _ => rfl⟩
  revert hcan
  induction S with
  | refl =>
    intro hcan
    exact ⟨hcan,Or.inl rfl⟩
  | step S C π hπ ih =>
    intro hcan
    obtain ⟨hc,hC⟩ := hcan
    refine ⟨ih hc,?_⟩
    rcases hC with he | hm
    · exact Or.inl he
    · have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
        (invFamily hn 0).isInvValue hM (H.append S) hc
      have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
      have hdict := generic_maximum_dictionary _ _
        ((invFamily hn 0).inv M (H.append S)) ((invFamily hn 0).inv M (interiorEmptyHistory H S))
        (geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1
        (recursiveHistoryShift 0 (M.E.length+H.length))
        (strictMono_recursiveHistoryShift 0 (M.E.length+H.length)) (fun _ _ => rfl)
      exact Or.inr (hm.trans hdict.symm)

/-- ALL-depth genuine history induction; no original caller supplies either induction predicate. -/
private theorem family_history_all (hn : 0<n) : ∀ k : ℕ, FamilyInteriorTransport.{u} hn k
  | 0 => family_history_zero hn
  | k+1 => family_history_succ hn k (step_history_of_family hn k (family_history_all hn k))

/-- The ENTIRE actual original family value at EVERY depth and original cosupport point. -/
theorem original_recursive_entire_family_interior_value (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp) :
    (invFamily hn k).inv M (interiorEmptyHistory H S) y=
      recursiveHistoryShift k (M.E.length+H.length) ((invFamily hn k).inv M (H.append S) y) :=
  (family_history_all hn k M hM H S hcan).2 y hy

/-- Only original OLD whole family CAN internally supplies inserted WHOLE CAN at EVERY depth. -/
theorem original_recursive_family_interior_isCanonical (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) (H.append S)) :
    IsCanonical M ((invFamily hn k).inv M) (interiorEmptyHistory H S) :=
  (family_history_all hn k M hM H S hcan).1

/-- Every Step depth internally consumes the completed ORIGINAL family history induction. -/
theorem original_recursive_entire_step_interior_value (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y=
      recursiveStepShift k (M.E.length+H.length)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y) :=
  step_entire_value_of_family hn k (family_history_all hn k) M hM hmax H S hcan y hy

theorem original_recursive_step_interior_isCanonical (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S)) :
    IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (interiorEmptyHistory H S) :=
  (step_history_of_family hn k (family_history_all hn k) M hM hmax H S hcan).1

theorem original_recursive_crossing_whole_lower_history (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hns : ¬ IsSpecial M (H.append S) y)
    (hreach : S.length≤regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y) :
    let ℓ := level M (H.append S) y
    let r := regimeRun (stepRegime M ℓ) (H.append S) y
    let K := head H (r-S.length)
    let B := tail H (r-S.length)
    let W := lowerMask M ℓ K ((B.append S).proj y)
    let J := lowerMarkedM M ℓ K ((B.append S).proj y)
    (J.E.length+B.length=M.E.length+H.length-ℓ) ∧
    ∃ (hp : (B.append S).proj y∈W) (hp' : (interiorEmptyHistory B S).proj y∈W),
      IsInvDomain k J ∧ IsCanonical J ((invFamily hn k).inv J) (restrict W (B.append S)) ∧
      IsCanonical J ((invFamily hn k).inv J) (restrict W (interiorEmptyHistory B S)) ∧
      (⟨y,hp⟩ : openPreimage (B.append S) W)∈(geoTransformAlong J (restrict W (B.append S))).cosupp ∧
      (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) W)∈
        (geoTransformAlong J (restrict W (interiorEmptyHistory B S))).cosupp ∧
      (invFamily hn k).inv J (restrict W (interiorEmptyHistory B S))
          (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) W)=
        recursiveHistoryShift k (J.E.length+B.length)
          ((invFamily hn k).inv J (restrict W (B.append S)) (⟨y,hp⟩ : openPreimage (B.append S) W)) := by
  dsimp only
  exact ⟨original_canonical_crossing_lower_index_exact hn k M hM hmax H S hcan y hns hreach,
    step_crossing_lower_of_family hn k (family_history_all hn k) M hM hmax H S hcan y hy hns hreach⟩

theorem original_recursive_crossing_whole_companion_history (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn (k+1)).inv M) (H.append S))
    (o : ℕ) (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hν : nmOrd (geoTransformAlong M (H.append S)) y=o) (ho : 1≤o)
    (hreach : S.length≤regimeRun (OrdRegime M o) (H.append S) y) :
    let r := regimeRun (OrdRegime M o) (H.append S) y
    let K := head H (r-S.length)
    let B := tail H (r-S.length)
    let U := ordMask (geoTransformAlong M K) o
    let J := compAt M o K
    ∃ (hp : (B.append S).proj y∈U) (hp' : (interiorEmptyHistory B S).proj y∈U),
      IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) (restrict U (B.append S)) ∧
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) (restrict U (interiorEmptyHistory B S)) ∧
      (⟨y,hp⟩ : openPreimage (B.append S) U)∈(geoTransformAlong J (restrict U (B.append S))).cosupp ∧
      (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) U)∈
        (geoTransformAlong J (restrict U (interiorEmptyHistory B S))).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J (restrict U (interiorEmptyHistory B S))
          (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) U)=
        recursiveStepShift k (M.E.length+H.length)
          (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J (restrict U (B.append S))
            (⟨y,hp⟩ : openPreimage (B.append S) U)) :=
  family_crossing_companion_of_step hn k (step_history_of_family hn k (family_history_all hn k))
    M hM H S hcan o y hy hν ho hreach

theorem original_recursive_entire_family_interior_comparisons (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) (H.append S))
    (y z : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hz : z∈(geoTransformAlong M (H.append S)).cosupp) :
    let v := (invFamily hn k).inv M (H.append S) y
    let w := (invFamily hn k).inv M (H.append S) z
    let v' := (invFamily hn k).inv M (interiorEmptyHistory H S) y
    let w' := (invFamily hn k).inv M (interiorEmptyHistory H S) z
    (v'<w' ↔ v<w) ∧ (v'≤w' ↔ v≤w) ∧ (v'=w' ↔ v=w) := by
  dsimp only
  rw [original_recursive_entire_family_interior_value hn k M hM H S hcan y hy,
    original_recursive_entire_family_interior_value hn k M hM H S hcan z hz]
  have hm := strictMono_recursiveHistoryShift k (M.E.length+H.length)
  exact ⟨hm.lt_iff_lt,hm.le_iff_le,hm.injective.eq_iff⟩

theorem original_recursive_entire_step_interior_comparisons (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y z : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hz : z∈(geoTransformAlong M (H.append S)).cosupp) :
    let v := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y
    let w := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) z
    let v' := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y
    let w' := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) z
    (v'<w' ↔ v<w) ∧ (v'≤w' ↔ v≤w) ∧ (v'=w' ↔ v=w) := by
  dsimp only
  rw [original_recursive_entire_step_interior_value hn k M hM hmax H S hcan y hy,
    original_recursive_entire_step_interior_value hn k M hM hmax H S hcan z hz]
  have hm := strictMono_recursiveStepShift k (M.E.length+H.length)
  exact ⟨hm.lt_iff_lt,hm.le_iff_le,hm.injective.eq_iff⟩

/-- Entire actual dominance loci, without an existence-of-maximum conclusion. -/
theorem original_recursive_family_actual_maximum_dictionary (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) (H.append S)) :
    ResolutionDriver.maxLocus ((invFamily hn k).inv M (interiorEmptyHistory H S))
        (geoTransformAlong M (interiorEmptyHistory H S)).cosupp=
      ResolutionDriver.maxLocus ((invFamily hn k).inv M (H.append S))
        (geoTransformAlong M (H.append S)).cosupp := by
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn k).isInvValue hM (H.append S) hcan
  have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
  exact generic_maximum_dictionary _ _ _ _ (geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1
    (recursiveHistoryShift k (M.E.length+H.length)) (strictMono_recursiveHistoryShift k (M.E.length+H.length))
    (fun y hy => original_recursive_entire_family_interior_value hn k M hM H S hcan y hy)

theorem original_recursive_step_actual_maximum_dictionary (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S)) :
    ResolutionDriver.maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S))
        (geoTransformAlong M (interiorEmptyHistory H S)).cosupp=
      ResolutionDriver.maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S))
        (geoTransformAlong M (H.append S)).cosupp :=
  step_maximum_of_family hn k (family_history_all hn k) M hM hmax H S hcan

theorem original_recursive_family_interior_canonical_resolution (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) (H.append S))
    (hres : IsGeoResolution M (H.append S)) :
    IsCanonical M ((invFamily hn k).inv M) (interiorEmptyHistory H S) ∧
      IsGeoResolution M (interiorEmptyHistory H S) := by
  have hH := (isGeoTestTower_append_iff M H S).mp hres.1 |>.1
  have ht := (isGeoTestTower_interior_empty_iff M hM.isWellFormed H hH S).mpr hres.1
  refine ⟨original_recursive_family_interior_isCanonical hn k M hM H S hcan,ht,?_⟩
  rw [(geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1,hres.2]

theorem original_recursive_step_interior_canonical_resolution (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (hres : IsGeoResolution M (H.append S)) :
    IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (interiorEmptyHistory H S) ∧
      IsGeoResolution M (interiorEmptyHistory H S) := by
  have hH := (isGeoTestTower_append_iff M H S).mp hres.1 |>.1
  have ht := (isGeoTestTower_interior_empty_iff M hM.isWellFormed H hH S).mpr hres.1
  refine ⟨original_recursive_step_interior_isCanonical hn k M hM hmax H S hcan,ht,?_⟩
  rw [(geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1,hres.2]

end
end Hironaka.HironakaOriginalRecursiveInteriorHistory
