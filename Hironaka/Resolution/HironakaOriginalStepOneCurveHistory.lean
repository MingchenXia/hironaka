/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCurveHistory
import Hironaka.Resolution.HironakaOriginalCrossingExactIndex
/-! Whole positive-inner original crossing over the COMPLETE curve family.
Complete four-node Mathematics.tex preceded proofs. Further outer/higher
family recursion and noncompact scheduling remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalStepOneCurveHistory
noncomputable section
open Classical
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  MarkedIdealBiholomorphism BlowupTowerIsomorphism BlowupTowerIsoTail
  HironakaOriginalInteriorEmptyHistory HironakaOriginalCrossingLowerHistory
  HironakaOriginalCanonicalNormalizedLowerTail HironakaOriginalCurveHistory
  HironakaOriginalCrossingExactIndex HironakaOriginalInvariantEmptyInsertion
  HironakaOriginalShortUniformIndex
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Actual original canonical input INTERNALLY constructs both WHOLE
restricted curve lower canonical histories/cosupport and their ENTIRE value
at EVERY lower order, including immediate emptyS. No insertedCAN certificate. -/
theorem original_crossing_entire_curve_lower_data (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M) (H.append S))
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
      IsInvDomain 1 J ∧ IsCanonical J ((invFamily hn 1).inv J) (restrict W (B.append S)) ∧
      IsCanonical J ((invFamily hn 1).inv J) (restrict W (interiorEmptyHistory B S)) ∧
      (⟨y,hp⟩ : openPreimage (B.append S) W)∈(geoTransformAlong J (restrict W (B.append S))).cosupp ∧
      (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) W)∈
        (geoTransformAlong J (restrict W (interiorEmptyHistory B S))).cosupp ∧
      (invFamily hn 1).inv J (restrict W (interiorEmptyHistory B S))
          (⟨y,hp'⟩ : openPreimage (interiorEmptyHistory B S) W)=
        shiftFamily 1 (J.E.length+B.length)
          ((invFamily hn 1).inv J (restrict W (B.append S)) (⟨y,hp⟩ : openPreimage (B.append S) W)) := by
  dsimp only
  obtain ⟨hp,hdom,hcanL,hcanN,hcosL,hcosN,hvold⟩ :=
    original_canonical_crossing_normalized_lower_data hn 1 M hM hmax H S hcan y hy hns hreach
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
  let p : openPreimage (B.append S) W := ⟨y,hp⟩
  let q := χ p
  have hpull : MarkedIdeal.pullback Φ J=J := ContactCanonicalAlong.pullback_id J hdom.isWellFormed.isCoherent
  have hcanNnew := original_curve_interior_isCanonical (X := CMfd.of (n := n) W)
    hn J hdom B' S' hcanN
  have htestN := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn 1).isInvValue hdom (B'.append S') hcanN
  have hB' := (isGeoTestTower_append_iff J B' S').mp htestN |>.1
  have hcosNnew : q∈(geoTransformAlong J (interiorEmptyHistory B' S')).cosupp := by
    rw [(geometric_dictionary (X := CMfd.of (n := n) W) J hdom.isWellFormed B' hB' S').2.2.2.1]
    exact hcosN
  have hvNnew := original_curve_entire_interior_value (X := CMfd.of (n := n) W)
    hn J hdom B' S' hcanN q hcosN
  have hp' : (interiorEmptyHistory B S).proj y∈W := by
    rw [proj_interiorEmptyHistory]
    exact hp
  let p' : openPreimage (interiorEmptyHistory B S) W := ⟨y,hp'⟩
  let χ' := opensCongr (n := n) (openPreimage_append
    (B.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S W).symm
  have hpoint : χ' p'=q := by apply Subtype.ext;rfl
  have hi := actual_restricted_empty_history W B S
  have hcanLnew := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
    (X := CMfd.of (n := n) W) (invFamily hn 1) hdom Φ hi hcanNnew
  rw [hpull] at hcanLnew
  have htNnew := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn 1).isInvValue hdom (interiorEmptyHistory B' S') hcanNnew
  have hcosnew := IsTowerIso.cosupp_geoTransformAlong Φ hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent hi htNnew
  rw [hpull] at hcosnew
  have hcosLnew : p'∈(geoTransformAlong J (restrict W (interiorEmptyHistory B S))).cosupp := by
    rw [hcosnew]
    change χ' p'∈(geoTransformAlong J (interiorEmptyHistory B' S')).cosupp
    rw [hpoint]
    exact hcosNnew
  have hvnew := (invFamily hn 1).isInvValue.towerIso Φ J hdom
    (restrict W (interiorEmptyHistory B S)) (interiorEmptyHistory B' S') χ' hi hcanNnew p'
    (by
      change χ' p'∈(geoTransformAlong J (interiorEmptyHistory B' S')).cosupp
      rw [hpoint]
      exact hcosNnew)
  rw [hpull] at hvnew
  change (invFamily hn 1).inv J (restrict W (interiorEmptyHistory B S)) p'=
    (invFamily hn 1).inv J (interiorEmptyHistory B' S') (χ' p') at hvnew
  rw [hpoint,hvNnew,hvold] at hvnew
  refine ⟨hp,hp',hdom,hcanL,hcanLnew,hcosL,hcosLnew,?_⟩
  simpa only [B',length_restrict] using hvnew

private def splitLowerValue (hn : 0<n) (M : MarkedIdeal n X) (s : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) : WithTop (ValTy 1) :=
  Seq.StepOneValueMasked.lowerValueL (invFamily hn 1) M (lowerMarkedM M) s v.2.1 v.2.2 y

private def fixedLowerValue (hn : 0<n) (M : MarkedIdeal n X) (s : ℕ)
    {D : CMfd.{u} n} (K : BlowupTower X D) (z : D) (Q : BlowupTower D Y) (y : Y) : WithTop (ValTy 1) :=
  if h : Q.proj y∈lowerMask M s K z then
    ((invFamily hn 1).inv (lowerMarkedM M s K z) (restrict (lowerMask M s K z) Q)
      (⟨y,h⟩ : openPreimage Q (lowerMask M s K z)) : WithTop (ValTy 1))
  else ⊤

/-- COMPLETE actual own-level crossing over R1: every lower order/level and
EVERY suffix, with actual original lower data supplied INTERNALLY. -/
theorem original_crossing_entire_stepOne_curve_value (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hns : ¬ IsSpecial M (H.append S) y)
    (hreach : S.length≤regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (interiorEmptyHistory H S) y=
      historyStepShift 1 (M.E.length+H.length)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (H.append S) y) := by
  obtain ⟨hp,hpnew,hdom,hcanL,hcanNew,hcosL,hcosNew,hval⟩ :=
    original_crossing_entire_curve_lower_data hn M hM hmax H S hcan y hy hns hreach
  have hindex := original_canonical_crossing_lower_index_exact hn 1 M hM hmax H S hcan y hns hreach
  dsimp only at hindex
  rw [hindex] at hval
  let ℓ := level M (H.append S) y
  let r := regimeRun (stepRegime M ℓ) (H.append S) y
  let K := head H (r-S.length)
  let B := tail H (r-S.length)
  let W := lowerMask M ℓ K ((B.append S).proj y)
  let J := lowerMarkedM M ℓ K ((B.append S).proj y)
  have hbar := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn 1) M hM hmax hn (H.append S) hcan).1
  have hH := (isGeoTestTower_append_iff (barMarked M) H S).mp hbar |>.1
  have hlevel : level M (interiorEmptyHistory H S) y=ℓ := level_dictionary M hM.isWellFormed H hH S y
  have hnewns : ¬ IsSpecial M (interiorEmptyHistory H S) y :=
    fun h => hns ((isSpecial_dictionary M hM.isWellFormed H hH S y).mp h)
  have hc := actual_crossing_selected_splits M hM.isWellFormed H hH S y hns hreach
  rw [hlevel] at hc
  have hcut := hc.2.2
  rw [hc.1] at hcut
  have hpair : Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (interiorEmptyHistory H S) y=
      pairShift (shiftFamily 1 (M.E.length+H.length-ℓ))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (H.append S) y) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns,if_neg hnewns,hlevel,hc.1]
    change toLex (ℓ,splitLowerValue hn M ℓ (split (interiorEmptyHistory H S) (r+1)) y)=
      pairShift (shiftFamily 1 (M.E.length+H.length-ℓ))
        (toLex (ℓ,splitLowerValue hn M ℓ (split (H.append S) r) y))
    simp only [pairShift,ofLex_toLex]
    apply congrArg (fun v : WithTop (ValTy 1) => toLex (ℓ,v))
    rw [hcut,hc.2.1]
    change fixedLowerValue hn M ℓ K ((interiorEmptyHistory B S).proj y) (interiorEmptyHistory B S) y=
      WithTop.map (shiftFamily 1 (M.E.length+H.length-ℓ))
        (fixedLowerValue hn M ℓ K ((B.append S).proj y) (B.append S) y)
    rw [proj_interiorEmptyHistory]
    unfold fixedLowerValue
    rw [dif_pos hpnew,dif_pos hp]
    exact congrArg (fun v : ValTy 1 => (v : WithTop (ValTy 1))) hval
  have hfst := Seq.StepOneValueMasked.stepOneInvL_fst (invFamily hn 1) M (lowerMarkedM M) (H.append S) y
  change (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (H.append S) y)).1=ℓ at hfst
  simpa only [pairShift,historyStepShift,hfst] using hpair

/-- ENTIRE actual Step One/R1 value at EVERY actual original cosupport
point, including all true short/crossing and zero/contact/positive branches. -/
theorem original_entire_stepOne_curve_interior_value (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (interiorEmptyHistory H S) y=
      historyStepShift 1 (M.E.length+H.length)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (H.append S) y) := by
  have hbar := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn 1) M hM hmax hn (H.append S) hcan).1
  have hH := (isGeoTestTower_append_iff (barMarked M) H S).mp hbar |>.1
  by_cases hsp : IsSpecial M (H.append S) y
  · have hspnew := (isSpecial_dictionary M hM.isWellFormed H hH S y).mpr hsp
    have hl := level_dictionary M hM.isWellFormed H hH S y
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hspnew,if_pos hsp]
    simp only [historyStepShift,ofLex_toLex,WithTop.map_top,hl]
  by_cases hs : regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y<S.length
  · exact actual_entire_short_stepOne_value hn 1 M hM.isWellFormed H S hbar y hs
  · exact original_crossing_entire_stepOne_curve_value hn M hM hmax H S hcan y hy hsp (le_of_not_gt hs)

theorem original_entire_stepOne_curve_interior_comparisons (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M) (H.append S))
    (y z : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hz : z∈(geoTransformAlong M (H.append S)).cosupp) :
    let v := Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (H.append S) y
    let w := Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (H.append S) z
    let v' := Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (interiorEmptyHistory H S) y
    let w' := Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (interiorEmptyHistory H S) z
    (v'<w' ↔ v<w) ∧ (v'≤w' ↔ v≤w) ∧ (v'=w' ↔ v=w) := by
  dsimp only
  rw [original_entire_stepOne_curve_interior_value hn M hM hmax H S hcan y hy,
    original_entire_stepOne_curve_interior_value hn M hM hmax H S hcan z hz]
  have hm := strictMono_historyStepShift 1 (M.E.length+H.length)
  exact ⟨hm.lt_iff_lt,hm.le_iff_le,hm.injective.eq_iff⟩

private theorem original_actual_stepOne_curve_maximum_dictionary (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M) (H.append S)) :
    ResolutionDriver.maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (interiorEmptyHistory H S))
        (geoTransformAlong M (interiorEmptyHistory H S)).cosupp=
      ResolutionDriver.maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M (H.append S))
        (geoTransformAlong M (H.append S)).cosupp := by
  have ht := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn 1) M hM hmax hn (H.append S) hcan).2.1
  have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
  have hcos := (geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1
  ext y
  change (y∈(geoTransformAlong M (interiorEmptyHistory H S)).cosupp ∧
    ∀ z∈(geoTransformAlong M (interiorEmptyHistory H S)).cosupp, _ ≤ _) ↔
    (y∈(geoTransformAlong M (H.append S)).cosupp ∧
    ∀ z∈(geoTransformAlong M (H.append S)).cosupp, _ ≤ _)
  rw [hcos]
  constructor
  · rintro ⟨hy,hdom⟩
    refine ⟨hy,fun z hz => ?_⟩
    exact (original_entire_stepOne_curve_interior_comparisons hn M hM hmax H S hcan z y hz hy).2.1.mp (hdom z hz)
  · rintro ⟨hy,hdom⟩
    refine ⟨hy,fun z hz => ?_⟩
    exact (original_entire_stepOne_curve_interior_comparisons hn M hM hmax H S hcan z y hz hy).2.1.mpr (hdom z hz)

/-- Genuine NEW whole Step One/R1 CANONICAL history is constructed from
ONLY original CAN/domain/maximal order; actual same original suffix/centres. -/
theorem original_entire_stepOne_curve_interior_isCanonical (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M) (H.append S)) :
    IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M) (interiorEmptyHistory H S) := by
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
    · exact Or.inr (hm.trans (original_actual_stepOne_curve_maximum_dictionary hn M hM hmax H S hc).symm)

theorem original_entire_stepOne_curve_interior_canonical_resolution (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M) (H.append S))
    (hres : IsGeoResolution M (H.append S)) :
    IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M) (interiorEmptyHistory H S) ∧
      IsGeoResolution M (interiorEmptyHistory H S) := by
  have hH := (isGeoTestTower_append_iff M H S).mp hres.1 |>.1
  have ht := (HironakaOriginalCrossingValueTransport.isGeoTestTower_interior_empty_iff
    M hM.isWellFormed H hH S).mpr hres.1
  refine ⟨original_entire_stepOne_curve_interior_isCanonical hn M hM hmax H S hcan,ht,?_⟩
  rw [(geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1,hres.2]

end
end Hironaka.HironakaOriginalStepOneCurveHistory
