/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCurveLowerReferenceRebase
import Hironaka.Resolution.HironakaOriginalCurveLocalReferenceComparison
/-! Positive-level original masked lower values compare across genuine
earlier-mask histories without lower CAN or a false global curve reference. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPositiveCurveLowerComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen InvDomainMemberRestriction InvDomainRebase
  HomogenizedIdealAlong HomogenizedIdealAlongTower HomogenizedGlueingTower
  StepOneValue StepOneValueMasked StepOneCompare StepOneNearby StepOneMaskTower BoundaryCount
  CanonicalCentres HironakaOriginalCurveFullLocality HironakaOriginalCurveLowerReferenceRebase
  HironakaOriginalCurveLocalReferenceComparison
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X A B Y : CMfd.{u} n}

/-- All true lower geometry is ordinary and explicit; actual whole member
rebasing/locality produces the ORIGINAL finite lower-value equality. -/
theorem positive_curve_lower_value_rebase (hn : 0<n) (k : ℕ)
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (s : ℕ)
    (P : BlowupTower X A) (M : BlowupTower A B) (T : BlowupTower B Y)
    (hUpper : IsGeoTestTower (barMarked J) ((P.append M).append T)) (y₀ : B)
    (hDom₀ : IsInvDomain 1 (lowerMarkedM J (s+1) (P.append M) y₀))
    (hTest₀ : IsGeoTestTower (lowerMarkedM J (s+1) (P.append M) y₀)
      (restrict (lowerMask J (s+1) (P.append M) y₀) T))
    (p : Y) (hpW : T.proj p∈lowerMask J (s+1) (P.append M) y₀)
    (hlp : level J (P.append M) (T.proj p)=level J (P.append M) y₀)
    (hCos₀ : (⟨p,hpW⟩ : openPreimage T (lowerMask J (s+1) (P.append M) y₀))∈
      (geoTransformAlong (lowerMarkedM J (s+1) (P.append M) y₀)
        (restrict (lowerMask J (s+1) (P.append M) y₀) T)).cosupp)
    (hp₁ : (M.append T).proj p∈lowerMask J (s+1) P ((M.append T).proj p))
    (hDom₁ : IsInvDomain 1 (lowerMarkedM J (s+1) P ((M.append T).proj p)))
    (hTest₁ : IsGeoTestTower (lowerMarkedM J (s+1) P ((M.append T).proj p))
      (restrict (lowerMask J (s+1) P ((M.append T).proj p)) (M.append T)))
    (hCos₁ : (⟨p,hp₁⟩ : openPreimage (M.append T) (lowerMask J (s+1) P ((M.append T).proj p)))∈
      (geoTransformAlong (lowerMarkedM J (s+1) P ((M.append T).proj p))
        (restrict (lowerMask J (s+1) P ((M.append T).proj p)) (M.append T))).cosupp)
    (hAvoid : RestrictEmptyTower.CentresAvoid (lowerMask J (s+1) P ((M.append T).proj p)) M) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) J (lowerMarkedM J) (s+1) P (M.append T) p=
      (((invFamily hn (k+1)).inv (lowerMarkedM J (s+1) (P.append M) y₀)
        (restrict (lowerMask J (s+1) (P.append M) y₀) T) ⟨p,hpW⟩ : ValTy (k+1)) : WithTop (ValTy (k+1))) := by
  rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hn (k+1)) J _ hp₁]
  congr 1
  set W' := lowerMask J (s+1) P ((M.append T).proj p) with hW'
  set N := geoTransformAlong (barMarked J) P with hN
  set E₀ := origMembers J P with hE₀
  have hUpper' : IsGeoTestTower (barMarked J) (P.append (M.append T)) := by
    rw [← BlowupTower.append_assoc];exact hUpper
  obtain ⟨hP,hMT⟩ := (isGeoTestTower_append_iff _ P (M.append T)).mp hUpper'
  obtain ⟨hM,_⟩ := (isGeoTestTower_append_iff _ M T).mp hMT
  have hPM := ((isGeoTestTower_append_iff _ _ T).mp hUpper).1
  have hBar := StepOneLowerDomain.isWellFormed_barMarked J hJ
  have hWF : N.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hBar P hP
  have hWF₀ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hBar _ hPM
  have hdN : 1≤N.d := by
    rw [hN,d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hE₀N : ∀ H∈E₀,H∈N.E := fun H hH => List.mem_of_mem_take hH
  obtain ⟨hTestB,hValB⟩ := curve_full_value_restrict_append hn W' _ hDom₁ M T hTest₁
  have hPoint : (M.append T).proj p=M.proj (T.proj p) := by rw [BlowupTower.proj_append];rfl
  have hq : p∈openPreimage T (openPreimage M W') := show M.proj (T.proj p)∈W' from hPoint ▸ hp₁
  obtain ⟨hCosB,hValB⟩ := hValB p hp₁ hq hCos₁
  rw [←hValB k]
  have hMembers : membersThrough N.E E₀ (M.proj (T.proj p))=membersThrough N.E E₀ ((M.append T).proj p) := by rw [hPoint]
  have e₁ : lowerMarkedM J (s+1) P ((M.append T).proj p)=
      MarkedIdeal.pullback (Subtype.val : W' → A) (memberRestrict N (membersThrough N.E E₀ (M.proj (T.proj p)))) := by
    rw [hMembers];rfl
  rw [e₁] at hDom₁ hTestB hCosB ⊢
  let q₀ : openPreimage M W' := ⟨T.proj p,hq⟩
  obtain ⟨hDomS,hTestS,_hCosS,hValS⟩ := memberRestrict_curve_full_rebase hn N hWF hdN hE₀N
    M hM W' hAvoid q₀ hDom₁ (restrict (openPreimage M W') T) hTestB
  rw [hValS ⟨p,hq⟩ hCosB k]
  have hcongr : memberRestrict (geoTransformAlong N M)
      (membersThrough (geoTransformAlong N M).E (E₀.map (strictAlong M)) q₀.val)=
      memberRestrict (geoTransformAlong (barMarked J) (P.append M))
        (membersThrough (geoTransformAlong (barMarked J) (P.append M)).E (origMembers J (P.append M)) y₀) :=
    memberRestrict_membersThrough_congr (geoTransformAlong_append _ P M).symm (origMembers_append J P M).symm
      (mem_origMembers_iff_of_mem_maskA J (P.append M) hpW hlp)
  rw [hcongr] at hDomS hTestS ⊢
  have hMemberWF := isWellFormed_memberRestrict hn hWF₀
    (membersThrough (geoTransformAlong (barMarked J) (P.append M)).E (origMembers J (P.append M)) y₀)
  exact ((local_curve_full_two_opens hn _ hMemberWF.isCoherent
    (lowerMask J (s+1) (P.append M) y₀) (openPreimage M W') hDom₀ hDomS T hTest₀ hTestS p hpW hq).2 hCos₀ k).symm

end
end Hironaka.HironakaOriginalPositiveCurveLowerComparison
