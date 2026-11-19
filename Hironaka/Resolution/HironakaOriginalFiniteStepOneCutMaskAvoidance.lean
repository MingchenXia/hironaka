/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteLevelCutLowerTests
/-! Literal finite original StepOne cuts provide real earlier-mask avoidance;
no centre equality with the whole maximum or canonical lower data is used. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteStepOneCutMaskAvoidance
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction
  StepOneLowerDomain StepOneValue StepOneValueMasked StepOneRegime StepOneCanonicalTail
  StepOneCompare StepOneMaskTower RestrictEmptyTower MemberRestrictAdmissible HironakaOriginalFrozenRecursiveLower
  HironakaOriginalFiniteLevelCutLowerTests
open ResolutionInvariantSpec (IsInvDomain)
variable {n k : ℕ} {X Y Z Y₀ : CMfd.{u} n}

def IsStepOneCutTower (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n},BlowupTower X Y → Prop
  | _,.refl => True
  | _,.step T C _ _ => IsStepOneCutTower hn k M T ∧
      (geoTransformAlong M T).IsAdmissibleCentre C ∧
      ∀ y∈(geoTransformAlong M T).cosupp,∀ c∈C,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c

theorem stepOneCutTower_levelCut (hn : 0<n) (M : MarkedIdeal n X)
    (T : BlowupTower X Y) (hT : IsStepOneCutTower hn k M T) : IsLevelCutTower M T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    exact levelCutTower_step_of_stepone_cut hn M T (ih hT.1) C hT.2.1 π hπ hT.2.2

private theorem actual_stepone_lt_outer_top (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsStepOneCutTower hn k M T)
    (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y<
      toLex (level M T y,(⊤ : WithTop (ValTy k))) := by
  obtain ⟨_hD,_hTest,_hCurrent,hp,_hPoint,_hCos⟩ := levelCutTower_current_lower_data
    hn M hM hmax T (stepOneCutTower_levelCut hn M T hT) y hy hns
  change Seq.StepOneValueMasked.stepOneInvL (invFamily hn k) M (lowerMarkedM M) T y<
    toLex (level M T y,(⊤ : WithTop (ValTy k)))
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial (invFamily hn k) M (lowerMarkedM M) T hns,
    Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hn k) M (lowerMarkedM M) hp,Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl,WithTop.coe_lt_top _⟩

/-- Real current mask membership, not lower CAN, proves the original value
strict comparison needed to avoid earlier masks along finite preparations. -/
theorem actual_stepone_lt_of_earlier_mask (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T₀ : BlowupTower X Y₀) (S : BlowupTower Y₀ Y)
    (hT : IsStepOneCutTower hn k M (T₀.append S))
    (s : ℕ) (p₀ : Y₀) (hp₀ : level M T₀ p₀=s)
    (q : Y) (hq : q∈(geoTransformAlong M (T₀.append S)).cosupp)
    (hqW : S.proj q∈lowerMask M s T₀ p₀)
    (w : Y) (hw : s≤level M (T₀.append S) w)
    (hnw : ¬stepRegime M s (T₀.append S) w) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (T₀.append S) q<
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (T₀.append S) w := by
  have hUpper := levelCutTower_geoTest M (T₀.append S) (stepOneCutTower_levelCut hn M _ hT)
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) (T₀.append S) := (he.2 _).1.mpr hUpper
  have hLe : level M (T₀.append S) q≤s :=
    level_le_of_mem_lowerMask M (fun H hH => hM.isWellFormed.isSNCDivisor.1 H hH) T₀ S hp₀ hqW
  rcases hLe.lt_or_eq with hLt|hEq
  · exact Seq.StepOneValueMasked.stepOneInvL_lt_of_level_lt (invFamily hn k) M (lowerMarkedM M) (hLt.trans_le hw)
  · have hReg := (stepRegime_and_le_regimeRun_of_mem_lowerMask M hM.isWellFormed
      hM.one_le_d hmax T₀ S hBar hp₀ hqW hEq).1
    have hFinite := actual_stepone_lt_outer_top hn M hM hmax (T₀.append S) hT q hq hReg.2
    rw [hEq] at hFinite
    exact hFinite.trans_le (Seq.StepOneValueMasked.toLex_top_le_stepOneInvL (invFamily hn k) M (lowerMarkedM M) _ hw hnw)

/-- The ordinary actual StepOne cut contradicts the strict earlier-mask
comparison; no equality with an entire maximum locus is required. -/
theorem stepOneCutTower_disjoint_earlier_mask (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T₀ : BlowupTower X Y₀) (S : BlowupTower Y₀ Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsStepOneCutTower hn k M (T₀.append (.step S C π hπ)))
    (s : ℕ) (p₀ : Y₀) (hp₀ : level M T₀ p₀=s)
    (w : Y) (hw : w∈(geoTransformAlong M (T₀.append S)).cosupp)
    (hlw : s≤level M (T₀.append S) w) (hnw : ¬stepRegime M s (T₀.append S) w) :
    Disjoint C (S.proj ⁻¹' (lowerMask M s T₀ p₀ : Set Y₀)) := by
  apply Set.disjoint_left.mpr
  intro q hqC hqW
  have hqCos : q∈(geoTransformAlong M (T₀.append S)).cosupp := hT.2.1.2.1 hqC
  have hStrict := actual_stepone_lt_of_earlier_mask hn M hM hmax T₀ S hT.1 s p₀ hp₀
    q hqCos hqW w hlw hnw
  exact (not_le.mpr hStrict) (hT.2.2 w hw q hqC)

/-- ALL real centres between two regime starts avoid the WHOLE earlier
mask along literal finite original cuts, without canonicality certificates. -/
theorem stepOneCutTower_centresAvoid_earlier_mask (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T₀ : BlowupTower X Y₀) (s : ℕ) (p₀ : Y₀) (hp₀ : level M T₀ p₀=s) :
    ∀ {Y Z : CMfd.{u} n} (S : BlowupTower Y₀ Y) (C : Set Y) (π : Z → Y)
      (hπ : IsBlowupAlong n C π),
      IsStepOneCutTower hn k M (T₀.append (.step S C π hπ)) →
      ∀ w∈(geoTransformAlong M (T₀.append S)).cosupp,s≤level M (T₀.append S) w →
        ¬stepRegime M s (T₀.append S) w →
          CentresAvoid (lowerMask M s T₀ p₀) (.step S C π hπ)
  | _,_,.refl,C,π,hπ,hT,w,hw,hlw,hnw => by
    exact ⟨trivial,stepOneCutTower_disjoint_earlier_mask hn M hM hmax T₀ .refl C π hπ
      hT s p₀ hp₀ w hw hlw hnw⟩
  | _,_,.step S₂ C₂ π₂ hπ₂,C,π,hπ,hT,w,hw,hlw,hnw => by
    have hPre : IsStepOneCutTower hn k M (T₀.append (.step S₂ C₂ π₂ hπ₂)) := hT.1
    have hPreTest := levelCutTower_geoTest M _ (stepOneCutTower_levelCut hn M _ hPre)
    have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.one_le_d
    have hBar : IsGeoTestTower (barMarked M) (T₀.append (.step S₂ C₂ π₂ hπ₂)) :=
      (he.2 _).1.mpr hPreTest
    have hwBar : w∈(geoTransformAlong (barMarked M) (T₀.append (.step S₂ C₂ π₂ hπ₂))).cosupp := by
      rw [(he.2 _).2 hBar];exact hw
    obtain ⟨hw₂,hl₂,hn₂⟩ := StepOneNearby.not_stepRegime_proj M hM.isWellFormed hM.one_le_d
      hn hmax hM.dimLE (T₀.append S₂) C₂ π₂ hπ₂ hBar hwBar hlw hnw
    have hEarlierTest := levelCutTower_geoTest M _ (stepOneCutTower_levelCut hn M _ hPre.1)
    have hBarEarlier : IsGeoTestTower (barMarked M) (T₀.append S₂) := (he.2 _).1.mpr hEarlierTest
    have hwOriginal : π₂ w∈(geoTransformAlong M (T₀.append S₂)).cosupp := by
      rwa [(he.2 _).2 hBarEarlier] at hw₂
    exact ⟨stepOneCutTower_centresAvoid_earlier_mask hn M hM hmax T₀ s p₀ hp₀
      S₂ C₂ π₂ hπ₂ hPre (π₂ w) hwOriginal hl₂ hn₂,
      stepOneCutTower_disjoint_earlier_mask hn M hM hmax T₀ (.step S₂ C₂ π₂ hπ₂)
        C π hπ hT s p₀ hp₀ w hw hlw hnw⟩

end
end Hironaka.HironakaOriginalFiniteStepOneCutMaskAvoidance
