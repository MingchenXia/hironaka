/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteStepOneCutMaskAvoidance
/-! Real middle histories between original run starts from literal finite cuts.
No canonical prefix or canonical lower-data field is supplied. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteStepOneCutMiddleHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong HomogenizedIdealAlongTower
  StepOneValue StepOneValueMasked StepOneRegime StepOneCanonicalTail StepOneNearby RestrictEmptyTower
  HironakaOriginalFiniteLevelCutLowerTests HironakaOriginalFiniteStepOneCutMaskAvoidance
open ResolutionInvariantSpec (IsInvDomain)
variable {n k : ℕ} {X Y : CMfd.{u} n}

theorem stepOneCutTower_head (hn : 0<n) (M : MarkedIdeal n X)
    (T : BlowupTower X Y) (hT : IsStepOneCutTower hn k M T) (r : ℕ) :
    IsStepOneCutTower hn k M (head T r) := by
  induction T generalizing r with
  | refl => cases r <;> trivial
  | step T C π hπ ih =>
    cases r with
    | zero => exact hT
    | succ r => exact ih hT.1 r

/-- Genuine split geometry and ALL-centres earlier-mask avoidance on actual
finite original cut histories, with no canonical or lower-value certificate. -/
theorem exists_actual_middle_of_stepone_cut (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsStepOneCutTower hn k M T)
    (z q : Y) (hz : z∈(geoTransformAlong M T).cosupp) (s : ℕ) (hs : level M T z=s)
    (rz rq : ℕ) (hrz : regimeRun (stepRegime M s) T z=rz)
    (hrq : regimeRun (stepRegime M s) T q=rq) (hle : rz≤rq)
    (hp₁ : level M (head T rq) ((tail T rq).proj q)=s) :
    ∃ B : BlowupTower (split T rq).1 (split T rz).1,
      (head T rq).append B=head T rz ∧ B.append (tail T rz)=tail T rq ∧
      CentresAvoid (lowerMask M s (head T rq) ((tail T rq).proj q)) B := by
  have hGeo := levelCutTower_geoTest M T (stepOneCutTower_levelCut hn M T hT)
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hGeo
  have hzBar : z∈(geoTransformAlong (barMarked M) T).cosupp := by
    rw [(he.2 T).2 hBar];exact hz
  rcases hle.lt_or_eq with hlt|heq
  · have hrqle : rq≤T.length := hrq ▸ regimeRun_le_length _ T q
    have hrzlt : rz<T.length := lt_of_lt_of_le hlt hrqle
    obtain ⟨τ,hτ₁,hτ₂⟩ := exists_split_le T (a := rz) (b := rz+1) (Nat.le_succ rz)
    have hτlen : τ.length=1 := by
      have hh := congrArg BlowupTower.length hτ₁
      rw [BlowupTower.length_append,length_head,length_head] at hh
      omega
    obtain ⟨Cm,πm,hπm,rfl⟩ := exists_eq_step_refl τ hτlen
    obtain ⟨B₂,hB₁,hB₂⟩ := exists_split_le T (a := rz+1) (b := rq) (by omega)
    refine ⟨B₂.append (.step .refl Cm πm hπm),?_,?_,?_⟩
    · rw [←BlowupTower.append_assoc,hB₁,hτ₁]
    · rw [BlowupTower.append_assoc,hτ₂,hB₂]
    · show CentresAvoid _ (.step B₂ Cm πm hπm)
      have hNot := not_regime_head_regimeRun (stepRegime M s) T z (by rw [hrz];exact hrzlt)
      rw [hrz] at hNot
      have hw := mem_cosupp_head M hM.isWellFormed T hBar hzBar (rz+1)
      have hlw := level_le_head M (fun H hH => hM.isWellFormed.isSNCDivisor.1 H hH) T z (rz+1)
      rw [hs] at hlw
      rw [←hB₁] at hNot hw hlw
      have hWhole : (head T rq).append (.step B₂ Cm πm hπm)=head T rz := by
        rw [←hτ₁,←hB₁]
        rfl
      have hPrefix : IsStepOneCutTower hn k M ((head T rq).append (.step B₂ Cm πm hπm)) := by
        rw [hWhole];exact stepOneCutTower_head hn M T hT rz
      have hOldTest := levelCutTower_geoTest M _ (stepOneCutTower_levelCut hn M _ hPrefix.1)
      have hOldBar : IsGeoTestTower (barMarked M) ((head T rq).append B₂) := (he.2 _).1.mpr hOldTest
      have hwOriginal := hw
      rw [(he.2 _).2 hOldBar] at hwOriginal
      exact stepOneCutTower_centresAvoid_earlier_mask hn M hM hmax (head T rq) s
        ((tail T rq).proj q) hp₁ B₂ Cm πm hπm hPrefix _ hwOriginal hlw hNot
  · subst heq
    obtain ⟨B,hB₁,hB₂⟩ := exists_split_le T (le_refl rz)
    refine ⟨B,hB₁,hB₂,centresAvoid_of_length_eq_zero _ B ?_⟩
    have hh := congrArg BlowupTower.length hB₁
    rw [BlowupTower.length_append] at hh
    omega

end
end Hironaka.HironakaOriginalFiniteStepOneCutMiddleHistory
