/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneSpecialAnalyticLoci

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-! All genuine Step 1 thresholds over the actual canonical lower base.
Blueprint `hironaka-step-one-dimzero-superlevels-extension.tex`.
The actual canonical lower base and historical mask generate all real thresholds. -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaStepOneDimZeroAnalyticSuperlevels

open Hironaka.BlowupSequences
open MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  StepOneValue StepOneValueMasked StepOneLowerDomain HomogenizedIdealAlong StepOneRegime
  HironakaStepOneSpecialAnalyticLoci HironakaBoundaryCountAnalyticSuperlevels CanonicalCentres

noncomputable section
universe u v
variable {n : ℕ} {X Y : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- Genuine lower-mask membership exposes the actual constant lower base
at every nonspecial cosupport point, including its actual historical tail. -/
theorem lowerValue_ofDimZero_eq (l₀ : Λ) (hn : 0 < n) (𝔍 : MarkedIdeal n X)
    (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp)
    (hsp : ¬ IsSpecial 𝔍 T y) :
    Seq.StepOneValueMasked.lowerValueL
      (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero Λ l₀) 𝔍 (lowerMarkedM 𝔍)
      (level 𝔍 T y) (BlowupTowerSplit.head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y))
      (BlowupTowerSplit.tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y = (l₀ : WithTop Λ) := by
  classical
  have hne := Seq.StepOneValueMasked.lowerValueL_ne_top
    (R := ResolutionInvariantSeq.ResolutionInvariant.ofDimZero Λ l₀)
    𝔍 h𝔍 hd hn hmax (lowerMarkedM 𝔍) T hT hy hsp
  unfold Seq.StepOneValueMasked.lowerValueL
  split_ifs with hmem
  · rfl
  · simp only [Seq.StepOneValueMasked.lowerValueL, dif_neg hmem] at hne
    exact False.elim (hne rfl)

private theorem threshold_iff (l₀ : Λ) (hn : 0 < n) (𝔍 : MarkedIdeal n X)
    (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (s : ℕ) (α : WithTop Λ) :
    toLex (s, α) ≤ Seq.StepOneValueMasked.stepOneInvM
      (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero Λ l₀) 𝔍 T y ↔
      s < level 𝔍 T y ∨ (s = level 𝔍 T y ∧ (IsSpecial 𝔍 T y ∨ α ≤ (l₀ : WithTop Λ))) := by
  classical
  by_cases hsp : IsSpecial 𝔍 T y
  · simp [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL,
      hsp, Prod.Lex.toLex_le_toLex]
  · have hlow := lowerValue_ofDimZero_eq l₀ hn 𝔍 h𝔍 hd hmax T hT hy hsp
    rw [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL, if_neg hsp,
      hlow, Prod.Lex.toLex_le_toLex]
    simp [hsp]

/-- The actual lower base makes every whole actual Step 1 threshold analytic;
the finite and top lower thresholds are both produced, without certificates. -/
theorem isComplexAnalyticSubset_stepOneInvM_ofDimZero_superlevel
    (l₀ : Λ) (hn : 0 < n) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T) (s : ℕ) (α : WithTop Λ) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        toLex (s, α) ≤ Seq.StepOneValueMasked.stepOneInvM
          (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero Λ l₀) 𝔍 T y} := by
  classical
  by_cases hα : α ≤ (l₀ : WithTop Λ)
  · have heq : {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        toLex (s, α) ≤ Seq.StepOneValueMasked.stepOneInvM
          (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero Λ l₀) 𝔍 T y} =
        (geoTransformAlong (barMarked 𝔍) T).cosupp ∩ {y | s ≤ level 𝔍 T y} := by
      ext y
      constructor
      · rintro ⟨hy, hv⟩
        rcases (threshold_iff l₀ hn 𝔍 h𝔍 hd hmax T hT hy s α).mp hv with
          hlt | ⟨heq, -⟩
        · exact ⟨hy, hlt.le⟩
        · exact ⟨hy, heq.le⟩
      · rintro ⟨hy, hle⟩
        change s ≤ level 𝔍 T y at hle
        refine ⟨hy, (threshold_iff l₀ hn 𝔍 h𝔍 hd hmax T hT hy s α).mpr ?_⟩
        rcases hle.lt_or_eq with hlt | heq
        · exact Or.inl hlt
        · exact Or.inr ⟨heq, Or.inr hα⟩
    rw [heq]
    have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (isWellFormed_barMarked 𝔍 h𝔍) T hT
    have hdT : 1 ≤ (geoTransformAlong (barMarked 𝔍) T).d := by
      rw [d_geoTransformAlong]
      exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
    exact (CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along
      hwf.isCoherent hwf.isClosedSubmanifold_N hdT).inter
        (isComplexAnalyticSubset_stepOne_level_superlevel hn 𝔍 h𝔍 T hT s)
  · have heq : {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        toLex (s, α) ≤ Seq.StepOneValueMasked.stepOneInvM
          (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero Λ l₀) 𝔍 T y} =
        {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
          toLex (s, (⊤ : WithTop Λ)) ≤ Seq.StepOneValueMasked.stepOneInvM
            (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero Λ l₀) 𝔍 T y} := by
      ext y
      by_cases hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp
      · simp only [mem_ofPred_eq, hy, true_and,
          threshold_iff l₀ hn 𝔍 h𝔍 hd hmax T hT hy s α,
          stepOneInvM_top_threshold_iff (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero Λ l₀)
            hn 𝔍 h𝔍 hd hmax T hT hy s, hα, or_false]
      · simp only [mem_ofPred_eq, hy, false_and]
    rw [heq]
    exact isComplexAnalyticSubset_stepOneInvM_top_superlevel
      (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero Λ l₀) hn 𝔍 h𝔍 hd hmax T hT s

/-- This is the actual lower base used by the constructed canonical recursion,
so all of its maximal-order Step 1 superlevels have been genuinely produced. -/
theorem isComplexAnalyticSubset_canonical_stepOne_base_superlevel
    (hn : 0 < n) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T) (s : ℕ) (α : WithTop (ValTy 0)) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        toLex (s, α) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 0) 𝔍 T y} := by
  simpa only [invFamily] using
    isComplexAnalyticSubset_stepOneInvM_ofDimZero_superlevel
      (Λ := ValTy 0) (show ValTy 0 from (0 : ℕ))
      hn 𝔍 h𝔍 hd hmax T hT s α

end
end Hironaka.HironakaStepOneDimZeroAnalyticSuperlevels
