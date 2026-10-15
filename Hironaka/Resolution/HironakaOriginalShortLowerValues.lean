/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalInteriorZeroLowerHistory
/-! Whole actual recursively constructed lower values in original short histories.
The complete mathematical route was written first in `hironaka-original-short-lower-values-extension.tex`.
No arbitrary-R empty-boundary/value certificate is assumed. Full crossing
recursive value transport and complete outer general history remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalShortLowerValues
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked MonomialInvariantEmptyMember
  HironakaOriginalInvariantEmptyInsertion HironakaOriginalInteriorEmptyHistory
  HironakaOriginalInteriorPositiveLower HironakaOriginalSelectedPositiveLowerTail
  HironakaOriginalInteriorZeroLowerHistory
variable {n : ℕ} {X A D Y : CMfd.{u} n}

open Classical in
private def actualMaskValue (hn : 0 < n) (k : ℕ) (U : Opens D)
    (J : MarkedIdeal n U) (Q : BlowupTower D Y) (y : Y) : WithTop (ValTy k) :=
  if h : Q.proj y ∈ U then
    ((invFamily hn k).inv J (restrict U Q) (⟨y,h⟩ : openPreimage Q U) : WithTop (ValTy k))
  else ⊤

/-- A private equal-open record helper for the SPECIFIC proved actual family;
its true insertion theorem is supplied internally, not a caller R certificate. -/
private theorem actualMaskValue_insertEmpty (hn : 0 < n) (k : ℕ)
    (U V : Opens D) (J : MarkedIdeal n U) (K : MarkedIdeal n V)
    (hUV : U=V) (j : ℕ) (hj : j ≤ K.E.length)
    (hJK : HEq J (insertEmpty j K)) (Q : BlowupTower D Y) (y : Y) :
    actualMaskValue hn k U J Q y =
      WithTop.map (shiftFamily k j) (actualMaskValue hn k V K Q y) := by
  classical
  subst V
  have hJ : J = insertEmpty j K := eq_of_heq hJK
  subst J
  unfold actualMaskValue
  split_ifs with h
  · exact congrArg (fun v : ValTy k => (v : WithTop (ValTy k)))
      (invFamily_insertEmpty hn k K j hj (restrict U Q) (⟨y,h⟩ : openPreimage Q U))
  · rfl

/-- The whole original zero lower value in ALL actual recursive dimensions,
including its genuine missing-mask top branch. -/
theorem original_zero_lowerValue (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H)
    (P : BlowupTower A D) (hP : 0 < P.length) (Q : BlowupTower D Y) (y : Y) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) 0
        (interiorEmptyHistory H P) Q y =
      WithTop.map (shiftFamily k (M.E.length + H.length))
        (Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) 0
          (H.append P) Q y) := by
  change actualMaskValue hn k _ _ Q y =
    WithTop.map (shiftFamily k (M.E.length + H.length)) (actualMaskValue hn k _ _ Q y)
  exact actualMaskValue_insertEmpty hn k _ _ _ _
    (lowerMask_dictionary M hM H hH P 0 (Q.proj y)) _
    (zeroLowerIndex_le_boundary M H P (Q.proj y))
    (original_zero_lower_record M hM H hH P hP (Q.proj y)) Q y

/-- The whole original positive lower value at its ACTUAL future filtered
index, without a hidden original-empty-prefix or desired lower-value premise. -/
theorem original_positive_lowerValue (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H)
    (P : BlowupTower A D) (hP : 0 < P.length) (Q : BlowupTower D Y) (y : Y) (s : ℕ) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) (s+1)
        (interiorEmptyHistory H P) Q y =
      WithTop.map (shiftFamily k (interiorPositiveLowerIndex M H P (Q.proj y)))
        (Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) (s+1)
          (H.append P) Q y) := by
  change actualMaskValue hn k _ _ Q y =
    WithTop.map (shiftFamily k (interiorPositiveLowerIndex M H P (Q.proj y)))
      (actualMaskValue hn k _ _ Q y)
  exact actualMaskValue_insertEmpty hn k _ _ _ _
    (lowerMask_dictionary M hM H hH P (s+1) (Q.proj y)) _
    (interiorPositiveLowerIndex_le_boundary M H P (Q.proj y) s)
    (original_positive_lower_record M hM H hH P hP (Q.proj y) s) Q y

private def splitLowerValue (hn : 0 < n) (k : ℕ) (M : MarkedIdeal n X) (s : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) : WithTop (ValTy k) :=
  Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) s v.2.1 v.2.2 y

/-- The ACTUAL entire own-level Step One value over the recursively
constructed family, uniformly on the original zero-level short branch. -/
theorem actual_short_zero_stepOne_value (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H)
    (S : BlowupTower A Y) (y : Y) (hlevel : level M (H.append S) y = 0)
    (hshort : regimeRun (stepRegime M 0) (H.append S) y < S.length) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y =
      pairShift (shiftFamily k (M.E.length + H.length))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y) := by
  classical
  have hnewlevel : level M (interiorEmptyHistory H S) y = 0 :=
    (level_dictionary M hM H hH S y).trans hlevel
  have hc := actual_short_all_level_splits M hM H hH S y (by simpa only [hlevel] using hshort)
  rw [hlevel,hnewlevel] at hc
  have hnewcut := hc.2.2
  rw [hc.1] at hnewcut
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [hlevel,hnewlevel]
  by_cases hs : IsSpecial M (H.append S) y
  · rw [if_pos hs,if_pos ((isSpecial_dictionary M hM H hH S y).mpr hs)]
    rfl
  · rw [if_neg hs,if_neg (fun h => hs ((isSpecial_dictionary M hM H hH S y).mp h))]
    rw [hc.1]
    change toLex (0,splitLowerValue hn k M 0
        (split (interiorEmptyHistory H S) (regimeRun (stepRegime M 0) (H.append S) y)) y) =
      pairShift (shiftFamily k (M.E.length + H.length))
        (toLex (0,splitLowerValue hn k M 0
          (split (H.append S) (regimeRun (stepRegime M 0) (H.append S) y)) y))
    simp only [pairShift,ofLex_toLex]
    apply congrArg (fun v : WithTop (ValTy k) => toLex (0,v))
    rw [hnewcut,hc.2.1]
    exact original_zero_lowerValue hn k M hM H hH _ (by rw [length_head];omega) _ y

/-- The ACTUAL entire positive short-run Step One value at the internally
computed future lower boundary index. No both-zero cross-index order claim. -/
theorem actual_short_positive_stepOne_value (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H)
    (S : BlowupTower A Y) (y : Y) (s : ℕ) (hlevel : level M (H.append S) y = s+1)
    (hshort : regimeRun (stepRegime M (s+1)) (H.append S) y < S.length) :
    let r := regimeRun (stepRegime M (s+1)) (H.append S) y
    let c := interiorPositiveLowerIndex M H (head S r) ((tail S r).proj y)
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y =
      pairShift (shiftFamily k c)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y) := by
  classical
  dsimp only
  have hnewlevel : level M (interiorEmptyHistory H S) y = s+1 :=
    (level_dictionary M hM H hH S y).trans hlevel
  have hc := actual_short_all_level_splits M hM H hH S y (by simpa only [hlevel] using hshort)
  rw [hlevel,hnewlevel] at hc
  have hnewcut := hc.2.2
  rw [hc.1] at hnewcut
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [hlevel,hnewlevel]
  by_cases hs : IsSpecial M (H.append S) y
  · rw [if_pos hs,if_pos ((isSpecial_dictionary M hM H hH S y).mpr hs)]
    rfl
  · rw [if_neg hs,if_neg (fun h => hs ((isSpecial_dictionary M hM H hH S y).mp h))]
    rw [hc.1]
    change toLex (s+1,splitLowerValue hn k M (s+1)
        (split (interiorEmptyHistory H S) (regimeRun (stepRegime M (s+1)) (H.append S) y)) y) =
      pairShift (shiftFamily k (interiorPositiveLowerIndex M H
        (head S (regimeRun (stepRegime M (s+1)) (H.append S) y))
        ((tail S (regimeRun (stepRegime M (s+1)) (H.append S) y)).proj y)))
        (toLex (s+1,splitLowerValue hn k M (s+1)
          (split (H.append S) (regimeRun (stepRegime M (s+1)) (H.append S) y)) y))
    simp only [pairShift,ofLex_toLex]
    apply congrArg (fun v : WithTop (ValTy k) => toLex (s+1,v))
    rw [hnewcut,hc.2.1]
    exact original_positive_lowerValue hn k M hM H hH _ (by rw [length_head];omega) _ y s

/-- All actual strict/weak/equality comparisons on the full original
zero-level short spectrum, at every actual recursive lower dimension. -/
theorem actual_short_zero_spectrum_comparisons (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y)
    (y z : Y) (hy : level M (H.append S) y = 0) (hz : level M (H.append S) z = 0)
    (hry : regimeRun (stepRegime M 0) (H.append S) y < S.length)
    (hrz : regimeRun (stepRegime M 0) (H.append S) z < S.length) :
    let v := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y
    let w := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) z
    let v' := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y
    let w' := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) z
    (v' < w' ↔ v < w) ∧ (v' ≤ w' ↔ v ≤ w) ∧ (v' = w' ↔ v = w) := by
  dsimp only
  rw [actual_short_zero_stepOne_value hn k M hM H hH S y hy hry,
    actual_short_zero_stepOne_value hn k M hM H hH S z hz hrz]
  have hm := strictMono_pairShift (strictMono_shiftFamily k (M.E.length + H.length))
  exact ⟨hm.lt_iff_lt,hm.le_iff_le,hm.injective.eq_iff⟩

/-- Maximum-DOMINANCE predicates on any actual zero-short set are unchanged;
no maximum existence or noncompact global scheduling is asserted. -/
theorem maxLocus_actual_short_zero_spectrum (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y)
    (Z : Set Y) (hZ : ∀ y ∈ Z, level M (H.append S) y = 0 ∧
      regimeRun (stepRegime M 0) (H.append S) y < S.length) :
    ResolutionDriver.maxLocus
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S)) Z =
      ResolutionDriver.maxLocus
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S)) Z := by
  ext y
  change (y ∈ Z ∧ ∀ z ∈ Z, _ ≤ _) ↔ (y ∈ Z ∧ ∀ z ∈ Z, _ ≤ _)
  constructor
  · rintro ⟨hy,hmax⟩
    refine ⟨hy,fun z hz => ?_⟩
    exact (actual_short_zero_spectrum_comparisons hn k M hM H hH S z y
      (hZ z hz).1 (hZ y hy).1 (hZ z hz).2 (hZ y hy).2).2.1.mp (hmax z hz)
  · rintro ⟨hy,hmax⟩
    refine ⟨hy,fun z hz => ?_⟩
    exact (actual_short_zero_spectrum_comparisons hn k M hM H hH S z y
      (hZ z hz).1 (hZ y hy).1 (hZ z hz).2 (hZ y hy).2).2.1.mpr (hmax z hz)

end
end Hironaka.HironakaOriginalShortLowerValues
