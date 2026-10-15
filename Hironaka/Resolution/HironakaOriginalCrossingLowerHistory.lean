/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalSelectedPositiveLowerTail
import Hironaka.Blowup.BlowupTowerIsoTail
/-! Actual selected original lower histories whose run crosses an interior empty step.
Complete mathematics written first in
`hironaka-original-crossing-lower-history-extension.tex`. Whole invariant value/order
transport and the short-run zero-contact carrier remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCrossingLowerHistory
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit StepOneRegime StepOneValue
  StepOneValueMasked HironakaOriginalInteriorEmptyHistory BlowupTowerIsomorphism
  BlowupTowerIsoTail
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- The current regime and the actual crossing run internally supply the
regime at the ORIGINAL head point; no base-regime certificate is assumed. -/
theorem regime_at_base_of_reaching_run (P : Regime X) (H : BlowupTower X A) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower A Y) (y : Y),
      P (H.append S) y → S.length ≤ regimeRun P (H.append S) y → P H (S.proj y)
  | _, .refl, _, hcurrent, _ => hcurrent
  | _, .step S C π hπ, y, _, hreach => by
    by_cases hp : P (H.append S) (π y)
    · have hr := regimeRun_step_of P (H.append S) C π hπ hp
      change S.length + 1 ≤ regimeRun P (.step (H.append S) C π hπ) y at hreach
      rw [hr] at hreach
      exact regime_at_base_of_reaching_run P H S (π y) hp (by omega)
    · have hr := regimeRun_step_of_not P (H.append S) C π hπ hp
      change S.length + 1 ≤ regimeRun P (.step (H.append S) C π hπ) y at hreach
      rw [hr] at hreach
      omega

/-- The FULL actual concatenation split beyond its final tail, including
saturated indices, with its literal original stage/head/tail. -/
theorem split_append_above_tail (H : BlowupTower X A) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower A Y) (r : ℕ), S.length ≤ r →
      split (H.append S) r = ⟨(split H (r-S.length)).1,
        head H (r-S.length),(tail H (r-S.length)).append S⟩
  | _, .refl, r, _ => by
    simp only [BlowupTower.append_refl,BlowupTower.length_refl,Nat.sub_zero]
  | _, .step S _ _ _, 0, h => by
    change S.length + 1 ≤ 0 at h
    omega
  | _, .step S C π hπ, r+1, h => by
    have ih := split_append_above_tail H S r (by
      change S.length+1 ≤ r+1 at h
      omega)
    show (⟨(split (H.append S) r).1,(split (H.append S) r).2.1,
      .step (split (H.append S) r).2.2 C π hπ⟩ :
      Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D _) = _
    rw [ih]
    have he : r+1-(S.length+1) = r-S.length := by omega
    simp only [BlowupTower.length_step]
    rw [he]
    rfl

/-- The ACTUAL current-level crossing run and BOTH whole original selected
splits; the same assignment head survives, including at level zero. -/
theorem actual_crossing_selected_splits (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y)
    (y : Y) (hnonspecial : ¬ IsSpecial M (H.append S) y)
    (hreach : S.length ≤ regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y) :
    let r := regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y
    let r' := regimeRun (stepRegime M (level M (interiorEmptyHistory H S) y)) (interiorEmptyHistory H S) y
    let a := r-S.length
    r' = r+1 ∧
      split (H.append S) r = ⟨(split H a).1,head H a,(tail H a).append S⟩ ∧
      split (interiorEmptyHistory H S) r' =
        ⟨(split H a).1,head H a,interiorEmptyHistory (tail H a) S⟩ := by
  classical
  dsimp only
  let ℓ := level M (H.append S) y
  let r := regimeRun (stepRegime M ℓ) (H.append S) y
  have hbase : stepRegime M ℓ H (S.proj y) :=
    regime_at_base_of_reaching_run (stepRegime M ℓ) H S y ⟨rfl,hnonspecial⟩ hreach
  have hr : regimeRun (stepRegime M (level M (interiorEmptyHistory H S) y))
      (interiorEmptyHistory H S) y = r+1 := by
    rw [level_dictionary M hM H hH S y,stepRegime_run_dictionary M hM H hH ℓ S y]
    rw [if_neg (not_lt_of_ge hreach),if_pos hbase]
  have hreachr : S.length ≤ r := hreach
  have hnew := split_append_above_tail
    (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S (r+1) (by omega)
  have hsub : r+1-S.length = (r-S.length)+1 := by omega
  rw [hsub] at hnew
  change split (interiorEmptyHistory H S) (r+1) =
    ⟨(split H (r-S.length)).1,head H (r-S.length),interiorEmptyHistory (tail H (r-S.length)) S⟩ at hnew
  refine ⟨hr,split_append_above_tail H S r hreach,?_⟩
  rw [hr]
  exact hnew

/-- The genuine identity empty blowup restricts to the SAME actual open
preimage with the literal identity projection and empty centre. -/
theorem restrict_identity_empty_step (W : Opens X) (B : BlowupTower X A) :
    restrict W (B.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) =
      (restrict W B).step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty := by
  rfl

/-- WHOLE actual restricted-tail diagram, with the genuine interior empty
identity step supplied internally by restriction and its true universal property. -/
theorem actual_restricted_empty_history (W : Opens X) (B : BlowupTower X A) (S : BlowupTower A Y) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞)
      (restrict W (interiorEmptyHistory B S))
      (interiorEmptyHistory (restrict W B) (restrict (openPreimage B W) S))
      (opensCongr (openPreimage_append
        (B.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S W).symm) := by
  have h := isTowerIso_restrict_append W
    (B.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S
  rw [restrict_identity_empty_step] at h
  exact h

/-- The actual common selected lower record and genuine new restricted tail
at EVERY level, including the original zero-contact lower record. -/
theorem actual_crossing_lower_history (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y)
    (y : Y) (hnonspecial : ¬ IsSpecial M (H.append S) y)
    (hreach : S.length ≤ regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y) :
    let ℓ := level M (H.append S) y
    let r := regimeRun (stepRegime M ℓ) (H.append S) y
    let a := r-S.length
    let K := head H a
    let B := tail H a
    let p := (B.append S).proj y
    let p' := (interiorEmptyHistory B S).proj y
    let W := lowerMask M ℓ K p
    regimeRun (stepRegime M (level M (interiorEmptyHistory H S) y)) (interiorEmptyHistory H S) y = r+1 ∧
      p' = p ∧ lowerMask M ℓ K p' = W ∧ HEq (lowerMarkedM M ℓ K p') (lowerMarkedM M ℓ K p) ∧
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞)
        (restrict W (interiorEmptyHistory B S))
        (interiorEmptyHistory (restrict W B) (restrict (openPreimage B W) S))
        (opensCongr (openPreimage_append
          (B.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S W).symm) := by
  dsimp only
  refine ⟨(actual_crossing_selected_splits M hM H hH S y hnonspecial hreach).1,?_,?_,?_,?_⟩
  · exact congrFun (proj_interiorEmptyHistory _ S) y
  · rw [proj_interiorEmptyHistory]
  · apply congr_arg_heq (lowerMarkedM M _ _)
    exact congrFun (proj_interiorEmptyHistory _ S) y
  · exact actual_restricted_empty_history _ _ S

end
end Hironaka.HironakaOriginalCrossingLowerHistory
