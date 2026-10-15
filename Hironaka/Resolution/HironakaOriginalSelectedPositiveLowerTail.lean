/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalInteriorPositiveLower
/-! The genuine selected positive lower-history diagram for a short original run.
Complete mathematics written first in
`hironaka-original-selected-positive-lower-tail-extension.tex`. Cross-insertion runs,
zero-contact carriers and full higher values/order/scheduling remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalSelectedPositiveLowerTail
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit StepOneRegime StepOneValue
  StepOneValueMasked MonomialInvariantEmptyMember HironakaOriginalInteriorEmptyHistory
  HironakaOriginalInteriorPositiveLower
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Both literal original split records, at the genuinely computed current-level run. -/
theorem actual_short_positive_splits (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y)
    (y : Y) (s : ℕ) (hlevel : level M (H.append S) y = s+1)
    (hshort : regimeRun (stepRegime M (s+1)) (H.append S) y < S.length) :
    let r := regimeRun (stepRegime M (s+1)) (H.append S) y
    let r' := regimeRun (stepRegime M (level M (interiorEmptyHistory H S) y)) (interiorEmptyHistory H S) y
    r' = r ∧
      split (H.append S) r = ⟨(split S r).1,H.append (head S r),tail S r⟩ ∧
      split (interiorEmptyHistory H S) r' =
        ⟨(split S r).1,interiorEmptyHistory H (head S r),tail S r⟩ := by
  dsimp only
  have hr : regimeRun (stepRegime M (level M (interiorEmptyHistory H S) y))
      (interiorEmptyHistory H S) y = regimeRun (stepRegime M (s+1)) (H.append S) y := by
    rw [level_dictionary M hM H hH S y,hlevel,stepRegime_run_dictionary M hM H hH (s+1) S y]
    exact if_pos hshort
  refine ⟨hr,StepOneEmptyPrefix.split_append_of_le H S _ hshort.le,?_⟩
  rw [hr]
  exact StepOneEmptyPrefix.split_append_of_le
    (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S _ hshort.le

private theorem restrict_heq_of_equal_masks {D B : CMfd.{u} n}
    (U V : Opens D) (hUV : U=V) (Q : BlowupTower D B) :
    HEq (restrict U Q) (restrict V Q) := by
  cases hUV
  rfl

/-- Actual selected original lower records and WHOLE restricted tail records.
The nonempty selected prefix and valid actual future index are supplied internally. -/
theorem actual_short_positive_lower_diagram (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y)
    (y : Y) (s : ℕ) (hlevel : level M (H.append S) y = s+1)
    (hshort : regimeRun (stepRegime M (s+1)) (H.append S) y < S.length) :
    let r := regimeRun (stepRegime M (s+1)) (H.append S) y
    let P := head S r
    let Q := tail S r
    let p := Q.proj y
    regimeRun (stepRegime M (level M (interiorEmptyHistory H S) y)) (interiorEmptyHistory H S) y = r ∧
      lowerMask M (s+1) (interiorEmptyHistory H P) p = lowerMask M (s+1) (H.append P) p ∧
      interiorPositiveLowerIndex M H P p ≤ (lowerMarkedM M (s+1) (H.append P) p).E.length ∧
      HEq (lowerMarkedM M (s+1) (interiorEmptyHistory H P) p)
        (insertEmpty (interiorPositiveLowerIndex M H P p) (lowerMarkedM M (s+1) (H.append P) p)) ∧
      HEq (restrict (lowerMask M (s+1) (interiorEmptyHistory H P) p) Q)
        (restrict (lowerMask M (s+1) (H.append P) p) Q) := by
  dsimp only
  have hp : 0 < (head S (regimeRun (stepRegime M (s+1)) (H.append S) y)).length := by
    rw [length_head]
    omega
  have hm := lowerMask_dictionary M hM H hH
    (head S (regimeRun (stepRegime M (s+1)) (H.append S) y)) (s+1)
    ((tail S (regimeRun (stepRegime M (s+1)) (H.append S) y)).proj y)
  exact ⟨(actual_short_positive_splits M hM H hH S y s hlevel hshort).1,hm,
    interiorPositiveLowerIndex_le_boundary M H _ _ s,
    original_positive_lower_record M hM H hH _ hp _ s,
    restrict_heq_of_equal_masks _ _ hm _⟩

end
end Hironaka.HironakaOriginalSelectedPositiveLowerTail
