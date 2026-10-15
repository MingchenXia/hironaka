/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalStepOneCurveHistory
/-! Actual initial-boundary compatibility for the complete indexed history map.
Complete two-node mathematics preceded code. Higher outer histories remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalBoundaryHistoryMap
noncomputable section
open Classical
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  BoundaryCount StepOneRegime StepOneValue StepOneValueMasked
  HironakaOriginalShortUniformIndex HironakaOriginalInvariantEmptyInsertion
  HironakaOriginalPositiveMemberEmptyInsertion HironakaOriginalCrossingLowerHistory
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- The actual retained original prefix contains the clamped index j-level. -/
theorem original_initial_lower_index_bound (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (p : A)
    (j : ℕ) (hj : j≤M.E.length) :
    j-level M H p≤actualLowerInsertionIndex M H p j := by
  let E := (geoTransformAlong (barMarked M) H).E
  let m := M.E.length
  let P : Set A → Bool := fun W => decide ¬(W∈E.take m ∧ p∈W)
  have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked M hM) H hH
  have hmE : m≤E.length := by
    dsimp only [E,m]
    rw [length_E_geoTransformAlong]
    change M.E.length≤M.E.length+H.length
    omega
  have hcount : ((E.take m).filter P).length=m-level M H p :=
    original_filtered_prefix_exact_count E hw.isSNCDivisor p m m le_rfl hmE
  have hlevel : level M H p≤m := by
    change (Finset.univ.filter fun i : Fin (E.take m).length => p∈(E.take m).get i).card≤m
    have hf := Finset.card_filter_le (Finset.univ : Finset (Fin (E.take m).length))
      (fun i => p∈(E.take m).get i)
    simpa only [Finset.card_univ,Fintype.card_fin,List.length_take,min_eq_left hmE] using hf
  have hsplit : E.take m=E.take j ++ (E.drop j).take (m-j) := by
    have ht := List.take_add (l := E) (i := j) (j := m-j)
    rwa [Nat.add_sub_of_le hj] at ht
  have hsuffix : (((E.drop j).take (m-j)).filter P).length≤m-j := by
    have hf := List.length_filter_le P ((E.drop j).take (m-j))
    simp only [List.length_take] at hf
    omega
  rw [hsplit,List.filter_append,List.length_append] at hcount
  change j-level M H p≤((E.take j).filter P).length
  omega

/-- The ACTUAL selected lower record has the true empty prefix of length j-level. -/
theorem original_initial_lower_history_empty_prefix
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (p : A)
    (j : ℕ) (hj : j≤M.E.length) :
    let d := j-level M H p
    let J := lowerMarkedM M (level M H p) H p
    d≤J.E.length ∧ J.E.take d=List.replicate d ∅ := by
  dsimp only
  have hp := lowerMarkedM_insertion_empty_prefix M hj H p (level M H p)
  have hc : j-level M H p≤(if level M H p=0 then j else actualLowerInsertionIndex M H p j) := by
    split_ifs with hz
    · omega
    · exact original_initial_lower_index_bound M hM H hH p j hj
  refine ⟨hc.trans hp.1,?_⟩
  have ht := congrArg (List.take (j-level M H p)) hp.2
  simpa only [List.take_take,List.take_replicate,min_eq_left hc] using ht

/-- Only the actual original lower record and true mask are used at ALL depths/orders. -/
theorem actual_lower_history_map_compatibility (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H)
    (Q : BlowupTower A Y) (y : Y) (j : ℕ) (hj : j≤M.E.length) :
    WithTop.map (shiftFamily k (j-level M H (Q.proj y)))
        (Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M)
          (level M H (Q.proj y)) H Q y)=
      WithTop.map (shiftFamily k 0)
        (Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M)
          (level M H (Q.proj y)) H Q y) := by
  have hp := original_initial_lower_history_empty_prefix M hM H hH (Q.proj y) j hj
  unfold Seq.StepOneValueMasked.lowerValueL
  split_ifs with h
  · simp only [WithTop.map_coe]
    apply congrArg (fun v : ValTy k => (v : WithTop (ValTy k)))
    exact shiftFamily_inv_eq_shiftFamily_zero hn k _ hp.1 hp.2 _ _
  · rfl

/-- The ENTIRE true value has the initial-boundary compatibility, not a supplied value certificate. -/
theorem actual_entire_step_history_map_compatibility (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T) (y : Y)
    (j : ℕ) (hj : j≤M.E.length) :
    historyStepShift k j (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y)=
      pairShift (shiftFamily k 0) (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T y) := by
  by_cases hsp : IsSpecial M T y
  · unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hsp]
    rfl
  let ℓ := level M T y
  let r := regimeRun (stepRegime M ℓ) T y
  let H := head T r
  let Q := tail T r
  have hH := (isGeoTestTower_iff_head_tail (barMarked M) T r).mp hT |>.1
  have hwhole : H.append Q=T := head_append_tail T r
  have hcurrent : stepRegime M ℓ (H.append Q) y := by rw [hwhole];exact ⟨rfl,hsp⟩
  have hreach : Q.length≤regimeRun (stepRegime M ℓ) (H.append Q) y := by
    rw [hwhole]
    change (tail T r).length≤r
    rw [length_tail]
    exact Nat.min_le_left _ _
  have hbase := regime_at_base_of_reaching_run (stepRegime M ℓ) H Q y hcurrent hreach
  have hv := actual_lower_history_map_compatibility hn k M hM H hH Q y j hj
  rw [hbase.1] at hv
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_neg hsp]
  simp only [historyStepShift,pairShift,ofLex_toLex]
  exact congrArg (fun v : WithTop (ValTy k) => toLex (ℓ,v)) hv

end
end Hironaka.HironakaOriginalBoundaryHistoryMap
