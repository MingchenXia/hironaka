/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveUniformStageAtlas

/-! Actual prefix successors and eventual genuine empty steps. Whole dependent
endpoint/tower equalities retain every actual position and original terminal. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveUniformPrefixSuccessors
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerSplit
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveEmptyPadding
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem headPacket_zero (T : BlowupTower X Y) :
    headPacket T 0=⟨Y,T⟩ := by
  cases T <;> rfl

private theorem headPacket_refl (j : ℕ) :
    headPacket (.refl : BlowupTower X X) j=⟨X,BlowupTower.refl⟩ := by
  cases j <;> rfl

theorem headPacket_head (T : BlowupTower X Y) (j r : ℕ) :
    headPacket (head T j) r=headPacket T (j+r) := by
  induction T generalizing j with
  | refl =>
    cases j with
    | zero => simp only [Nat.zero_add];rfl
    | succ j =>
      change headPacket (.refl : BlowupTower X X) r=headPacket .refl (j+1+r)
      rw [headPacket_refl,headPacket_refl]
  | step T C π hπ ih =>
    cases j with
    | zero => simp only [Nat.zero_add];rfl
    | succ j =>
      rw [Nat.succ_add]
      change headPacket (head T j) r=headPacket T (j+r)
      exact ih j

private theorem headPacket_full (T : BlowupTower X Y) :
    headPacket T T.length=⟨X,BlowupTower.refl⟩ := by
  induction T with
  | refl => rfl
  | step T C π hπ ih => exact ih

theorem uniformPrefix_zero (T : BlowupTower X Y) :
    uniformPrefix T 0=⟨X,BlowupTower.refl⟩ := headPacket_full T

theorem uniformPrefix_head_one (T : BlowupTower X Y) (k : ℕ) :
    headPacket (uniformPrefix T (k+1)).2 1=uniformPrefix T k := by
  change headPacket (head (T.append (identityEmptyTail Y (k+1))) T.length) 1=_
  rw [headPacket_head]
  rfl

private theorem actual_last_step_of_packet
    (T : BlowupTower X Y) (P : Σ V : CMfd.{u} n,BlowupTower X V)
    (hPos : 0<T.length) (hHead : headPacket T 1=P) :
    ∃ (C : Set P.1) (π : Y → P.1) (hπ : IsBlowupAlong n C π),
      T=BlowupTower.step P.2 C π hπ := by
  cases T with
  | refl => simp only [BlowupTower.length_refl] at hPos;omega
  | step T C π hπ =>
    change headPacket T 0=P at hHead
    rw [headPacket_zero] at hHead
    cases hHead
    exact ⟨C,π,hπ,rfl⟩

/-- Actual last constructor supplies centre, arrow and blowup proof internally. -/
theorem uniformPrefix_successor (T : BlowupTower X Y) (k : ℕ) :
    ∃ (C : Set (uniformPrefix T k).1)
      (π : (uniformPrefix T (k+1)).1 → (uniformPrefix T k).1)
      (hπ : IsBlowupAlong n C π),
      (uniformPrefix T (k+1)).2=BlowupTower.step (uniformPrefix T k).2 C π hπ ∧
      (uniformPrefix T (k+1)).2.proj=(uniformPrefix T k).2.proj ∘ π := by
  obtain ⟨C,π,hπ,hStep⟩ := actual_last_step_of_packet
    (uniformPrefix T (k+1)).2 (uniformPrefix T k)
    (by rw [uniformPrefix_length];omega) (uniformPrefix_head_one T k)
  exact ⟨C,π,hπ,hStep,by rw [hStep];rfl⟩

private theorem headPacket_empty_suffix (T : BlowupTower X Y) (r j : ℕ) (hj : j≤r) :
    headPacket (T.append (identityEmptyTail Y r)) j=
      ⟨Y,T.append (identityEmptyTail Y (r-j))⟩ := by
  induction j generalizing r with
  | zero => rw [headPacket_zero,Nat.sub_zero]
  | succ j ih =>
    cases r with
    | zero => omega
    | succ r =>
      change headPacket (T.append (identityEmptyTail Y r)) j=
        ⟨Y,T.append (identityEmptyTail Y ((r+1)-(j+1)))⟩
      simpa only [Nat.succ_sub_succ_eq_sub] using ih r (by omega)

theorem uniformPrefix_of_length_le (T : BlowupTower X Y) (k : ℕ) (hk : T.length≤k) :
    uniformPrefix T k=⟨Y,T.append (identityEmptyTail Y (k-T.length))⟩ :=
  headPacket_empty_suffix T k T.length hk

theorem uniformPrefix_after_length (T : BlowupTower X Y) (r : ℕ) :
    uniformPrefix T (T.length+r)=⟨Y,T.append (identityEmptyTail Y r)⟩ := by
  simpa only [Nat.add_sub_cancel_left] using uniformPrefix_of_length_le T (T.length+r) (by omega)

/-- Under exact packet identification, the next arrow is the real empty identity blowup. -/
theorem uniformPrefix_after_length_successor (T : BlowupTower X Y) (r : ℕ) :
    uniformPrefix T (T.length+(r+1))=⟨Y,BlowupTower.step
      (T.append (identityEmptyTail Y r)) ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty⟩ :=
  uniformPrefix_after_length T (r+1)

end
end Hironaka.HironakaSharpActualCurveUniformPrefixSuccessors
