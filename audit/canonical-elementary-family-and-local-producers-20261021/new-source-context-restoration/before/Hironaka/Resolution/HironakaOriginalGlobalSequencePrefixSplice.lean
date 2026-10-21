/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.GrowingSeqTail
/-! Real finite original prefix splicing, preserving every stage/map/empty step,
SAME original canonicality and literal global counts. No invariant rebasing. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalGlobalSequencePrefixSplice
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals ResolutionInvariantSeq
open ResolutionInvariantSpec (IsCanonical countCentresMeeting)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual one-step prefix, including its original map and any empty centre. -/
def prependStep {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (s : GrowingSeq Y) : GrowingSeq X where
  stage
    | 0 => ⟨X,.refl⟩
    | i+1 => ⟨(s.stage i).1,(BlowupTower.step .refl C π hπ).append (s.stage i).2⟩
  zero := rfl
  succ i := by
    cases i with
    | zero =>
      change ∃ (D : Set X) (ρ : (s.stage 0).1 → X) (hρ : IsBlowupAlong n D ρ),
        (BlowupTower.step .refl C π hπ).append (s.stage 0).2 = .step .refl D ρ hρ
      rw [s.zero]
      exact ⟨C,π,hπ,rfl⟩
    | succ i =>
      obtain ⟨D,ρ,hρ,he⟩ := s.succ i
      refine ⟨D,ρ,hρ,?_⟩
      change (BlowupTower.step .refl C π hπ).append (s.stage (i+1)).2 =
        .step ((BlowupTower.step .refl C π hπ).append (s.stage i).2) D ρ hρ
      rw [he]
      rfl

/-- Genuine recursive splicing of the ENTIRE actual finite original prefix. -/
def prependTower : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → GrowingSeq Y → GrowingSeq X
  | _, .refl, s => s
  | _, .step T _ _ hπ, s => prependTower T (prependStep hπ s)

/-- Exact dependent actual stage pair, not just its composite projection. -/
theorem prependTower_stage_length_add : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (s : GrowingSeq Y) (i : ℕ),
    (prependTower T s).stage (T.length+i)=⟨(s.stage i).1,T.append (s.stage i).2⟩
  | _, .refl, s, i => by simp only [prependTower,BlowupTower.length_refl,zero_add,BlowupTower.refl_append]
  | _, .step T C π hπ, s, i => by
    change (prependTower T (prependStep hπ s)).stage (T.length+1+i)=_
    rw [show T.length+1+i=T.length+(i+1) by omega,prependTower_stage_length_add]
    change (⟨(s.stage i).1,T.append ((BlowupTower.step .refl C π hπ).append (s.stage i).2)⟩ :
      Σ Z : CMfd.{u} n,BlowupTower X Z)=
      ⟨(s.stage i).1,(BlowupTower.step T C π hπ).append (s.stage i).2⟩
    rw [← BlowupTower.append_assoc]
    rfl

/-- Every real intermediate prefix and later stage is canonical for the SAME
ORIGINAL invariant. The actual invariant is never re-based on the current record. -/
theorem prependTower_canonical {Λ : Type v} [LinearOrder Λ] (m : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n},BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (s : GrowingSeq Y),
      IsCanonical m inv T → (∀ i,IsCanonical m inv (T.append (s.stage i).2)) →
      ∀ i,IsCanonical m inv ((prependTower T s).stage i).2
  | _, .refl, s, _hT, hS, i => by simpa only [prependTower,BlowupTower.refl_append] using hS i
  | _, .step T C π hπ, s, hT, hS, i => by
    apply prependTower_canonical m inv T (prependStep hπ s) hT.1 ?_ i
    intro j
    cases j with
    | zero => exact hT.1
    | succ j =>
      change IsCanonical m inv (T.append ((BlowupTower.step .refl C π hπ).append (s.stage j).2))
      rw [← BlowupTower.append_assoc]
      exact hS j

/-- Literal global counts on the ACTUAL spliced stage retain the real whole
prefix contribution and the exact true projection-preimage tail count. -/
theorem count_prependTower_length_add (T : BlowupTower X Y) (s : GrowingSeq Y)
    (K : Set X) (i : ℕ) :
    countCentresMeeting K ((prependTower T s).stage (T.length+i)).2=
      countCentresMeeting K T + countCentresMeeting (T.proj ⁻¹' K) (s.stage i).2 := by
  calc
    _=countCentresMeeting K (T.append (s.stage i).2) :=
      congrArg (fun p : Σ Z : CMfd.{u} n,BlowupTower X Z => countCentresMeeting K p.2)
        (prependTower_stage_length_add T s i)
    _=_ := TowerPreimageCompact.countCentresMeeting_append K T (s.stage i).2

end
end Hironaka.HironakaOriginalGlobalSequencePrefixSplice
