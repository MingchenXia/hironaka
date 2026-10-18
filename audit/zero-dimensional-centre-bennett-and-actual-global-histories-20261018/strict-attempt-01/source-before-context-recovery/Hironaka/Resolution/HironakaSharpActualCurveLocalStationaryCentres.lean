/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalPrefixTowers

/-! Genuine literal empty last constructors force actual locally stationary
centres for the same globally descended blowup sequence. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveLocalStationaryCentres
noncomputable section
open Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformPrefixSuccessors
  HironakaSharpActualCurveUniformSuccessorComparison HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveGlobalSuccessorCentre
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X Y : CMfd.{u} n} {J : Type u}

private def finalCentreEmpty : {V : CMfd.{u} n} → BlowupTower X V → Prop
  | _,.refl => True
  | _,.step _ C _ _ => C=∅

theorem actualUniformSuccessor_centre_empty (T : BlowupTower X Y) (k : ℕ) (hk : T.length≤k) :
    (actualUniformSuccessor T k).centre=∅ := by
  obtain ⟨r,rfl⟩ : ∃ r,k=T.length+r := ⟨k-T.length,by omega⟩
  let P : (Σ V : CMfd.{u} n,BlowupTower X V) → Prop := fun R => finalCentreEmpty R.2
  have hEmpty : P (uniformPrefix T (T.length+(r+1))) :=
    Eq.mpr (congrArg P (uniformPrefix_after_length_successor T r)) rfl
  change finalCentreEmpty (uniformPrefix T (T.length+(r+1))).2 at hEmpty
  have hNat : T.length+(r+1)=T.length+r+1 := by omega
  have hRead : finalCentreEmpty (uniformPrefix T (T.length+r+1)).2 :=
    Eq.mp (congrArg (fun j => finalCentreEmpty (uniformPrefix T j).2) hNat) hEmpty
  rw [(actualUniformSuccessor T (T.length+r)).step_eq] at hRead
  exact hRead

/-- ENTIRE stage projection preimage, not only the complement of exceptional points. -/
theorem globalUniformCentre_disjoint_preimage_open (A : ActualEndpointHistories X J)
    (k : ℕ) (i : J) (hk : ((A.prefixTower i).append (A.tail i)).length≤k) :
    Disjoint (globalUniformCentre A k)
      ((gluedProjection (uniformStageHistories A k)) ⁻¹' (A.openSet i : Set X)) := by
  apply disjoint_left.mpr
  intro q hC hU
  have hRange : q∈range (endpointLocalInclusion (uniformStageHistories A k) i) := by
    rw [localInclusion_range]
    exact hU
  obtain ⟨z,rfl⟩ := hRange
  have hz := (mem_globalUniformCentre_iff A k i z).mp hC
  change z∈(actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k).centre at hz
  rw [actualUniformSuccessor_centre_empty _ k hk] at hz
  exact hz

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- ONLY original geometry supplies a real original neighbourhood and stopping bound. -/
theorem originalUniformCentres_locally_stationary (x : X) :
    ∃ U : Opens X,x∈U ∧ ∃ L : ℕ,∀ k,L≤k →
      Disjoint (originalUniformCentre hn hW hE hdense hr k)
        ((originalUniformStageProjection hn hW hE hdense hr k) ⁻¹' (U : Set X)) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  refine ⟨A.openSet x,originalEndpointHistories_point_mem hn hW hE hdense hr x,
    ((A.prefixTower x).append (A.tail x)).length,?_⟩
  intro k hk
  exact globalUniformCentre_disjoint_preimage_open A k x hk

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveLocalStationaryCentres
