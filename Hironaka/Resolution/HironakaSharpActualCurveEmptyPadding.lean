/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.BlowupEmptyIdentityExact
import Hironaka.Resolution.HironakaSharpActualCurveFiniteRecipeComparison
import Hironaka.Blowup.BlowupExistenceCodimOne

/-! Genuine identity-empty blowup padding retains every ordered exceptional
position and is an actual terminal difference recipe, without deleting steps. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveEmptyPadding
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowerTransforms BlowupStrictSubmanifold
  BlowupTowerIsomorphism HironakaSharpActualCurveFiniteRecipeComparison
  HironakaSharpActualCurveFiniteAmbientDifferencePhase HironakaSharpActualCurveWholeAmbientDifferenceCentre
  HironakaSharpActualCurveExceptionalDifference HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalMemberProductDomain
  NormalCrossings
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A genuine length-r tower of ACTUAL identity blowups of the empty centre. -/
def identityEmptyTail (Y : CMfd.{u} n) : ℕ → BlowupTower Y Y
  | 0 => .refl
  | r+1 => .step (identityEmptyTail Y r) ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty

@[simp] theorem identityEmptyTail_length (Y : CMfd.{u} n) (r : ℕ) :
    (identityEmptyTail Y r).length=r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [identityEmptyTail,BlowupTower.length_step,ih]

@[simp] theorem identityEmptyTail_proj (Y : CMfd.{u} n) (r : ℕ) :
    (identityEmptyTail Y r).proj=id := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [identityEmptyTail,BlowupTower.proj_step,ih,Function.id_comp]

theorem identityEmptyTail_isEmptyTower (Y : CMfd.{u} n) (r : ℕ) :
    ResolutionInvariantExt.IsEmptyTower (identityEmptyTail Y r) := by
  induction r with
  | zero => trivial
  | succ r ih => exact ⟨ih,rfl⟩

private theorem actual_identity_empty_strict {H : Set Y} (hH : IsClosed H) :
    geoStrictTransform (id : Y → Y) ∅ H=H := by
  simpa only [geoStrictTransform,Set.sdiff_empty,Set.preimage_id] using hH.closure_eq

/-- Actual well-formed TEST geometry, including the ENTIRE ordered empty-slot
ledger. Ambient ideal representatives need not be equal after normalization. -/
theorem identityEmptyTail_geometric_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (P : BlowupTower X Y) (hP : IsGeoTestTower M P) (r : ℕ) :
    IsGeoTestTower M (P.append (identityEmptyTail Y r)) ∧
    (geoTransformAlong M (P.append (identityEmptyTail Y r))).N=(geoTransformAlong M P).N ∧
    (geoTransformAlong M (P.append (identityEmptyTail Y r))).d=(geoTransformAlong M P).d ∧
    (geoTransformAlong M (P.append (identityEmptyTail Y r))).cosupp=(geoTransformAlong M P).cosupp ∧
    (geoTransformAlong M (P.append (identityEmptyTail Y r))).E=
      (geoTransformAlong M P).E++List.replicate r (∅ : Set Y) := by
  induction r with
  | zero => exact ⟨hP,rfl,rfl,rfl,by simp [identityEmptyTail]⟩
  | succ r ih =>
    let A := geoTransformAlong M (P.append (identityEmptyTail Y r))
    have hw : A.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      hM _ ih.1
    have ht : IsGeoTestTower M (P.append (identityEmptyTail Y (r+1))) :=
      ⟨ih.1,isAdmissibleCentre_empty A⟩
    have hN : (A.geoTransform ∅ id).N=A.N := actual_identity_empty_strict hw.isClosedSubmanifold_N.1
    have hCos : (A.geoTransform ∅ id).cosupp=A.cosupp := by
      ext z
      exact TransformOffCentre.mem_cosupp_geoTransform_iff A hw.isClosedSubmanifold_N.1
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hw.isCoherent hg)
        BlowupExistenceCodimOne.isBlowupAlong_id_empty (by simp)
    have hMap : A.E.map (geoStrictTransform (id : Y → Y) ∅)=A.E := by
      have hh : A.E.map (geoStrictTransform (id : Y → Y) ∅)=A.E.map id := by
        apply List.map_congr_left
        intro H hH
        exact actual_identity_empty_strict (hw.isSNCDivisor.1 H hH)
      simpa only [List.map_id] using hh
    refine ⟨ht,hN.trans ih.2.1,ih.2.2.1,hCos.trans ih.2.2.2.1,?_⟩
    change A.E.map (geoStrictTransform (id : Y → Y) ∅)++[id ⁻¹' (∅ : Set Y)]=_
    rw [hMap,show id ⁻¹' (∅ : Set Y)=(∅ : Set Y) from rfl,ih.2.2.2.2]
    rw [List.replicate_add,List.replicate_one,List.append_assoc]

/-- Terminal ACTUAL Delta gives a genuine literal recipe of empty successors;
its true difference remains empty at every padded endpoint. -/
theorem original_curve_terminal_difference_padding (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P)
    (hD : actualAmbientExceptionalDifference W E P=∅) (r : ℕ) :
    actualAmbientDifferenceSteps W E P (identityEmptyTail Y r) ∧
    actualAmbientExceptionalDifference W E (P.append (identityEmptyTail Y r))=∅ := by
  induction r with
  | zero => exact ⟨trivial,hD⟩
  | succ r ih =>
    have ht := actual_ambient_difference_steps_original_test hn hW hE hdense hr P hP _ ih.1
    have hπ : IsBlowupAlong n
        (actualAmbientExceptionalDifference W E (P.append (identityEmptyTail Y r))) (id : Y → Y) := by
      rw [ih.2]
      exact BlowupExistenceCodimOne.isBlowupAlong_id_empty
    have hLoc := original_curve_new_ambient_difference_over_old hn hW hE hdense hr _ ht hπ
    have hNext : actualAmbientExceptionalDifference W E
        ((P.append (identityEmptyTail Y r)).step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hz' : z ∈ actualAmbientExceptionalDifference W E
          ((P.append (identityEmptyTail Y r)).step
            (actualAmbientExceptionalDifference W E (P.append (identityEmptyTail Y r))) id hπ) := by
        simpa only [ih.2] using hz
      have hh := hLoc hz'
      simp [ih.2] at hh
    exact ⟨⟨ih.1,ih.2.symm⟩,hNext⟩

/-- Literal tower concatenation of ACTUAL identity-empty successors. -/
theorem identityEmptyTail_append (Y : CMfd.{u} n) (r s : ℕ) :
    identityEmptyTail Y (r+s)=(identityEmptyTail Y r).append (identityEmptyTail Y s) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change (identityEmptyTail Y (r+s)).step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty=
      ((identityEmptyTail Y r).append (identityEmptyTail Y s)).step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty
    rw [ih]

/-- Every actual biholomorphism compares actual empty tails, retaining the
same terminal map and every empty position. -/
theorem identityEmptyTail_isTowerIso {Y' : CMfd.{u} n}
    (e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) (r : ℕ) :
    IsTowerIso e (identityEmptyTail Y' r) (identityEmptyTail Y r) e := by
  induction r with
  | zero => exact IsTowerIso.refl
  | succ r ih =>
    exact IsTowerIso.step ih BlowupExistenceCodimOne.isBlowupAlong_id_empty
      BlowupExistenceCodimOne.isBlowupAlong_id_empty e (fun _ => rfl) (by simp)

end
end Hironaka.HironakaSharpActualCurveEmptyPadding
