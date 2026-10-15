/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalRecursiveInteriorHistory
/-! Actual all-depth interior identity-empty deletion from the inserted history.
Complete three-node Mathematics.tex preceded code. Deleted prefix canonicity
is constructed before actual dominance/value transport; no OLD CAN certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalRecursiveEmptyDeletion
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres HomogenizedIdealAlong
  HironakaOriginalInteriorEmptyHistory HironakaOriginalRecursiveInteriorHistory
  HironakaOriginalRecursiveBoundaryHistoryMap
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X A Y : CMfd.{u} n}

theorem original_recursive_family_empty_deletion_isCanonical_iff (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (H : BlowupTower X A) (S : BlowupTower A Y) :
    IsCanonical M ((invFamily hn k).inv M) (interiorEmptyHistory H S) ↔
      IsCanonical M ((invFamily hn k).inv M) (H.append S) := by
  constructor
  · intro hcan
    revert hcan
    induction S with
    | refl =>
      intro hcan
      exact hcan.1
    | step S C π hπ ih =>
      rintro ⟨hc,hC⟩
      have hOld := ih hc
      refine ⟨hOld,?_⟩
      rcases hC with he | hm
      · exact Or.inl he
      · exact Or.inr (hm.trans (original_recursive_family_actual_maximum_dictionary hn k M hM H S hOld))
  · exact original_recursive_family_interior_isCanonical hn k M hM H S

theorem original_recursive_step_empty_deletion_isCanonical_iff (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y) :
    IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (interiorEmptyHistory H S) ↔
      IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S) := by
  constructor
  · intro hcan
    revert hcan
    induction S with
    | refl =>
      intro hcan
      exact hcan.1
    | step S C π hπ ih =>
      rintro ⟨hc,hC⟩
      have hOld := ih hc
      refine ⟨hOld,?_⟩
      rcases hC with he | hm
      · exact Or.inl he
      · exact Or.inr (hm.trans (original_recursive_step_actual_maximum_dictionary hn k M hM hmax H S hOld))
  · exact original_recursive_step_interior_isCanonical hn k M hM hmax H S

theorem original_recursive_family_empty_deletion_entire_values (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) (interiorEmptyHistory H S)) :
    IsCanonical M ((invFamily hn k).inv M) (H.append S) ∧
      ∀ y∈(geoTransformAlong M (interiorEmptyHistory H S)).cosupp,
        (invFamily hn k).inv M (interiorEmptyHistory H S) y=
          recursiveHistoryShift k (M.E.length+H.length) ((invFamily hn k).inv M (H.append S) y) := by
  have hOld := (original_recursive_family_empty_deletion_isCanonical_iff hn k M hM H S).mp hcan
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn k).isInvValue hM (H.append S) hOld
  have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
  refine ⟨hOld,?_⟩
  intro y hy
  rw [(geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1] at hy
  exact original_recursive_entire_family_interior_value hn k M hM H S hOld y hy

theorem original_recursive_step_empty_deletion_entire_values (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (interiorEmptyHistory H S)) :
    IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S) ∧
      ∀ y∈(geoTransformAlong M (interiorEmptyHistory H S)).cosupp,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y=
          recursiveStepShift k (M.E.length+H.length)
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y) := by
  have hOld := (original_recursive_step_empty_deletion_isCanonical_iff hn k M hM hmax H S).mp hcan
  have ht := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) M hM hmax hn (H.append S) hOld).2.1
  have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
  refine ⟨hOld,?_⟩
  intro y hy
  rw [(geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1] at hy
  exact original_recursive_entire_step_interior_value hn k M hM hmax H S hOld y hy

theorem original_recursive_family_empty_deletion_canonical_resolution_iff (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (H : BlowupTower X A) (S : BlowupTower A Y) :
    (IsCanonical M ((invFamily hn k).inv M) (interiorEmptyHistory H S) ∧
      IsGeoResolution M (interiorEmptyHistory H S)) ↔
    (IsCanonical M ((invFamily hn k).inv M) (H.append S) ∧ IsGeoResolution M (H.append S)) := by
  constructor
  · rintro ⟨hcan,hres⟩
    have hOld := (original_recursive_family_empty_deletion_isCanonical_iff hn k M hM H S).mp hcan
    have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
      (invFamily hn k).isInvValue hM (H.append S) hOld
    have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
    have hcos := (geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1
    refine ⟨hOld,ht,?_⟩
    rw [← hcos,hres.2]
  · rintro ⟨hcan,hres⟩
    exact original_recursive_family_interior_canonical_resolution hn k M hM H S hcan hres

theorem original_recursive_step_empty_deletion_canonical_resolution_iff (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y) :
    (IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (interiorEmptyHistory H S) ∧
      IsGeoResolution M (interiorEmptyHistory H S)) ↔
    (IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S) ∧
      IsGeoResolution M (H.append S)) := by
  constructor
  · rintro ⟨hcan,hres⟩
    have hOld := (original_recursive_step_empty_deletion_isCanonical_iff hn k M hM hmax H S).mp hcan
    have ht := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
      (invFamily hn k) M hM hmax hn (H.append S) hOld).2.1
    have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
    have hcos := (geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1
    refine ⟨hOld,ht,?_⟩
    rw [← hcos,hres.2]
  · rintro ⟨hcan,hres⟩
    exact original_recursive_step_interior_canonical_resolution hn k M hM hmax H S hcan hres

end
end Hironaka.HironakaOriginalRecursiveEmptyDeletion
