/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.MonomialInvariantEmptyMember
import Hironaka.Invariant.GeneralEmptyPrefix

/-!
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude

Original whole companion and actual regime/run dictionaries for empty insertion.
The prior complete Mathematics.tex is implemented without an invariant-order or
scheduling certificate. Recursive lower-value order alignment remains open.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPositiveCompanionEmptyInsertion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MonomialPartAlong NonmonomialOrderLocal
  MonomialInvariantEmptyMember CompanionReductionAlong CompanionRebase
  BlowupTowers BlowupTowerTransforms NonmonomialOrderRegime NonmonomialOrderTail
  StepOneRegime StepOneEmptyPrefix
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

theorem companionOf_insertEmpty (m : MarkedIdeal n X) {j : ℕ} (hj : j ≤ m.E.length) (o : ℕ) :
    companionOf n (insertEmpty j m) o = insertEmpty j (companionOf n m o) := by
  have hN : nonmonomialPartAlong n m.N m.ideal (m.E.insertIdx j ∅) =
      nonmonomialPartAlong n m.N m.ideal m.E := nmPart_insertEmpty m hj
  have hM := monomialPartAlong_insertIdx_empty m.N m.ideal m.E hj
  unfold companionOf
  dsimp only [insertEmpty]
  rw [hN, hM]
  unfold companionAlong
  split_ifs <;> rfl

theorem companionOf_geoTransformAlong_insertEmpty (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) {Y : CMfd.{u} n} (T : BlowupTower X Y) (o : ℕ) :
    companionOf n (geoTransformAlong (insertEmpty j m) T) o =
      insertEmpty j (companionOf n (geoTransformAlong m T) o) := by
  rw [geoTransformAlong_insertEmpty m hj T]
  exact companionOf_insertEmpty _ (le_length_E_geoTransformAlong m hj T) o

theorem whole_coherent_companion_empty_dictionary (hn : 0 < n) {k : ℕ}
    {m : MarkedIdeal n X} (h : IsInvDomain k m) {j : ℕ} (hj : j ≤ m.E.length)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower m T) :
    ∀ o : ℕ, 1 ≤ o →
      (companionOf n (geoTransformAlong (insertEmpty j m) T) o).ideal.IsCoherent ∧
      ∀ x : Y, ∀ g : Y → ℂ,
        (companionOf n (geoTransformAlong (insertEmpty j m) T) o).ideal.mem x g ↔
          (companionOf n (geoTransformAlong m T) o).ideal.mem x g := by
  have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  intro o ho
  have hc := InvDomainCompanion.isInvDomain_companionAlong hn hdom ho
  rw [companionOf_geoTransformAlong_insertEmpty m hj T o]
  exact ⟨hc.isWellFormed.isCoherent, fun _ _ => Iff.rfl⟩

theorem ordMask_geoTransformAlong_insertEmpty (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) {Y : CMfd.{u} n} (T : BlowupTower X Y) (o : ℕ) :
    ordMask (geoTransformAlong (insertEmpty j m) T) o = ordMask (geoTransformAlong m T) o := by
  rw [geoTransformAlong_insertEmpty m hj T]
  apply Opens.ext
  change (closure (ordGe (insertEmpty j (geoTransformAlong m T)) (o+1)))ᶜ =
    (closure (ordGe (geoTransformAlong m T) (o+1)))ᶜ
  rw [ordGe_insertEmpty _ (le_length_E_geoTransformAlong m hj T)]

theorem ordRegime_insertEmpty_iff (m : MarkedIdeal n X) {j : ℕ} (hj : j ≤ m.E.length)
    (o : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    OrdRegime (insertEmpty j m) o T y ↔ OrdRegime m o T y := by
  unfold OrdRegime
  rw [cosupp_geoTransformAlong_insertEmpty m hj T, nmOrd_geoTransformAlong_insertEmpty m hj T y]

theorem regimeRun_insertEmpty (m : MarkedIdeal n X) {j : ℕ} (hj : j ≤ m.E.length) (o : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y),
      regimeRun (OrdRegime (insertEmpty j m) o) T y = regimeRun (OrdRegime m o) T y
  | _, .refl, _ => rfl
  | _, .step T C π hπ, y => by
    rw [regimeRun_step, regimeRun_step]
    have hq := ordRegime_insertEmpty_iff m hj o T (π y)
    by_cases h : OrdRegime m o T (π y)
    · rw [if_pos (hq.mpr h), if_pos h, regimeRun_insertEmpty m hj o T (π y)]
    · rw [if_neg (fun hi => h (hq.mp hi)), if_neg h]

theorem ordRegime_step_empty_append_iff (m : MarkedIdeal n X) (o : ℕ)
    {Y₀ Z₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (σ : Z₀ → Y₀)
    (hσ : IsBlowupAlong n (∅ : Set Y₀) σ) (S : BlowupTower Z₀ Y) (y : Y) :
    OrdRegime m o ((BlowupTower.step T₀ ∅ σ hσ).append S) y ↔
      OrdRegime (emptyStepBase (geoTransformAlong m T₀) σ) o S y := by
  unfold OrdRegime
  rw [cosupp_step_empty_append m T₀ σ hσ S, nmOrd_step_empty_append m T₀ σ hσ S y]

theorem regimeRun_step_empty_append_cases (m : MarkedIdeal n X) (o : ℕ)
    {Y₀ Z₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (σ : Z₀ → Y₀)
    (hσ : IsBlowupAlong n (∅ : Set Y₀) σ) (S : BlowupTower Z₀ Y) (y : Y) :
    let r := regimeRun (OrdRegime (emptyStepBase (geoTransformAlong m T₀) σ) o) S y
    regimeRun (OrdRegime m o) ((BlowupTower.step T₀ ∅ σ hσ).append S) y =
      if r < S.length then r else
        S.length + regimeRun (OrdRegime m o) (BlowupTower.step T₀ ∅ σ hσ) (S.proj y) := by
  classical
  dsimp only
  have hG : ∀ {A B : CMfd.{u} n} (H : BlowupTower Z₀ A) (C : Set A) (π : B → A)
      (hπ : IsBlowupAlong n C π), True → True := fun _ _ _ _ h => h
  have hQ : ∀ {A : CMfd.{u} n} (H : BlowupTower Z₀ A) (z : A), True →
      (OrdRegime m o ((BlowupTower.step T₀ ∅ σ hσ).append H) z ↔
        OrdRegime (emptyStepBase (geoTransformAlong m T₀) σ) o H z) :=
    fun H z _ => ordRegime_step_empty_append_iff m o T₀ σ hσ H z
  by_cases hlt : regimeRun (OrdRegime (emptyStepBase (geoTransformAlong m T₀) σ) o) S y < S.length
  · rw [if_pos hlt]
    exact regimeRun_append_of_lt (OrdRegime m o) _ (BlowupTower.step T₀ ∅ σ hσ)
      (fun _ => True) hG hQ S y trivial hlt
  · rw [if_neg hlt]
    have heq := le_antisymm (regimeRun_le_length _ S y) (Nat.le_of_not_gt hlt)
    exact regimeRun_append_of_eq (OrdRegime m o) _ (BlowupTower.step T₀ ∅ σ hσ)
      (fun _ => True) hG hQ S y trivial heq

end
end Hironaka.HironakaOriginalPositiveCompanionEmptyInsertion
