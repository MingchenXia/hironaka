/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionCanonicalValueDimensionShift
/-! Actual original family comparison at every positive-depth monomial leaf.
Complete mathematical proofs preceded Lean in `Mathematics.tex`.
Positive companion recursion and the full canonical driver remain open. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionActualFamilyMonomialLeaf
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  NonmonomialOrderLocal NonmonomialOrderRegime GeneralValue
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionNonmonomialHistory HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain)
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

/-- Original domain and actual test history internally supply source domain
and the whole original family value at a genuine order-zero branch. -/
theorem IsActualTowerPullback.actual_family_monomial_leaf
    (hn : 0 < n) (hm : 0 < m) (h : IsActualTowerPullback f Q T g)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hT : IsGeoTestTower M T) (z : D')
    (h0 : nmOrd (geoTransformAlong M T) (g z) = 0) :
    IsInvDomain ((m-n)+k+1) (markedPullback (m := m) f M) ∧
    (invFamily hm ((m-n)+k+1)).inv (markedPullback (m := m) f M) Q z =
      familyDimensionMap (m-n) (k+1) ((invFamily hn (k+1)).inv M T (g z)) := by
  have hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f := by
    clear h0 z hT
    induction h with
    | refl hf => exact hf
    | step _ _ _ _ ih => exact ih
  constructor
  · convert isInvDomain_markedPullback_submersion hf M hM using 1
    omega
  · have hsource : nmOrd (geoTransformAlong (markedPullback (m := m) f M) Q) z = 0 :=
      (IsActualTowerPullback.orderAt_dictionary hn h M hM hT z).trans h0
    change genInv (fun {A} J {B} S y =>
        Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hm ((m-n)+k)) J (Y := B) S y)
        (markedPullback (m := m) f M) Q z =
      familyDimensionMap (m-n) (k+1)
        (genInv (fun {A} J {B} S y =>
          Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) S y) M T (g z))
    unfold familyDimensionMap generalDimensionMap genInv genSecond
    rw [hsource,h0]
    simp only [ite_true,ofLex_toLex,Sum.map_inl]
    rw [IsActualTowerPullback.gammaAlong_stage_dimension_shift h M hM.isWellFormed hT z]

/-- Two actual complete family values reflect every comparison at genuine
monomial leaves; the same true fibre dimension is used at both points. -/
theorem IsActualTowerPullback.actual_family_monomial_comparisons
    (hn : 0 < n) (hm : 0 < m) (h : IsActualTowerPullback f Q T g)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hT : IsGeoTestTower M T) (z w : D')
    (hz : nmOrd (geoTransformAlong M T) (g z) = 0)
    (hw : nmOrd (geoTransformAlong M T) (g w) = 0) :
    let V := (invFamily hm ((m-n)+k+1)).inv (markedPullback (m := m) f M) Q
    let v := (invFamily hn (k+1)).inv M T
    (V z < V w ↔ v (g z) < v (g w)) ∧
    (V z ≤ V w ↔ v (g z) ≤ v (g w)) ∧
    (V z = V w ↔ v (g z) = v (g w)) := by
  dsimp only
  rw [(IsActualTowerPullback.actual_family_monomial_leaf hn hm h M hM hT z hz).2,
    (IsActualTowerPullback.actual_family_monomial_leaf hn hm h M hM hT w hw).2]
  exact familyDimensionMap_comparisons (m-n) (k+1) _ _

/-- ONLY original input constructs the whole source test history and all
literal prefix maps with actual complete family comparisons at their leaves. -/
theorem exists_original_actual_family_monomial_prefixes (hn : 0 < n) (hm : 0 < m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      IsInvDomain ((m-n)+k+1) (markedPullback (m := m) f M) ∧
      IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q =
        markedPullback (m := m) g (geoTransformAlong M T) ∧
      (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp =
        g ⁻¹' (geoTransformAlong M T).cosupp ∧
      ∀ j : ℕ, ∃ a : (split Q j).1 → (split T j).1,
        IsActualTowerPullback f (head Q j) (head T j) a ∧
        ∀ z : (split Q j).1,
          nmOrd (geoTransformAlong M (head T j)) (a z) = 0 →
          (invFamily hm ((m-n)+k+1)).inv (markedPullback (m := m) f M) (head Q j) z =
            familyDimensionMap (m-n) (k+1) ((invFamily hn (k+1)).inv M (head T j) (a z)) := by
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  have hdom : IsInvDomain ((m-n)+k+1) (markedPullback (m := m) f M) := by
    convert isInvDomain_markedPullback_submersion hf M hM using 1
    omega
  obtain ⟨hQ,hmark⟩ := IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hT
  refine ⟨D',Q,g,h,hdom,hQ,hmark,
    IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hT,?_⟩
  intro j
  obtain ⟨a,ha⟩ := h.head j
  have hhead := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  exact ⟨a,ha,fun z hz => (IsActualTowerPullback.actual_family_monomial_leaf
    hn hm ha M hM hhead z hz).2⟩

end
end Hironaka.HironakaSmoothSubmersionActualFamilyMonomialLeaf
