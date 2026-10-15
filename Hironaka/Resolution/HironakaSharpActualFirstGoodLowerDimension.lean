/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFirstGoodExceptionalTraceDensity

/-! Actual finite-history pure dimension and TRUE lower input dimension drop.
No compactness, lower-transverse boundary or recursive-driver certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFirstGoodLowerDimension
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFirstGoodExceptionalTraceDensity HironakaSharpActualFirstGoodLowerProduct
  HironakaSharpActualFirstGoodReducedTraces HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualFiniteChronologicalHistory NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The SAME actual finite geometric history preserves genuine original pure
regular dimension, without compactness or a supplied current-purity premise. -/
theorem actual_template_regular_dimension {W : Set X} (hW : IsClosedSubmanifold n W)
    (k : ℕ) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x k) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate W []) T →
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
        RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N y k
  | _, .refl, _ => hr
  | _, .step T C π hπ, ht => by
    have hw : (geometricTemplate W []).IsWellFormed :=
      ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht.1
    intro y hy
    exact BlowupStrictSubmanifold.regularAtDim_geoStrictTransform hπ hwT.isClosedSubmanifold_N.1
      (actual_template_regular_dimension hW k hr T ht.1) ht.2.subset_N hy

/-- ONLY original pure geometry identifies EACH actual reduced FIRST-good
trace's genuine dimension d, not merely its ambient dimension bound. -/
theorem exists_original_first_good_trace_dimension (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    ∃ O : Opens Y,(O : Set Y)=(chronologicalDistinctDefect W E T)ᶜ ∧
      ∀ i : Fin E.length,
        IsClosedSubmanifold n ((Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T) ∧
        ∀ x ∈ (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T,
          RegularAtDim (n := n) ((Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T) x d := by
  obtain ⟨O,hO,hTraces⟩ := exists_actual_first_good_open_reduced_traces hn hW hE hdense d hr T hT
  have hPure := actual_template_regular_dimension hW (d+1) hr T hT
  refine ⟨O,hO,fun i => ⟨(hTraces i).1,?_⟩⟩
  intro x hx
  obtain ⟨k,hNk,hSk⟩ := (hTraces i).2.1 x hx
  have hk : k=d+1 := Nat.le_antisymm
    (RegularPointDimension.le_of_regularAtDim hNk (hPure x hx.1))
    (RegularPointDimension.le_of_regularAtDim (hPure x hx.1) hNk)
  simpa only [hk,Nat.add_sub_cancel] using hSk

/-- The SAME actual lower carrier has true pure dimension d, whole actual
exceptional density and the real remaining product domain of smaller bound d. -/
theorem exists_original_first_good_lower_dimensional_input (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    ∃ O : Opens Y,(O : Set Y)=(chronologicalDistinctDefect W E T)ᶜ ∧
      IsSNCDivisor n ((geoTransformAlong (geometricTemplate W []) T).E.map ((Subtype.val : O → Y) ⁻¹' ·)) ∧
      ∀ i : Fin E.length,
        let S := (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T
        let F := (geoTransformAlong (geometricTemplate W []) T).E.map ((Subtype.val : O → Y) ⁻¹' ·)
        let P := actualRemainingLowerProduct W E i T O
        IsClosedSubmanifold n S ∧ (∀ x ∈ S,RegularAtDim (n := n) S x d) ∧
          S ⊆ closure (S \ ⋃ H ∈ F,H) ∧ IsInvDomain d (⟨S,[],P,1⟩ : MarkedIdeal n O) := by
  obtain ⟨O,hO,hProd⟩ := exists_original_first_good_lower_product_domain hn hW hE hdense d hr T hT
  obtain ⟨O₂,hO₂,hE₂,hDensity⟩ := exists_original_first_good_exceptional_trace_density hn hW hE hdense d hr T hT
  have hOO₂ : O₂=O := SetLike.coe_injective (hO₂.trans hO.symm)
  subst O₂
  obtain ⟨O₃,hO₃,hDim⟩ := exists_original_first_good_trace_dimension hn hW hE hdense d hr T hT
  have hOO₃ : O₃=O := SetLike.coe_injective (hO₃.trans hO.symm)
  subst O₃
  refine ⟨O,hO,hE₂,?_⟩
  intro i
  obtain ⟨_hc,hnz,_hpr,_hOrd,hDom⟩ := hProd i
  exact ⟨(hDim i).1,(hDim i).2,(hDensity i).2,
    ⟨hDom.isWellFormed,fun x hx => ⟨d,le_rfl,(hDim i).2 x hx⟩,le_rfl,hnz⟩⟩

end
end Hironaka.HironakaSharpActualFirstGoodLowerDimension
