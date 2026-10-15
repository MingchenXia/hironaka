/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFirstGoodLowerDimension
import Hironaka.Analytic.PositiveDimensionalComponent

/-! Genuine zero-dimensional lower base on the actual FIRST-good open of a
smooth upper curve. No Z-erasing/whole Sigma or termination claim. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFirstGoodCurveBase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFirstGoodLowerDimension HironakaSharpActualFirstGoodLowerProduct
  HironakaSharpActualFirstGoodReducedTraces HironakaSharpActualFirstGoodTraceRestrictionNonzero
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualFiniteMemberProduct RelativePrincipalizationSpan RestrictedIdealExtension
  DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem unit_mem_of_regular_zero {S : Set Y} {x : Y}
    (hr : RegularAtDim (n := n) S x 0) {I : GermIdeal n Y} (hI : I.IsCoherent)
    (hnz : IsNonzeroAlongAt S I x) : I.mem x (1 : Y → ℂ) := by
  obtain ⟨U,hU,hxU,hsub⟩ := PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hr
  obtain ⟨g,hg,hfreq⟩ := hnz
  obtain ⟨y,⟨hyS,hygn⟩,hyU⟩ := (hfreq.and_eventually (hU.mem_nhds hxU)).exists
  have hyx : y=x := mem_singleton_iff.mp (hsub ⟨hyS,hyU⟩)
  have hgn : g x ≠ 0 := hyx ▸ hygn
  have hgh := GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  apply HomogenizedIdeal.mem_of_isInSpanAt hI
  refine isInSpanAt_of_eq_mul hg (holomorphicAt_const 1) (holomorphicAt_inv hgh hgn) ?_
  filter_upwards [hgh.continuousAt.eventually_ne hgn] with z hz
  exact (inv_mul_cancel₀ hz).symm

/-- True isolated-point neighborhoods force an actual nonzero normalized ideal
to be the WHOLE ambient unit, including all normal germs and off-carrier units. -/
theorem actual_zero_dimensional_normalized_ideal_eq_unit {S : Set Y}
    (hS : IsClosedSubmanifold n S) (hr : ∀ x ∈ S,RegularAtDim (n := n) S x 0)
    {I : GermIdeal n Y} (hI : I.IsCoherent)
    (hnz : ∀ x ∈ S,IsNonzeroAlongAt S (restrictOn n S I) x) :
    restrictOn n S I=unitIdeal n Y := by
  have hA := isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hS)
  ext x g
  constructor
  · exact fun hg => hg.1
  · intro hg
    by_cases hx : x ∈ S
    · have h1 := unit_mem_of_regular_zero (hr x hx) hA (hnz x hx)
      exact HomogenizedIdeal.mem_of_isInSpanAt hA
        (isInSpanAt_of_eq_mul h1 hg hg (Eventually.of_forall fun _ => by simp))
    · exact restrictOn_eq_top_of_disjoint hS.1.isOpen_compl hx (by simp) hg

private theorem not_mem_of_isolated_frequent {S H : Set Y} {x : Y}
    (hr : RegularAtDim (n := n) S x 0) (hf : ∃ᶠ y in 𝓝 x,y ∈ S ∧ y ∉ H) : x ∉ H := by
  obtain ⟨U,hU,hxU,hsub⟩ := PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hr
  obtain ⟨y,⟨hyS,hyH⟩,hyU⟩ := (hf.and_eventually (hU.mem_nhds hxU)).exists
  have hyx : y=x := mem_singleton_iff.mp (hsub ⟨hyS,hyU⟩)
  exact hyx ▸ hyH

/-- ONLY original smooth-curve inputs construct the computed open on which
true reduced traces are pairwise disjoint and avoid the ENTIRE accumulated E. -/
theorem exists_original_curve_first_good_trace_separation (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    ∃ O : Opens Y,(O : Set Y)=(chronologicalDistinctDefect W E T)ᶜ ∧
      ∀ i : Fin E.length,
        let S := (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T
        let F := (geoTransformAlong (geometricTemplate W []) T).E.map ((Subtype.val : O → Y) ⁻¹' ·)
        IsClosedSubmanifold n S ∧ (∀ x ∈ S,RegularAtDim (n := n) S x 0) ∧
          Disjoint S (⋃ H ∈ F,H) ∧ ∀ j : Fin E.length,j ≠ i →
            Disjoint S ((Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E j T) := by
  obtain ⟨O,hO,_hF,hLower⟩ := exists_original_first_good_lower_dimensional_input hn hW hE hdense 0 hr T hT
  refine ⟨O,hO,?_⟩
  intro i
  refine ⟨(hLower i).1,(hLower i).2.1,disjoint_left.mpr ?_,?_⟩
  · intro x hx hxE
    obtain ⟨U,hU,hxU,hsub⟩ := PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero ((hLower i).2.1 x hx)
    obtain ⟨y,hyU,hyS,hyE⟩ := mem_closure_iff.mp ((hLower i).2.2.1 hx) U hU hxU
    have hyx : y=x := mem_singleton_iff.mp (hsub ⟨hyS,hyU⟩)
    exact hyE (hyx.symm ▸ hxE)
  · intro j hji
    apply disjoint_left.mpr
    intro x hx hxs
    have hxGood : (x : Y) ∉ chronologicalDistinctDefect W E T := by
      change (x : Y) ∈ (chronologicalDistinctDefect W E T)ᶜ
      rw [←hO]
      exact x.property
    have hfreq := original_first_good_trace_not_contained_in_other_zero hn hW hE hdense T hT i j hji.symm hx hxGood
    rw [← O.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x] at hfreq
    have hfreqO := Filter.frequently_map.mp hfreq
    exact not_mem_of_isolated_frequent (Y := CMfd.of O) ((hLower i).2.1 x hx) hfreqO hxs.2

private theorem restrictOn_unit (S : Set Y) : restrictOn n S (unitIdeal n Y)=unitIdeal n Y := by
  ext x g
  exact ⟨fun hg => hg.1,fun hg => le_restrictOn isCoherent_unitIdeal x g hg⟩

private theorem relativeProduct_eq_unit (S : Set Y) (L : List (GermIdeal n Y))
    (hL : ∀ I ∈ L,I=unitIdeal n Y) : relativeIdealListProduct S L=unitIdeal n Y := by
  induction L with
  | nil => rfl
  | cons I L ih =>
    change restrictOn n S (I.mul (relativeIdealListProduct S L))=unitIdeal n Y
    rw [hL I (by simp),ih (fun J hJ => hL J (List.mem_cons_of_mem I hJ)),
      RestrictLeCalculus.mul_unitIdeal isCoherent_unitIdeal,restrictOn_unit]

/-- Original geometry and the actual zero-dimensional lower carrier internally
give WHOLE unit ideals for ALL remaining normalized members and their product. -/
theorem exists_original_curve_first_good_lower_units (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    ∃ O : Opens Y,(O : Set Y)=(chronologicalDistinctDefect W E T)ᶜ ∧
      ∀ i : Fin E.length,
        (∀ j : Fin E.length,j ≠ i → actualLowerTraceMember W E i j T O=unitIdeal n O) ∧
        actualRemainingLowerProduct W E i T O=unitIdeal n O := by
  obtain ⟨O,hO,hDim⟩ := exists_original_first_good_trace_dimension hn hW hE hdense 0 hr T hT
  obtain ⟨O₂,hO₂,hMembers⟩ := exists_original_first_good_lower_members hn hW hE hdense 0 hr T hT
  have hOO₂ : O₂=O := SetLike.coe_injective (hO₂.trans hO.symm)
  subst O₂
  refine ⟨O,hO,?_⟩
  intro i
  have hUnits : ∀ j : Fin E.length,j ≠ i → actualLowerTraceMember W E i j T O=unitIdeal n O := by
    intro j hji
    have hI := (original_members_actual_finite_chronological_geometry hn hW hE hdense j T hT).2.2.2.1.isCoherent
    have hraw := GermIdealPullbackCalculus.isCoherent_pullback (f := (Subtype.val : O → Y)) contMDiff_subtype_val hI
    exact actual_zero_dimensional_normalized_ideal_eq_unit (Y := CMfd.of O) (hDim i).1 (hDim i).2
      hraw ((hMembers i).2 j hji).2.1
  refine ⟨hUnits,?_⟩
  apply relativeProduct_eq_unit (Y := CMfd.of O)
  intro I hIL
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hIL
  exact hUnits j (of_decide_eq_true (List.mem_filter.mp hj).2)

end
end Hironaka.HironakaSharpActualFirstGoodCurveBase
