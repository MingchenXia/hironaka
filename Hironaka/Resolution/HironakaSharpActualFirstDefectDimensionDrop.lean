/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFamilyDefectOpenNaturality
import Hironaka.Analytic.ThinDimensionDrop
import Hironaka.MarkedIdeal.HomogenizedGlueing
/-! The literal actual FIRST defect has genuine dense complement and smaller
pure-carrier dimension, before any resolving or terminating driver is built. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFirstDefectDimensionDrop
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualFiniteMemberProduct HironakaSharpOriginalProductTraceOrder
  RelativePrincipalizationSpan RestrictedIdealExtension IdealWeightPowers
  GermIdealOrder DivisorExponentAlong NormalCrossings AnalyticDimensionBasics
variable {n m : ℕ} {X : CMfd.{u} n}

private theorem family_product_geometry {N : Set X} (hN : IsClosedSubmanifold n N)
    (F : Fin m → GermIdeal n X) (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y∈N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y∈N,∃ f : X → ℂ,HolomorphicAt n f y ∧
      ∀ g,(F i).mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g) :
    (relativeIdealListProduct N (List.ofFn F)).IsCoherent ∧
      ∀ x∈N,IsNonzeroAlongAt N (relativeIdealListProduct N (List.ofFn F)) x := by
  have hf : ∀ I∈List.ofFn F,I.IsCoherent ∧ (∀ y∈N,IsNonzeroAlongAt N I y) ∧
      ∀ y∈N,∃ f : X → ℂ,HolomorphicAt n f y ∧
        ∀ g,I.mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g := by
    intro I hI
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hI
    exact ⟨hc i,hnz i,hpr i⟩
  have h := relativeIdealListProduct_actual_geometry hN (List.ofFn F)
    (fun I hI => (hf I hI).1) (fun I hI => (hf I hI).2.1) (fun I hI => (hf I hI).2.2)
  exact ⟨h.1,h.2.1⟩

private theorem first_subset_product_zero {N : Set X} (hN : IsClosedSubmanifold n N)
    (F : Fin m → GermIdeal n X)
    (hP : (relativeIdealListProduct N (List.ofFn F)).IsCoherent)
    (hnz : ∀ x∈N,IsNonzeroAlongAt N (relativeIdealListProduct N (List.ofFn F)) x) :
    actualFamilyDistinctDefect N F⊆(relativeIdealListProduct N (List.ofFn F)).zeroLocus := by
  intro x hx
  have ho : 1≤ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x := by
    have hlt := hx.2
    omega
  have hz := (ordinaryTraceOrder_cosupport_iff hN hP hnz hx.1 1).mpr ho
  rw [cosupport_one (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hP hg)] at hz
  exact hz.2

/-- Real propagated coherent members give dense complement and whole thinness. -/
theorem actual_family_first_thin_dense {N : Set X} (hN : IsClosedSubmanifold n N)
    (F : Fin m → GermIdeal n X) (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y∈N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y∈N,∃ f : X → ℂ,HolomorphicAt n f y ∧
      ∀ g,(F i).mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g) :
    actualFamilyDistinctDefect N F⊆(relativeIdealListProduct N (List.ofFn F)).zeroLocus ∧
      N⊆closure (N \ actualFamilyDistinctDefect N F) ∧
      ∀ O : Set X,IsOpen O → O∩N⊆actualFamilyDistinctDefect N F → O∩N=∅ := by
  obtain ⟨hP,hNZ⟩ := family_product_geometry hN F hc hnz hpr
  have hz := first_subset_product_zero hN F hP hNZ
  refine ⟨hz,?_,?_⟩
  · intro x hx
    obtain ⟨g,hg,hfreq⟩ := hNZ x hx
    have hmem := HomogenizedGlueing.eventually_mem hP hg
    apply mem_closure_iff_frequently.mpr
    exact (hfreq.and_eventually hmem).mono fun y hy =>
      ⟨hy.1.1,fun hbad => hy.1.2 (hz hbad g hy.2)⟩
  · intro O hO hsub
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨g,hg,hfreq⟩ := hNZ x hx.2
    have hnot : ∀ᶠ y in 𝓝 x,¬(y∈N ∧ g y≠0) := by
      filter_upwards [HomogenizedGlueing.eventually_mem hP hg,hO.mem_nhds hx.1] with y hgy hyO
      intro hy
      exact hy.2 (hz (hsub ⟨hyO,hy.1⟩) g hgy)
    exact hfreq hnot

/-- Actual finite equations plus true thinness give the real lower-dimensional analytic object. -/
theorem actual_family_first_analytic_dimdrop {N : Set X} (hN : IsClosedSubmanifold n N)
    (F : Fin m → GermIdeal n X) (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y∈N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y∈N,∃ f : X → ℂ,HolomorphicAt n f y ∧
      ∀ g,(F i).mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g)
    (d : ℕ) (hreg : ∀ x∈N,RegularAtDim (n := n) N x (d+1)) :
    IsComplexAnalyticSubset (n := n) (actualFamilyDistinctDefect N F) ∧
      DimLE (n := n) (actualFamilyDistinctDefect N F) d := by
  have ha := isComplexAnalyticSubset_actualFamilyDistinctDefect hN hc hnz hpr d hreg
  have hthin := (actual_family_first_thin_dense hN F hc hnz hpr).2.2
  have hdim : DimLE (n := n) N (d+1) := by
    intro x j hx
    exact (RegularPointDimension.eq_of_regularAtDim hx (hreg x hx.2.1)).le
  refine ⟨ha,?_⟩
  simpa using (ThinDimensionDrop.dimLE_pred_of_thin
    (T' := actualFamilyDistinctDefect N F)
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN)
    (fun _ hx => hx.1) hthin hdim)

private theorem actual_template_regular {W : Set X} (hW : IsClosedSubmanifold n W)
    (d : ℕ) (hreg : ∀ x∈W,RegularAtDim (n := n) W x d) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate W []) T →
      ∀ y∈(geoTransformAlong (geometricTemplate W []) T).N,
        RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N y d
  | _,.refl,_,_,hy => hreg _ hy
  | _,.step T C π hπ,hT,y,hy => by
    have hw : (geometricTemplate W []).IsWellFormed :=
      ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT.1
    exact BlowupStrictSubmanifold.regularAtDim_geoStrictTransform hπ hwT.isClosedSubmanifold_N.1
      (actual_template_regular hW d hreg T hT.1) hT.2.subset_N hy

/-- ONLY original positive-pure carrier/SNC/density and actual history supply all lower-dimensional FIRST data. -/
theorem original_chronological_first_lower_dim (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hdense : W⊆closure (W \ ⋃ H∈E,H))
    (d : ℕ) (hreg : ∀ x∈W,RegularAtDim (n := n) W x (d+1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    IsComplexAnalyticSubset (n := n) (chronologicalDistinctDefect W E T) ∧
      (geoTransformAlong (geometricTemplate W []) T).N⊆
        closure ((geoTransformAlong (geometricTemplate W []) T).N \ chronologicalDistinctDefect W E T) ∧
      (∀ O : Set Y,IsOpen O → O∩(geoTransformAlong (geometricTemplate W []) T).N⊆
        chronologicalDistinctDefect W E T → O∩(geoTransformAlong (geometricTemplate W []) T).N=∅) ∧
      DimLE (n := n) (chronologicalDistinctDefect W E T) d := by
  let N := (geoTransformAlong (geometricTemplate W []) T).N
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hN := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT).isClosedSubmanifold_N
  have hfam : ∀ i,(F i).IsCoherent ∧ (∀ y∈N,IsNonzeroAlongAt N (F i) y) ∧
      ∀ y∈N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ g,(F i).mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g := by
    intro i
    obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
    rw [hNi] at hnzi hpri
    exact ⟨hwi.isCoherent,hnzi,hpri⟩
  have htd := actual_family_first_thin_dense hN F (fun i => (hfam i).1)
    (fun i => (hfam i).2.1) (fun i => (hfam i).2.2)
  have ha := actual_family_first_analytic_dimdrop hN F (fun i => (hfam i).1)
    (fun i => (hfam i).2.1) (fun i => (hfam i).2.2) d (actual_template_regular hW (d+1) hreg T hT)
  exact ⟨ha.1,htd.2.1,htd.2.2,ha.2⟩
end
end Hironaka.HironakaSharpActualFirstDefectDimensionDrop
