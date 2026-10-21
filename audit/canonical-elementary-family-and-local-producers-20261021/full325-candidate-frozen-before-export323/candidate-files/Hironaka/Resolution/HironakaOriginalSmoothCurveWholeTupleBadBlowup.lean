/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalSmoothCurveFullHSVariation
/-! The ENTIRE independently computed simultaneous bad locus is a genuine
GLOBAL original-admissible centre on a real smooth curve, even noncompact.
Actual original test-prefix extension only; transformed comparisons stay open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalSmoothCurveWholeTupleBadBlowup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaOriginalSmoothCurveFullHSVariation HironakaOriginalFullValueVariationLocus
  HironakaOneDimensionalCanonicalSuperlevels HironakaHolomorphicJetChartInvariance
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms CanonicalCentres
  ResolutionDriver ResolutionInvariantDriver AnalyticDimensionBasics
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {t : ℕ} {X Y : CMfd.{u} (1+t)}

/-- The TRUE original full value and EVERY original family HS order. -/
def actualOriginalCurveTupleProfile {ι : Type*} (d : ℕ) (m : MarkedIdeal (1+t) X)
    (T : BlowupTower X Y) (A : ι → GermIdeal (1+t) Y) : Y → ValTy d × (ι → ℕ → ℕ) :=
  fun x => ((invFamily (by omega : 0<1+t) d).inv m T x,fun i ℓ => hilbertSamuelAt (A i) x ℓ)

/-- The ENTIRE literal bad set is defined BEFORE any centre geometry is used. -/
def actualOriginalCurveWholeBad {ι : Type*} (d : ℕ) (m : MarkedIdeal (1+t) X)
    (T : BlowupTower X Y) (A : ι → GermIdeal (1+t) Y) (S : Set Y) : Set Y :=
  actualValueVariationLocus (n := 1+t) (actualOriginalCurveTupleProfile d m T A) S 1

/-- Only original geometry makes the ENTIRE actual tuple bad set a genuine
original-admissible centre with real local constancy of its ENTIRE tuple. -/
theorem original_smooth_curve_whole_tuple_bad_admissible (d : ℕ)
    (m : MarkedIdeal (1+t) X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily (by omega : 0<1+t) d).inv m) T)
    {S : Set Y} (hS : IsComplexAnalyticSubset (n := 1+t) S)
    (hreg : ∀ x ∈ S,RegularAtDim (n := 1+t) S x 1) (hSP : S ⊆ (geoTransformAlong m T).cosupp)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal (1+t) Y) (hA : ∀ i,(A i).IsCoherent) :
    let C := actualOriginalCurveWholeBad d m T A S
    IsComplexAnalyticSubset (n := 1+t) C ∧ DimLE (n := 1+t) C 0 ∧
      (geoTransformAlong m T).IsAdmissibleCentre C ∧
      (∀ x ∈ C,RegularAtDim (n := 1+t) C x 0) ∧
      ∀ x ∈ C,∃ U : Set Y,IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ C ∩ U,actualOriginalCurveTupleProfile d m T A y=actualOriginalCurveTupleProfile d m T A x := by
  dsimp only
  obtain ⟨hCa,hdC⟩ := original_smooth_curve_full_invariant_all_hs_variation_analytic d m h T hc hS hreg hSP A hA
  have ht := (invFamily (by omega : 0<1+t) d).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hcur := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  have hsub : actualOriginalCurveWholeBad d m T A S ⊆ (geoTransformAlong m T).cosupp := fun x hx => hSP hx.1
  have hSM := isClosedSubmanifold_subset_of_analytic_dimLE_zero hCa hdC subset_rfl
  have hNC := hasNormalCrossings_subset_of_analytic_dimLE_zero hCa hdC subset_rfl hcur.isWellFormed.isSNCDivisor
  refine ⟨hCa,hdC,⟨hSM,hsub,hNC⟩,(fun _ hx => regularAtDim_zero_of_analytic_dimLE_zero hCa hdC hx),?_⟩
  intro x hx
  obtain ⟨U,hUsub,hUo,hxU⟩ := mem_nhds_iff.mp
    (eventually_eq_on_analytic_dimLE_zero hCa hdC (actualOriginalCurveTupleProfile d m T A) hx)
  exact ⟨U,hUo,hxU,fun y hy => hUsub hy.2 hy.1⟩

/-- The SAME ENTIRE actual tuple bad set gives a genuine GLOBAL blowup,
BOTH whole good-region inverse equations and SAME ORIGINAL test-prefix/domain. -/
theorem exists_original_smooth_curve_whole_tuple_bad_blowup (d : ℕ)
    (m : MarkedIdeal (1+t) X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily (by omega : 0<1+t) d).inv m) T)
    {S : Set Y} (hS : IsComplexAnalyticSubset (n := 1+t) S)
    (hreg : ∀ x ∈ S,RegularAtDim (n := 1+t) S x 1) (hSP : S ⊆ (geoTransformAlong m T).cosupp)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal (1+t) Y) (hA : ∀ i,(A i).IsCoherent) :
    let C := actualOriginalCurveWholeBad d m T A S
    ∃ (Z : CMfd.{u} (1+t)) (π : Z → Y) (hπ : IsBlowupAlong (1+t) C π),
      IsGeoTestTower m (.step T C π hπ) ∧
      IsInvDomain d (geoTransformAlong m (.step T C π hπ)) ∧
      IsProperMap π ∧ ContMDiff 𝓘(ℂ,ComplexModel (1+t)) 𝓘(ℂ,ComplexModel (1+t)) ∞ π ∧
      IsIsomorphismOver (1+t) π Cᶜ ∧
      NormalCrossings.IsSNCDivisor (1+t) ((geoTransformAlong m T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  dsimp only
  obtain ⟨_hCa,_hdC,hCadm,_hregC,_hlocal⟩ :=
    original_smooth_curve_whole_tuple_bad_admissible d m h T hc hS hreg hSP A hA
  have ht := (invFamily (by omega : 0<1+t) d).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hcur := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  have hint : interior (actualOriginalCurveWholeBad d m T A S)=∅ := eq_empty_of_subset_empty
    ((interior_mono hCadm.2.1).trans (interior_cosupp_eq_empty hcur).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup _ hCadm.1 hint
  have hstep : IsGeoTestTower m (.step T _ π hπ) := ⟨ht,hCadm⟩
  have hpost := InvDomainTowerAlong.isInvDomain_geoTransformAlong h _ hstep
  exact ⟨Z,π,hπ,hstep,hpost,HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,
    hπ.contMDiff,BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ,
    hpost.isWellFormed.isSNCDivisor⟩

end
end Hironaka.HironakaOriginalSmoothCurveWholeTupleBadBlowup
