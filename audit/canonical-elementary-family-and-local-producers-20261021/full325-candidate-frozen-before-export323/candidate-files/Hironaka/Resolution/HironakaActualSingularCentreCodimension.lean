/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHSConstantSingularCentre
import Hironaka.Analytic.DimensionMonotone
import Hironaka.Analytic.PureSingularLocus
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels
/-!
# Normal codimension of the same actual singular centre

The genuine analytic singular-locus dimension theorem and analytic
dimension-zero regularity force every regular centre dimension to have
normal codimension at least two. The original singular proper-blowup
producer retains exactly the same internally selected centre and map.

Blueprint: `hironaka-actual-singular-centre-codimension-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSingularCentreCodimension
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences AnalyticDimensionBasics
  DimensionMonotone HironakaOneDimensionalCanonicalSuperlevels HironakaHolomorphicJetChartInvariance
  HironakaActualHSSingularOriginalPrefix HironakaActualHSConstantSingularCentre
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SimultaneousNormalCrossings
  BlowupTowers BlowupTowerTransforms ResolutionDriver HironakaActualReferenceHSSingularCentre
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem regular_singular_centre_add_two_le {W C : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {r : ℕ} (hr : r<n)
    (hpure : IsPureDim (n := n) W r)
    (hCS : C ⊆ W \ regularLocus (n := n) W r)
    {x : M} {k : ℕ} (hreg : RegularAtDim (n := n) C x k) : k+2≤n := by
  have hxS := hCS hreg.2.1
  have hrpos : 0<r := by
    by_contra hz
    have hr0 : r=0 := by omega
    subst r
    exact hxS.2 (regularAtDim_zero_of_analytic_dimLE_zero hW hpure.dimLE hxS.1)
  have hS := PureSingularLocus.isComplexAnalyticSubset_diff_regularLocus hW hpure
  have hdim := DimensionMonotone.DimLE.anti hS hCS (PureSingularLocus.dimLE_diff_regularLocus hW hpure)
  have hk := hdim x k hreg
  omega

theorem normal_codimension_two_of_regular_singular_centre {d t : ℕ}
    {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X]
    [IsComplexManifold (d+t) X] {W C : Set X}
    (hW : IsComplexAnalyticSubset (n := d+t) W) {r : ℕ} (hr : r<d+t)
    (hpure : IsPureDim (n := d+t) W r)
    (hCS : C ⊆ W \ regularLocus (n := d+t) W r)
    {x : X} (hreg : RegularAtDim (n := d+t) C x d) : 2≤t := by
  have h := regular_singular_centre_add_two_le hW hr hpure hCS hreg
  omega

theorem exists_actual_original_singular_centre_proper_blowup_codimension_two
    {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {r : ℕ} (hr : r<n)
    (hpure : IsPureDim (n := n) W r) (hns : ¬ IsClosedSubmanifold n W)
    {E : List (Set X)} (hE : IsSNCDivisor n E) :
    ∃ (a : X) (C : Set X) (Y : CMfd.{u} n) (π : Y → X),
      a ∈ W \ regularLocus (n := n) W r ∧ C.Nonempty ∧
      C ⊆ W \ regularLocus (n := n) W r ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      (∀ x ∈ C, ∀ i, hilbertSamuelAt (vanishingIdeal (n := n) W) x i=
        hilbertSamuelAt (vanishingIdeal (n := n) W) a i) ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (W \ regularLocus (n := n) W r)ᶜ ∧
      IsSNCDivisor n (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      (∀ y : Y, π y ∉ C → ∀ i,
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) y i=
          hilbertSamuelAt (vanishingIdeal (n := n) W) (π y) i) ∧
      C=maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (actualReferenceHSMarked (n := n) W E a) (.refl : BlowupTower X X))
        (actualReferenceHSMarked (n := n) W E a).cosupp ∧
      ∀ x k, RegularAtDim (n := n) C x k → k+2≤n := by
  obtain ⟨a,C,Y,π,ha,hCne,hCS,hCadm,hconst,hπ,hproper,hholo,hiso,hE',hoff,hCeq⟩ :=
    exists_actual_original_hs_constant_singular_centre_proper_blowup hW hK hr hpure hns hE
  exact ⟨a,C,Y,π,ha,hCne,hCS,hCadm,hconst,hπ,hproper,hholo,hiso,hE',hoff,hCeq,
    fun _ _ hreg => regular_singular_centre_add_two_le hW hr hpure hCS hreg⟩

end
end Hironaka.HironakaActualSingularCentreCodimension
