/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualReferenceHSSingularCentre
import Hironaka.Resolution.HironakaHypersurfaceMultiplicityDescent
import Hironaka.Analytic.AnalyticRegularStratumTopology

/-! The same genuine singular HS blowup preserves actual current geometry for a fresh next input. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualHSSingularBlowupRestart
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  AnalyticDimensionBasics MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings SimultaneousNormalCrossings BlowupTowers BlowupTowerTransforms ResolutionDriver
  HironakaActualReferenceHSSingularCentre
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Original analyticity and true geometric purity INTERNALLY produce dense SAME-dimensional regular points. -/
theorem actualPure_subset_closure_regularLocus {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hpure : IsPureDim (n := n) W d) :
    W ⊆ closure (regularLocus (n := n) W d) := by
  apply (RegularLocusDense.subset_closure_iUnion_regularLocus hW).trans
  apply closure_mono
  intro y hy
  obtain ⟨j,hj⟩ := mem_iUnion.mp hy
  have he := hpure y j hj
  exact he ▸ hj

/-- Genuine dense d-regular points force the actual dimension of EVERY regular point, including exceptional points. -/
theorem actualPure_of_subset_closure_regularLocus {W : Set M} {d : ℕ}
    (hdense : W ⊆ closure (regularLocus (n := n) W d)) : IsPureDim (n := n) W d := by
  intro y j hy
  obtain ⟨z,hz,hzd⟩ := mem_closure_iff_nhds.mp (hdense hy.2.1) _
    (RegularPatchNeighborhood.eventually_regularAtDim hy)
  exact RegularPointDimension.eq_of_regularAtDim (hz hzd.2.1) hzd

/-- A genuine current-singular blowup retains the literal next carrier's actual analytic compact pure geometry. -/
theorem actual_singular_blowup_next_current_geometry {X Y : CMfd.{u} n} {W C : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ}
    (hpure : IsPureDim (n := n) W d) (hCS : C ⊆ W \ regularLocus (n := n) W d)
    {π : Y → X} (hπ : IsBlowupAlong n C π) :
    IsComplexAnalyticSubset (n := n) (strictTransform n π W) ∧
    IsCompact (strictTransform n π W) ∧ IsPureDim (n := n) (strictTransform n π W) d := by
  have hSa := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hW
  have hSdense := HironakaHypersurfaceMultiplicityDescent.strictTransform_subset_closure_regularLocus
    hW.isClosed (actualPure_subset_closure_regularLocus hW hpure) hCS hπ
  have hSk : IsCompact (strictTransform n π W) :=
    (HironakaLocalPrincipalization.isCompact_preimage_of_isBlowupAlong hπ hK).of_isClosed_subset
      isClosed_closure (closure_minimal sdiff_subset (hW.isClosed.preimage hπ.contMDiff.continuous))
  exact ⟨hSa,hSk,actualPure_of_subset_closure_regularLocus hSdense⟩

/-- The ACTUAL transformed boundary and the literal reduced next current ideal meet every original domain field. -/
theorem actual_singular_blowup_next_marked_domain {X Y : CMfd.{u} n} {W C : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) {E : List (Set X)} (hE : IsSNCDivisor n E)
    (hCadm : (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C)
    (hCS : C ⊆ W \ regularLocus (n := n) W d) {π : Y → X} (hπ : IsBlowupAlong n C π) :
    IsInvDomain n (⟨univ,E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C],
      vanishingIdeal (n := n) (strictTransform n π W),1⟩ : MarkedIdeal n Y) ∧
    (⟨univ,E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C],
      vanishingIdeal (n := n) (strictTransform n π W),1⟩ : MarkedIdeal n Y).cosupp = strictTransform n π W := by
  obtain ⟨hSa,_hSk,hSp⟩ := actual_singular_blowup_next_current_geometry hW hK hpure hCS hπ
  have hMwell : (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence W hW,
      hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hE' := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hMwell hCadm hπ).isSNCDivisor
  exact ⟨HironakaEmbeddedBoundary.isInvDomain_boundary hSa (currentPure_interior_empty hd hSp) hE',
    HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hSa.isClosed _⟩

/-- ONLY original input produces the SAME HS singular first blowup and a genuine independently justified next input. -/
theorem exists_actual_hs_singular_first_blowup_genuine_next_input {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) (hns : ¬ IsClosedSubmanifold n W)
    {E : List (Set X)} (hE : IsSNCDivisor n E) :
    ∃ (a : X) (C : Set X) (Y : CMfd.{u} n) (π : Y → X),
      a ∈ W \ regularLocus (n := n) W d ∧ C.Nonempty ∧
      C ⊆ actualReferenceHSLocus (vanishingIdeal (n := n) W) a ∧
      C ⊆ W \ regularLocus (n := n) W d ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (W \ regularLocus (n := n) W d)ᶜ ∧
      IsSNCDivisor n (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      IsComplexAnalyticSubset (n := n) (strictTransform n π W) ∧
      IsCompact (strictTransform n π W) ∧ IsPureDim (n := n) (strictTransform n π W) d ∧
      IsInvDomain n (⟨univ,E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C],
        vanishingIdeal (n := n) (strictTransform n π W),1⟩ : MarkedIdeal n Y) ∧
      (⟨univ,E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C],
        vanishingIdeal (n := n) (strictTransform n π W),1⟩ : MarkedIdeal n Y).cosupp = strictTransform n π W ∧
      C = maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (actualReferenceHSMarked (n := n) W E a) (.refl : BlowupTower X X))
        (actualReferenceHSMarked (n := n) W E a).cosupp := by
  obtain ⟨a,C,Y,π,ha,hCne,hCSa,hCS,hCadm,hπ,hproper,hholo,hiso,hE',hCeq⟩ :=
    exists_actual_current_full_hs_singular_first_blowup hW hK hd hpure hns hE
  obtain ⟨hSa,hSk,hSp⟩ := actual_singular_blowup_next_current_geometry hW hK hpure hCS hπ
  obtain ⟨hdom,hcos⟩ := actual_singular_blowup_next_marked_domain hW hK hd hpure hE hCadm hCS hπ
  exact ⟨a,C,Y,π,ha,hCne,hCSa,hCS,hCadm,hπ,hproper,hholo,hiso,hE',hSa,hSk,hSp,hdom,hcos,hCeq⟩

end
end Hironaka.HironakaActualHSSingularBlowupRestart
