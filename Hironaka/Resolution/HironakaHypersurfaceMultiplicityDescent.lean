/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupDerivativeMaximalOrder
import Hironaka.Invariant.CompanionMaximalOrder
import Hironaka.MarkedIdeal.MaximalOrderBound
import Hironaka.Blowup.BlowupStrictIdealControlled
import Hironaka.Resolution.HironakaHypersurfaceStrictIdeal
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Analytic.AnalyticJacobianCriterion
import Hironaka.Resolution.HironakaPureCodimensionOneInvertibleIdeal
import Hironaka.Resolution.HironakaSmoothStageCenters

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaHypersurfaceMultiplicityDescent

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold
open GermIdealOrder HironakaStageCenters HironakaHypersurfaceStrictIdeal

noncomputable section

variable {n : ℕ}

/-- The actual singular-centre blowup internally preserves regular density. -/
theorem strictTransform_subset_closure_regularLocus {X Y : CMfd.{u} n} {W C : Set X}
    (hW : IsClosed W) {d : ℕ} (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (hCS : C ⊆ W \ regularLocus (n := n) W d) {π : Y → X}
    (hπ : IsBlowupAlong n C π) :
    strictTransform n π W ⊆ closure (regularLocus (n := n) (strictTransform n π W) d) := by
  have hWDense : W ⊆ closure (W \ C) := hpure.trans (closure_mono (by
    intro x hx
    exact ⟨hx.2.1, fun hxC => (hCS hxC).2 hx⟩))
  have hgeo := BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hWDense
  have hcl : geoStrictTransform π C W ⊆
      closure (regularLocus (n := n) (strictTransform n π W) d) := by
    apply closure_minimal _ isClosed_closure
    rintro z ⟨hzW, hzC⟩
    have hzE : z ∉ exceptionalLocus n π := fun hz => hzC
      (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ hz)
    rw [mem_closure_iff_nhds]
    intro U hU
    have hU' : U ∩ (exceptionalLocus n π)ᶜ ∈ 𝓝 z :=
      inter_mem hU ((StrictTransformComposition.isOpen_compl_exceptionalLocus hπ.contMDiff).mem_nhds hzE)
    have himg : π '' (U ∩ (exceptionalLocus n π)ᶜ) ∈ 𝓝 (π z) := by
      rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hπ.contMDiff hzE]
      exact image_mem_map hU'
    obtain ⟨_, ⟨y, ⟨hyU, hyE⟩, rfl⟩, hyreg⟩ :=
      mem_closure_iff_nhds.mp (hpure hzW) _ himg
    exact ⟨y, hyU, (regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus
      hπ.contMDiff hW hyE d).mpr hyreg⟩
  rwa [hgeo] at hcl

/-- The original geometric finite order bound gives the actual derivative
unit condition on the entire ambient space, not only on the original set. -/
theorem isMaximalOrder_vanishingIdeal_of_order_le {X : CMfd.{u} n} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (μ : ℕ)
    (hbound : ∀ x ∈ W, order n univ (vanishingIdeal (n := n) W) x ≤ (μ : ℕ∞)) :
    MaximalContact.IsMaximalOrder (vanishingIdeal (n := n) W) μ := by
  apply CompanionReduction.isMaximalOrder_of_forall_notMem (CartanIrreducible.cartanCoherence W hWa)
  intro x hx
  have hxW : x ∈ W := by
    have hx1 := cosupport_anti (by omega : 1 ≤ μ + 1) hx
    simpa [SmoothCentreLocus.cosupport_vanishingIdeal_one hWa.isClosed] using hx1
  have hb := (le_order_iff (𝔞 := vanishingIdeal (n := n) W) (fun _ hg => hg.1)).mpr hx.2
  have : μ + 1 ≤ μ := by exact_mod_cast hb.trans (hbound x hxW)
  omega

/-- The genuine derivative-unit bound controls the actual order itself. -/
theorem order_le_of_isMaximalOrder {X : CMfd.{u} n} {I : GermIdeal n X} {μ : ℕ}
    (hmax : MaximalContact.IsMaximalOrder I μ) (x : X) : order n univ I x ≤ (μ : ℕ∞) := by
  apply iSup₂_le
  intro q hq
  have hqle : q ≤ μ := by
    by_contra hqle
    apply CodimOneCentre.notMem_cosupport_succ_of_isMaximalOrder hmax x
    exact ⟨mem_univ x, fun g hg => (hq g hg).mono (by omega)⟩
  exact_mod_cast hqle

/-- Every literal prefix in a maximum-order hypersurface phase has the
actual complete reduced strict ideal and all original hypersurface geometry.
No later-stage equality or geometric certificate is input. -/
theorem strictIdeal_and_geometry_geoTransformAlong {m : ℕ} {X : CMfd.{u} (m + 1)}
    {W : Set X} {E : List (Set X)}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W)
    (hI : (vanishingIdeal (n := m + 1) W).IsInvertible)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m))
    (hE : NormalCrossings.IsSNCDivisor (m + 1) E) {μ : ℕ} (hμ : 2 ≤ μ)
    (hbound : ∀ x ∈ W, order (m + 1) univ (vanishingIdeal (n := m + 1) W) x ≤ (μ : ℕ∞)) :
    ∀ {Y : CMfd.{u} (m + 1)} (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ : MarkedIdeal (m + 1) X) T →
      IsComplexAnalyticSubset (n := m + 1) (strictTransform (m + 1) T.proj W) ∧
      (strictTransform (m + 1) T.proj W ⊆
        closure (regularLocus (n := m + 1) (strictTransform (m + 1) T.proj W) m)) ∧
      (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)).IsInvertible ∧
      (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ : MarkedIdeal (m + 1) X) T).ideal =
        vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W) ∧
      MaximalContact.IsMaximalOrder
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ : MarkedIdeal (m + 1) X) T).ideal μ
  | _, .refl, _ => by
      have hmax := isMaximalOrder_vanishingIdeal_of_order_le hWa μ hbound
      simpa [strictTransform, exceptionalLocus_id, hWa.isClosed.closure_eq] using
        (show IsComplexAnalyticSubset (n := m + 1) W ∧
          (W ⊆ closure (regularLocus (n := m + 1) W m)) ∧
          (vanishingIdeal (n := m + 1) W).IsInvertible ∧
          vanishingIdeal (n := m + 1) W = vanishingIdeal (n := m + 1) W ∧
          MaximalContact.IsMaximalOrder (vanishingIdeal (n := m + 1) W) μ from
          ⟨hWa, hpure, hI, rfl, hmax⟩)
  | _, .step T C π hπ, hT => by
      obtain ⟨hSa, hSpure, hSI, hTI, hmax⟩ :=
        strictIdeal_and_geometry_geoTransformAlong hWa hI hpure hE hμ hbound T hT.1
      let M : MarkedIdeal (m + 1) X := ⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩
      have hcoh : M.ideal.IsCoherent := CartanIrreducible.cartanCoherence W hWa
      obtain ⟨hNT, hcT, _⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := M) rfl hcoh T hT.1
      have hwf : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, hcoh, hE,
        SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
      have hEt := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwf T hT.1).isSNCDivisor
      have hMeq : geoTransformAlong M T =
          (⟨univ, (geoTransformAlong M T).E,
            vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W), μ⟩ : MarkedIdeal (m + 1) _) :=
        MarkedIdealOperationsTransform.MarkedIdeal.ext_of hNT rfl hTI (d_geoTransformAlong M T)
      have hCadm : (⟨univ, (geoTransformAlong M T).E,
          vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W), μ⟩ : MarkedIdeal (m + 1) _).IsAdmissibleCentre C := by
        rw [← hMeq]
        exact hT.2
      have hB : ∀ x ∈ strictTransform (m + 1) T.proj W,
          order (m + 1) univ (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)) x ≤ (μ : ℕ∞) := by
        intro x _
        rw [← hTI]
        exact order_le_of_isMaximalOrder hmax x
      have hCS : C ⊆ strictTransform (m + 1) T.proj W \
          regularLocus (n := m + 1) (strictTransform (m + 1) T.proj W) m := fun x hx =>
        HironakaHypersurfaceStageCenters.cosupport_high_mark_subset_diff_regularLocus hSa.isClosed
          (Nat.lt_succ_self m) hμ (hCadm.2.1 hx)
      have hRi := controlledTransform_vanishingIdeal_eq_strictTransform hSa hSI hSpure hEt hμ hB hCadm hπ
      have hle : (geoTransformAlong M T).ideal.Le
          (IdealWeightPowers.idealPow (vanishingIdeal (n := m + 1) C) μ) := by
        simpa only [d_geoTransformAlong] using
          HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hNT hcT hT.2
      have hcurrentInv : (geoTransformAlong M T).ideal.IsInvertible := by
        rw [hTI]
        exact hSI
      have hRinv := isInvertible_controlledTransform hπ hcurrentInv μ hle
      have hnewmax := hmax.controlledTransform hπ hcT hle
      have hnewI : (geoTransformAlong M (.step T C π hπ)).ideal =
          vanishingIdeal (n := m + 1) (strictTransform (m + 1) π (strictTransform (m + 1) T.proj W)) := by
        rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNT hcT hπ,
          d_geoTransformAlong, hTI]
        exact hRi
      have hcomp : strictTransform (m + 1) (.step T C π hπ : BlowupTower X _).proj W =
          strictTransform (m + 1) π (strictTransform (m + 1) T.proj W) := by
        rw [BlowupTower.proj_step]
        exact StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff W
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hcomp]
        exact HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hSa
      · rw [hcomp]
        exact strictTransform_subset_closure_regularLocus hSa.isClosed hSpure hCS hπ
      · rw [hcomp, ← hRi, ← hTI]
        exact hRinv
      · rw [hcomp]
        exact hnewI
      · rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNT hcT hπ, d_geoTransformAlong]
        exact hnewmax

/-- Literal recorded centres lie in the actual current singular locus,
including on the accumulated boundary, and have actual current order mu. -/
theorem stageCentres_singular_and_exact_order {m : ℕ} {X : CMfd.{u} (m + 1)}
    {W : Set X} {E : List (Set X)}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W)
    (hI : (vanishingIdeal (n := m + 1) W).IsInvertible)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m))
    (hE : NormalCrossings.IsSNCDivisor (m + 1) E) {μ : ℕ} (hμ : 2 ≤ μ)
    (hbound : ∀ x ∈ W, order (m + 1) univ (vanishingIdeal (n := m + 1) W) x ≤ (μ : ℕ∞)) :
    ∀ {Y : CMfd.{u} (m + 1)} (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ : MarkedIdeal (m + 1) X) T →
      StageCentres (fun S C =>
        C ⊆ strictTransform (m + 1) S.proj W \
          regularLocus (n := m + 1) (strictTransform (m + 1) S.proj W) m ∧
        ∀ c ∈ C, order (m + 1) univ
          (vanishingIdeal (n := m + 1) (strictTransform (m + 1) S.proj W)) c = (μ : ℕ∞)) T
  | _, .refl, _ => trivial
  | _, .step T C _π _hπ, hT => by
      refine ⟨stageCentres_singular_and_exact_order hWa hI hpure hE hμ hbound T hT.1, ?_⟩
      obtain ⟨hSa, _, _, hTI, hmax⟩ :=
        strictIdeal_and_geometry_geoTransformAlong hWa hI hpure hE hμ hbound T hT.1
      let M : MarkedIdeal (m + 1) X := ⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩
      have hNT := (pullback_eq_mul_geoTransformAlong (𝔪 := M) rfl
        (CartanIrreducible.cartanCoherence W hWa) T hT.1).1
      change (geoTransformAlong M T).ideal = _ at hTI
      have hCcos : C ⊆ cosupport (m + 1) univ
          (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)) μ := by
        have hh := hT.2.2.1
        change C ⊆ cosupport (m + 1) (geoTransformAlong M T).N
          (geoTransformAlong M T).ideal (geoTransformAlong M T).d at hh
        simpa only [hNT, hTI, d_geoTransformAlong] using hh
      refine ⟨fun x hx => HironakaHypersurfaceStageCenters.cosupport_high_mark_subset_diff_regularLocus
        hSa.isClosed (Nat.lt_succ_self m) hμ (hCcos hx), fun c hc => ?_⟩
      apply le_antisymm
      · rw [← hTI]
        exact order_le_of_isMaximalOrder hmax c
      · exact (le_order_iff (𝔞 := vanishingIdeal (n := m + 1)
          (strictTransform (m + 1) T.proj W)) (fun _ hg => hg.1)).mpr (hCcos hc).2

/-- A genuine finite canonical maximum-multiplicity phase is constructed
internally. Every actual centre lies in the current singular locus, and the
complete final current ideal has strictly smaller maximum order everywhere. -/
theorem exists_maximal_multiplicity_drop_phase {m : ℕ} {X : CMfd.{u} (m + 1)} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W) (hK : IsCompact W)
    (hI : (vanishingIdeal (n := m + 1) W).IsInvertible)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m)) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor (m + 1) E)
    (hhigh : ∃ x ∈ W, (2 : ℕ∞) ≤ order (m + 1) univ (vanishingIdeal (n := m + 1) W) x) :
    ∃ (μ : ℕ) (Y : CMfd.{u} (m + 1)) (T : BlowupTower X Y), 2 ≤ μ ∧
      (∀ x ∈ W, order (m + 1) univ (vanishingIdeal (n := m + 1) W) x ≤ (μ : ℕ∞)) ∧
      (∃ x ∈ W, order (m + 1) univ (vanishingIdeal (n := m + 1) W) x = (μ : ℕ∞)) ∧
      IsGeoResolution (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ : MarkedIdeal (m + 1) X) T ∧
      StageCentres (fun S C =>
        C ⊆ strictTransform (m + 1) S.proj W \
          regularLocus (n := m + 1) (strictTransform (m + 1) S.proj W) m ∧
        ∀ c ∈ C, order (m + 1) univ
          (vanishingIdeal (n := m + 1) (strictTransform (m + 1) S.proj W)) c = (μ : ℕ∞)) T ∧
      IsComplexAnalyticSubset (n := m + 1) (strictTransform (m + 1) T.proj W) ∧
      IsCompact (strictTransform (m + 1) T.proj W) ∧
      (strictTransform (m + 1) T.proj W ⊆
        closure (regularLocus (n := m + 1) (strictTransform (m + 1) T.proj W) m)) ∧
      (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)).IsInvertible ∧
      (∀ y : Y, order (m + 1) univ
        (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)) y < (μ : ℕ∞)) ∧
      NormalCrossings.IsSNCDivisor (m + 1)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ : MarkedIdeal (m + 1) X) T).E ∧
      GermIdeal.pullback (m := m + 1) T.proj (vanishingIdeal (n := m + 1) W) =
        (IdealWeightPowers.idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal μ).mul
          (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)) := by
  obtain ⟨μ, C, hμ, hne, _hadm, hCS, hbound, horder⟩ :=
    HironakaHypersurfaceStageCenters.exists_fresh_maximal_order_centre
      hWa hK (Nat.lt_succ_self m) hpure hE hhigh
  let M : MarkedIdeal (m + 1) X := ⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩
  have hint := HironakaEmbeddedReducible.interior_eq_empty_of_pure (Nat.lt_succ_self m) hpure
  have hd1 : ResolutionInvariantSpec.IsInvDomain (m + 1)
      (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) :=
    HironakaEmbeddedBoundary.isInvDomain_boundary hWa hint hE
  have hdom : ResolutionInvariantSpec.IsInvDomain (m + 1) M :=
    ⟨⟨hd1.isWellFormed.isClosedSubmanifold_N, hd1.isWellFormed.isCoherent,
        hd1.isWellFormed.isSNCDivisor, hd1.isWellFormed.isTransverse⟩,
      hd1.dimLE, by change 1 ≤ μ; omega, hd1.isNonzeroAlongAt⟩
  have hcosW : M.cosupp ⊆ W := fun x hx =>
    (HironakaHypersurfaceStageCenters.cosupport_high_mark_subset_diff_regularLocus
      hWa.isClosed (Nat.lt_succ_self m) hμ hx).1
  have hcosK : IsCompact M.cosupp := hK.of_isClosed_subset
    (OrderTaylor.isClosed_cosupport hdom.isWellFormed.isCoherent μ) hcosW
  obtain ⟨Y, T, _hcan, hres⟩ := HironakaAdmissibleSequence.exists_isGeoResolution_isCanonical_of_isCompact
    (CanonicalCentres.canonicalInvariant.{u} (m + 1)) hdom hcosK
  obtain ⟨hSa, hSpure, hSinv, hTI, _hmax⟩ :=
    strictIdeal_and_geometry_geoTransformAlong hWa hI hpure hE hμ hbound T hres.1
  obtain ⟨hNT, _hcT, hpb⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := M) rfl
    hdom.isWellFormed.isCoherent T hres.1
  obtain ⟨c, hc⟩ := hne
  refine ⟨μ, Y, T, hμ, hbound, ⟨c, (hCS hc).1, horder c hc⟩, hres,
    stageCentres_singular_and_exact_order hWa hI hpure hE hμ hbound T hres.1,
    hSa, HironakaAdmissibleCalculus.isCompact_strictTransform T.isBlowupSequence hK,
    hSpure, hSinv, ?_,
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hdom.isWellFormed T hres.1).isSNCDivisor, ?_⟩
  · intro y
    apply lt_of_not_ge
    intro hge
    have hy : y ∈ (geoTransformAlong M T).cosupp := by
      rw [MarkedIdeal.cosupp, hNT, hTI, d_geoTransformAlong]
      exact ⟨mem_univ y, (le_order_iff (𝔞 := vanishingIdeal (n := m + 1)
        (strictTransform (m + 1) T.proj W)) (fun _ hg => hg.1)).mp hge⟩
    rw [hres.2] at hy
    exact hy
  · change (geoTransformAlong M T).ideal = _ at hTI
    rw [hTI] at hpb
    exact hpb

/-- Actual maximal-order phase centres avoid every original regular open,
proved by induction from their internally produced current singular position. -/
theorem centresAvoid_regularOpen_of_maximalOrder_testTower {m : ℕ} {X : CMfd.{u} (m + 1)}
    {W : Set X} {E : List (Set X)}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W)
    (hI : (vanishingIdeal (n := m + 1) W).IsInvertible)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m))
    (hE : NormalCrossings.IsSNCDivisor (m + 1) E) {μ : ℕ} (hμ : 2 ≤ μ)
    (hbound : ∀ x ∈ W, order (m + 1) univ (vanishingIdeal (n := m + 1) W) x ≤ (μ : ℕ∞))
    (O : Opens X) (hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := m + 1) W x m) :
    ∀ {Y : CMfd.{u} (m + 1)} (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ : MarkedIdeal (m + 1) X) T →
      RestrictEmptyTower.CentresAvoid O T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      have havoid := centresAvoid_regularOpen_of_maximalOrder_testTower hWa hI hpure hE hμ hbound O hreg T hT.1
      have hstage := (stageCentres_singular_and_exact_order hWa hI hpure hE hμ hbound
        (.step T C π hπ) hT).2.1
      refine ⟨havoid, disjoint_left.mpr fun c hc hcO => ?_⟩
      have hcW := HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous
        hWa.isClosed (hstage hc).1
      have hcreg := (regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus T.contMDiff_proj hWa.isClosed
        (EmbeddedFromResolution.notMem_exceptionalLocus_of_centresAvoid O T havoid c hcO) m).mpr
          (hreg _ hcW hcO)
      exact (hstage hc).2 hcreg

private theorem fderiv_local_generator_ne_zero {X : CMfd.{u} n} (I : GermIdeal n X)
    {x : X} (f : X → ℂ) (hf : HolomorphicAt n f x) (hfx : f x = 0)
    (hgen : ∀ g, I.mem x g ↔ IsInSpanAt (n := n) (· = f) x g)
    (horder : order n univ I x < (2 : ℕ∞)) :
    fderiv ℂ (f ∘ (complexChartAt (n := n) x).val.symm)
      ((complexChartAt (n := n) x).val x) ≠ 0 := by
  intro hdf
  let e := complexChartAt (n := n) x
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hqt := e.val.map_source hxe
  have hsq := e.val.left_inv hxe
  have hfh : DifferentiableAt ℂ (f ∘ e.val.symm) (e.val x) := by
    change DifferentiableAt ℂ (f ∘ (chartAt (ComplexModel n) x).symm) (chartAt (ComplexModel n) x x)
    exact BlowupSpaceTangent.differentiableAt_comp_chart_symm hqt
      (by change MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f (e.val.symm (e.val x)); rw [hsq]; exact hf.mdifferentiableAt)
  have hF0 : (f ∘ e.val.symm) (e.val x) = 0 := by simpa only [Function.comp_apply, hsq] using hfx
  have hinv : Tendsto e.val.symm (𝓝 (e.val x)) (𝓝 x) := by
    simpa only [hsq] using (e.val.continuousAt_symm hqt).tendsto
  have hge : (2 : ℕ∞) ≤ order n univ I x := by
    apply (le_order_iff (𝔞 := I) (fun g hg => ((hgen g).mp hg).holomorphicAt)).mpr
    intro g hg
    obtain ⟨hgh, a, ha, heq⟩ := isInSpanAt_eq_iff.mp ((hgen g).mp hg)
    have hah : DifferentiableAt ℂ (a ∘ e.val.symm) (e.val x) := by
      change DifferentiableAt ℂ (a ∘ (chartAt (ComplexModel n) x).symm) (chartAt (ComplexModel n) x x)
      exact BlowupSpaceTangent.differentiableAt_comp_chart_symm hqt
        (by change MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) a (e.val.symm (e.val x)); rw [hsq]; exact ha.mdifferentiableAt)
    have heqchart : g ∘ e.val.symm =ᶠ[𝓝 (e.val x)]
        fun z => (a ∘ e.val.symm) z * (f ∘ e.val.symm) z := hinv.eventually heq
    have hgd : fderiv ℂ (g ∘ e.val.symm) (e.val x) = 0 := by
      rw [heqchart.fderiv_eq]
      change fderiv ℂ ((a ∘ e.val.symm) * (f ∘ e.val.symm)) (e.val x) = 0
      rw [(hah.hasFDerivAt.mul hfh.hasFDerivAt).fderiv]
      ext v
      change fderiv ℂ (f ∘ e.val.symm) (e.val x) = 0 at hdf
      simp [Function.comp_apply, hsq, hfx, hdf]
    refine ⟨g, ?_, Eventually.of_forall fun _ _ => rfl⟩
    apply OrderTaylor.mem_idealPow_of_iterChartDeriv_eq_zero (e := e) hxe hgh 2
    intro L hL
    cases L with
    | nil =>
      change g x = 0
      rw [heq.self_of_nhds]
      exact mul_eq_zero_of_right _ hfx
    | cons v L =>
      have hlen : L.length = 0 := by simp only [List.length_cons] at hL; omega
      have hnil : L = [] := List.eq_nil_of_length_eq_zero hlen
      subst L
      rw [OrderTaylor.iterChartDeriv_cons, OrderTaylor.iterChartDeriv_nil]
      change fderiv ℂ (g ∘ e.val.symm) (e.val x) v = 0
      rw [hgd]
      simp
  exact (not_le_of_gt horder) hge

/-- Order below two of the actual invertible reduced ideal internally
produces the original hypersurface's true regular flattening. -/
theorem regularAtDim_of_order_lt_two_of_isInvertible {m : ℕ} {X : CMfd.{u} (m + 1)}
    {W : Set X} (hW : IsClosed W) (hI : (vanishingIdeal (n := m + 1) W).IsInvertible)
    {x : X} (hxW : x ∈ W)
    (horder : order (m + 1) univ (vanishingIdeal (n := m + 1) W) x < (2 : ℕ∞)) :
    RegularAtDim (n := m + 1) W x m := by
  obtain ⟨U, hU, hxU, f, hf, _hnon, hgen⟩ := hI x
  have hfh : HolomorphicAt (m + 1) f x :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hf hxU
  have hfx : f x = 0 := ((hgen x hxU f).mpr
    (InvertibleIdealQuotient.isInSpanAt_self rfl hfh)).2.self_of_nhds hxW
  have hdf := fderiv_local_generator_ne_zero _ f hfh hfx (hgen x hxU) horder
  have hzero : ∀ y ∈ U, y ∈ W ↔ f y = 0 := by
    intro y hy
    have hfy : HolomorphicAt (m + 1) f y :=
      InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hf hy
    constructor
    · intro hyW
      exact ((hgen y hy f).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hfy)).2.self_of_nhds hyW
    · intro hfy0
      by_contra hyW
      have h1 : (vanishingIdeal (n := m + 1) W).mem y (fun _ => (1 : ℂ)) := by
        refine ⟨holomorphicAt_const 1, ?_⟩
        filter_upwards [hW.isOpen_compl.mem_nhds hyW] with z hz hzW
        exact False.elim (hz hzW)
      obtain ⟨_, a, _, heq⟩ := isInSpanAt_eq_iff.mp ((hgen y hy _).mp h1)
      have h1z := heq.self_of_nhds
      simp only [hfy0, mul_zero] at h1z
      exact one_ne_zero h1z
  let e := complexChartAt (n := m + 1) x
  let V : Set (ComplexModel (m + 1)) := e.val.target ∩ e.val.symm ⁻¹' U
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  let P : ComplexAnalyticPresentationAt (n := m + 1) W x := {
    generatorCount := 1
    generator := fun _ => f ∘ e.val.symm
    coordinateNeighborhood := V
    isOpen_coordinateNeighborhood := e.val.isOpen_inter_preimage_symm hU
    center_mem_coordinateNeighborhood :=
      ⟨e.val.map_source hxe, by change e.val.symm (e.val x) ∈ U; rw [e.val.left_inv hxe]; exact hxU⟩
    coordinateNeighborhood_subset_target := inter_subset_left
    generator_holomorphic := fun _ z hz => by
      apply DifferentiableAt.differentiableWithinAt
      change DifferentiableAt ℂ (f ∘ (chartAt (ComplexModel (m + 1)) x).symm) z
      exact BlowupSpaceTangent.differentiableAt_comp_chart_symm hz.1
        ((hf).mdifferentiableAt (hU.mem_nhds hz.2))
    zeroLocus := by
      intro y hy hyV
      have hyU : y ∈ U := by
        have hh : e.val.symm (e.val y) ∈ U := hyV.2
        rwa [e.val.left_inv hy] at hh
      change y ∈ W ↔ ∀ _ : Fin 1, f (e.val.symm (e.val y)) = 0
      simpa only [e.val.left_inv hy, forall_const] using hzero y hyU }
  have hli : LinearIndependent ℂ (fun i : Fin 1 =>
      fderiv ℂ (P.generator i) ((complexChartAt (n := m + 1) x).val x)) := by
    rw [linearIndependent_unique_iff]
    exact hdf
  have hr := AnalyticJacobianCriterion.regularAtDim_of_presentation_fullRank P hxW hli
  simpa only [P, Nat.add_sub_cancel_right] using hr


/-- Actual boundary lists are independent of the ideal and mark. -/
theorem boundary_geoTransformAlong_eq_of_boundary_eq {X : CMfd.{u} n}
    (M N : MarkedIdeal n X) (hE : M.E = N.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong M T).E = (geoTransformAlong N T).E
  | _, .refl => hE
  | _, .step T C π _hπ => by
      rw [geoTransformAlong_step, geoTransformAlong_step, geoTransform_E, geoTransform_E,
        boundary_geoTransformAlong_eq_of_boundary_eq M N hE T]

/-- Genuine admissibility gives the literal normal-crossing witness for every centre. -/
theorem stageCentres_normalCrossings_of_isGeoTestTower {X : CMfd.{u} n}
    (M : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower M T →
      StageCentres (fun P C => NormalCrossings.HasNormalCrossings n C (geoTransformAlong M P).E) T
  | _, .refl, _ => trivial
  | _, .step T _C _π _hπ, hT =>
      ⟨stageCentres_normalCrossings_of_isGeoTestTower M T hT.1, hT.2.2.2⟩

/-- Concatenation transports literal singular positions and actual NC boundaries. -/
theorem stageCentres_singular_normalCrossings_append {m : ℕ} {X Y Z : CMfd.{u} (m + 1)}
    (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (hT : StageCentres (fun P C =>
      C ⊆ strictTransform (m + 1) P.proj W \
        regularLocus (n := m + 1) (strictTransform (m + 1) P.proj W) m ∧
      NormalCrossings.HasNormalCrossings (m + 1) C
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E) T)
    (hS : StageCentres (fun P C =>
      C ⊆ strictTransform (m + 1) P.proj (strictTransform (m + 1) T.proj W) \
        regularLocus (n := m + 1)
          (strictTransform (m + 1) P.proj (strictTransform (m + 1) T.proj W)) m ∧
      NormalCrossings.HasNormalCrossings (m + 1) C
        (geoTransformAlong (⟨univ,
          (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E,
          vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W), 1⟩ : MarkedIdeal (m + 1) Y) P).E) S) :
    StageCentres (fun P C =>
      C ⊆ strictTransform (m + 1) P.proj W \
        regularLocus (n := m + 1) (strictTransform (m + 1) P.proj W) m ∧
      NormalCrossings.HasNormalCrossings (m + 1) C
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E) (T.append S) := by
  induction S with
  | refl => exact hT
  | @step A B S C π hπ ih =>
      refine ⟨ih hS.1, ?_⟩
      have hstrict := StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj W
      rw [← BlowupTower.proj_append] at hstrict
      dsimp only
      rw [hstrict]
      refine ⟨hS.2.1, ?_⟩
      rw [geoTransformAlong_append]
      rw [boundary_geoTransformAlong_eq_of_boundary_eq
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T)
        (⟨univ, (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E,
          vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W), 1⟩ : MarkedIdeal (m + 1) Y) rfl S]
      exact hS.2.2

/-- A tower with internally produced singular positions avoids every original regular open. -/
theorem centresAvoid_regularOpen_of_stageCentres_singular {m : ℕ} {X : CMfd.{u} (m + 1)}
    {W : Set X} (hW : IsClosed W) (O : Opens X)
    (hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := m + 1) W x m) :
    ∀ {Y : CMfd.{u} (m + 1)} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ strictTransform (m + 1) P.proj W \
        regularLocus (n := m + 1) (strictTransform (m + 1) P.proj W) m) T →
      RestrictEmptyTower.CentresAvoid O T
  | _, .refl, _ => trivial
  | _, .step T _C _π _hπ, hT => by
      have havoid := centresAvoid_regularOpen_of_stageCentres_singular hW O hreg T hT.1
      refine ⟨havoid, disjoint_left.mpr fun c hc hcO => ?_⟩
      have hcW := HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous
        hW (hT.2 hc).1
      have hcreg := (regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus T.contMDiff_proj hW
        (EmbeddedFromResolution.notMem_exceptionalLocus_of_centresAvoid O T havoid c hcO) m).mpr
          (hreg _ hcW hcO)
      exact (hT.2 hc).2 hcreg


private theorem stageCentres_pair_imp {X : CMfd.{u} n}
    {P Q R : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Set Y → Prop}
    (himp : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) C, P T C → Q T C → R T C) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), StageCentres P T → StageCentres Q T → StageCentres R T
  | _, .refl, _, _ => trivial
  | _, .step T C _π _hπ, hP, hQ =>
      ⟨stageCentres_pair_imp himp T hP.1 hQ.1, himp T C hP.2 hQ.2⟩

/-- Strong induction on a natural bound actually constructs finitely many
fresh reduced multiplicity phases; every recorded centre is currently singular. -/
theorem exists_tower_smooth_of_order_le {m : ℕ} (b : ℕ) :
    ∀ {X : CMfd.{u} (m + 1)} {W : Set X},
    IsComplexAnalyticSubset (n := m + 1) W → IsCompact W →
    (vanishingIdeal (n := m + 1) W).IsInvertible →
    (W ⊆ closure (regularLocus (n := m + 1) W m)) →
    ∀ {E : List (Set X)}, NormalCrossings.IsSNCDivisor (m + 1) E →
    (∀ x ∈ W, order (m + 1) univ (vanishingIdeal (n := m + 1) W) x ≤ (b : ℕ∞)) →
    ∃ (Y : CMfd.{u} (m + 1)) (T : BlowupTower X Y),
      IsComplexAnalyticSubset (n := m + 1) (strictTransform (m + 1) T.proj W) ∧
      IsCompact (strictTransform (m + 1) T.proj W) ∧
      (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)).IsInvertible ∧
      (∀ y ∈ strictTransform (m + 1) T.proj W,
        RegularAtDim (n := m + 1) (strictTransform (m + 1) T.proj W) y m) ∧
      NormalCrossings.IsSNCDivisor (m + 1)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      StageCentres (fun P C =>
        C ⊆ strictTransform (m + 1) P.proj W \
          regularLocus (n := m + 1) (strictTransform (m + 1) P.proj W) m ∧
        NormalCrossings.HasNormalCrossings (m + 1) C
          (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E) T := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
      intro X W hWa hK hI hpure E hE hbound
      by_cases hhigh : ∃ x ∈ W, (2 : ℕ∞) ≤ order (m + 1) univ (vanishingIdeal (n := m + 1) W) x
      · obtain ⟨μ, Y, T, hμ, hμbound, ⟨x, hxW, hxμ⟩, hres, hstage,
          hSa, hSK, hSpure, hSI, hdrop, hTE, _hpb⟩ :=
          exists_maximal_multiplicity_drop_phase hWa hK hI hpure hE hhigh
        have hμle : μ ≤ b := by exact_mod_cast (hxμ ▸ hbound x hxW)
        have hpred : μ - 1 < b := by omega
        let M : MarkedIdeal (m + 1) X := ⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩
        let S0 := strictTransform (m + 1) T.proj W
        let ET := (geoTransformAlong M T).E
        have hEeq := boundary_geoTransformAlong_eq_of_boundary_eq
          (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ : MarkedIdeal (m + 1) X) M rfl T
        have hET : NormalCrossings.IsSNCDivisor (m + 1) ET := by
          rw [hEeq] at hTE
          exact hTE
        have hSbound : ∀ y ∈ S0, order (m + 1) univ (vanishingIdeal (n := m + 1) S0) y ≤ ((μ - 1 : ℕ) : ℕ∞) := by
          intro y _hy
          apply ENat.lt_natCast_add_one_iff.mp
          have hμsucc : μ - 1 + 1 = μ := by omega
          have hh : order (m + 1) univ (vanishingIdeal (n := m + 1) S0) y < ((μ - 1 + 1 : ℕ) : ℕ∞) := by
            simpa only [hμsucc] using hdrop y
          simpa only [Nat.cast_add, Nat.cast_one] using hh
        obtain ⟨Z, R, hFa, hFK, hFI, hFreg, hFE, hRstage⟩ :=
          ih (μ - 1) hpred hSa hSK hSI hSpure hET hSbound
        have hTstage : StageCentres (fun P C =>
            C ⊆ strictTransform (m + 1) P.proj W \
              regularLocus (n := m + 1) (strictTransform (m + 1) P.proj W) m ∧
            NormalCrossings.HasNormalCrossings (m + 1) C (geoTransformAlong M P).E) T := by
          refine stageCentres_pair_imp (P := fun P C =>
            C ⊆ strictTransform (m + 1) P.proj W \
              regularLocus (n := m + 1) (strictTransform (m + 1) P.proj W) m ∧
            ∀ c ∈ C, order (m + 1) univ (vanishingIdeal (n := m + 1) (strictTransform (m + 1) P.proj W)) c = (μ : ℕ∞))
            (Q := fun P C => NormalCrossings.HasNormalCrossings (m + 1) C
              (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ : MarkedIdeal (m + 1) X) P).E)
            (fun P C hP hQ => ⟨hP.1, ?_⟩) T hstage
            (stageCentres_normalCrossings_of_isGeoTestTower _ T hres.1)
          rw [← boundary_geoTransformAlong_eq_of_boundary_eq
            (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ : MarkedIdeal (m + 1) X) M rfl P]
          exact hQ
        have hstrict := StrictTransformComposition.strictTransform_comp T.contMDiff_proj R.contMDiff_proj W
        rw [← BlowupTower.proj_append] at hstrict
        have hfinalE : (geoTransformAlong M (T.append R)).E =
            (geoTransformAlong (⟨univ, ET, vanishingIdeal (n := m + 1) S0, 1⟩ : MarkedIdeal (m + 1) Y) R).E := by
          rw [geoTransformAlong_append]
          exact boundary_geoTransformAlong_eq_of_boundary_eq (geoTransformAlong M T)
            (⟨univ, ET, vanishingIdeal (n := m + 1) S0, 1⟩ : MarkedIdeal (m + 1) Y) rfl R
        refine ⟨Z, T.append R, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rwa [hstrict]
        · rwa [hstrict]
        · rwa [hstrict]
        · rwa [hstrict]
        · rwa [hfinalE]
        · exact stageCentres_singular_normalCrossings_append W E T R hTstage hRstage
      · have hreg : ∀ x ∈ W, RegularAtDim (n := m + 1) W x m := by
          intro x hx
          apply regularAtDim_of_order_lt_two_of_isInvertible hWa.isClosed hI hx
          exact lt_of_not_ge (fun h => hhigh ⟨x, hx, h⟩)
        have hST : strictTransform (m + 1) (id : X → X) W = W := by
          simp [strictTransform, exceptionalLocus_id, hWa.isClosed.closure_eq]
        refine ⟨X, .refl, ?_, ?_, ?_, ?_, hE, trivial⟩
        · simpa only [BlowupTower.proj_refl, hST] using hWa
        · simpa only [BlowupTower.proj_refl, hST] using hK
        · simpa only [BlowupTower.proj_refl, hST] using hI
        · simpa only [BlowupTower.proj_refl, hST] using hreg


private theorem stageCentres_imp {X : CMfd.{u} n}
    {P Q : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Set Y → Prop}
    (himp : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) C, P T C → Q T C) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), StageCentres P T → StageCentres Q T
  | _, .refl, _ => trivial
  | _, .step T C _π _hπ, hP => ⟨stageCentres_imp himp T hP.1, himp T C hP.2⟩

private theorem admissible_of_stageCentres_normalCrossings {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (F : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      StageCentres (fun P C => NormalCrossings.HasNormalCrossings n C (geoTransformAlong M P).E) T →
      RestrictEmptyTower.CentresOver F T →
      HironakaAdmissibleSequence.IsAdmissibleBlowupSequence n X M.E F Y T.proj (geoTransformAlong M T).E
  | _, .refl, _, _ => HironakaAdmissibleSequence.IsAdmissibleBlowupSequence.refl
  | _, .step T C π hπ, hNC, hF =>
      HironakaAdmissibleSequence.IsAdmissibleBlowupSequence.step T.proj _ C π
        (admissible_of_stageCentres_normalCrossings M F T hNC.1 hF.1) hπ hNC.2 hF.2

/-- Construct all reduced multiplicity restarts internally, with no supplied
order bound or termination data. Every literal centre is currently singular;
the actual admissible tower preserves every original regular open. -/
theorem exists_tower_smooth_singular_stage_centres {m : ℕ} {X : CMfd.{u} (m + 1)} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W) (hK : IsCompact W)
    (hI : (vanishingIdeal (n := m + 1) W).IsInvertible)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m)) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor (m + 1) E) :
    ∃ (Y : CMfd.{u} (m + 1)) (T : BlowupTower X Y),
      IsComplexAnalyticSubset (n := m + 1) (strictTransform (m + 1) T.proj W) ∧
      IsCompact (strictTransform (m + 1) T.proj W) ∧
      (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)).IsInvertible ∧
      IsClosedSubmanifold (m + 1) (strictTransform (m + 1) T.proj W) ∧
      (∀ y ∈ strictTransform (m + 1) T.proj W,
        RegularAtDim (n := m + 1) (strictTransform (m + 1) T.proj W) y m) ∧
      NormalCrossings.IsSNCDivisor (m + 1)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      HironakaAdmissibleSequence.IsAdmissibleBlowupSequence (m + 1) X E
        (W \ regularLocus (n := m + 1) W m) Y T.proj
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      (∀ (O : Opens X), (∀ x ∈ W, x ∈ O → RegularAtDim (n := m + 1) W x m) →
        RestrictEmptyTower.CentresAvoid O T) ∧
      StageCentres (fun P C =>
        C ⊆ strictTransform (m + 1) P.proj W \
          regularLocus (n := m + 1) (strictTransform (m + 1) P.proj W) m ∧
        NormalCrossings.HasNormalCrossings (m + 1) C
          (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E) T := by
  have hexbound : ∃ b : ℕ, ∀ x ∈ W,
      order (m + 1) univ (vanishingIdeal (n := m + 1) W) x ≤ (b : ℕ∞) := by
    by_cases hhigh : ∃ x ∈ W, (2 : ℕ∞) ≤ order (m + 1) univ (vanishingIdeal (n := m + 1) W) x
    · obtain ⟨μ, _C, _hμ, _hne, _hadm, _hCS, hbound, _horder⟩ :=
        HironakaHypersurfaceStageCenters.exists_fresh_maximal_order_centre hWa hK (Nat.lt_succ_self m) hpure hE hhigh
      exact ⟨μ, hbound⟩
    · refine ⟨1, fun x hx => ?_⟩
      apply ENat.lt_natCast_add_one_iff.mp
      exact lt_of_not_ge (fun h => hhigh ⟨x, hx, h⟩)
  obtain ⟨b, hbound⟩ := hexbound
  obtain ⟨Y, T, hSa, hSK, hSI, hreg, hTE, hstage⟩ :=
    exists_tower_smooth_of_order_le b hWa hK hI hpure hE hbound
  have hsing : StageCentres (fun P C => C ⊆ strictTransform (m + 1) P.proj W \
      regularLocus (n := m + 1) (strictTransform (m + 1) P.proj W) m) T :=
    stageCentres_imp (fun _ _ h => h.1) T hstage
  have hNC : StageCentres (fun P C => NormalCrossings.HasNormalCrossings (m + 1) C
      (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E) T :=
    stageCentres_imp (fun _ _ h => h.2) T hstage
  have havoid : ∀ (O : Opens X), (∀ x ∈ W, x ∈ O → RegularAtDim (n := m + 1) W x m) →
      RestrictEmptyTower.CentresAvoid O T := fun O hO =>
    centresAvoid_regularOpen_of_stageCentres_singular hWa.isClosed O hO T hsing
  let O : Opens X := ⟨(W \ regularLocus (n := m + 1) W m)ᶜ,
    (HironakaEmbeddedReducible.isClosed_diff_regularLocus hWa.isClosed m).isOpen_compl⟩
  have hOreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := m + 1) W x m := by
    intro x hxW hxO
    by_contra hxreg
    exact hxO ⟨hxW, hxreg⟩
  have hOver : RestrictEmptyTower.CentresOver (W \ regularLocus (n := m + 1) W m) T := by
    have hh := HironakaAdmissibleSequence.centresOver_compl_of_centresAvoid O T (havoid O hOreg)
    simpa only [O, Opens.coe_mk, compl_compl] using hh
  have hAdm := admissible_of_stageCentres_normalCrossings
    (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X)
    (W \ regularLocus (n := m + 1) W m) T hNC hOver
  exact ⟨Y, T, hSa, hSK, hSI, ⟨hSa.isClosed, fun y hy => ⟨m, hreg y hy⟩⟩,
    hreg, hTE, hAdm, havoid, hstage⟩


/-- For an actual original irreducible hypersurface, invertibility is produced
by its geometric codimension-one local equations, including singular points. -/
theorem exists_tower_smooth_irreducible_hypersurface {m : ℕ} {X : CMfd.{u} (m + 1)}
    (V : ClosedIrreducibleAnalyticSubvariety (m + 1) X) (hdim : V.dim = m)
    (hK : IsCompact V.carrier) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor (m + 1) E) :
    ∃ (Y : CMfd.{u} (m + 1)) (T : BlowupTower X Y),
      IsComplexAnalyticSubset (n := m + 1) (strictTransform (m + 1) T.proj V.carrier) ∧
      IsCompact (strictTransform (m + 1) T.proj V.carrier) ∧
      (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj V.carrier)).IsInvertible ∧
      IsClosedSubmanifold (m + 1) (strictTransform (m + 1) T.proj V.carrier) ∧
      (∀ y ∈ strictTransform (m + 1) T.proj V.carrier,
        RegularAtDim (n := m + 1) (strictTransform (m + 1) T.proj V.carrier) y m) ∧
      NormalCrossings.IsSNCDivisor (m + 1)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) V.carrier, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      HironakaAdmissibleSequence.IsAdmissibleBlowupSequence (m + 1) X E
        (V.carrier \ regularLocus (n := m + 1) V.carrier m) Y T.proj
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) V.carrier, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      (∀ (O : Opens X), (∀ x ∈ V.carrier, x ∈ O → RegularAtDim (n := m + 1) V.carrier x m) →
        RestrictEmptyTower.CentresAvoid O T) ∧
      StageCentres (fun P C =>
        C ⊆ strictTransform (m + 1) P.proj V.carrier \
          regularLocus (n := m + 1) (strictTransform (m + 1) P.proj V.carrier) m ∧
        NormalCrossings.HasNormalCrossings (m + 1) C
          (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) V.carrier, 1⟩ : MarkedIdeal (m + 1) X) P).E) T := by
  have hpure := HironakaEmbeddedReducible.subset_closure_regularLocus V
  rw [hdim] at hpure
  have hI := HironakaPureCodimensionOneInvertibleIdeal.isInvertible_vanishingIdeal_of_pure V.analytic hpure
  exact exists_tower_smooth_singular_stage_centres V.analytic hK hI hpure hE


/-- Original regular density and density off the original closed boundary
produce actual density off their entire union. -/
theorem subset_closure_diff_boundary_union_singular {X : CMfd.{u} n} {W B : Set X} {d : ℕ}
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) (hB : IsClosed B)
    (hdense : W ⊆ closure (W \ B)) :
    W ⊆ closure (W \ (B ∪ (W \ regularLocus (n := n) W d))) := by
  refine hdense.trans (closure_minimal ?_ isClosed_closure)
  rintro y ⟨hyW, hyB⟩
  rw [mem_closure_iff_nhds]
  intro U hU
  have hUB : U ∩ Bᶜ ∈ 𝓝 y := inter_mem hU (hB.isOpen_compl.mem_nhds hyB)
  obtain ⟨z, ⟨hzU, hzB⟩, hzreg⟩ := mem_closure_iff_nhds.mp (hpure hyW) _ hUB
  exact ⟨z, hzU, hzreg.2.1, fun h => h.elim hzB (fun h => h.2 hzreg)⟩


/-- Genuine regular-density propagation through every actual singular-centre
prefix, without a later-stage purity certificate. -/
theorem strictTransform_subset_closure_regularLocus_of_stageCentres_singular {X : CMfd.{u} n}
    {W : Set X} (hW : IsClosed W) {d : ℕ} (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ strictTransform n P.proj W \
        regularLocus (n := n) (strictTransform n P.proj W) d) T →
      strictTransform n T.proj W ⊆ closure (regularLocus (n := n) (strictTransform n T.proj W) d)
  | _, .refl, _ => by
      simpa [strictTransform, exceptionalLocus_id, hW.closure_eq] using hpure
  | _, .step T C π hπ, hT => by
      have hP := strictTransform_subset_closure_regularLocus_of_stageCentres_singular hW hpure T hT.1
      have hNew := strictTransform_subset_closure_regularLocus isClosed_closure hP hT.2 hπ
      rw [BlowupTower.proj_step, StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff]
      exact hNew

/-- The actual pure-dimension dictionary identifies every produced
singular centre with current points nonregular in every dimension. -/
theorem stageCentres_all_nonregular_of_stageCentres_singular {X : CMfd.{u} n}
    {W : Set X} (hW : IsClosed W) {d : ℕ} (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ strictTransform n P.proj W \
        regularLocus (n := n) (strictTransform n P.proj W) d) T →
      StageCentres (fun P C => C ⊆ {x | x ∈ strictTransform n P.proj W ∧
        ∀ k, ¬ RegularAtDim (n := n) (strictTransform n P.proj W) x k}) T
  | _, .refl, _ => trivial
  | _, .step T _C _π _hπ, hT => by
      refine ⟨stageCentres_all_nonregular_of_stageCentres_singular hW hpure T hT.1, ?_⟩
      have hP := strictTransform_subset_closure_regularLocus_of_stageCentres_singular hW hpure T hT.1
      dsimp only
      rw [← HironakaEmbeddedReducible.diff_regularLocus_eq_of_pure hP]
      exact hT.2

/-- Concatenate the genuinely produced singular phase and the genuinely
produced smooth-boundary tail with literal current centre positions. -/
theorem stageCentres_embedded_position_append {m : ℕ} {X Y Z : CMfd.{u} (m + 1)}
    (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (hT : StageCentres (fun P C =>
      C ⊆ {x | x ∈ strictTransform (m + 1) P.proj W ∧
        ∀ k, ¬ RegularAtDim (n := m + 1) (strictTransform (m + 1) P.proj W) x k} ∧
      NormalCrossings.HasNormalCrossings (m + 1) C
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E) T)
    (hS : StageCentres (fun P C =>
      (IsClosedSubmanifold (m + 1) (strictTransform (m + 1) P.proj (strictTransform (m + 1) T.proj W)) ∧
      C ⊆ strictTransform (m + 1) P.proj (strictTransform (m + 1) T.proj W) ∩ ⋃ H ∈
        (geoTransformAlong (⟨univ,
          (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E,
          vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W), 1⟩ : MarkedIdeal (m + 1) Y) P).E, H) ∧
      NormalCrossings.HasNormalCrossings (m + 1) C
        (geoTransformAlong (⟨univ,
          (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E,
          vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W), 1⟩ : MarkedIdeal (m + 1) Y) P).E) S) :
    StageCentres (fun P C =>
      (C ⊆ {x | x ∈ strictTransform (m + 1) P.proj W ∧
        ∀ k, ¬ RegularAtDim (n := m + 1) (strictTransform (m + 1) P.proj W) x k} ∨
      (IsClosedSubmanifold (m + 1) (strictTransform (m + 1) P.proj W) ∧
        C ⊆ strictTransform (m + 1) P.proj W ∩ ⋃ H ∈
          (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E, H)) ∧
      NormalCrossings.HasNormalCrossings (m + 1) C
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E) (T.append S) := by
  induction S with
  | refl => exact stageCentres_imp (fun _ _ h => ⟨Or.inl h.1, h.2⟩) T hT
  | @step A B S C π hπ ih =>
      refine ⟨ih hS.1, ?_⟩
      have hstrict := StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj W
      rw [← BlowupTower.proj_append] at hstrict
      dsimp only
      rw [hstrict, geoTransformAlong_append,
        boundary_geoTransformAlong_eq_of_boundary_eq
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T)
        (⟨univ, (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E,
          vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W), 1⟩ : MarkedIdeal (m + 1) Y) rfl S]
      exact ⟨Or.inr hS.2.1, hS.2.2⟩


/-- A genuinely produced embedded hypersurface resolution with literal
per-stage centre positions, including centres on the accumulated boundary. -/
theorem exists_tower_embedded_hypersurface_stage_centres {m : ℕ} {X : CMfd.{u} (m + 1)} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W) (hK : IsCompact W)
    (hI : (vanishingIdeal (n := m + 1) W).IsInvertible)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m)) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor (m + 1) E)
    (hEDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) :
    ∃ (Y : CMfd.{u} (m + 1)) (T : BlowupTower X Y),
      HironakaAdmissibleSequence.IsAdmissibleBlowupSequence (m + 1) X E
        ((W \ regularLocus (n := m + 1) W m) ∪ (W ∩ ⋃ H ∈ E, H)) Y T.proj
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      NormalCrossings.IsSNCDivisor (m + 1)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      IsClosedSubmanifold (m + 1) (strictTransform (m + 1) T.proj W) ∧
      (∀ y ∈ strictTransform (m + 1) T.proj W,
        RegularAtDim (n := m + 1) (strictTransform (m + 1) T.proj W) y m) ∧
      NormalCrossings.HasNormalCrossings (m + 1) (strictTransform (m + 1) T.proj W)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      NormalCrossings.IsTransverse (m + 1) (strictTransform (m + 1) T.proj W)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      IsIsomorphismOver (m + 1) T.proj
        ((W \ regularLocus (n := m + 1) W m) ∪ (W ∩ ⋃ H ∈ E, H))ᶜ ∧
      StageCentres (fun P C =>
        (C ⊆ {x | x ∈ strictTransform (m + 1) P.proj W ∧
          ∀ k, ¬ RegularAtDim (n := m + 1) (strictTransform (m + 1) P.proj W) x k} ∨
        (IsClosedSubmanifold (m + 1) (strictTransform (m + 1) P.proj W) ∧
          C ⊆ strictTransform (m + 1) P.proj W ∩ ⋃ H ∈
            (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E, H)) ∧
        NormalCrossings.HasNormalCrossings (m + 1) C
          (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E) T := by
  obtain ⟨Y, T, hSa, hSK, _hSI, hSM, hSreg, hTE, hAdmT, _havoid, hTstage⟩ :=
    exists_tower_smooth_singular_stage_centres hWa hK hI hpure hE
  let M : MarkedIdeal (m + 1) X := ⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩
  let S0 := strictTransform (m + 1) T.proj W
  let ET := (geoTransformAlong M T).E
  let F := (W \ regularLocus (n := m + 1) W m) ∪ (W ∩ ⋃ H ∈ E, H)
  have hJoint := subset_closure_diff_boundary_union_singular hpure
    (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE.1) hEDense
  have hsupp := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.biUnion_subset hAdmT hE.1
  have hS0Dense : S0 ⊆ closure (S0 \ ⋃ H ∈ ET, H) :=
    (HironakaAdmissibleCalculus.strictTransform_subset_closure_diff T.contMDiff_proj hWa.isClosed hJoint).trans
      (closure_mono (fun _ hy => ⟨hy.1, fun h => hy.2 (hsupp h)⟩))
  obtain ⟨Z, R, hRtest, hAdmR, hRE, hRSM, hRreg, hRNC, hRTr, hRstage⟩ :=
    HironakaSmoothStageCenters.exists_tower_embeddedResolution_smooth_boundary_stage_centres
      hSa hSM hSK (Nat.lt_succ_self m) hSreg hTE hS0Dense
  have hstrict := StrictTransformComposition.strictTransform_comp T.contMDiff_proj R.contMDiff_proj W
  rw [← BlowupTower.proj_append] at hstrict
  have hfinalE : (geoTransformAlong M (T.append R)).E =
      (geoTransformAlong (⟨univ, ET, vanishingIdeal (n := m + 1) S0, 1⟩ : MarkedIdeal (m + 1) Y) R).E := by
    rw [geoTransformAlong_append]
    exact boundary_geoTransformAlong_eq_of_boundary_eq (geoTransformAlong M T)
      (⟨univ, ET, vanishingIdeal (n := m + 1) S0, 1⟩ : MarkedIdeal (m + 1) Y) rfl R
  have hAdmTF := hAdmT.mono (show W \ regularLocus (n := m + 1) W m ⊆ F from subset_union_left)
  have hTailF : S0 ∩ (⋃ H ∈ ET, H) ⊆ T.proj ⁻¹' F := by
    rintro y ⟨hyS, hyE⟩
    have hyW := HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous hWa.isClosed hyS
    rcases hsupp hyE with hyB | hySing
    · exact Or.inr ⟨hyW, hyB⟩
    · exact Or.inl hySing
  have hAdmF := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.comp hAdmTF (hAdmR.mono hTailF)
  have hFinalAdm : HironakaAdmissibleSequence.IsAdmissibleBlowupSequence (m + 1) X E F Z
      (T.append R).proj (geoTransformAlong M (T.append R)).E := by
    rw [BlowupTower.proj_append, hfinalE]
    exact hAdmF
  have hRcombined : StageCentres (fun P C =>
      (IsClosedSubmanifold (m + 1) (strictTransform (m + 1) P.proj S0) ∧
        C ⊆ strictTransform (m + 1) P.proj S0 ∩ ⋃ H ∈
          (geoTransformAlong (⟨univ, ET, vanishingIdeal (n := m + 1) S0, 1⟩ : MarkedIdeal (m + 1) Y) P).E, H) ∧
      NormalCrossings.HasNormalCrossings (m + 1) C
        (geoTransformAlong (⟨univ, ET, vanishingIdeal (n := m + 1) S0, 1⟩ : MarkedIdeal (m + 1) Y) P).E) R :=
    stageCentres_pair_imp (fun _ _ hP hQ => ⟨hP, hQ⟩) R hRstage
      (stageCentres_normalCrossings_of_isGeoTestTower _ R hRtest)
  have hTSing := stageCentres_all_nonregular_of_stageCentres_singular hWa.isClosed hpure T
    (stageCentres_imp (fun _ _ h => h.1) T hTstage)
  have hTNC := stageCentres_imp (fun _ _ h => h.2) T hTstage
  have hTstrong : StageCentres (fun P C =>
      C ⊆ {x | x ∈ strictTransform (m + 1) P.proj W ∧
        ∀ k, ¬ RegularAtDim (n := m + 1) (strictTransform (m + 1) P.proj W) x k} ∧
      NormalCrossings.HasNormalCrossings (m + 1) C (geoTransformAlong M P).E) T :=
    stageCentres_pair_imp (fun _ _ hP hQ => ⟨hP, hQ⟩) T hTSing hTNC
  refine ⟨Z, T.append R, hFinalAdm, ?_, ?_, ?_, ?_, ?_,
    HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hFinalAdm, ?_⟩
  · rwa [hfinalE]
  · rwa [hstrict]
  · rwa [hstrict]
  · rwa [hstrict, hfinalE]
  · rwa [hstrict, hfinalE]
  · exact stageCentres_embedded_position_append W E T R hTstrong hRcombined


/-- Natural compact irreducible hypersurface embedded resolution: the original
invertible ideal and regular density are constructed from actual geometry. -/
theorem exists_tower_embedded_irreducible_hypersurface_stage_centres {m : ℕ} {X : CMfd.{u} (m + 1)}
    (V : ClosedIrreducibleAnalyticSubvariety (m + 1) X) (hdim : V.dim = m)
    (hK : IsCompact V.carrier) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor (m + 1) E)
    (hEDense : V.carrier ⊆ closure (V.carrier \ ⋃ H ∈ E, H)) :
    ∃ (Y : CMfd.{u} (m + 1)) (T : BlowupTower X Y),
      HironakaAdmissibleSequence.IsAdmissibleBlowupSequence (m + 1) X E
        ((V.carrier \ regularLocus (n := m + 1) V.carrier m) ∪ (V.carrier ∩ ⋃ H ∈ E, H)) Y T.proj
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) V.carrier, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      NormalCrossings.IsSNCDivisor (m + 1)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) V.carrier, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      IsClosedSubmanifold (m + 1) (strictTransform (m + 1) T.proj V.carrier) ∧
      (∀ y ∈ strictTransform (m + 1) T.proj V.carrier,
        RegularAtDim (n := m + 1) (strictTransform (m + 1) T.proj V.carrier) y m) ∧
      NormalCrossings.HasNormalCrossings (m + 1) (strictTransform (m + 1) T.proj V.carrier)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) V.carrier, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      NormalCrossings.IsTransverse (m + 1) (strictTransform (m + 1) T.proj V.carrier)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) V.carrier, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      IsIsomorphismOver (m + 1) T.proj
        ((V.carrier \ regularLocus (n := m + 1) V.carrier m) ∪ (V.carrier ∩ ⋃ H ∈ E, H))ᶜ ∧
      StageCentres (fun P C =>
        (C ⊆ {x | x ∈ strictTransform (m + 1) P.proj V.carrier ∧
          ∀ k, ¬ RegularAtDim (n := m + 1) (strictTransform (m + 1) P.proj V.carrier) x k} ∨
        (IsClosedSubmanifold (m + 1) (strictTransform (m + 1) P.proj V.carrier) ∧
          C ⊆ strictTransform (m + 1) P.proj V.carrier ∩ ⋃ H ∈
            (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) V.carrier, 1⟩ : MarkedIdeal (m + 1) X) P).E, H)) ∧
        NormalCrossings.HasNormalCrossings (m + 1) C
          (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) V.carrier, 1⟩ : MarkedIdeal (m + 1) X) P).E) T := by
  have hpure := HironakaEmbeddedReducible.subset_closure_regularLocus V
  rw [hdim] at hpure
  have hI := HironakaPureCodimensionOneInvertibleIdeal.isInvertible_vanishingIdeal_of_pure V.analytic hpure
  exact exists_tower_embedded_hypersurface_stage_centres V.analytic hK hI hpure hE hEDense


/-- The natural pure compact hypersurface embedded-resolution producer.
The complete original invertible ideal is constructed internally from actual
locally finite components, including reducible original hypersurfaces. -/
theorem exists_tower_embedded_pure_hypersurface_stage_centres {m : ℕ} {X : CMfd.{u} (m + 1)} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W) (hK : IsCompact W)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m)) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor (m + 1) E)
    (hEDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) :
    ∃ (Y : CMfd.{u} (m + 1)) (T : BlowupTower X Y),
      HironakaAdmissibleSequence.IsAdmissibleBlowupSequence (m + 1) X E
        ((W \ regularLocus (n := m + 1) W m) ∪ (W ∩ ⋃ H ∈ E, H)) Y T.proj
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      NormalCrossings.IsSNCDivisor (m + 1)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      IsClosedSubmanifold (m + 1) (strictTransform (m + 1) T.proj W) ∧
      (∀ y ∈ strictTransform (m + 1) T.proj W,
        RegularAtDim (n := m + 1) (strictTransform (m + 1) T.proj W) y m) ∧
      NormalCrossings.HasNormalCrossings (m + 1) (strictTransform (m + 1) T.proj W)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      NormalCrossings.IsTransverse (m + 1) (strictTransform (m + 1) T.proj W)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T).E ∧
      IsIsomorphismOver (m + 1) T.proj
        ((W \ regularLocus (n := m + 1) W m) ∪ (W ∩ ⋃ H ∈ E, H))ᶜ ∧
      StageCentres (fun P C =>
        (C ⊆ {x | x ∈ strictTransform (m + 1) P.proj W ∧
          ∀ k, ¬ RegularAtDim (n := m + 1) (strictTransform (m + 1) P.proj W) x k} ∨
        (IsClosedSubmanifold (m + 1) (strictTransform (m + 1) P.proj W) ∧
          C ⊆ strictTransform (m + 1) P.proj W ∩ ⋃ H ∈
            (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E, H)) ∧
        NormalCrossings.HasNormalCrossings (m + 1) C
          (geoTransformAlong (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) P).E) T := by
  have hI := HironakaPureCodimensionOneInvertibleIdeal.isInvertible_vanishingIdeal_of_pure hWa hpure
  exact exists_tower_embedded_hypersurface_stage_centres hWa hK hI hpure hE hEDense

end
end Hironaka.HironakaHypersurfaceMultiplicityDescent
