/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaCurrentStrictTransformIdeal
import Hironaka.MarkedIdeal.CoherentOrderUpperSemicontinuity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Actual fresh maximal-multiplicity centres

Blueprint `hironaka-hypersurface-stage-centres-extension.tex`.
The present reduced ideal has order one at a regular point. Its genuine
compact maximum multiplicity and the actual canonical marked centre are
produced internally. The centre has constant maximum multiplicity, lies
in the present singular locus, and has normal crossings with the actual
boundary. The hypersurface weak-transform equality and finite restarted
descent remain to be proved; no current-stage certificate is assumed.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaHypersurfaceStageCenters

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
open BlowupFlatCoordinates ResolutionInvariantSpec ResolutionDriver
open RelativePrincipalizationSpan BlowupStrictSubmanifold IdealWeightPowers

noncomputable section

variable {n : ℕ}

/-- The actual reduced ideal of any positive-codimension regular germ has order one. -/
theorem order_vanishingIdeal_eq_one_of_regularAtDim {X : CMfd.{u} n} {W : Set X}
    {x : X} {d : ℕ} (hd : d < n) (hx : RegularAtDim (n := n) W x d) :
    order n univ (vanishingIdeal (n := n) W) x = 1 := by
  obtain ⟨_, hxW, Φ, _, _, hflat⟩ := hx
  let t : Fin n := ⟨d, hd⟩
  have hcoord := flatCoord_mem_vanishingIdeal Φ hflat (i := t) le_rfl (mem_flatDomain_self Φ)
  have hnot := MonomialCase.flatCoord_notMem_idealPow_two Φ t (mem_flatDomain_self Φ)
  apply le_antisymm
  · refine iSup₂_le fun q hq => ?_
    have hq1 : q ≤ 1 := by
      by_contra hq1
      apply hnot
      exact OrderTaylor.mem_idealPow_of_vanishesToOrderOn_univ
        ((hq (flatCoord Φ t) hcoord).mono (by omega))
    exact_mod_cast hq1
  · apply (le_order_iff (𝔞 := vanishingIdeal (n := n) W) (fun _ hg => hg.1)).mpr
    exact fun g hg => (vanishesToOrderOn_one_iff (mem_univ x) hg.1).mpr (hg.2.self_of_nhds hxW)

/-- High reduced multiplicity is contained in the genuine present singular locus. -/
theorem cosupport_high_mark_subset_diff_regularLocus {X : CMfd.{u} n} {W : Set X}
    (hW : IsClosed W) {d μ : ℕ} (hd : d < n) (hμ : 2 ≤ μ) :
    cosupport n univ (vanishingIdeal (n := n) W) μ ⊆ W \ regularLocus (n := n) W d := by
  intro x hx
  have hxW : x ∈ W := by
    have hx1 := cosupport_anti (by omega : 1 ≤ μ) hx
    simpa [SmoothCentreLocus.cosupport_vanishingIdeal_one hW] using hx1
  refine ⟨hxW, fun hxreg => ?_⟩
  have horder := (le_order_iff (𝔞 := vanishingIdeal (n := n) W) (fun _ hg => hg.1)).mpr hx.2
  rw [order_vanishingIdeal_eq_one_of_regularAtDim hd hxreg] at horder
  have : μ ≤ 1 := by exact_mod_cast horder
  omega

/-- Produce the actual finite maximum reduced multiplicity, a nonempty canonical
centre in the present singular locus with NC boundary, and constant multiplicity
on that centre. No chosen multiplicity bound or centre data is supplied. -/
theorem exists_fresh_maximal_order_centre {X : CMfd.{u} n} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor n E)
    (hhigh : ∃ x ∈ W, (2 : ℕ∞) ≤ order n univ (vanishingIdeal (n := n) W) x) :
    ∃ (μ : ℕ) (C : Set X), 2 ≤ μ ∧ C.Nonempty ∧
      (⟨univ, E, vanishingIdeal (n := n) W, μ⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      C ⊆ W \ regularLocus (n := n) W d ∧
      (∀ x ∈ W, order n univ (vanishingIdeal (n := n) W) x ≤ (μ : ℕ∞)) ∧
      (∀ c ∈ C, order n univ (vanishingIdeal (n := n) W) c = (μ : ℕ∞)) := by
  let a := vanishingIdeal (n := n) W
  have hint := HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure
  have hdom1 : IsInvDomain n (⟨univ, E, a, 1⟩ : MarkedIdeal n X) :=
    HironakaEmbeddedBoundary.isInvDomain_boundary hWa hint hE
  have husc : ResolutionInvariantOrder.IsInvUSCOn (order n univ a) W := fun x _ =>
    (OrderInvariance.eventually_order_le hdom1.isWellFormed.isCoherent x).mono fun _ hy _ => hy
  obtain ⟨x₀, hx₀, hmax⟩ := husc.exists_isMaxOn hK (by obtain ⟨x, hx, _⟩ := hhigh; exact ⟨x, hx⟩)
  have hdom0 : IsInvDomain n (⟨univ, [], a, 1⟩ : MarkedIdeal n X) :=
    HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_pure le_rfl hWa hd hpure
  let O : Opens X := ⟨univ, isOpen_univ⟩
  have hfinite := HironakaCurrentStrictTransformIdeal.fresh_order_le_nmOrd_geoTransformAlong
    (by omega : 0 < n) hWa.isClosed hdom0 O
    (by simpa [O] using (subset_closure : W ⊆ closure W))
    (fun H hH => by cases hH) (.refl : BlowupTower X X) trivial trivial x₀
  have hST : strictTransform n (id : X → X) W = W := by
    simp [strictTransform, exceptionalLocus_id, hWa.isClosed.closure_eq]
  simp only [BlowupTower.proj_refl, hST, geoTransformAlong_refl] at hfinite
  have hnotTop : order n univ a x₀ ≠ ⊤ := ne_top_of_le_ne_top (by simp) hfinite
  obtain ⟨μ, hμeq⟩ := ENat.ne_top_iff_exists.mp hnotTop
  have hμ : 2 ≤ μ := by
    obtain ⟨x, hx, hhigh⟩ := hhigh
    have hbound := hhigh.trans (hmax x hx)
    rw [← hμeq] at hbound
    exact_mod_cast hbound
  let m : MarkedIdeal n X := ⟨univ, E, a, μ⟩
  have hdom : IsInvDomain n m :=
    ⟨⟨hdom1.isWellFormed.isClosedSubmanifold_N, hdom1.isWellFormed.isCoherent,
        hdom1.isWellFormed.isSNCDivisor, hdom1.isWellFormed.isTransverse⟩,
      hdom1.dimLE, by change 1 ≤ μ; omega, hdom1.isNonzeroAlongAt⟩
  have hcosW : m.cosupp ⊆ W := fun x hx =>
    (cosupport_high_mark_subset_diff_regularLocus hWa.isClosed hd hμ hx).1
  have hcosne : m.cosupp.Nonempty := ⟨x₀, mem_univ x₀,
    (le_order_iff (𝔞 := a) (fun _ hg => hg.1)).mp (by rw [← hμeq])⟩
  have hcosK : IsCompact m.cosupp := hK.of_isClosed_subset
    (OrderTaylor.isClosed_cosupport hdom.isWellFormed.isCoherent μ) hcosW
  let R := CanonicalCentres.canonicalInvariant.{u} n
  have hRusc := R.isInvValue.usc m hdom (.refl : BlowupTower X X) trivial
  rw [geoTransformAlong_refl] at hRusc
  obtain ⟨c, hc, hcmax⟩ := hRusc.exists_isMaxOn hcosK hcosne
  let C := maxLocus (R.inv m (.refl : BlowupTower X X)) m.cosupp
  have hadm := (HironakaFromSeqInvariant.embeddingFields_of_seq R).isAdmissibleCentre_maxLocus
    hdom (.refl : BlowupTower X X) trivial trivial
  rw [geoTransformAlong_refl] at hadm
  refine ⟨μ, C, hμ, ⟨c, hc, hcmax⟩, hadm,
    fun z hz => cosupport_high_mark_subset_diff_regularLocus hWa.isClosed hd hμ hz.1,
    fun z hz => by rw [hμeq]; exact hmax z hz, fun z hz => ?_⟩
  apply le_antisymm
  · rw [hμeq]
    exact hmax z (hcosW hz.1)
  · exact (le_order_iff (𝔞 := a) (fun _ hg => hg.1)).mpr hz.1.2

/-- The internally produced maximum-multiplicity centre yields an actual
blowup with coherent controlled ideal and no remaining exceptional factor.
Its actual next strict transform is analytic and compact; the accumulated
boundary is SNC. Reducedness of the whole controlled ideal is not assumed. -/
theorem exists_fresh_maximal_order_blowup {X : CMfd.{u} n} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor n E)
    (hhigh : ∃ x ∈ W, (2 : ℕ∞) ≤ order n univ (vanishingIdeal (n := n) W) x) :
    ∃ (μ : ℕ) (C : Set X) (Y : CMfd.{u} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
      2 ≤ μ ∧ C.Nonempty ∧
      (⟨univ, E, vanishingIdeal (n := n) W, μ⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      C ⊆ W \ regularLocus (n := n) W d ∧
      (∀ c ∈ C, order n univ (vanishingIdeal (n := n) W) c = (μ : ℕ∞)) ∧
      (BlowupControlledTransform.controlledTransform hπ (vanishingIdeal (n := n) W) μ).IsCoherent ∧
      GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) W) =
        (idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal μ).mul
          (BlowupControlledTransform.controlledTransform hπ (vanishingIdeal (n := n) W) μ) ∧
      (∀ z ∈ π ⁻¹' C, ∃ g,
        (BlowupControlledTransform.controlledTransform hπ (vanishingIdeal (n := n) W) μ).mem z g ∧
          ¬ (vanishingIdeal (n := n) (π ⁻¹' C)).mem z g) ∧
      IsComplexAnalyticSubset (n := n) (strictTransform n π W) ∧
      IsCompact (strictTransform n π W) ∧
      NormalCrossings.IsSNCDivisor n (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  obtain ⟨μ, C, hμ, hCne, hCadm, hCS, _, hCorder⟩ :=
    exists_fresh_maximal_order_centre hWa hK hd hpure hE hhigh
  have hCint : interior C = ∅ := eq_empty_of_subset_empty ((interior_mono
    (hCS.trans sdiff_subset)).trans (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure).subset)
  obtain ⟨Y, π, hπ⟩ := ResolutionDriver.exists_blowup C hCadm.1 hCint
  let m : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, μ⟩
  have hcoh := CartanIrreducible.cartanCoherence W hWa
  have hle := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hcoh hCadm.1 hCadm.2.1
  have hwf : m.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, hcoh, hE,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  refine ⟨μ, C, Y, π, hπ, hμ, hCne, hCadm, hCS, hCorder,
    BlowupControlledTransform.isCoherent_controlledTransform hπ hcoh hle,
    BlowupControlledTransform.pullback_eq_mul_controlledTransform hπ hcoh hle, ?_,
    HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hWa,
    HironakaAdmissibleCalculus.isCompact_strictTransform (IsBlowupSequence.step id C π .refl hπ) hK, ?_⟩
  · intro z hz
    have hzN : z ∈ geoStrictTransform π C m.N := by rw [geoStrictTransform_univ hπ]; exact mem_univ z
    have hnot : π z ∉ cosupport n m.N m.ideal (m.d + 1) := by
      intro h
      have hb := (le_order_iff (𝔞 := m.ideal) (fun _ hg => hg.1)).mpr h.2
      rw [hCorder (π z) hz] at hb
      have : μ + 1 ≤ μ := by exact_mod_cast hb
      omega
    obtain ⟨g, hg, hng⟩ := ExceptionalPushforwardAlong.exists_not_isInSpanOnAt_exceptionalDivisor
      hπ hwf.isClosedSubmanifold_N hcoh hCadm.2.1 hz hzN hnot
    refine ⟨g, ?_, fun hgE => hng ?_⟩
    · rwa [geoTransform_ideal_eq_controlledTransform (𝔪 := m) rfl hcoh hπ] at hg
    · exact RelativePrincipalizationSpan.IsInSpanAt.restrict
        (InvertibleIdealQuotient.isInSpanAt_self
          (NonmonomialTransformTower.exceptionalDivisor_mem_of_vanishingIdeal_mem hπ hE hCadm.2.2 hz hgE) hgE.1)
  · exact (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwf hCadm hπ).isSNCDivisor

end

end Hironaka.HironakaHypersurfaceStageCenters
