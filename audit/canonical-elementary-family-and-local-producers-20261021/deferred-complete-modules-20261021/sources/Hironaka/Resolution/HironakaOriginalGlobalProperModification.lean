/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalGlobalOffZero
import Hironaka.Resolution.HironakaOriginalTerminalProperProjection
import Hironaka.MarkedIdeal.CodimOneSupport

/-! Actual intrinsic proper holomorphic modification geometry for the same
original global principalization. The true closed analytic thin loci and whole
inverse section are constructed internally; no broad energy interface or global
scheduled blowup history is assumed. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalGlobalProperModification
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalGlobalPrincipalization HironakaOriginalGlobalOffZero
  HironakaOriginalTerminalProperProjection
open ResolutionInvariantSpec (IsInvDomain)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual global divisor's genuine nonzero local generators prove its
support nowhere dense, without any caller density certificate. -/
theorem originalTerminalPrincipalizationDivisor_interior_support_eq_empty
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) :
    interior (originalTerminalPrincipalizationDivisor M hM hN hd).support = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  let D := originalTerminalPrincipalizationDivisor M hM hN hd
  obtain ⟨U, hU, hyU, g, hg, hnon, hgen⟩ := D.isInvertible y
  obtain ⟨z, hz, hgz⟩ := hnon (interior D.support ∩ U)
    (isOpen_interior.inter hU) inter_subset_right ⟨y, hy, hyU⟩
  have hgh : HolomorphicAt n g z :=
    eventually_of_mem (hU.mem_nhds hz.2) fun w hw =>
      (hg w hw).mdifferentiableAt (hU.mem_nhds hw)
  have hmem := (hgen z hz.2 g).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hgh)
  exact hgz (interior_subset hz.1 g hmem)

/-- Original coherence, same-P holomorphicity, actual divisor support and genuine
surjectivity construct BOTH actual closed thin analytic loci. -/
theorem originalTerminalPrincipalization_analytic_loci
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) :
    let D := originalTerminalPrincipalizationDivisor M hM hN hd
    IsClosed D.support ∧ IsComplexAnalyticSubset (n := n) D.support ∧ interior D.support = ∅ ∧
      IsClosed M.ideal.zeroLocus ∧ IsComplexAnalyticSubset (n := n) M.ideal.zeroLocus ∧
      interior M.ideal.zeroLocus = ∅ ∧
      (originalTerminalGluedProjection M hM : originalTerminalManifold M hM → X) ⁻¹'
        M.ideal.zeroLocus = D.support := by
  dsimp only
  let D := originalTerminalPrincipalizationDivisor M hM hN hd
  have hB := CodimOneSupport.isComplexAnalyticSubset_zeroLocus hM.isWellFormed.isCoherent
  have hsupport := originalTerminalPrincipalizationDivisor_support M hM hN hd
  have hA : IsComplexAnalyticSubset (n := n) D.support := by
    rw [hsupport]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (originalTerminalGluedProjection_contMDiff M hM) hB
  have hAi := originalTerminalPrincipalizationDivisor_interior_support_eq_empty M hM hN hd
  refine ⟨hA.isClosed, hA, hAi, hB.isClosed, hB, ?_, hsupport.symm⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y, hy⟩ := originalTerminalGluedProjection_surjective M hM x
  have hyopen : y ∈ (originalTerminalGluedProjection M hM) ⁻¹' interior M.ideal.zeroLocus := by
    change originalTerminalGluedProjection M hM y ∈ interior M.ideal.zeroLocus
    rw [hy]
    exact hx
  have hsub : (originalTerminalGluedProjection M hM) ⁻¹' interior M.ideal.zeroLocus ⊆ D.support := by
    rw [hsupport]
    exact preimage_mono interior_subset
  have hDy : y ∈ interior D.support :=
    mem_interior_iff_mem_nhds.mpr (mem_of_superset
      ((isOpen_interior.preimage (originalTerminalGluedProjection M hM).continuous).mem_nhds hyopen) hsub)
  rw [hAi] at hDy
  exact hDy

/-- The genuine complement inverse and independent whole surjectivity construct
a whole section with both actual inverse equations off the true original loci. -/
theorem exists_originalTerminalWholeInverseSection
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) :
    ∃ s : X → originalTerminalManifold M hM,
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s M.ideal.zeroLocusᶜ ∧
        (∀ x ∉ M.ideal.zeroLocus, originalTerminalGluedProjection M hM (s x) = x) ∧
        ∀ y ∉ (originalTerminalPrincipalizationDivisor M hM hN hd).support,
          s (originalTerminalGluedProjection M hM y) = y := by
  classical
  let e := originalTerminalOffZeroBiholomorphism M hM hN hd
  let s₀ : originalTerminalOffZeroBaseOpen M hM → originalTerminalManifold M hM :=
    fun x => (e.symm x).val
  have hs₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₀ :=
    contMDiff_subtype_val.comp e.symm.contMDiff
  let a : X → originalTerminalManifold M hM :=
    fun x => Classical.choose (originalTerminalGluedProjection_surjective M hM x)
  let s : X → originalTerminalManifold M hM :=
    fun x => if hx : x ∈ M.ideal.zeroLocusᶜ then s₀ ⟨x, hx⟩ else a x
  have hrestrict : (fun x : originalTerminalOffZeroBaseOpen M hM => s x.val) = s₀ := by
    funext x
    change (if hx : x.val ∈ M.ideal.zeroLocusᶜ then s₀ ⟨x.val, hx⟩ else a x.val) = s₀ x
    exact dif_pos x.property
  have hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s M.ideal.zeroLocusᶜ := by
    have hsd : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (fun x : originalTerminalOffZeroBaseOpen M hM => s x.val) := hrestrict ▸ hs₀
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hsd ⟨x, hx⟩)).contMDiffWithinAt
  refine ⟨s, hs, ?_, ?_⟩
  · intro x hx
    rw [show s x = s₀ ⟨x, hx⟩ from dif_pos hx]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  · intro y hy
    have hyB : originalTerminalGluedProjection M hM y ∈ M.ideal.zeroLocusᶜ := by
      change y ∉ (originalTerminalGluedProjection M hM) ⁻¹' M.ideal.zeroLocus
      rw [← originalTerminalPrincipalizationDivisor_support M hM hN hd]
      exact hy
    rw [show s (originalTerminalGluedProjection M hM y) =
      s₀ ⟨originalTerminalGluedProjection M hM y, hyB⟩ from dif_pos hyB]
    let q : originalTerminalOffZeroSourceOpen M hM := ⟨y, hyB⟩
    have hq : e q = ⟨originalTerminalGluedProjection M hM y, hyB⟩ := rfl
    change (e.symm ⟨originalTerminalGluedProjection M hM y, hyB⟩).val = y
    rw [← hq, e.symm_apply_apply]

/-- Expanded intrinsic proper-modification geometry, with the actual original
zero locus and actual global divisor support as the proved analytic witnesses.
No broad legacy interface or globally scheduled history is imported or assumed. -/
theorem originalTerminalGlobalProperModification_geometry
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) :
    let P := (originalTerminalGluedProjection M hM : originalTerminalManifold M hM → X)
    let D := originalTerminalPrincipalizationDivisor M hM hN hd
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P ∧ IsProperMap P ∧
      (IsClosed D.support ∧ IsComplexAnalyticSubset (n := n) D.support ∧ interior D.support = ∅ ∧
        IsClosed M.ideal.zeroLocus ∧ IsComplexAnalyticSubset (n := n) M.ideal.zeroLocus ∧
        interior M.ideal.zeroLocus = ∅ ∧ P ⁻¹' M.ideal.zeroLocus = D.support) ∧
      ∃ s : X → originalTerminalManifold M hM,
        ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s M.ideal.zeroLocusᶜ ∧
          (∀ x ∉ M.ideal.zeroLocus, P (s x) = x) ∧ ∀ y ∉ D.support, s (P y) = y :=
  ⟨originalTerminalGluedProjection_contMDiff M hM,
    originalTerminalGluedProjection_isProperMap M hM,
    originalTerminalPrincipalization_analytic_loci M hM hN hd,
    exists_originalTerminalWholeInverseSection M hM hN hd⟩

end
end Hironaka.HironakaOriginalGlobalProperModification
