import Hironaka.Analytic.AdmissibleBlowupHolomorphicInverse
import Hironaka.Analytic.AnalyticModificationLocalDiscrepancy
import Hironaka.Resolution.HironakaAdmissibleCalculus
import Hironaka.MarkedIdeal.CodimOneSupport

set_option autoImplicit false

/-! # Genuine standard analytic modification data from actual principalization geometry -/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.AdmissiblePrincipalizationAnalyticModification

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaAdmissibleSequence

noncomputable section

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

omit [IsComplexManifold n Y] in
private theorem interior_support_eq_empty (D : EffectiveDivisor n Y) :
    interior D.support = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨U, hU, hyU, g, hg, hnon, hgen⟩ := D.isInvertible y
  obtain ⟨z, hz, hgz⟩ := hnon (interior D.support ∩ U)
    (isOpen_interior.inter hU) inter_subset_right ⟨y, hy, hyU⟩
  have hgh : HolomorphicAt n g z :=
    eventually_of_mem (hU.mem_nhds hz.2) fun w hw =>
      (hg w hw).mdifferentiableAt (hU.mem_nhds hw)
  have hmem := (hgen z hz.2 g).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hgh)
  exact hgz (interior_subset hz.1 g hmem)

/-- The actual sequence, coherence and effective support identity produce
all standard proper holomorphic modification data internally. -/
theorem isAnalyticModification_of_support_preimage
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    {E₀ : List (Set X)} {E : List (Set Y)} {π : Y → X}
    (hπ : IsAdmissibleBlowupSequence n X E₀ 𝔞.zeroLocus Y π E)
    (D : EffectiveDivisor n Y) (hsupport : D.support = π ⁻¹' 𝔞.zeroLocus) :
    AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π := by
  classical
  have hhol := hπ.isBlowupSequence.contMDiff
  have hproper := HironakaAdmissibleCalculus.isProperMap_of_isBlowupSequence
    hπ.isBlowupSequence
  have hsurj := HironakaLocalPrincipalization.IsBlowupSequence.surjective
    hπ.isBlowupSequence
  have hBanalytic := CodimOneSupport.isComplexAnalyticSubset_zeroLocus h𝔞
  have hBclosed := hBanalytic.isClosed
  have hDint := interior_support_eq_empty D
  have hBint : interior 𝔞.zeroLocus = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨y, hy⟩ := hsurj x
    have hyopen : y ∈ π ⁻¹' interior 𝔞.zeroLocus := by simpa only [mem_preimage, hy] using hx
    have hsub : π ⁻¹' interior 𝔞.zeroLocus ⊆ D.support := by
      rw [hsupport]
      exact preimage_mono interior_subset
    have hDy : y ∈ interior D.support :=
      mem_interior_iff_mem_nhds.mpr (mem_of_superset
        ((isOpen_interior.preimage hhol.continuous).mem_nhds hyopen) hsub)
    rw [hDint] at hDy
    exact hDy
  let A := π ⁻¹' 𝔞.zeroLocus
  have hAc : IsClosed A := hBclosed.preimage hhol.continuous
  have hAa : IsComplexAnalyticSubset (n := n) A :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hhol hBanalytic
  have hAi : interior A = ∅ := by
    change interior (π ⁻¹' 𝔞.zeroLocus) = ∅
    rw [← hsupport]
    exact hDint
  obtain ⟨s₀, hs₀, hright, hleft⟩ :=
    AdmissibleBlowupHolomorphicInverse.exists_section_compl hBclosed hπ
  let a : X → Y := fun x => Classical.choose (hsurj x)
  let s : X → Y := fun x => if hx : x ∈ 𝔞.zeroLocusᶜ then s₀ ⟨x, hx⟩ else a x
  have hrestrict : (fun x : (⟨𝔞.zeroLocusᶜ, hBclosed.isOpen_compl⟩ :
      TopologicalSpace.Opens X) => s x) = s₀ := by
    funext x
    change (if hx : x.1 ∈ 𝔞.zeroLocusᶜ then s₀ ⟨x.1, hx⟩ else a x.1) = s₀ x
    have hx : x.1 ∈ 𝔞.zeroLocusᶜ := x.2
    exact dif_pos hx
  have hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      s 𝔞.zeroLocusᶜ := by
    have hsd : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (fun x : (⟨𝔞.zeroLocusᶜ, hBclosed.isOpen_compl⟩ : TopologicalSpace.Opens X) => s x) :=
      hrestrict ▸ hs₀
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hsd ⟨x, hx⟩)).contMDiffWithinAt
  refine ⟨hhol, hproper, A, 𝔞.zeroLocus, s, hAc, hAa, hAi,
    hBclosed, hBanalytic, hBint, rfl, hs, ?_, ?_⟩
  · intro x hx
    rw [show s x = s₀ ⟨x, hx⟩ from dif_pos hx]
    exact congrFun hright ⟨x, hx⟩
  · intro y hy
    have hyB : π y ∈ 𝔞.zeroLocusᶜ := hy
    rw [show s (π y) = s₀ ⟨π y, hyB⟩ from dif_pos hyB]
    exact hleft y hyB

end
end Hironaka.AdmissiblePrincipalizationAnalyticModification
