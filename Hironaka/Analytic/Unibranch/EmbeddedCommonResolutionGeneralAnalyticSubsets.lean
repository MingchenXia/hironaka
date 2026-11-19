import Hironaka.Analytic.Unibranch.Resolution

/-!
# Intrinsic analytic subsets of the original embedded reduced complex space

The literal image in the original ambient manifold is proved analytic from
original intrinsic local traces. In particular, its closedness is a conclusion,
not an input. No alternate complex-space definition is introduced.

Blueprint: `embedded-common-resolution-general.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.SourceReducedComplexSpace

noncomputable section

open Hironaka Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex

/-- In ANY original local embedding, the ambient image of an intrinsic analytic
subset is analytic, including empty germs outside the closed carrier. -/
theorem IsAnalyticSubset.analytic_image_localEmbedding {X : SourceReducedComplexSpace}
    {A : Set X.obj.left} (hA : X.IsAnalyticSubset A) (e : LocalEmbedding X) :
    IsComplexAnalyticSubset (n := e.dim)
      (Subtype.val '' (e.toPoint ⁻¹' A) : Set e.ambient) := by
  apply AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro u
  by_cases hu : u ∈ e.carrier
  · obtain ⟨O, huO, A', hA', hiff⟩ := hA.exists_local_trace e ⟨u, hu⟩
    refine ⟨O, huO, ?_⟩
    have hCO : IsComplexAnalyticSubset (n := e.dim)
        ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) :=
      AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O
    have heq : (Subtype.val : O → e.ambient) ⁻¹'
        (Subtype.val '' (e.toPoint ⁻¹' A)) = A' ∩
          ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) := by
      ext o
      constructor
      · rintro ⟨a, ha, hao⟩
        have hoC : o.val ∈ e.carrier := hao ▸ a.property
        refine ⟨(hiff ⟨o.val, hoC⟩ o.property).mp ?_, hoC⟩
        have hca : (⟨o.val, hoC⟩ : e.carrier) = a := Subtype.ext hao.symm
        rwa [hca]
      · rintro ⟨ho, hoC⟩
        exact ⟨⟨o.val, hoC⟩, (hiff ⟨o.val, hoC⟩ o.property).mpr ho, rfl⟩
    rw [heq]
    exact hA'.inter hCO
  · let O : Opens e.ambient := ⟨e.carrierᶜ, e.analytic.isClosed.isOpen_compl⟩
    refine ⟨O, hu, ?_⟩
    have heq : (Subtype.val : O → e.ambient) ⁻¹'
        (Subtype.val '' (e.toPoint ⁻¹' A)) = ∅ := by
      ext o
      simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
      intro a _ hao
      exact o.property (hao ▸ a.property)
    rw [heq]
    exact isComplexAnalyticSubset_empty

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {D : Set M} {hD : IsComplexAnalyticSubset (n := n) D}

/-- The image of an ORIGINAL intrinsic analytic subset of the reduced closed
subspace is analytic in the ORIGINAL ambient manifold. -/
theorem isComplexAnalyticSubset_image_of_isAnalyticSubset_closedAnalytic
    {A : Set D} (hA : (ofClosedAnalytic D hD).IsAnalyticSubset A) :
    IsComplexAnalyticSubset (n := n) (Subtype.val '' A : Set M) := by
  apply AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro x
  let e := LocalEmbedding.ofChart D hD x
  let d := chartDiffeo (n := n) x
  have hchart := hA.analytic_image_localEmbedding e
  have hp := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage d.contMDiff hchart
  refine ⟨chartDomain (n := n) x, mem_chartDomain (n := n) x, ?_⟩
  have heq : (Subtype.val : chartDomain (n := n) x → M) ⁻¹' (Subtype.val '' A) =
      d ⁻¹' (Subtype.val '' (e.toPoint ⁻¹' A)) := by
    ext p
    constructor
    · rintro ⟨a, ha, hap⟩
      have hpD : p.val ∈ D := hap ▸ a.property
      let c : e.carrier := ⟨d p, by
        change (d.symm (d p)).val ∈ D
        rw [d.symm_apply_apply]
        exact hpD⟩
      refine ⟨c, ?_, rfl⟩
      have hca : e.toPoint c = a := by
        apply Subtype.ext
        change (d.symm (d p)).val = a.val
        rw [d.symm_apply_apply]
        exact hap.symm
      change e.toPoint c ∈ A
      rwa [hca]
    · rintro ⟨c, hc, hcp⟩
      refine ⟨e.toPoint c, hc, ?_⟩
      change (d.symm c.val).val = p.val
      rw [hcp, d.symm_apply_apply]
  rw [heq]
  exact hp

/-- The intrinsic/ambient analytic-subset dictionary on the SAME original
closed subspace; ambient closedness follows from this analytic conclusion. -/
theorem isAnalyticSubset_closedAnalytic_iff (A : Set D) :
    (ofClosedAnalytic D hD).IsAnalyticSubset A ↔
      IsComplexAnalyticSubset (n := n) (Subtype.val '' A : Set M) := by
  refine ⟨isComplexAnalyticSubset_image_of_isAnalyticSubset_closedAnalytic, fun h => ?_⟩
  have hi := isAnalyticSubset_preimage_val hD h
  rwa [Subtype.val_injective.preimage_image] at hi

end

end Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
