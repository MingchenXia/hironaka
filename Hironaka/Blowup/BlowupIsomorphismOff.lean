/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.HolomorphicGermAlgebra
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A blowup is an isomorphism off its centre

`isIsomorphismOver_compl_of_isBlowupAlong`: a blowup `π : Z → M` along a closed submanifold `C`
(`IsBlowupAlong`, a universal property) is an isomorphism over `M \ C`: it maps `π⁻¹(M \ C)`
bijectively onto `M \ C` and its differential is bijective there.  In particular
`exceptionalLocus n π ⊆ π⁻¹ C` (`exceptionalLocus_subset_preimage`).

The inclusion of `M \ C` lifts to `s : M \ C → Z` (the ideal of `C` is the unit ideal there),
and on `π⁻¹(M \ C)` both the inclusion and `s ∘ π` lift `π`, so `s ∘ π = id` by uniqueness.
The chain rule for `π ∘ s = id` makes `dπ` surjective, hence bijective.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupIsomorphismOff

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M}

/-- The differential of the inclusion of an open subset is the identity. -/
theorem mfderiv_subtype_val {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsManifold 𝓘(ℂ, ComplexModel n) ∞ X] (O : TopologicalSpace.Opens X) (x : O) :
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (Subtype.val : O → X) x =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
  have hd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (Subtype.val : O → X) x := (contMDiff_subtype_val (n := ∞) x).mdifferentiableAt (by simp)
  rw [hd.mfderiv]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  refine HasFDerivAt.fderiv ((hasFDerivAt_id _).congr_of_eventuallyEq ?_)
  have h1 := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
    (H := ComplexModel n) O (x := x)
  have h2 : ∀ᶠ u in 𝓝 (chartAt (ComplexModel n) x.1 x.1),
      u ∈ (chartAt (ComplexModel n) x.1).target :=
    (chartAt (ComplexModel n) x.1).open_target.mem_nhds
      ((chartAt (ComplexModel n) x.1).map_source (mem_chart_source _ _))
  change _ =ᶠ[𝓝 (chartAt (ComplexModel n) x.1 x.1)] _
  filter_upwards [h1, h2] with u hu1 hu2
  change chartAt (ComplexModel n) x.1 ((chartAt (ComplexModel n) x).symm u).1 = u
  rw [← Function.comp_apply (f := Subtype.val), ← hu1]
  exact (chartAt (ComplexModel n) x.1).right_inv hu2

/-- The inclusion of the complement of the centre lifts to a holomorphic section of the
blowup, which inverts `π` over the complement. -/
theorem exists_section_compl (hπ : IsBlowupAlong n C π) :
    ∃ s : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens M) → Z,
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s ∧ π ∘ s = Subtype.val ∧
      ∀ z (hz : π z ∈ Cᶜ), s ⟨π z, hz⟩ = z := by
  classical
  have hC : IsClosed C := hπ.1.1
  set N : TopologicalSpace.Opens M := ⟨Cᶜ, hC.isOpen_compl⟩
  obtain ⟨s, ⟨hs, hsπ⟩, -⟩ := hπ.2.2.2.2 n N Subtype.val contMDiff_subtype_val
    (isInvertible_pullback_vanishingIdeal_of_disjoint hC fun x => x.2)
  set O : TopologicalSpace.Opens Z := ⟨π ⁻¹' Cᶜ, hC.isOpen_compl.preimage hπ.contMDiff.continuous⟩
  set ρ : O → N := fun x => ⟨π x.1, x.2⟩
  have hρ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ρ := by
    intro x
    rw [contMDiffAt_iff_target]
    refine ⟨(hπ.contMDiff.continuous.comp continuous_subtype_val).subtype_mk _ |>.continuousAt, ?_⟩
    exact ((contMDiffAt_iff_target.mp ((hπ.contMDiff.comp contMDiff_subtype_val) x)).2 : _)
  have huniq := hπ.2.2.2.2 n O (π ∘ Subtype.val) (hπ.contMDiff.comp contMDiff_subtype_val)
    (isInvertible_pullback_vanishingIdeal_of_disjoint hC fun x => x.2)
  have heq : s ∘ ρ = Subtype.val :=
    huniq.unique ⟨hs.comp hρ, by rw [← Function.comp_assoc, hsπ]; rfl⟩
      ⟨contMDiff_subtype_val, rfl⟩
  exact ⟨s, hs, hsπ, fun z hz => congrFun heq ⟨z, hz⟩⟩

/-- **A blowup is an isomorphism off its centre.** -/
theorem isIsomorphismOver_compl_of_isBlowupAlong (hπ : IsBlowupAlong n C π) :
    IsIsomorphismOver n π Cᶜ := by
  obtain ⟨s, hs, hsπ, hsec⟩ := exists_section_compl hπ
  refine ⟨⟨fun z hz => hz, fun z₁ hz₁ z₂ hz₂ h => ?_, fun y hy => ⟨s ⟨y, hy⟩, ?_, ?_⟩⟩, ?_⟩
  · rw [← hsec z₁ hz₁, ← hsec z₂ hz₂]
    congr 1
    exact Subtype.ext h
  · show π (s ⟨y, hy⟩) ∈ Cᶜ
    rw [show π (s ⟨y, hy⟩) = y from congrFun hsπ ⟨y, hy⟩]
    exact hy
  · exact congrFun hsπ ⟨y, hy⟩
  · refine Set.disjoint_left.mpr fun z hz hexc => hexc ?_
    set x : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens M) := ⟨π z, hz⟩
    have hπd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π (s x) :=
      (hπ.contMDiff (s x)).mdifferentiableAt (by simp)
    have hsd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s x :=
      (hs x).mdifferentiableAt (by simp)
    have h1 := mfderiv_comp x hπd hsd
    rw [hsπ, mfderiv_subtype_val, hsec z hz] at h1
    have hsurj : Function.Surjective
        (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z) := fun v =>
      ⟨mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s x v, (DFunLike.congr_fun h1 v).symm⟩
    set L : ComplexModel n →ₗ[ℂ] ComplexModel n :=
      (show ComplexModel n →L[ℂ] ComplexModel n from
        mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z).toLinearMap
    have hinj : Function.Injective L :=
      LinearMap.injective_iff_surjective (V := ComplexModel n) (f := L) |>.mpr hsurj
    exact ⟨hinj, hsurj⟩

/-- The exceptional locus of a blowup lies over the centre. -/
theorem exceptionalLocus_subset_preimage (hπ : IsBlowupAlong n C π) :
    exceptionalLocus n π ⊆ π ⁻¹' C := fun z hz => by
  by_contra h
  exact Set.disjoint_left.mp (isIsomorphismOver_compl_of_isBlowupAlong hπ).2 h hz

end

end Hironaka.BlowupIsomorphismOff
