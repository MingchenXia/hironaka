/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.ExceptionalLocus
import Hironaka.Blowup.BlowupCompact
import Hironaka.Blowup.BlowupIsomorphismOff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Strict transforms along a composition of blowups

Source: CT22, Section 4 (strict transforms under a composition of blowups with smooth centres).

* `map_nhds_eq_of_not_mem_exceptionalLocus`: a holomorphic map between
  manifolds of the same dimension is open at every point where its differential
  is bijective (inverse function theorem in charts).
* `strictTransform_comp`: `(f ∘ g)^{-1}_{strict} A = g^{-1}_{strict}(f^{-1}_{strict} A)`
  when `g` is holomorphic.
* `surjective_of_isBlowupAlong`: a blowup of a compact manifold is surjective,
  because it is an isomorphism over the dense open complement of its centre and
  its image is compact.
* `image_exceptionalLocus_comp`: `(f ∘ g)(Exc (f ∘ g)) = f(g(Exc g)) ∪ f(Exc f)`
  for a surjective `g`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StrictTransformComposition

open Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ}
  {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z]

omit [IsComplexManifold n Y] [IsComplexManifold n Z] in
/-- **Openness off the exceptional locus.**  A holomorphic map of equidimensional
manifolds maps neighbourhoods of a point with bijective differential onto
neighbourhoods of its image. -/
theorem map_nhds_eq_of_not_mem_exceptionalLocus {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {z : Z}
    (hz : z ∉ exceptionalLocus n g) :
    map g (𝓝 z) = 𝓝 (g z) := by
  set I := 𝓘(ℂ, ComplexModel n) with hI
  have hmd : MDifferentiableAt I I g z := (hg z).mdifferentiableAt (by simp)
  set p := extChartAt I z z with hp
  set F := writtenInExtChartAt I I z g with hF
  have hrange : range I = univ := by simp [hI]
  have hderiv : mfderiv I I g z = fderiv ℂ F p := by
    rw [hmd.mfderiv, hrange, fderivWithin_univ]
  have hbij : Function.Bijective (fderiv ℂ F p) := by
    have := hz
    simp only [exceptionalLocus, mem_ofPred_eq, not_not] at this
    rwa [hderiv] at this
  have hcd : ContDiffAt ℂ ∞ F p := by
    have h := (contMDiffAt_iff.mp (hg z)).2
    rw [hrange, contDiffWithinAt_univ] at h
    exact h
  have hstrict : HasStrictFDerivAt F (fderiv ℂ F p) p :=
    hcd.hasStrictFDerivAt (by simp)
  let L : ComplexModel n ≃L[ℂ] ComplexModel n :=
    (LinearEquiv.ofBijective (fderiv ℂ F p).toLinearMap hbij).toContinuousLinearEquiv
  have hstrict' : HasStrictFDerivAt F (L : ComplexModel n →L[ℂ] ComplexModel n) p := by
    convert hstrict using 1
    exact ContinuousLinearMap.ext fun v => rfl
  have hmap : map F (𝓝 p) = 𝓝 (F p) := HasStrictFDerivAt.map_nhds_eq_of_equiv hstrict'
  have hsymm : map (extChartAt I z).symm (𝓝 p) = 𝓝 z := by
    have := map_extChartAt_symm_nhdsWithin_range (I := I) z
    rwa [hrange, nhdsWithin_univ] at this
  have hsymm' : map (extChartAt I (g z)).symm (𝓝 (extChartAt I (g z) (g z))) = 𝓝 (g z) := by
    have := map_extChartAt_symm_nhdsWithin_range (I := I) (g z)
    rwa [hrange, nhdsWithin_univ] at this
  have hFp : F p = extChartAt I (g z) (g z) := by
    simp [hF, hp, writtenInExtChartAt]
  have hev : (extChartAt I (g z)).symm ∘ F =ᶠ[𝓝 p] g ∘ (extChartAt I z).symm := by
    have hcont : ContinuousAt (g ∘ (extChartAt I z).symm) p := by
      refine ContinuousAt.comp (f := (extChartAt I z).symm) ?_ ?_
      · simpa [hp, extChartAt_to_inv] using hg.continuous.continuousAt
      · exact (continuousAt_extChartAt_symm (I := I) z)
    have hsrc : (extChartAt I (g z)).source ∈ 𝓝 ((g ∘ (extChartAt I z).symm) p) := by
      simpa [hp, extChartAt_to_inv] using extChartAt_source_mem_nhds (I := I) (g z)
    filter_upwards [hcont.preimage_mem_nhds hsrc] with y hy
    simp only [Function.comp_apply, hF, writtenInExtChartAt]
    exact (extChartAt I (g z)).left_inv hy
  calc map g (𝓝 z) = map g (map (extChartAt I z).symm (𝓝 p)) := by rw [hsymm]
    _ = map (g ∘ (extChartAt I z).symm) (𝓝 p) := by rw [Filter.map_map]
    _ = map ((extChartAt I (g z)).symm ∘ F) (𝓝 p) := (map_congr hev).symm
    _ = map (extChartAt I (g z)).symm (map F (𝓝 p)) := by rw [Filter.map_map]
    _ = 𝓝 (g z) := by rw [hmap, hFp, hsymm']

/-- **The exceptional locus is closed.**  In charts the differential is the
derivative of a smooth map, conjugated by invertible chart differentials, and
invertible operators form an open set. -/
theorem isOpen_compl_exceptionalLocus {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) :
    IsOpen (exceptionalLocus n g)ᶜ := by
  set I := 𝓘(ℂ, ComplexModel n) with hI
  have hrange : range I = univ := by simp [hI]
  rw [isOpen_iff_mem_nhds]
  intro z hz
  set e := extChartAt I z with he
  set e' := extChartAt I (g z) with he'
  set F : ComplexModel n → ComplexModel n := e' ∘ g ∘ e.symm with hF
  set O := e.target ∩ e.symm ⁻¹' (univ ∩ g ⁻¹' e'.source) with hO
  have hFO : ContDiffOn ℂ ∞ F O := (contMDiffOn_iff.mp hg.contMDiffOn).2 z (g z)
  have hOopen : IsOpen O :=
    (continuousOn_extChartAt_symm z).isOpen_inter_preimage (isOpen_extChartAt_target z)
      (isOpen_univ.inter (hg.continuous.isOpen_preimage _ (isOpen_extChartAt_source (g z))))
  have hsrc : IsOpen (e.source ∩ g ⁻¹' e'.source) :=
    (isOpen_extChartAt_source z).inter
      (hg.continuous.isOpen_preimage _ (isOpen_extChartAt_source (g z)))
  -- the differential in charts
  have hchain : ∀ y ∈ e.source ∩ g ⁻¹' e'.source,
      mfderiv I I g y = (mfderiv I I e'.symm (F (e y))).comp
        ((fderiv ℂ F (e y)).comp (mfderiv I 𝓘(ℂ, ComplexModel n) e y)) := by
    intro y hy
    have hyO : e y ∈ O := ⟨e.map_source hy.1, by simpa [e.left_inv hy.1] using hy.2⟩
    have hev : g =ᶠ[𝓝 y] e'.symm ∘ F ∘ e := by
      filter_upwards [hsrc.mem_nhds hy] with w hw
      simp only [hF, Function.comp_apply, e.left_inv hw.1, e'.left_inv hw.2]
    have hFe : F (e y) = e' (g y) := by simp [hF, e.left_inv hy.1]
    have hdF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) F (e y) :=
      ((hFO.differentiableOn (by simp)).differentiableAt
        (hOopen.mem_nhds hyO)).mdifferentiableAt
    have hde : MDifferentiableAt I 𝓘(ℂ, ComplexModel n) e y :=
      mdifferentiableAt_extChartAt (by simpa [he, extChartAt_source] using hy.1)
    have hde' : MDifferentiableAt 𝓘(ℂ, ComplexModel n) I e'.symm (F (e y)) := by
      have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := g z)
        (z := F (e y)) (by rw [hFe]; exact e'.map_source hy.2)
      rwa [hrange, mdifferentiableWithinAt_univ] at h
    rw [hev.mfderiv_eq, mfderiv_comp y hde' (hdF.comp y hde), mfderiv_comp y hdF hde,
      mfderiv_eq_fderiv]
    rfl
  have hinv_e : ∀ y ∈ e.source ∩ g ⁻¹' e'.source,
      (mfderiv I I e'.symm (F (e y))).IsInvertible ∧
        (mfderiv I 𝓘(ℂ, ComplexModel n) e y).IsInvertible := by
    intro y hy
    have hFe : F (e y) = e' (g y) := by simp [hF, e.left_inv hy.1]
    refine ⟨?_, isInvertible_mfderiv_extChartAt hy.1⟩
    have h := isInvertible_mfderivWithin_extChartAt_symm (I := I) (x := g z)
      (y := F (e y)) (by rw [hFe]; exact e'.map_source hy.2)
    rwa [hrange, mfderivWithin_univ] at h
  have hbij_iff : ∀ y ∈ e.source ∩ g ⁻¹' e'.source,
      Function.Bijective (mfderiv I I g y) ↔ (fderiv ℂ F (e y)).IsInvertible := by
    intro y hy
    obtain ⟨hA, hC⟩ := hinv_e y hy
    rw [hchain y hy]
    have hAb : Function.Bijective (mfderiv I I e'.symm (F (e y))) := by
      obtain ⟨E, hE⟩ := hA; rw [← hE]; exact E.bijective
    have hCb : Function.Bijective (mfderiv I 𝓘(ℂ, ComplexModel n) e y) := by
      obtain ⟨E, hE⟩ := hC; rw [← hE]; exact E.bijective
    constructor
    · intro hb
      have h1 : Function.Bijective ((mfderiv I I e'.symm (F (e y))) ∘
          ((fderiv ℂ F (e y)) ∘ (mfderiv I 𝓘(ℂ, ComplexModel n) e y))) := hb
      have h2 := (Function.Bijective.of_comp_iff' hAb _).mp h1
      have h3 := (Function.Bijective.of_comp_iff _ hCb).mp h2
      exact ⟨(LinearEquiv.ofBijective (fderiv ℂ F (e y)).toLinearMap h3).toContinuousLinearEquiv,
        ContinuousLinearMap.ext fun v => rfl⟩
    · intro hB
      have hBb : Function.Bijective (fderiv ℂ F (e y)) := by
        obtain ⟨E, hE⟩ := hB; rw [← hE]; exact E.bijective
      exact hAb.comp (hBb.comp hCb)
  have hzsrc : z ∈ e.source ∩ g ⁻¹' e'.source :=
    ⟨mem_extChartAt_source z, mem_extChartAt_source (g z)⟩
  have hzO : e z ∈ O := ⟨e.map_source hzsrc.1, by simpa [e.left_inv hzsrc.1] using hzsrc.2⟩
  have hFz : (fderiv ℂ F (e z)).IsInvertible := by
    have := hz
    simp only [mem_compl_iff, exceptionalLocus, mem_ofPred_eq, not_not] at this
    exact (hbij_iff z hzsrc).mp this
  have hcont : ContinuousOn (fderiv ℂ F) O := hFO.continuousOn_fderiv_of_isOpen hOopen (by simp)
  have hW : IsOpen (O ∩ fderiv ℂ F ⁻¹' range ((↑) : (ComplexModel n ≃L[ℂ] ComplexModel n) →
      ComplexModel n →L[ℂ] ComplexModel n)) :=
    hcont.isOpen_inter_preimage hOopen ContinuousLinearEquiv.isOpen
  have hU : IsOpen ((e.source ∩ e ⁻¹' (O ∩ fderiv ℂ F ⁻¹' range
      ((↑) : (ComplexModel n ≃L[ℂ] ComplexModel n) → ComplexModel n →L[ℂ] ComplexModel n)))
        ∩ (e.source ∩ g ⁻¹' e'.source)) :=
    ((continuousOn_extChartAt z).isOpen_inter_preimage (isOpen_extChartAt_source z) hW).inter
      hsrc
  obtain ⟨E₀, hE₀⟩ := hFz
  refine Filter.mem_of_superset (hU.mem_nhds ⟨⟨hzsrc.1, hzO, E₀, hE₀⟩, hzsrc⟩) ?_
  rintro y ⟨⟨-, -, E, hE⟩, hy⟩
  simp only [mem_compl_iff, exceptionalLocus, mem_ofPred_eq, not_not]
  exact (hbij_iff y hy).mpr ⟨E, hE⟩

omit [IsComplexManifold n X] in
/-- **Strict transforms compose.** -/
theorem strictTransform_comp {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) (A : Set X) :
    strictTransform n (f ∘ g) A = strictTransform n g (strictTransform n f A) := by
  have hexc := exceptionalLocus_comp (hf.mdifferentiable (by simp))
    (hg.mdifferentiable (by simp))
  unfold strictTransform
  rw [hexc]
  set S := f ⁻¹' A \ exceptionalLocus n f with hS
  have hset : (f ∘ g) ⁻¹' A \ (exceptionalLocus n g ∪ g ⁻¹' exceptionalLocus n f) =
      g ⁻¹' S \ exceptionalLocus n g := by
    ext z
    simp only [hS, Set.mem_sdiff, mem_preimage, mem_union, Function.comp_apply]
    tauto
  rw [hset]
  refine subset_antisymm (closure_mono (sdiff_subset_sdiff_left (preimage_mono subset_closure)))
    (closure_minimal ?_ isClosed_closure)
  rintro z ⟨hzS, hzE⟩
  rw [mem_closure_iff_nhds]
  intro t ht
  have ht' : t ∩ (exceptionalLocus n g)ᶜ ∈ 𝓝 z :=
    inter_mem ht ((isOpen_compl_exceptionalLocus hg).mem_nhds hzE)
  have himg : g '' (t ∩ (exceptionalLocus n g)ᶜ) ∈ 𝓝 (g z) := by
    rw [← map_nhds_eq_of_not_mem_exceptionalLocus hg hzE]
    exact image_mem_map ht'
  obtain ⟨_, ⟨w, ⟨hwt, hwE⟩, rfl⟩, hwS⟩ := mem_closure_iff_nhds.mp hzS _ himg
  exact ⟨w, hwt, hwS, hwE⟩

omit [IsComplexManifold n X] [IsComplexManifold n Y] [IsComplexManifold n Z] in
/-- The image of the exceptional locus of the first factor lies in the image of the
exceptional locus of a composition with a surjective second factor. -/
theorem image_exceptionalLocus_subset_comp {f : Y → X} {g : Z → Y}
    (hf : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f)
    (hg : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g)
    (hgs : Function.Surjective g) :
    f '' exceptionalLocus n f ⊆ (f ∘ g) '' exceptionalLocus n (f ∘ g) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, rfl⟩ := hgs y
  exact ⟨z, by rw [exceptionalLocus_comp hf hg]; exact Or.inr hy, rfl⟩

omit [IsComplexManifold n X] [IsComplexManifold n Y] [IsComplexManifold n Z] in
/-- **Non-containment in the image of the exceptional locus passes to the strict
transform.**  If `V ⊄ (f ∘ g)(Exc (f ∘ g))` for surjective holomorphic `f, g`, then
the strict transform of `V` under `f` is not contained in `g(Exc g)`. -/
theorem not_strictTransform_subset_image_exceptionalLocus {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g) {V : Set X}
    (hV : ¬ V ⊆ (f ∘ g) '' exceptionalLocus n (f ∘ g)) :
    ¬ strictTransform n f V ⊆ g '' exceptionalLocus n g := by
  intro hsub
  apply hV
  intro v hv
  obtain ⟨y, rfl⟩ := hfs v
  by_cases hy : y ∈ exceptionalLocus n f
  · exact image_exceptionalLocus_subset_comp (hf.mdifferentiable (by simp))
      (hg.mdifferentiable (by simp)) hgs ⟨y, hy, rfl⟩
  · obtain ⟨w, hw, rfl⟩ := hsub (subset_closure ⟨hv, hy⟩)
    refine ⟨w, ?_, rfl⟩
    rw [exceptionalLocus_comp (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp))]
    exact Or.inl hw

end

end Hironaka.StrictTransformComposition
