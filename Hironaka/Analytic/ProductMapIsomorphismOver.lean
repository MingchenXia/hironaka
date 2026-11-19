import Hironaka.Analytic.HolomorphicLocalInverse
import Hironaka.Analytic.ProductComplexManifold
import Hironaka.Blowup.BlowupIsomorphismOff

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `g × id` is an isomorphism over `N × W` when `g` is an isomorphism over `N`

Step U1(a) of the uniform nef core of Boucksom 4.8 (TN.4 plan §1 F6 "(P) GRAPH ROUTE";
`.archon-horizon/scratch/tn-classical-round-0154-r2.md`): the fixed concentration of mass on the
diagonal of `X × X` is pulled back along `ν = μ × id : Y × X → X × X` (`μ` a blowup sequence), and
`ν⁻¹(Δ)` is the graph of `μ`.  The change of variables of global mixed measures
(`ModificationMassInvariance.globalMixedMeasure_restrict_preimage_eq_map`) needs `ν` to be an
isomorphism over an open set (`IsIsomorphismOver`), which is proved here for `g × id`.

* `contMDiffAt_prodMk` — the pointwise form of `ProductComplexManifold.contMDiff_prodMk`.
* `not_mem_exceptionalLocus_prodMap` — if `dg` is bijective at `z`, then `d(g × id)` is bijective at
  `(z, w)`: a holomorphic local inverse `s` of `g` (`HolomorphicLocalInverse.exists_localInverse`)
  gives the local inverse `s × id` of `g × id`, so `d(g × id)` is onto, hence bijective.
* `isIsomorphismOver_prodMap` — `g` an isomorphism over `N` ⇒ `g × id` an isomorphism over `N × W`.
-/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ProductMapIsomorphismOver

open Hironaka.BlowupSequences ProductComplexManifold
open scoped ProductComplexManifold

section ProdMk

variable {n m k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y] {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]

/-- **The pair of two maps holomorphic at a point is holomorphic there** (pointwise form of
`ProductComplexManifold.contMDiff_prodMk`). -/
theorem contMDiffAt_prodMk {f : Z → X} {g : Z → Y} {z : Z}
    (hf : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f z)
    (hg : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) ∞ g z) :
    ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (n + m)) ∞ (fun z => (f z, g z)) z := by
  rw [contMDiffAt_iff_target] at hf hg ⊢
  refine ⟨hf.1.prodMk hg.1, ?_⟩
  have hpair := hf.2.prodMk_space hg.2
  refine (((prodModelEquiv n m : (ComplexModel n × ComplexModel m) →L[ℂ] ComplexModel (n + m)).contMDiff
    ).contMDiffAt.comp z hpair).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun z' => by simp [extChartAt, OpenPartialHomeomorph.extend]

end ProdMk

section Exceptional

variable {n m : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] {W : Type u} [TopologicalSpace W] [ChartedSpace (ComplexModel m) W]
  [IsComplexManifold m W]

/-- **The exceptional locus of `g × id`**: if `dg` is bijective at `z`, then `d(g × id)` is
bijective at `(z, w)` for every `w`. -/
theorem not_mem_exceptionalLocus_prodMap {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {z : Z}
    (hz : z ∉ exceptionalLocus n g) (w : W) :
    (z, w) ∉ exceptionalLocus (n + m) (Prod.map g (id : W → W)) := by
  obtain ⟨V, s, hV, hgzV, hsgz, hgs, hsmooth, -⟩ :=
    HolomorphicLocalInverse.exists_localInverse hg hz
  set ν : Z × W → Y × W := Prod.map g (id : W → W) with hνdef
  set σ : Y × W → Z × W := fun p => (s p.1, p.2) with hσdef
  have hν : ContMDiff 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) ∞ ν :=
    contMDiff_prodMap hg contMDiff_id
  have hσ : ContMDiffAt 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) ∞ σ (g z, w) :=
    contMDiffAt_prodMk ((hsmooth (g z) hgzV).comp (g z, w) contMDiff_fst.contMDiffAt)
      contMDiff_snd.contMDiffAt
  have hσp : σ (g z, w) = (z, w) := by
    simp only [hσdef, hsgz]
  have heq : ν ∘ σ =ᶠ[𝓝 (g z, w)] id := by
    filter_upwards [(hV.prod isOpen_univ).mem_nhds (show (g z, w) ∈ V ×ˢ (univ : Set W) from
      ⟨hgzV, mem_univ _⟩)] with p hp
    simp only [Function.comp_apply, hνdef, hσdef, Prod.map_apply, id_eq, hgs p.1 hp.1]
  have hσd : MDifferentiableAt 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) σ (g z, w) :=
    hσ.mdifferentiableAt (by simp)
  have hνd : MDifferentiableAt 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) ν
      (σ (g z, w)) := (hν _).mdifferentiableAt (by simp)
  have h1 := mfderiv_comp (g z, w) hνd hσd
  rw [heq.mfderiv_eq, mfderiv_id] at h1
  have hsurj' : Function.Surjective
      (mfderiv 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) ν (σ (g z, w))) := fun v =>
    ⟨mfderiv 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) σ (g z, w) v,
      (DFunLike.congr_fun h1 v).symm⟩
  rw [hσp] at hsurj'
  intro hexc
  apply hexc
  have hsurj : Function.Surjective
      (mfderiv 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) ν (z, w)) := hsurj'
  set L : ComplexModel (n + m) →ₗ[ℂ] ComplexModel (n + m) :=
    (show ComplexModel (n + m) →L[ℂ] ComplexModel (n + m) from
      mfderiv 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) ν (z, w)).toLinearMap
  have hinj : Function.Injective L :=
    LinearMap.injective_iff_surjective (V := ComplexModel (n + m)) (f := L) |>.mpr hsurj
  exact ⟨hinj, hsurj⟩

/-- **`g × id` is an isomorphism over `N × W`** whenever `g` is an isomorphism over `N`. -/
theorem isIsomorphismOver_prodMap {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {N : Set Y}
    (hiso : IsIsomorphismOver n g N) :
    IsIsomorphismOver (n + m) (Prod.map g (id : W → W)) (N ×ˢ (univ : Set W)) := by
  obtain ⟨⟨hmaps, hinj, hsurj⟩, hdisj⟩ := hiso
  refine ⟨⟨fun p hp => hp, ?_, ?_⟩, ?_⟩
  · rintro ⟨z₁, w₁⟩ hp₁ ⟨z₂, w₂⟩ hp₂ h
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h
    have h₁ : z₁ ∈ g ⁻¹' N := hp₁.1
    have h₂ : z₂ ∈ g ⁻¹' N := hp₂.1
    rw [hinj h₁ h₂ h.1, h.2]
  · rintro ⟨y, w⟩ ⟨hy, -⟩
    obtain ⟨z, hz, hzy⟩ := hsurj hy
    exact ⟨(z, w), ⟨hz, mem_univ _⟩, by simp [hzy]⟩
  · refine disjoint_left.mpr fun p hp => ?_
    have hp1 : p.1 ∉ exceptionalLocus n g := disjoint_left.mp hdisj hp.1
    exact not_mem_exceptionalLocus_prodMap hg hp1 p.2

end Exceptional

end Hironaka.ProductMapIsomorphismOver
