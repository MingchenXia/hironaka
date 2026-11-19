import Hironaka.Analytic.Unibranch.HironakaG10GenGluing
import Hironaka.Analytic.Unibranch.OriginalSmoothSourceAnalytic
import Hironaka.Analytic.Unibranch.OriginalNativeModification
import Hironaka.Resolution.HironakaG10ChowRiemannExtension

/-!
# Riemann extension for maps from complex manifolds to reduced complex spaces

A continuous map `φ : W → B` from a complex manifold to a (possibly singular) reduced complex space
which, off a closed analytic subset `A ⊆ W` with empty interior, is locally the point map of a
morphism of reduced complex spaces, is the point map of a morphism `wholeModel W ⟶ B`
(`exists_hom_of_continuous_of_thin`).

Near a point `t ∈ A`, choose a local embedding `(Ω, C) → B` at `φ t` with `Ω ⊆ ℂ^N` open.  On
the open set `O = φ⁻¹(image)`, `φ` reads as a continuous map `ψ : O → C ⊆ ℂ^N`; off `A` it is
holomorphic, since every morphism from a manifold model is locally given by a holomorphic map into
the ambient space of any local embedding (`OriginalSmoothSourceAnalytic.exists_local_chart_lift`).
The Riemann extension theorem for maps (`HironakaG10ChowRiemannExtension`) makes `ψ` holomorphic
on `O`, and `ψ` induces the morphism of the models.  The local morphisms glue
(`HironakaG10GenGluing.exists_hom_of_local'`).

Blueprint: `hironaka-g10-gen-chow-general.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10GenRiemannExtension

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic

noncomputable section

variable {m : ℕ} {W : Type} [TopologicalSpace W] [ChartedSpace (ComplexModel m) W]
  [IsComplexManifold m W] {B : SourceReducedComplexSpace}

/-- The native inclusion of an open subset of a complex manifold. -/
abbrev openInclusion (O : Opens W) : wholeModel (n := m) O ⟶ wholeModel (n := m) W :=
  nativeMorphism (n := m) (m := m)
    (contMDiff_subtype_val : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞
      (Subtype.val : O → W))

theorem openInclusion_isOpenImmersion (O : Opens W) :
    LocallyRingedSpace.IsOpenImmersion (openInclusion (m := m) O).hom.left :=
  actualOpenSubspaceMap_isOpenImmersion (n := m) (univ : Set W) O

/-- **Local Riemann extension.**  Under the hypotheses of `exists_hom_of_continuous_of_thin`,
every point has an open neighbourhood on which `φ` is the point map of a morphism. -/
theorem exists_local_extension (φ : W → B.obj.left) (hφ : Continuous φ) {A : Set W}
    (hA : IsComplexAnalyticSubset (n := m) A) (hAc : IsClosed A) (hAi : interior A = ∅)
    (hloc : ∀ w, w ∉ A → ∃ (O : Opens W) (_ : w ∈ O) (F : wholeModel (n := m) O ⟶ B),
      ∀ u : O, pointMap F u = φ u) (t : W) :
    ∃ (O : Opens W) (_ : t ∈ O) (F : wholeModel (n := m) O ⟶ B), ∀ u : O, pointMap F u = φ u := by
  classical
  by_cases htA : t ∉ A
  · exact hloc t htA
  let e := LocalEmbedding.ofPoint B (φ t)
  let R : Set B.obj.left := range e.toPoint
  have hR : IsOpen R := e.isOpen_range_toPoint
  let O : Opens W := ⟨φ ⁻¹' R, hR.preimage hφ⟩
  have htO : t ∈ O := LocalEmbedding.mem_range_ofPoint B (φ t)
  let h : e.carrier ≃ₜ range e.toPoint := e.isOpenEmbedding_toPoint.isEmbedding.toHomeomorph
  let ψ : O → e.carrier := fun u => h.symm ⟨φ u, u.2⟩
  have hψc : Continuous ψ :=
    h.symm.continuous.comp ((hφ.comp continuous_subtype_val).subtype_mk _)
  have hψ : ∀ u, e.toPoint (ψ u) = φ u := fun u =>
    congrArg Subtype.val (h.apply_symm_apply ⟨φ u, u.2⟩)
  let Φ : O → ComplexModel e.dim := fun u => ((ψ u).val : ComplexModel e.dim)
  have hΦc : Continuous Φ := continuous_subtype_val.comp (continuous_subtype_val.comp hψc)
  let Ψ : W → ComplexModel e.dim := fun w => if hw : w ∈ O then Φ ⟨w, hw⟩ else 0
  have hΨΦ : (fun u : O => Ψ u) = Φ := by
    funext u
    exact dif_pos u.2
  let A' : Set O := (Subtype.val : O → W) ⁻¹' A
  have hA' : IsComplexAnalyticSubset (n := m) A' :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hA O
  have hA'c : IsClosed A' := hAc.preimage continuous_subtype_val
  have hA'i : interior A' = ∅ := by
    have hi := O.isOpen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
      continuous_subtype_val A
    exact hi.symm.trans (by rw [hAi, preimage_empty])
  have hΨ : ∀ u : O, u ∉ A' → ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel e.dim) ∞ Ψ u := by
    intro u hu
    obtain ⟨O₁, hu₁, F₁, hF₁⟩ := hloc u.val hu
    have hx : pointMap F₁ ⟨u.val, hu₁⟩ ∈ range e.toPoint := by
      rw [hF₁]
      exact u.2
    obtain ⟨U', hxU', g', hg', hw', hpoint', -⟩ := exists_local_chart_lift F₁ e ⟨u.val, hu₁⟩ hx
    have hU'O : ∀ v : U', v.val.val ∈ O := by
      intro v
      change φ v.val.val ∈ R
      rw [← hF₁ v.val, ← hpoint' v]
      exact ⟨_, rfl⟩
    have heq : (fun v : U' => Ψ v.val.val) = fun v => ((g' v : e.ambient) : ComplexModel e.dim) := by
      funext v
      change (if hw : v.val.val ∈ O then Φ ⟨v.val.val, hw⟩ else 0) = _
      rw [dif_pos (hU'O v)]
      have hinj : ψ ⟨v.val.val, hU'O v⟩ = ⟨g' v, hw' v⟩ := by
        apply e.toPoint_injective
        rw [hψ, hpoint' v]
        exact (hF₁ v.val).symm
      change ((ψ ⟨v.val.val, hU'O v⟩).val : ComplexModel e.dim) = _
      rw [hinj]
    have h3 : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel e.dim) ∞
        (fun v : U' => Ψ v.val.val) ⟨⟨u.val, hu₁⟩, hxU'⟩ := by
      rw [heq]
      exact (contMDiff_subtype_val.comp hg').contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel e.dim) ∞
        (fun x : O₁ => Ψ x) ⟨u.val, hu₁⟩ :=
      (contMDiffAt_subtype_iff (U := U') (f := fun x : O₁ => Ψ x)
        (x := ⟨⟨u.val, hu₁⟩, hxU'⟩)).mp h3
    exact (contMDiffAt_subtype_iff (U := O₁) (f := Ψ) (x := ⟨u.val, hu₁⟩)).mp h2
  have hΦA : ∀ u : O, u ∉ A' →
      MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel e.dim) Φ u := by
    intro u hu
    have h1 := (contMDiffAt_subtype_iff (U := O) (f := Ψ) (x := u)).mpr (hΨ u hu)
    rw [hΨΦ] at h1
    exact h1.mdifferentiableAt (by simp)
  have hΦs : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel e.dim) ∞ Φ :=
    HironakaG10ChowRiemannExtension.contMDiff_of_continuous_of_isComplexAnalyticSubset
      hΦc hA' hA'c hA'i hΦA
  let ψa : O → e.ambient := fun u => (ψ u).val
  have hψa : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel e.dim) ∞ ψa :=
    (ContMDiff.subtypeVal_comp_iff e.ambient ψa).mp hΦs
  have hmaps : ∀ u ∈ (univ : Set O), ψa u ∈ e.carrier := fun u _ => (ψ u).2
  have hover : (actualSubspaceMap hψa hmaps ≫ e.map) ≫ B.obj.hom =
      (wholeModel (n := m) O).obj.hom := by
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (fun k => actualSubspaceMap hψa hmaps ≫ k) e.overPoint).trans
      (actualSubspaceMap_point hψa hmaps)
  let F : wholeModel (n := m) O ⟶ B :=
    ObjectProperty.homMk (Over.homMk (actualSubspaceMap hψa hmaps ≫ e.map) hover)
  refine ⟨O, htO, F, fun u => ?_⟩
  change e.toPoint ⟨ψa u, (ψ u).2⟩ = φ u
  exact hψ u

/-- **Riemann extension into a reduced complex space.**  Let `W` be a complex manifold, `B` a
reduced complex space and `φ : W → B` continuous.  If `φ` is, near every point off a closed
analytic subset `A ⊆ W` with empty interior, the point map of a morphism of reduced complex
spaces, then `φ` is the point map of a morphism `wholeModel W ⟶ B`. -/
theorem exists_hom_of_continuous_of_thin (φ : W → B.obj.left) (hφ : Continuous φ) {A : Set W}
    (hA : IsComplexAnalyticSubset (n := m) A) (hAc : IsClosed A) (hAi : interior A = ∅)
    (hloc : ∀ w, w ∉ A → ∃ (O : Opens W) (_ : w ∈ O) (F : wholeModel (n := m) O ⟶ B),
      ∀ u : O, pointMap F u = φ u) :
    ∃ G : wholeModel (n := m) W ⟶ B, ∀ w, pointMap G w = φ w := by
  obtain ⟨G, hG⟩ := HironakaG10GenGluing.exists_hom_of_local' (A := wholeModel (n := m) W)
    (B := B) (fun a => φ a.val) (fun a => by
      obtain ⟨O, haO, F, hF⟩ := exists_local_extension φ hφ hA hAc hAi hloc a.val
      refine ⟨wholeModel (n := m) O, openInclusion O, F, openInclusion_isOpenImmersion O,
        ⟨⟨⟨a.val, haO⟩, mem_univ _⟩, Subtype.ext rfl⟩, fun u => ?_⟩
      exact hF u.val)
  exact ⟨G, fun w => hG ⟨w, mem_univ w⟩⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10GenRiemannExtension
