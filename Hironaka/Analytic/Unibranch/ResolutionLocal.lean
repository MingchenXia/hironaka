import Hironaka.Analytic.Unibranch.Resolution
import Hironaka.Resolution.HironakaResolutionSpaceLocal

/-!
# Local resolution of singularities of complex spaces

Source: Appendix B (`appendix_unibranch.tex`), proof of `thm:GRexten2`, case (2): "Let
`π : Y → X` be a resolution of singularities", after shrinking `X` around a point (the existence
part of the theorem is local).  This file proves that every point of a complex space of the book
has an open neighbourhood with a resolution (`exists_local_resolution`, with `IsResolution` of
`def:primdiv`): in a local embedding `(Ω, C)` through the point, the embedded resolution of
`C ⊆ Ω` over a small ball (Hironaka library, `HironakaResolutionSpaceLocal`) resolves the open
subspace `C ∩ ball`.

This is one of the inputs of the proof of `thm:GRexten2`; the others (Zariski's main theorem for
singular unibranch spaces, the implication (2) ⇒ (1) of `thm:FN`, lifting discs through `π`)
are not formalized.

Blueprint: `claude-unibranch-res.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka Hironaka.BlowupSequences
open Hironaka.HironakaReducedComplexAnalyticSpaces
open Hironaka.HironakaActualAnalyticSubspaceMaps
open Hironaka.HironakaActualAnalyticSubspaceOpenRestriction
open Hironaka.HironakaResolutionSpace
open Hironaka.HironakaResolutionSpaceComplex
open Hironaka.HironakaEmbeddedAnalytic (singularSet)

namespace Hironaka.Analytic.Unibranch

noncomputable section

open SourceReducedComplexSpace

section Proper

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {M' : Type} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] {W : Set M} {σ : M' → M} {E : List (Set M')}

/-- The resolution morphism of a proper blowup sequence (no compactness) is a resolution. -/
theorem isResolution_resolutionMorphism_of_isProperMap (hWa : IsComplexAnalyticSubset (n := n) W)
    (h : IsStrictTransformResolution n W σ E) (hσ : IsProperMap σ) :
    IsResolution (resolutionMorphism hWa h) := by
  refine ⟨isSmooth_ofClosedAnalytic_of_isClosedSubmanifold h.isClosedSubmanifold,
    Hironaka.HironakaResolutionSpaceLocal.resolutionMap_isProperMap_of_isProperMap
      h hσ,
    (Subtype.val : W → M) ⁻¹' singularSet (n := n) W,
    isAnalyticSubset_preimage_val hWa
      (Hironaka.HironakaResolutionSpaceSingular.isComplexAnalyticSubset_singularSet
        hWa), ?_, ?_, ?_⟩
  · rw [interior_eq_empty_iff_dense_compl]
    exact dense_regular hWa
  · rw [interior_eq_empty_iff_dense_compl]
    exact dense_preimage_regular h
  · exact resolutionMap_isIsoOver h hWa.isClosed

end Proper

/-- **Local resolution of complex spaces.**  Every point `x` of a complex space `X` has an open
neighbourhood `V` (an open subspace: `j : V ⟶ X` is an open immersion with `x` in its image)
which has a resolution `π : Y ⟶ V` (`IsResolution`: `Y` smooth, `π` proper and an isomorphism
over the complement of a nowhere dense analytic subset with nowhere dense preimage). -/
theorem exists_local_resolution (X : SourceReducedComplexSpace) (x : X.obj.left) :
    ∃ (V : SourceReducedComplexSpace) (j : V ⟶ X), LocallyRingedSpace.IsOpenImmersion j.hom.left ∧
      x ∈ range j.hom.left.base ∧ ∃ (Y : SourceReducedComplexSpace) (π : Y ⟶ V), IsResolution π := by
  let e := LocalEmbedding.ofPoint X x
  obtain ⟨c, hc⟩ := LocalEmbedding.mem_range_ofPoint X x
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.ambient.isOpen c.val.val c.val.property
  have hr : 0 < ε / 2 := half_pos hε
  have hcl : Metric.closedBall c.val.val (ε / 2) ⊆ e.ambient :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  let X₀ : Opens e.ambient :=
    ⟨(Subtype.val : e.ambient → ComplexModel e.dim) ⁻¹' Metric.ball c.val.val (ε / 2),
      Metric.isOpen_ball.preimage continuous_subtype_val⟩
  let K : Set e.ambient :=
    (Subtype.val : e.ambient → ComplexModel e.dim) ⁻¹' Metric.closedBall c.val.val (ε / 2)
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have himg : (Subtype.val : e.ambient → ComplexModel e.dim) '' K =
        Metric.closedBall c.val.val (ε / 2) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, hcl hz⟩, hz, rfl⟩
    rw [himg]
    exact isCompact_closedBall _ _
  have hX₀ : (X₀ : Set e.ambient) ⊆ K := preimage_mono Metric.ball_subset_closedBall
  obtain ⟨X₀', _, _, _, σ, E, hprop, h⟩ :=
    Hironaka.HironakaResolutionSpaceLocal.exists_isStrictTransformResolution_local
      e.analytic X₀ hK hX₀
  have hV := Hironaka.AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
    e.analytic X₀
  let V := ofClosedAnalytic ((Subtype.val : X₀ → e.ambient) ⁻¹' e.carrier) hV
  have hover : (actualOpenSubspaceMap (n := e.dim) e.carrier X₀ ≫ e.map) ≫ X.obj.hom =
      V.obj.hom := by
    rw [Category.assoc, e.overPoint]
    change actualOpenSubspaceMap (n := e.dim) e.carrier X₀ ≫ subspacePointMap (n := e.dim) e.carrier =
      subspacePointMap (n := e.dim) _
    rw [actualOpenSubspaceMap]
    exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)
  let j : V ⟶ X :=
    ObjectProperty.homMk (Over.homMk (actualOpenSubspaceMap (n := e.dim) e.carrier X₀ ≫ e.map) hover)
  refine ⟨V, j, ?_, ?_, _, resolutionMorphism hV h,
    isResolution_resolutionMorphism_of_isProperMap hV h hprop⟩
  · change LocallyRingedSpace.IsOpenImmersion
      (actualOpenSubspaceMap (n := e.dim) e.carrier X₀ ≫ e.map)
    have := e.isOpenImmersion
    infer_instance
  · have hcX₀ : c.val ∈ X₀ := Metric.mem_ball_self hr
    refine ⟨⟨⟨c.val, hcX₀⟩, c.property⟩, ?_⟩
    exact (show _ = (LocalEmbedding.ofPoint X x).toPoint c from rfl).trans hc

end

end Hironaka.Analytic.Unibranch
