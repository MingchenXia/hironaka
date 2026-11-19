import Hironaka.Analytic.Unibranch.Resolution
import Hironaka.Analytic.Unibranch.SourceMorphismExt

/-!
# Full closed analytic factorization from an arbitrary original reduced source

Only ordinary point landing in the actual closed analytic subspace is input.
Genuine original source charts and local ambient holomorphic lifts construct
full local quotient maps. Actual-model faithfulness supplies their full
squares; the native inclusion is mono and the fixed-source gluer constructs
the unique full original factor. No global source countability is introduced.
Blueprint: `original-closed-subspace-factorization.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalClosedSubspaceFactorization

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaActualAnalyticSubspaceLocalFunctions
  HironakaActualAnalyticSubspaceManifoldCharts HironakaResolutionSpaceComplex
  HironakaReducedComplexAnalyticSpaces HironakaIntrinsicMorphismGluing
  SourceReducedComplexSpace

noncomputable section

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {W₀ W : Set M} (hW₀ : IsComplexAnalyticSubset (n := n) W₀)
  (hW : IsComplexAnalyticSubset (n := n) W) (hsub : W₀ ⊆ W)

/-- The genuine full original closed-subspace inclusion induced by the identity of M. -/
@[implicit_reducible]
def inclusion : ofClosedAnalytic W₀ hW₀ ⟶ ofClosedAnalytic W hW :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (f := (id : M → M)) contMDiff_id (fun _ hx => hsub hx))
    (actualSubspaceMap_point contMDiff_id (fun _ hx => hsub hx)))

/-- The point map retains the literal original ambient point. -/
theorem inclusion_base_val (x : W₀) :
    ((inclusion hW₀ hW hsub).hom.left.base x).val = x.val := rfl

/-- The ENTIRE original ambient inclusion square, including all quotient sheaf maps. -/
theorem inclusion_ambient :
    (inclusion hW₀ hW hsub).hom.left ≫ actualSubspaceInclusion (n := n) W =
      actualSubspaceInclusion (n := n) W₀ := by
  change actualSubspaceMap (f := (id : M → M)) contMDiff_id (fun _ hx => hsub hx) ≫
    actualSubspaceInclusion (n := n) W = actualSubspaceInclusion (n := n) W₀
  simpa only [ChartedSpace.locallyRingedSpace_id, Category.comp_id] using
    (actualSubspaceMap_inclusion (f := (id : M → M)) contMDiff_id
      (fun _ hx => hsub hx)).symm

/-- Actual quotient stalks give monicity; no inclusion certificate is supplied. -/
instance inclusion_left_mono : Mono (inclusion hW₀ hW hsub).hom.left := by
  have : Mono (actualSubspaceInclusion (n := n) W₀) := actualSubspaceInclusion_mono W₀
  exact mono_of_mono_fac (inclusion_ambient hW₀ hW hsub)

private theorem exists_local_factorization (A : SourceReducedComplexSpace)
    (F : A ⟶ ofClosedAnalytic W hW)
    (hland : ∀ a : A.obj.left, (F.hom.left.base a).val ∈ W₀) (x : A.obj.left) :
    ∃ (P : LocallyRingedSpace) (j : P ⟶ A.obj.left)
      (K : P ⟶ actualSubspaceLocallyRingedSpace (n := n) W₀),
      LocallyRingedSpace.IsOpenImmersion j ∧ x ∈ range j.base ∧
      K ≫ (inclusion hW₀ hW hsub).hom.left = j ≫ F.hom.left := by
  let a := LocalEmbedding.ofPoint A x
  obtain ⟨c, hcx⟩ := LocalEmbedding.mem_range_ofPoint A x
  let F₀ := a.map ≫ F.hom.left
  have hFp : F.hom.left ≫ subspacePointMap (n := n) W = A.obj.hom := Over.w F.hom
  have hF₀ : F₀ ≫ subspacePointMap (n := n) W =
      subspacePointMap (n := a.dim) a.carrier := by
    calc
      _ = a.map ≫ (F.hom.left ≫ subspacePointMap (n := n) W) := Category.assoc _ _ _
      _ = a.map ≫ A.obj.hom := congrArg (fun t => a.map ≫ t) hFp
      _ = _ := a.overPoint
  let p : M := (F₀.base c).val
  let e := LocalEmbedding.ofChart W hW p
  have hc : F₀.base c ∈ range e.toPoint :=
    mem_range_chartModelMap (n := n) W (F₀.base c).property
  obtain ⟨O, hcO, f, hf, hfac⟩ :=
    LocalEmbedding.exists_contMDiff_factor F₀ hF₀ e c hc
  let S : Set O := (Subtype.val : O → a.ambient) ⁻¹' a.carrier
  let P := actualSubspaceLocallyRingedSpace (n := a.dim) S
  let j₀ := actualOpenSubspaceMap (n := a.dim) a.carrier O
  let j := j₀ ≫ a.map
  let : LocallyRingedSpace.IsOpenImmersion a.map := a.isOpenImmersion
  let g : O → M := fun y => ((chartDiffeo (n := n) p).symm (f y)).val
  have hg : ContMDiff 𝓘(ℂ, ComplexModel a.dim) 𝓘(ℂ, ComplexModel n) ∞ g :=
    contMDiff_subtype_val.comp ((chartDiffeo (n := n) p).symm.contMDiff.comp hf)
  have hgpoint (y : S) : g y.val = (F₀.base (j₀.base y)).val := by
    obtain ⟨z, hzf, hzF⟩ := hfac (j₀.base y) y.val.property
    calc
      _ = (e.toPoint z).val := by
        change ((chartDiffeo (n := n) p).symm (f y.val)).val =
          ((chartDiffeo (n := n) p).symm z.val).val
        rw [hzf]
        rfl
      _ = _ := congrArg Subtype.val hzF
  have hCD : ∀ y ∈ S, g y ∈ W₀ := by
    intro y hy
    rw [hgpoint (⟨y, hy⟩ : S)]
    exact hland (a.map.base (j₀.base (⟨y, hy⟩ : S)))
  let K : P ⟶ actualSubspaceLocallyRingedSpace (n := n) W₀ := actualSubspaceMap hg hCD
  have hjp : j ≫ A.obj.hom = subspacePointMap (n := a.dim) S := by
    change (j₀ ≫ a.map) ≫ A.obj.hom = _
    rw [Category.assoc, a.overPoint]
    exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)
  refine ⟨P, j, K, inferInstance, ?_, ?_⟩
  · refine ⟨⟨⟨c.val, hcO⟩, c.property⟩, ?_⟩
    exact hcx
  · apply actualSubspaceMap_eq_of_base_eq (K ≫ (inclusion hW₀ hW hsub).hom.left)
      (j ≫ F.hom.left)
    · have hip : (inclusion hW₀ hW hsub).hom.left ≫ subspacePointMap (n := n) W =
          subspacePointMap (n := n) W₀ := Over.w (inclusion hW₀ hW hsub).hom
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun t => K ≫ t) hip).trans (actualSubspaceMap_point hg hCD))
    · exact (Category.assoc _ _ _).trans ((congrArg (fun t => j ≫ t) hFp).trans hjp)
    · ext y
      apply Subtype.ext
      exact hgpoint y

/-- Ordinary point landing from an arbitrary ORIGINAL reduced A constructs
the UNIQUE FULL original factor, with no source SC/lift/ideal certificate. -/
theorem exists_unique_factorization (A : SourceReducedComplexSpace)
    (F : A ⟶ ofClosedAnalytic W hW)
    (hland : ∀ a : A.obj.left, (F.hom.left.base a).val ∈ W₀) :
    ∃! G : A ⟶ ofClosedAnalytic W₀ hW₀, G ≫ inclusion hW₀ hW hsub = F := by
  classical
  choose P j K hj hx hfac using exists_local_factorization hW₀ hW hsub A F hland
  let : ∀ x, LocallyRingedSpace.IsOpenImmersion (j x) := hj
  have hcover : ∀ x : A.obj.left, ∃ (a : A.obj.left) (u : P a), (j a).base u = x := by
    intro x
    obtain ⟨u, hu⟩ := hx x
    exact ⟨x, u, hu⟩
  have hcompat : ∀ a c, pullback.fst (j a) (j c) ≫ K a = pullback.snd (j a) (j c) ≫ K c := by
    intro a c
    apply (cancel_mono (inclusion hW₀ hW hsub).hom.left).mp
    simpa only [Category.assoc, hfac] using
      congrArg (fun u => u ≫ F.hom.left) (pullback.condition (f := j a) (g := j c))
  have hpoint (a : A.obj.left) :
      K a ≫ (ofClosedAnalytic W₀ hW₀).obj.hom = j a ≫ A.obj.hom := by
    rw [← Over.w (inclusion hW₀ hW hsub).hom, ← Category.assoc, hfac a,
      Category.assoc, Over.w F.hom]
  obtain ⟨G, hG, _⟩ := exists_unique_over P j hcover A.obj.hom
    (ofClosedAnalytic W₀ hW₀).obj.hom K hcompat hpoint
  have hGi : G.left ≫ (inclusion hW₀ hW hsub).hom.left = F.hom.left := by
    apply HironakaIntrinsicMorphismGluing.hom_ext P j hcover
    intro a
    rw [← Category.assoc, hG a, hfac a]
  refine ⟨ObjectProperty.homMk G, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hGi
  · intro G' hG'
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono (inclusion hW₀ hW hsub).hom.left).mp
    exact (congrArg (fun H => H.hom.left) hG').trans hGi.symm

end

end Hironaka.Analytic.Unibranch.OriginalClosedSubspaceFactorization
