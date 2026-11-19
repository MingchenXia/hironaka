import Hironaka.Analytic.Unibranch.ComplexSpaceAnalyticSubsets
import Hironaka.Resolution.HironakaResolutionSpaceComplex
import Hironaka.Resolution.HironakaResolutionSpaceSingular

/-!
# Resolution of singularities of embedded compact complex spaces

Source: Appendix B (`appendix_unibranch.tex`), `thm:res` ("Let `X` be a compact complex space.
Then there is a modification `π : Y → X` such that `Y` is smooth"; Bierstone--Milman 1997,
Włodarczyk 2009), together with the notion of *resolution* of `def:primdiv` (a proper
bimeromorphic morphism from a smooth space).

This file proves `thm:res` for the compact complex spaces that are closed analytic subspaces of
a compact complex manifold (goal G11a of the Hironaka library).  It introduces, on the book's
complex spaces (`SourceReducedComplexSpace`):

* `SourceReducedComplexSpace.ofClosedAnalytic`: the reduced closed subspace `(C, 𝒪_M / 𝓘_C)` on
  a closed analytic subset `C` of a complex manifold `M`, with its local embeddings
  `LocalEmbedding.ofChart` given by the charts of `M`; analytic subsets of `M` restrict to
  analytic subsets of it (`isAnalyticSubset_preimage_val`);
* `SourceReducedComplexSpace.IsSmooth`: every point has an open neighbourhood isomorphic, over the
  complex point, to an open subset of some `ℂ^d` with its sheaf of holomorphic functions;
* `SourceReducedComplexSpace.IsIsoOver π U`: `π` restricts to an isomorphism `π⁻¹ U ≅ U` of open
  subspaces;
* `SourceReducedComplexSpace.IsProperBimeromorphic π`: `π` is proper and an isomorphism over the
  complement of a nowhere dense analytic subset whose preimage is nowhere dense;
* `SourceReducedComplexSpace.IsResolution π`: the source is smooth and `π` is proper
  bimeromorphic (the *resolutions* of `def:primdiv`).

Main result: `exists_resolution_ofClosedAnalytic` (`thm:res` for `X = (W, 𝒪_M/𝓘_W)`, `W` a closed
analytic subset of a compact complex manifold `M`): there are a compact
complex manifold `M'`, a finite composition `σ : M' → M` of blowups with smooth nowhere dense
centres lying over the singular set of `W`, and a resolution `π : Y ⟶ X` from the compact smooth
strict transform `Y = (W', 𝒪/𝓘_{W'})`, surjective and equal to `σ` on points, an isomorphism over
the complement of the analytic singular set of `X`.  `exists_resolution_of_iso` transfers the
resolution to every complex space isomorphic to such an `X`.

What is **not** proved here (so `thm:res` is only partially formalized): compact complex spaces
that are not closed analytic subspaces of a compact manifold (this needs embedding independence
and functoriality of the embedded resolution, goal G1 of the Hironaka library, and a gluing
argument), and the identification of `π` with a finite composition of blowups of `X` itself along
smooth centres (`def:modif` for singular spaces: blowups of complex spaces are not formalized).

Blueprint: `claude-unibranch-res.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka Hironaka.BlowupSequences
open Hironaka.HironakaReducedComplexAnalyticSpaces
open Hironaka.HironakaActualAnalyticSubspace
open Hironaka.HironakaResolutionSpace
open Hironaka.HironakaResolutionSpaceComplex
open Hironaka.HironakaEmbeddedAnalytic (singularSet)

namespace Hironaka.Analytic.Unibranch

noncomputable section

/-! ### Closed analytic subspaces of complex manifolds as complex spaces -/

section ClosedAnalytic

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The reduced closed subspace `(C, 𝒪_M / 𝓘_C)` on a closed analytic subset `C` of a complex
manifold `M`, as a complex space of the book (reduced, Hausdorff, paracompact, locally an
embedded model). -/
def SourceReducedComplexSpace.ofClosedAnalytic (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) : SourceReducedComplexSpace := by
  refine ⟨Over.mk (subspacePointMap (n := n) C), ?_, ?_, fun x => ⟨n, exists_model_chart hC x⟩⟩
  · change T2Space C
    infer_instance
  · change ParacompactSpace C
    have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel n) M
    have : LocallyCompactSpace C := hC.isClosed.locallyCompactSpace
    infer_instance

@[simp] theorem SourceReducedComplexSpace.ofClosedAnalytic_left (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    (SourceReducedComplexSpace.ofClosedAnalytic C hC).obj.left =
      actualSubspaceLocallyRingedSpace (n := n) C := rfl

/-- The local embedding of `(C, 𝒪_M/𝓘_C)` given by the chart of `M` at `x`. -/
def LocalEmbedding.ofChart (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C) (x : M) :
    LocalEmbedding (SourceReducedComplexSpace.ofClosedAnalytic C hC) where
  dim := n
  ambient := chartImage (n := n) x
  carrier := chartTrace (n := n) C x
  analytic := isComplexAnalyticSubset_chartTrace hC x
  map := chartModelMap (n := n) C x
  isOpenImmersion := inferInstance
  overPoint := chartModelMap_point (n := n) C x

/-- Analytic subsets of the manifold restrict to analytic subsets of the complex space. -/
theorem SourceReducedComplexSpace.isAnalyticSubset_preimage_val {C : Set M}
    (hC : IsComplexAnalyticSubset (n := n) C) {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) :
    (SourceReducedComplexSpace.ofClosedAnalytic C hC).IsAnalyticSubset
      ((Subtype.val : C → M) ⁻¹' A) := by
  intro x
  refine ⟨LocalEmbedding.ofChart C hC x.val, mem_range_chartModelMap (n := n) C x.property,
    chartTrace (n := n) A x.val, isComplexAnalyticSubset_chartTrace hA x.val, ?_⟩
  ext c
  rfl

end ClosedAnalytic

/-! ### Smoothness, isomorphisms over open sets, resolutions -/

namespace SourceReducedComplexSpace

/-- A complex space is *smooth* (a complex manifold, possibly of varying dimension) if every
point has an open neighbourhood isomorphic, over the complex point, to an open subset of some
`ℂ^d` with its sheaf of holomorphic functions. -/
def IsSmooth (X : SourceReducedComplexSpace) : Prop :=
  ∀ x : X.obj.left, ∃ (d : ℕ) (V : Opens (ComplexModel d))
    (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) V ⟶ X.obj.left),
    LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ X.obj.hom = ambientPointMap d V ∧
      x ∈ range i.base

/-- A morphism `π : Y ⟶ X` of complex spaces is an *isomorphism over* `U ⊆ X` if an open
immersion `j` onto `π⁻¹ U` composes with `π` to an open immersion onto `U`, i.e. `π` restricts
to an isomorphism of the open subspaces `π⁻¹ U ≅ U`. -/
def IsIsoOver {X Y : SourceReducedComplexSpace} (π : Y ⟶ X) (U : Set X.obj.left) : Prop :=
  ∃ (V : LocallyRingedSpace) (j : V ⟶ Y.obj.left), LocallyRingedSpace.IsOpenImmersion j ∧
    range j.base = π.hom.left.base ⁻¹' U ∧
    LocallyRingedSpace.IsOpenImmersion (j ≫ π.hom.left) ∧ range (j ≫ π.hom.left).base = U

/-- A morphism `π : Y ⟶ X` of complex spaces is *proper bimeromorphic* if it is proper and an
isomorphism over the complement of a nowhere dense analytic subset `Z ⊆ X` whose preimage is
nowhere dense in `Y`. -/
def IsProperBimeromorphic {X Y : SourceReducedComplexSpace} (π : Y ⟶ X) : Prop :=
  IsProperMap π.hom.left.base ∧
    ∃ Z : Set X.obj.left, X.IsAnalyticSubset Z ∧ interior Z = ∅ ∧
      interior (π.hom.left.base ⁻¹' Z) = ∅ ∧ IsIsoOver π Zᶜ

/-- A *resolution* of `X` (`def:primdiv`): a proper bimeromorphic morphism `π : Y ⟶ X` from a
smooth complex space. -/
def IsResolution {X Y : SourceReducedComplexSpace} (π : Y ⟶ X) : Prop :=
  Y.IsSmooth ∧ IsProperBimeromorphic π

end SourceReducedComplexSpace

open SourceReducedComplexSpace

/-! ### Resolution of embedded compact complex spaces (`thm:res`, G11a) -/

section Embedded

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A closed complex submanifold is a smooth complex space. -/
theorem isSmooth_ofClosedAnalytic_of_isClosedSubmanifold {C : Set M}
    (hC : IsClosedSubmanifold n C) :
    (ofClosedAnalytic C
      (Hironaka.AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
        hC)).IsSmooth := by
  intro y
  obtain ⟨d, hd⟩ := hC.2 y.val y.property
  obtain ⟨V, i, hi, hp, hy⟩ := exists_native_chart (n := n) C hd
  exact ⟨d, V, i, hi, hp, hy⟩

variable {M' : Type} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] {W : Set M} {σ : M' → M} {E : List (Set M')}

/-- The resolution morphism of complex spaces `(W', 𝒪/𝓘_{W'}) ⟶ (W, 𝒪/𝓘_W)` of a resolution of
`W` by its strict transform. -/
def resolutionMorphism (hWa : IsComplexAnalyticSubset (n := n) W)
    (h : IsStrictTransformResolution n W σ E) :
    ofClosedAnalytic (strictTransform n σ W)
        (Hironaka.AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
          h.isClosedSubmanifold) ⟶ ofClosedAnalytic W hWa :=
  ObjectProperty.homMk (Over.homMk (resolutionMap h) (resolutionMap_point h))

theorem resolutionMorphism_left (hWa : IsComplexAnalyticSubset (n := n) W)
    (h : IsStrictTransformResolution n W σ E) :
    (resolutionMorphism hWa h).hom.left = resolutionMap h := rfl

/-- The resolution morphism is a resolution in the sense of `def:primdiv`. -/
theorem isResolution_resolutionMorphism [CompactSpace M] (hWa : IsComplexAnalyticSubset (n := n) W)
    (h : IsStrictTransformResolution n W σ E) : IsResolution (resolutionMorphism hWa h) := by
  refine ⟨isSmooth_ofClosedAnalytic_of_isClosedSubmanifold h.isClosedSubmanifold,
    resolutionMap_isProperMap h, (Subtype.val : W → M) ⁻¹' singularSet (n := n) W,
    isAnalyticSubset_preimage_val hWa
      (Hironaka.HironakaResolutionSpaceSingular.isComplexAnalyticSubset_singularSet
        hWa), ?_, ?_, ?_⟩
  · rw [interior_eq_empty_iff_dense_compl]
    exact dense_regular hWa
  · rw [interior_eq_empty_iff_dense_compl]
    exact dense_preimage_regular h
  · exact resolutionMap_isIsoOver h hWa.isClosed

/-- **Source `thm:res` for a closed analytic subspace of a compact complex manifold (G11a).**
Let `W` be a closed analytic subset of a compact complex manifold `M` (its irreducible
components may have different dimensions, and it may contain connected components of `M`) and
`X = (W, 𝒪_M/𝓘_W)` its reduced complex space.  There are a compact complex manifold `M'` and a
finite composition `σ : M' → M` of blowups with smooth nowhere dense centres lying over the
singular set of `W` whose strict transform `W'` resolves `W` (`IsStrictTransformResolution`),
and a resolution `π : Y ⟶ X` (`IsResolution`: `Y` smooth, `π` proper and an isomorphism over the
complement of a nowhere dense analytic subset with nowhere dense preimage), where `Y` is the
compact strict transform `(W', 𝒪/𝓘_{W'})`; `π` is surjective and equals `σ` on points. -/
theorem exists_resolution_ofClosedAnalytic [CompactSpace M] {W : Set M}
    (hWa : IsComplexAnalyticSubset (n := n) W) :
    ∃ (M' : Type) (_ : TopologicalSpace M') (_ : ChartedSpace (ComplexModel n) M')
      (_ : IsComplexManifold n M') (σ : M' → M),
      CompactSpace M' ∧ (∃ E : List (Set M'), IsStrictTransformResolution n W σ E) ∧
      IsBlowupSequence n M M' σ ∧
      (∀ y : M', σ y ∈ W \ singularSet (n := n) W → y ∈ strictTransform n σ W) ∧
      ∃ (hW' : IsComplexAnalyticSubset (n := n) (strictTransform n σ W))
        (π : ofClosedAnalytic (strictTransform n σ W) hW' ⟶ ofClosedAnalytic W hWa),
        CompactSpace (ofClosedAnalytic (strictTransform n σ W) hW').obj.left ∧
        IsResolution π ∧ Function.Surjective π.hom.left.base ∧
        ∀ y, (π.hom.left.base y).val = σ y.val := by
  obtain ⟨M', _, _, _, σ, E, hcpt, h⟩ := exists_isStrictTransformResolution_of_isAnalytic hWa
  refine ⟨M', inferInstance, inferInstance, inferInstance, σ, hcpt, ⟨E, h⟩, h.isBlowupSequence, ?_, _,
    resolutionMorphism hWa h, ?_, isResolution_resolutionMorphism hWa h,
    resolutionMap_surjective h, fun y => rfl⟩
  · intro y hy
    have hmem : y ∈ σ ⁻¹' (W \ singularSet (n := n) W) := hy
    rw [← h.inter_preimage_compl] at hmem
    exact hmem.1
  · change CompactSpace (strictTransform n σ W)
    exact isCompact_iff_compactSpace.mp h.isCompact_strictTransform

end Embedded


/-! ### Transport along isomorphisms -/

section Iso

namespace SourceReducedComplexSpace

/-- The isomorphism of locally ringed spaces underlying an isomorphism of complex spaces. -/
def isoLeft {X X' : SourceReducedComplexSpace} (e : X ≅ X') : X.obj.left ≅ X'.obj.left :=
  (Over.forget complexPoint).mapIso (sourceReducedComplexSpaceProperty.ι.mapIso e)

/-- The homeomorphism of underlying spaces of an isomorphism of complex spaces. -/
def isoHomeomorph {X X' : SourceReducedComplexSpace} (e : X ≅ X') : X.obj.left ≃ₜ X'.obj.left where
  toFun := (isoLeft e).hom.base
  invFun := (isoLeft e).inv.base
  left_inv x := by
    have hh := congrArg (fun k => k.base x) (isoLeft e).hom_inv_id
    exact hh
  right_inv x := by
    have hh := congrArg (fun k => k.base x) (isoLeft e).inv_hom_id
    exact hh
  continuous_toFun := (isoLeft e).hom.base.hom.continuous
  continuous_invFun := (isoLeft e).inv.base.hom.continuous

theorem isoHomeomorph_apply {X X' : SourceReducedComplexSpace} (e : X ≅ X') (x : X.obj.left) :
    isoHomeomorph e x = e.hom.hom.left.base x := rfl

theorem isoHomeomorph_symm_apply {X X' : SourceReducedComplexSpace} (e : X ≅ X')
    (x : X'.obj.left) : (isoHomeomorph e).symm x = e.inv.hom.left.base x := rfl

/-- Analytic subsets pull back to analytic subsets along isomorphisms of complex spaces. -/
theorem IsAnalyticSubset.preimage_iso {X X' : SourceReducedComplexSpace} (e : X ≅ X')
    {Z : Set X'.obj.left} (hZ : X'.IsAnalyticSubset Z) :
    X.IsAnalyticSubset (isoHomeomorph e ⁻¹' Z) := by
  intro x
  obtain ⟨e', ⟨c, hc⟩, A', hA', hpre⟩ := hZ (isoHomeomorph e x)
  let f : LocalEmbedding X :=
    { dim := e'.dim
      ambient := e'.ambient
      carrier := e'.carrier
      analytic := e'.analytic
      map := e'.map ≫ (isoLeft e).inv
      isOpenImmersion := by
        have := e'.isOpenImmersion
        infer_instance
      overPoint := by
        change (e'.map ≫ e.inv.hom.left) ≫ X.obj.hom = _
        rw [Category.assoc, Over.w e.inv.hom]
        exact e'.overPoint }
  have hto : ∀ c', f.toPoint c' = (isoHomeomorph e).symm (e'.toPoint c') := fun _ => rfl
  refine ⟨f, ⟨c, ?_⟩, A', hA', ?_⟩
  · rw [hto, hc]
    exact (isoHomeomorph e).symm_apply_apply x
  · rw [← hpre]
    ext c'
    simp only [mem_preimage, hto, Homeomorph.apply_symm_apply]

/-- Resolutions compose with isomorphisms of the target. -/
theorem IsResolution.comp_iso {X X' Y : SourceReducedComplexSpace} {π : Y ⟶ X'}
    (hπ : IsResolution π) (e : X ≅ X') : IsResolution (π ≫ e.inv) := by
  obtain ⟨hY, hprop, Z, hZa, hZint, hpint, V, j, hj, hrange, hj2, hrange2⟩ := hπ
  let h := isoHomeomorph e
  have hbase : (⇑(π ≫ e.inv).hom.left.base) = h.symm ∘ ⇑π.hom.left.base := rfl
  have hpre : ∀ S : Set X'.obj.left,
      (π ≫ e.inv).hom.left.base ⁻¹' (h ⁻¹' S) = π.hom.left.base ⁻¹' S := by
    intro S
    rw [hbase]
    ext y
    simp only [mem_preimage, Function.comp_apply, Homeomorph.apply_symm_apply]
  refine ⟨hY, ?_, h ⁻¹' Z, IsAnalyticSubset.preimage_iso e hZa, ?_, ?_, V, j, hj, ?_, ?_, ?_⟩
  · rw [hbase]
    exact h.symm.isProperMap.comp hprop
  · rw [← h.preimage_interior, hZint, preimage_empty]
  · rw [hpre]
    exact hpint
  · rw [← preimage_compl, hpre]
    exact hrange
  · change LocallyRingedSpace.IsOpenImmersion ((j ≫ π.hom.left) ≫ (isoLeft e).inv)
    have := hj2
    infer_instance
  · have hc : ⇑(j ≫ (π ≫ e.inv).hom.left).base = h.symm ∘ ⇑(j ≫ π.hom.left).base := rfl
    rw [hc, range_comp, hrange2, ← preimage_compl, h.image_symm]

end SourceReducedComplexSpace

open SourceReducedComplexSpace

/-- **Source `thm:res` for a complex space with a closed embedding into a compact complex
manifold (G11a).**  If the complex space `X` is isomorphic to the reduced closed subspace
`(W, 𝒪_M/𝓘_W)` on a closed analytic subset `W` of a compact complex manifold `M`, then `X` has
a resolution `π : Y ⟶ X` from a compact smooth complex space, induced by a finite composition
of blowups `σ : M' → M` with smooth centres (see `exists_resolution_ofClosedAnalytic`). -/
theorem exists_resolution_of_iso {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W)
    {X : SourceReducedComplexSpace} (e : X ≅ ofClosedAnalytic W hWa) :
    ∃ (Y : SourceReducedComplexSpace) (π : Y ⟶ X),
      CompactSpace Y.obj.left ∧ IsResolution π ∧ Function.Surjective π.hom.left.base := by
  obtain ⟨M', _, _, _, σ, -, -, -, -, hW', π, hcpt, hres, hsurj, -⟩ :=
    exists_resolution_ofClosedAnalytic hWa
  refine ⟨_, π ≫ e.inv, hcpt, hres.comp_iso e, ?_⟩
  change Function.Surjective ((isoHomeomorph e).symm ∘ π.hom.left.base)
  exact (isoHomeomorph e).symm.surjective.comp hsurj

end Iso

end

end Hironaka.Analytic.Unibranch
