import Hironaka.Resolution.HironakaResolutionSpace
import Hironaka.Resolution.HironakaActualAnalyticSubspaceManifoldCharts
import Hironaka.Analytic.AdmissibleBlowupHolomorphicInverse
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Blowup.BlowupRestrictOpen

/-!
# The resolution of goal G11a as a morphism of reduced complex spaces

Blueprint: `blueprint/src/hironaka-g11-resolution.tex` (goal G11, milestone G11a).

For a complex manifold `M` (in `Type`) and a closed analytic subset `C ⊆ M`, the reduced closed
subspace `(C, 𝒪_M / 𝓘_C)` is `actualSubspaceLocallyRingedSpace C`.  This file proves:

* `exists_model_chart`, `closedAnalyticSpace`: the reduced closed subspace on a closed analytic
  subset of a complex manifold is a reduced complex analytic space: every point lies in the image of
  an open immersion over the complex point of an embedded model `(Ω, C')`, `Ω ⊆ ℂ^n` open and
  `C' ⊆ Ω` closed analytic (built from a chart of `M`);
* `exists_native_chart`: at a point where `C` is a submanifold of dimension `d`, the reduced
  closed subspace contains an open subspace isomorphic, over the complex point, to an open subset
  of `ℂ^d` with its sheaf of holomorphic functions;
* for a resolution `σ : M' → M` of `W` by its strict transform `W'`
  (`HironakaResolutionSpace.IsStrictTransformResolution`):
  `resolutionMap : (W', 𝒪/𝓘_{W'}) ⟶ (W, 𝒪/𝓘_W)` is a morphism of locally ringed spaces over the
  complex point (`resolutionMap_point`), surjective and proper when `M` is compact, and an
  isomorphism over the regular part `W \ W_sing` (`resolutionMap_isIsoOver`): the open
  subspace `W' ∩ σ⁻¹ (M \ W_sing)` is carried isomorphically onto the open subspace
  `W \ W_sing` (`regularIso`, `regularIso_comm`).  The regular part is dense in `W` and its
  preimage is dense in `W'` (`dense_regular`, `dense_preimage_regular`).

Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaResolutionSpaceComplex

open Hironaka.BlowupSequences
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceManifoldCharts HironakaActualFlatCoordinateIntrinsicHS
  BlowupFlatCoordinates HironakaResolutionSpace
open HironakaEmbeddedAnalytic (singularSet isClosed_singularSet)

noncomputable section

/-! ### Two elementary facts on the subspace maps -/

section Basic

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace N] [ChartedSpace (ComplexModel m) N]
  [IsComplexManifold m N]

/-- On points, the subspace map induced by `f` is `f`. -/
theorem actualSubspaceMap_base_val {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) (x : C) :
    ((actualSubspaceMap hf hCD).base x).val = f x.val := rfl

/-- The subspace map depends only on the underlying function. -/
theorem actualSubspaceMap_congr {f g : M → N} (hfg : f = g)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ g)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) (hCD' : ∀ x ∈ C, g x ∈ D) :
    actualSubspaceMap hf hCD = actualSubspaceMap hg hCD' := by
  subst hfg
  rfl

/-- The image of the open restriction `C ∩ U → C` consists of the points of `C` in `U`. -/
theorem range_actualOpenSubspaceMap (C : Set M) (U : Opens M) :
    range (actualOpenSubspaceMap (n := n) C U).base = {c : C | c.val ∈ U} := by
  ext c
  constructor
  · rintro ⟨y, rfl⟩
    exact y.val.property
  · intro hc
    exact ⟨⟨⟨c.val, hc⟩, c.property⟩, rfl⟩

/-- Composing with an isomorphism does not change the image. -/
theorem range_iso_hom_comp_base {X Y Z : LocallyRingedSpace} (e : X ≅ Y) (j : Y ⟶ Z) :
    range (e.hom ≫ j).base = range j.base := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom.base x, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv.base y, ?_⟩
    have hh := congrArg (fun k => k.base y) e.inv_hom_id
    change e.hom.base (e.inv.base y) = y at hh
    change j.base (e.hom.base (e.inv.base y)) = j.base y
    rw [hh]

end Basic

/-! ### Local models of a closed analytic subset of a manifold -/

section Models

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The identity local holomorphic equivalence on the target of the preferred chart at `x`. -/
def chartTargetEquiv (x : M) :
    LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x) where
  source := (chartAt (ComplexModel n) x).target
  target := (chartAt (ComplexModel n) x).target
  isOpen_source := (chartAt (ComplexModel n) x).open_target
  isOpen_target := (chartAt (ComplexModel n) x).open_target
  center_mem_source := (chartAt (ComplexModel n) x).map_source (mem_chart_source _ x)
  toFun := id
  invFun := id
  toFun_holomorphic := differentiableOn_id
  invFun_holomorphic := differentiableOn_id
  mapsTo_toFun := mapsTo_id _
  mapsTo_invFun := mapsTo_id _
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

/-- The chart domain at `x`, an open neighbourhood of `x` in `M`. -/
def chartDomain (x : M) : Opens M :=
  ⟨flatDomain (chartTargetEquiv (n := n) x), isOpen_flatDomain _⟩

/-- The chart image at `x`, an open subset of `ℂ^n`. -/
def chartImage (x : M) : Opens (ComplexModel n) :=
  ⟨(chartTargetEquiv (n := n) x).target, (chartTargetEquiv (n := n) x).isOpen_target⟩

theorem mem_chartDomain (x : M) : x ∈ chartDomain (n := n) x :=
  mem_flatDomain_self (chartTargetEquiv (n := n) x)

/-- The chart at `x` as a biholomorphism of its domain onto its image. -/
def chartDiffeo (x : M) :
    chartDomain (n := n) x ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ chartImage (n := n) x :=
  actualFlatCoordinateDiffeomorph (chartTargetEquiv (n := n) x) subset_rfl

/-- The coordinate image of `C` in the chart at `x`. -/
def chartTrace (C : Set M) (x : M) : Set (chartImage (n := n) x) :=
  {u | (((chartDiffeo (n := n) x).symm u : chartDomain (n := n) x) : M) ∈ C}

theorem isComplexAnalyticSubset_chartTrace {C : Set M} (hC : IsComplexAnalyticSubset (n := n) C)
    (x : M) : IsComplexAnalyticSubset (n := n) (chartTrace (n := n) C x) := by
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun u : chartImage (n := n) x =>
        (((chartDiffeo (n := n) x).symm u : chartDomain (n := n) x) : M)) :=
    contMDiff_subtype_val.comp (chartDiffeo (n := n) x).symm.contMDiff
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hC

/-- The chart open immersion of the embedded model `(chartImage x, chartTrace C x)` into the
reduced closed subspace on `C`. -/
def chartModelMap (C : Set M) (x : M) :
    (modelOver (chartImage (n := n) x) (chartTrace (n := n) C x)).left ⟶
      actualSubspaceLocallyRingedSpace (n := n) C :=
  (actualSubspaceBiholomorphicIso (chartDiffeo (n := n) x).symm (chartTrace (n := n) C x)
      ((Subtype.val : chartDomain (n := n) x → M) ⁻¹' C) (fun _ => Iff.rfl)).hom ≫
    actualOpenSubspaceMap (n := n) C (chartDomain (n := n) x)

instance chartModelMap_isOpenImmersion (C : Set M) (x : M) :
    LocallyRingedSpace.IsOpenImmersion (chartModelMap (n := n) C x) := by
  unfold chartModelMap
  infer_instance

theorem chartModelMap_point (C : Set M) (x : M) :
    chartModelMap (n := n) C x ≫ subspacePointMap (n := n) C =
      (modelOver (chartImage (n := n) x) (chartTrace (n := n) C x)).hom := by
  unfold chartModelMap
  change _ ≫ subspacePointMap (n := n) C = subspacePointMap (n := n) _
  rw [Category.assoc, actualOpenSubspaceMap,
    actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)]
  exact actualSubspaceMap_point (chartDiffeo (n := n) x).symm.contMDiff _

theorem mem_range_chartModelMap (C : Set M) {x : M} (hx : x ∈ C) :
    (⟨x, hx⟩ : C) ∈ range (chartModelMap (n := n) C x).base := by
  let p : chartDomain (n := n) x := ⟨x, mem_chartDomain (n := n) x⟩
  have hp : (chartDiffeo (n := n) x).symm (chartDiffeo (n := n) x p) = p :=
    (chartDiffeo (n := n) x).symm_apply_apply p
  have hc : chartDiffeo (n := n) x p ∈ chartTrace (n := n) C x := by
    change (((chartDiffeo (n := n) x).symm (chartDiffeo (n := n) x p) : chartDomain (n := n) x) :
      M) ∈ C
    rw [hp]
    exact hx
  refine ⟨⟨chartDiffeo (n := n) x p, hc⟩, ?_⟩
  apply Subtype.ext
  change (((chartDiffeo (n := n) x).symm (chartDiffeo (n := n) x p) : chartDomain (n := n) x) :
    M) = x
  rw [hp]

/-- **Local models.**  Every point of a closed analytic subset `C` of a complex manifold lies in
the image of an open immersion, over the complex point, of an embedded model `(Ω, C')` with
`Ω ⊆ ℂ^n` open and `C' ⊆ Ω` closed analytic, into the reduced closed subspace on `C`. -/
theorem exists_model_chart {C : Set M} (hC : IsComplexAnalyticSubset (n := n) C) (c : C) :
    ∃ (U : Opens (ComplexModel n)) (C' : Set U), IsComplexAnalyticSubset (n := n) C' ∧
      ∃ i : (modelOver U C').left ⟶ actualSubspaceLocallyRingedSpace (n := n) C,
        LocallyRingedSpace.IsOpenImmersion i ∧
        i ≫ subspacePointMap (n := n) C = (modelOver U C').hom ∧ c ∈ range i.base :=
  ⟨chartImage (n := n) c.val, chartTrace (n := n) C c.val,
    isComplexAnalyticSubset_chartTrace hC c.val, chartModelMap (n := n) C c.val, inferInstance,
    chartModelMap_point (n := n) C c.val, mem_range_chartModelMap (n := n) C c.property⟩

/-- The reduced closed subspace on a closed analytic subset of a complex manifold has the local
analytic-model property (with Hausdorffness and second countability). -/
theorem hasAnalyticCharts_subspace {C : Set M} (hC : IsComplexAnalyticSubset (n := n) C) :
    hasAnalyticCharts (Over.mk (subspacePointMap (n := n) C)) := by
  refine ⟨?_, ?_, ?_⟩
  · change T2Space C
    infer_instance
  · change SecondCountableTopology C
    infer_instance
  intro x
  exact ⟨n, exists_model_chart hC x⟩

/-- **The reduced closed subspace on a closed analytic subset of a complex manifold**, as an
object of the category of reduced complex analytic spaces. -/
def closedAnalyticSpace (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C) :
    ReducedComplexAnalyticSpace :=
  ⟨Over.mk (subspacePointMap (n := n) C), hasAnalyticCharts_subspace hC⟩

/-- **Native charts at regular points.**  At a point where `C` is a complex submanifold of
dimension `d`, the reduced closed subspace on `C` contains an open subspace isomorphic, over the
complex point, to an open subset of `ℂ^d` with its sheaf of holomorphic functions. -/
theorem exists_native_chart (C : Set M) {x : M} {d : ℕ} (hreg : RegularAtDim (n := n) C x d) :
    ∃ (V : Opens (ComplexModel d))
      (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) V ⟶
        actualSubspaceLocallyRingedSpace (n := n) C),
      LocallyRingedSpace.IsOpenImmersion i ∧
      i ≫ subspacePointMap (n := n) C = ambientPointMap d V ∧
      (⟨x, hreg.2.1⟩ : C) ∈ range i.base := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hreg.1
  exact exists_actual_regular_subspace_manifold_chart C x hreg

end Models

/-! ### The resolution morphism -/

section Resolution

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {M' : Type} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] {W : Set M} {σ : M' → M} {E : List (Set M')}

/-- The morphism of reduced closed subspaces `W' → W` induced by a resolution `σ` of `W` by its
strict transform `W'`. -/
def resolutionMap (h : IsStrictTransformResolution n W σ E) :
    actualSubspaceLocallyRingedSpace (n := n) (strictTransform n σ W) ⟶
      actualSubspaceLocallyRingedSpace (n := n) W :=
  actualSubspaceMap h.contMDiff (fun _ hy => h.strictTransform_subset_preimage hy)

theorem resolutionMap_point (h : IsStrictTransformResolution n W σ E) :
    resolutionMap h ≫ subspacePointMap (n := n) W =
      subspacePointMap (n := n) (strictTransform n σ W) :=
  actualSubspaceMap_point _ _

theorem resolutionMap_base_val (h : IsStrictTransformResolution n W σ E)
    (y : strictTransform n σ W) : ((resolutionMap h).base y).val = σ y.val := rfl

/-- The resolution morphism is surjective. -/
theorem resolutionMap_surjective (h : IsStrictTransformResolution n W σ E) :
    Function.Surjective (resolutionMap h).base := by
  intro x
  have hx : x.val ∈ σ '' strictTransform n σ W := by
    rw [h.image_eq]
    exact x.property
  obtain ⟨y, hy, hyx⟩ := hx
  exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

/-- Over a compact base the resolution morphism is proper. -/
theorem resolutionMap_isProperMap [CompactSpace M] (h : IsStrictTransformResolution n W σ E) :
    IsProperMap (resolutionMap h).base := by
  have : CompactSpace (strictTransform n σ W) :=
    isCompact_iff_compactSpace.mp h.isCompact_strictTransform
  change IsProperMap (fun y : strictTransform n σ W => (⟨σ y.val, _⟩ : W))
  exact ((h.contMDiff.continuous.comp continuous_subtype_val).subtype_mk _).isProperMap

variable (n) in
/-- The regular open set `M \ W_sing`. -/
def regularOpen {W : Set M} (hW : IsClosed W) : Opens M :=
  ⟨(singularSet (n := n) W)ᶜ, (isClosed_singularSet (n := n) hW).isOpen_compl⟩

variable (n) in
/-- Its preimage `σ⁻¹ (M \ W_sing)`. -/
def regularPreimageOpen (hW : IsClosed W) (σ : M' → M) (hσ : Continuous σ) : Opens M' :=
  ⟨σ ⁻¹' (singularSet (n := n) W)ᶜ, (isClosed_singularSet (n := n) hW).isOpen_compl.preimage hσ⟩

/-- Over the regular open set `σ` is a biholomorphism. -/
def regularBiholomorphism (h : IsStrictTransformResolution n W σ E) (hW : IsClosed W) :
    regularPreimageOpen n hW σ h.contMDiff.continuous ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      regularOpen n hW :=
  let hs := AdmissibleBlowupHolomorphicInverse.exists_section_compl (isClosed_singularSet (n := n) hW)
    h.admissible
  let s := Classical.choose hs
  have hspec := Classical.choose_spec hs
  have hsσ : ∀ x : regularOpen n hW, σ (s x) = x.val := fun x => congrFun hspec.2.1 x
  { toFun := fun y => ⟨σ y.val, y.property⟩
    invFun := fun x => ⟨s x, by
      change σ (s x) ∈ (singularSet (n := n) W)ᶜ
      rw [hsσ x]
      exact x.property⟩
    left_inv := fun y => Subtype.ext (hspec.2.2 y.val y.property)
    right_inv := fun x => Subtype.ext (hsσ x)
    contMDiff_toFun :=
      BlowupRestrictOpen.contMDiff_opens_mk (h.contMDiff.comp contMDiff_subtype_val)
        (fun y => y.property)
    contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk hspec.1 (fun x => by
      change σ (s x) ∈ (singularSet (n := n) W)ᶜ
      rw [hsσ x]
      exact x.property) }

theorem regularBiholomorphism_val (h : IsStrictTransformResolution n W σ E) (hW : IsClosed W)
    (y : regularPreimageOpen n hW σ h.contMDiff.continuous) :
    ((regularBiholomorphism h hW y : regularOpen n hW) : M) = σ y.val := rfl

/-- Over the regular open set, `W'` and `σ⁻¹ W` agree. -/
theorem mem_strictTransform_iff (h : IsStrictTransformResolution n W σ E) (hW : IsClosed W)
    (y : regularPreimageOpen n hW σ h.contMDiff.continuous) :
    y.val ∈ strictTransform n σ W ↔ σ y.val ∈ W := by
  constructor
  · intro hy
    exact h.strictTransform_subset_preimage hy
  · intro hy
    have hmem : y.val ∈ σ ⁻¹' (W \ singularSet (n := n) W) := ⟨hy, y.property⟩
    rw [← h.inter_preimage_compl] at hmem
    exact hmem.1

/-- **The isomorphism over the regular part**: `σ` identifies the open subspace
`W' ∩ σ⁻¹ (M \ W_sing)` of `W'` with the open subspace `W \ W_sing` of `W`. -/
def regularIso (h : IsStrictTransformResolution n W σ E) (hW : IsClosed W) :
    actualSubspaceLocallyRingedSpace (n := n)
        ((Subtype.val : regularPreimageOpen n hW σ h.contMDiff.continuous → M') ⁻¹'
          strictTransform n σ W) ≅
      actualSubspaceLocallyRingedSpace (n := n)
        ((Subtype.val : regularOpen n hW → M) ⁻¹' W) :=
  actualSubspaceBiholomorphicIso (regularBiholomorphism h hW) _ _
    (fun y => mem_strictTransform_iff h hW y)

/-- The isomorphism over the regular part is the restriction of the resolution morphism. -/
theorem regularIso_comm (h : IsStrictTransformResolution n W σ E) (hW : IsClosed W) :
    actualOpenSubspaceMap (n := n) (strictTransform n σ W)
        (regularPreimageOpen n hW σ h.contMDiff.continuous) ≫ resolutionMap h =
      (regularIso h hW).hom ≫ actualOpenSubspaceMap (n := n) W (regularOpen n hW) := by
  unfold actualOpenSubspaceMap resolutionMap regularIso actualSubspaceBiholomorphicIso
  dsimp only
  rw [← actualSubspaceMap_comp, ← actualSubspaceMap_comp]

/-- **`σ` is an isomorphism over the regular part.**  The open immersion of the open subspace
`W' ∩ σ⁻¹ (M \ W_sing)` into `W'`, with image the preimage of `W \ W_sing`, composes with the
resolution morphism to an open immersion with image `W \ W_sing`. -/
theorem resolutionMap_isIsoOver (h : IsStrictTransformResolution n W σ E) (hW : IsClosed W) :
    ∃ (V : LocallyRingedSpace)
      (j : V ⟶ actualSubspaceLocallyRingedSpace (n := n) (strictTransform n σ W)),
      LocallyRingedSpace.IsOpenImmersion j ∧
      range j.base = (resolutionMap h).base ⁻¹' {x : W | x.val ∉ singularSet (n := n) W} ∧
      LocallyRingedSpace.IsOpenImmersion (j ≫ resolutionMap h) ∧
      range (j ≫ resolutionMap h).base = {x : W | x.val ∉ singularSet (n := n) W} := by
  refine ⟨_, actualOpenSubspaceMap (n := n) (strictTransform n σ W)
    (regularPreimageOpen n hW σ h.contMDiff.continuous), inferInstance, ?_, ?_, ?_⟩
  · rw [range_actualOpenSubspaceMap]
    rfl
  · rw [regularIso_comm h hW]
    infer_instance
  · rw [regularIso_comm h hW, range_iso_hom_comp_base, range_actualOpenSubspaceMap]
    rfl

/-- The regular part is dense in `W`. -/
theorem dense_regular {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W) :
    Dense {x : W | x.val ∉ singularSet (n := n) W} := by
  rw [dense_iff_closure_eq, eq_univ_iff_forall]
  intro x
  rw [closure_subtype]
  have hx := subset_closure_diff_singularSet hWa x.property
  refine closure_mono ?_ hx
  rintro _ ⟨hyW, hyS⟩
  exact ⟨⟨_, hyW⟩, hyS, rfl⟩

/-- The preimage of the regular part is dense in `W'`. -/
theorem dense_preimage_regular (h : IsStrictTransformResolution n W σ E) :
    Dense ((resolutionMap h).base ⁻¹' {x : W | x.val ∉ singularSet (n := n) W}) := by
  rw [dense_iff_closure_eq, eq_univ_iff_forall]
  intro y
  rw [closure_subtype]
  have hy := h.strictTransform_subset_closure y.property
  refine closure_mono ?_ hy
  rintro _ ⟨hyW, hyS⟩
  exact ⟨⟨_, hyW⟩, hyS, rfl⟩

/-- The strict transform is smooth: every point of the reduced closed subspace on `W'` has a
native chart of some dimension. -/
theorem exists_native_chart_strictTransform (h : IsStrictTransformResolution n W σ E)
    (y : strictTransform n σ W) :
    ∃ (d : ℕ) (V : Opens (ComplexModel d))
      (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) V ⟶
        actualSubspaceLocallyRingedSpace (n := n) (strictTransform n σ W)),
      LocallyRingedSpace.IsOpenImmersion i ∧
      i ≫ subspacePointMap (n := n) (strictTransform n σ W) = ambientPointMap d V ∧
      y ∈ range i.base := by
  obtain ⟨d, hd⟩ := h.isClosedSubmanifold.2 y.val y.property
  obtain ⟨V, i, hi, hp, hy⟩ := exists_native_chart (n := n) (strictTransform n σ W) hd
  exact ⟨d, V, i, hi, hp, hy⟩

end Resolution

end

end Hironaka.HironakaResolutionSpaceComplex
