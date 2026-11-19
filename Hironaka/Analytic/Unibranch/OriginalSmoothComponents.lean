import Hironaka.Analytic.Unibranch.OriginalSmoothDimension
import Mathlib.Topology.Connected.LocallyConnected

/-!
# The actual finite connected components of compact ORIGINAL smooth spaces

Local connectedness comes from the actual original smooth OI models. Native
compact/discrete component finiteness is reused. Every component object is the
literal original LRS restriction, with full inclusion and scalar map; compactness,
connectedness, smoothness and each component's dimension are derived.
Blueprint: `original-smooth-components.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalSmoothComponents

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceManifoldCharts
  HironakaReducedComplexAnalyticSpaces SourceReducedComplexSpace OriginalSmoothDimension

noncomputable section

variable {X : SourceReducedComplexSpace}

/-- The SAME original topology is locally connected, derived from genuine
smooth local-model OIs, without a fixed dimension or global native atlas. -/
theorem locallyConnectedSpace_of_isSmooth (h : X.IsSmooth) :
    LocallyConnectedSpace X.obj.left := by
  apply locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr
  intro x U hU
  obtain ⟨n, V, i, hi, _hp, v, hv⟩ := h x
  let : LocallyConnectedSpace V := ChartedSpace.locallyConnectedSpace (ComplexModel n) V
  have hpre : i.base ⁻¹' U ∈ 𝓝 v := by
    apply i.base.hom.continuous.continuousAt.preimage_mem_nhds
    rwa [hv]
  obtain ⟨W, hWU, hW, hvW, hWc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
      (inferInstance : LocallyConnectedSpace V) v _ hpre
  exact ⟨i.base '' W, image_subset_iff.mpr hWU,
    hi.base_open.isOpenMap W hW, ⟨v, hvW, hv⟩,
    hWc.image i.base i.base.hom.continuous.continuousOn⟩

/-- Native finite compact-discrete quotient theorem, on the ACTUAL connected
components of the SAME original point set. -/
theorem finite_connectedComponents [CompactSpace X.obj.left] (h : X.IsSmooth) :
    Finite (ConnectedComponents X.obj.left) := by
  let := locallyConnectedSpace_of_isSmooth h
  infer_instance

private theorem isOpenImmersion_lift {A B T : LocallyRingedSpace}
    (f : A ⟶ T) (g : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (hr : range g.base ⊆ range f.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift f g hr) := by
  let : IsIso (pullback.snd f g) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset f g hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

private theorem native_inclusion_point {n : ℕ} (V : Opens (ComplexModel n)) :
    ChartedSpace.locallyRingedSpaceMap (Subtype.val : V → ComplexModel n)
        (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n))) ≫
      ambientPointMap n (ComplexModel n) = ambientPointMap n V :=
  (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ, ComplexModel n))
    (IN := 𝓘(ℂ, ComplexModel n)) (IP := 𝓘(ℂ, ComplexModel 0))
    contMDiff_subtype_val contMDiff_const).symm

/-- Genuine native smooth local models of the literal ORIGINAL restriction,
with full scalar triangles. All restriction lifts are internally constructed. -/
theorem restriction_smooth_models (h : X.IsSmooth) (U : Opens X.obj.left)
    (x : (X.obj.left.restrict U.isOpenEmbedding)) :
    ∃ (n : ℕ) (V : Opens (ComplexModel n))
      (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) V ⟶
        X.obj.left.restrict U.isOpenEmbedding),
      LocallyRingedSpace.IsOpenImmersion i ∧
      i ≫ (X.obj.left.ofRestrict U.isOpenEmbedding ≫ X.obj.hom) = ambientPointMap n V ∧
        x ∈ range i.base := by
  obtain ⟨n, V, i, hi, hp, v, hv⟩ := h x.val
  let := hi
  let j := X.obj.left.ofRestrict U.isOpenEmbedding
  let Ω : Opens (ComplexModel n) :=
    ⟨(Subtype.val : V → ComplexModel n) '' (i.base ⁻¹' (U : Set X.obj.left)),
      V.isOpen.isOpenMap_subtype_val _ (U.isOpen.preimage i.base.hom.continuous)⟩
  let f := ChartedSpace.locallyRingedSpaceMap (Subtype.val : V → ComplexModel n)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n)))
  let g := ChartedSpace.locallyRingedSpaceMap (Subtype.val : Ω → ComplexModel n)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n)))
  have hr : range g.base ⊆ range f.base := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, _ha, haz⟩ := z.property
    exact ⟨a, haz⟩
  let L := LocallyRingedSpace.IsOpenImmersion.lift f g hr
  have hL : L ≫ f = g := LocallyRingedSpace.IsOpenImmersion.lift_fac f g hr
  let : LocallyRingedSpace.IsOpenImmersion L := isOpenImmersion_lift f g hr
  have hbaseL (z : Ω) : (L.base z).val = z.val :=
    congrArg (fun F => F.base z) hL
  have hLp : L ≫ ambientPointMap n V = ambientPointMap n Ω := by
    rw [← native_inclusion_point V, ← Category.assoc, hL]
    exact native_inclusion_point Ω
  let F := L ≫ i
  have hrF : range F.base ⊆ range j.base := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨i.base (L.base z), ?_⟩, rfl⟩
    obtain ⟨a, ha, haz⟩ := z.property
    have hLa : L.base z = a := Subtype.ext ((hbaseL z).trans haz.symm)
    change i.base (L.base z) ∈ U
    rw [hLa]
    exact ha
  let K := LocallyRingedSpace.IsOpenImmersion.lift j F hrF
  have hK : K ≫ j = F := LocallyRingedSpace.IsOpenImmersion.lift_fac j F hrF
  let : LocallyRingedSpace.IsOpenImmersion K := isOpenImmersion_lift j F hrF
  have hFp : F ≫ X.obj.hom = ambientPointMap n Ω := by
    rw [show F = L ≫ i from rfl, Category.assoc, hp]
    exact hLp
  have hKp : K ≫ (j ≫ X.obj.hom) = ambientPointMap n Ω := by
    rw [← Category.assoc, hK]
    exact hFp
  have hvU : i.base v ∈ U := hv.symm ▸ x.property
  let z : Ω := ⟨v.val, ⟨v, hvU, rfl⟩⟩
  have hLv : L.base z = v := Subtype.ext (hbaseL z)
  have hKz : (K.base z).val = i.base v := by
    have H := congrArg (fun G => G.base z) hK
    change (K.base z).val = i.base (L.base z) at H
    rwa [hLv] at H
  exact ⟨n, Ω, K, inferInstance, hKp, z, Subtype.ext (hKz.trans hv)⟩

section CompactRestrictions

variable [hcompact : CompactSpace X.obj.left]

/-- The SAME literal compact original open restriction, with all original
category topology and analytic-model clauses internally derived. -/
@[implicit_reducible]
def compactOpenRestriction (h : X.IsSmooth) (U : Opens X.obj.left)
    (hU : IsClosed (U : Set X.obj.left)) : SourceReducedComplexSpace := by
  let := X.property.1
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  let T := X.obj.left.restrict U.isOpenEmbedding
  let j := X.obj.left.ofRestrict U.isOpenEmbedding
  refine ⟨Over.mk (j ≫ X.obj.hom), ?_, ?_, ?_⟩
  · change T2Space U
    infer_instance
  · change ParacompactSpace U
    infer_instance
  intro x
  obtain ⟨n, V, i, hi, hp, v, hv⟩ := restriction_smooth_models h U x
  let Q := actualSubspaceUnivIso (n := n) (M := V)
  refine ⟨n, V, univ, isComplexAnalyticSubset_univ (n := n), Q.hom ≫ i, ?_, ?_, ?_⟩
  · exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ Q.hom (inferInstance) i hi
  · change (Q.hom ≫ i) ≫
      (X.obj.left.ofRestrict U.isOpenEmbedding ≫ X.obj.hom) =
        subspacePointMap (n := n) (univ : Set V)
    rw [Category.assoc, hp]
    rfl
  · exact ⟨⟨v, mem_univ v⟩, hv⟩

/-- The FULL original inclusion of the same literal restriction. -/
def compactOpenRestrictionInclusion (h : X.IsSmooth) (U : Opens X.obj.left)
    (hU : IsClosed (U : Set X.obj.left)) : compactOpenRestriction h U hU ⟶ X :=
  ObjectProperty.homMk (Over.homMk (X.obj.left.ofRestrict U.isOpenEmbedding) rfl)

instance compactOpenRestrictionInclusion_isOpenImmersion (h : X.IsSmooth)
    (U : Opens X.obj.left) (hU : IsClosed (U : Set X.obj.left)) :
    LocallyRingedSpace.IsOpenImmersion (compactOpenRestrictionInclusion h U hU).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion (X.obj.left.ofRestrict U.isOpenEmbedding)
  infer_instance

include hcompact in
theorem compactOpenRestriction_isSmooth (h : X.IsSmooth) (U : Opens X.obj.left)
    (hU : IsClosed (U : Set X.obj.left)) : (compactOpenRestriction h U hU).IsSmooth :=
  restriction_smooth_models h U

theorem compactSpace_compactOpenRestriction (h : X.IsSmooth) (U : Opens X.obj.left)
    (hU : IsClosed (U : Set X.obj.left)) : CompactSpace (compactOpenRestriction h U hU).obj.left := by
  change CompactSpace U
  exact isCompact_iff_compactSpace.mp hU.isCompact

end CompactRestrictions

/-- Canonical actual component fibre on the original point set. -/
def componentSet (c : ConnectedComponents X.obj.left) : Set X.obj.left :=
  ConnectedComponents.mk ⁻¹' {c}

theorem componentSet_eq_connectedComponent (x : X.obj.left) :
    componentSet (ConnectedComponents.mk x) = connectedComponent x :=
  connectedComponents_preimage_singleton

theorem component_isClopen (h : X.IsSmooth) (c : ConnectedComponents X.obj.left) :
    IsClopen (componentSet c) := by
  let := locallyConnectedSpace_of_isSmooth h
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [componentSet_eq_connectedComponent]
  exact isClopen_connectedComponent

theorem component_isConnected (c : ConnectedComponents X.obj.left) :
    IsConnected (componentSet c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [componentSet_eq_connectedComponent]
  exact isConnected_connectedComponent

/-- Actual component open, derived from original smoothness. -/
def componentOpen (h : X.IsSmooth) (c : ConnectedComponents X.obj.left) : Opens X.obj.left :=
  ⟨componentSet c, (component_isClopen h c).2⟩

section Components

variable [hcompact : CompactSpace X.obj.left]

/-- The SAME literal original LRS component restriction, internally an original object. -/
@[implicit_reducible]
def componentObject (h : X.IsSmooth) (c : ConnectedComponents X.obj.left) :
    SourceReducedComplexSpace :=
  compactOpenRestriction h (componentOpen h c) (component_isClopen h c).1

/-- The entire actual component restriction inclusion in the ORIGINAL category. -/
def componentInclusion (h : X.IsSmooth) (c : ConnectedComponents X.obj.left) :
    componentObject h c ⟶ X :=
  compactOpenRestrictionInclusion h (componentOpen h c) (component_isClopen h c).1

instance componentInclusion_isOpenImmersion (h : X.IsSmooth)
    (c : ConnectedComponents X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (componentInclusion h c).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion
    (X.obj.left.ofRestrict (componentOpen h c).isOpenEmbedding)
  infer_instance

include hcompact in
theorem componentInclusion_range (h : X.IsSmooth) (c : ConnectedComponents X.obj.left) :
    range (componentInclusion h c).hom.left.base = componentSet c :=
  Subtype.range_coe

include hcompact in
theorem componentInclusion_jointly_surjective (h : X.IsSmooth) (x : X.obj.left) :
    ∃ (c : ConnectedComponents X.obj.left) (y : (componentObject h c).obj.left),
      (componentInclusion h c).hom.left.base y = x :=
  ⟨ConnectedComponents.mk x, ⟨x, rfl⟩, rfl⟩

omit hcompact in
theorem componentSet_pairwise_disjoint :
    Pairwise (fun c d : ConnectedComponents X.obj.left => Disjoint (componentSet c) (componentSet d)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro x hc hd
  exact hcd (hc.symm.trans hd)

theorem compactSpace_componentObject (h : X.IsSmooth) (c : ConnectedComponents X.obj.left) :
    CompactSpace (componentObject h c).obj.left :=
  compactSpace_compactOpenRestriction h (componentOpen h c) (component_isClopen h c).1

include hcompact in
theorem connectedSpace_componentObject (h : X.IsSmooth) (c : ConnectedComponents X.obj.left) :
    ConnectedSpace (componentObject h c).obj.left := by
  change ConnectedSpace (componentSet c)
  exact isConnected_iff_connectedSpace.mp (component_isConnected c)

theorem componentObject_isSmooth (h : X.IsSmooth) (c : ConnectedComponents X.obj.left) :
    (componentObject h c).IsSmooth :=
  compactOpenRestriction_isSmooth h (componentOpen h c) (component_isClopen h c).1

/-- EACH actual original component has its OWN internally derived uniform
dimension; different components are not assumed to have the same dimension. -/
theorem component_uniform_smooth_models (h : X.IsSmooth) (c : ConnectedComponents X.obj.left) :
    ∃ n : ℕ, ∀ x : (componentObject h c).obj.left, ∃ (V : Opens (ComplexModel n))
      (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) V ⟶ (componentObject h c).obj.left),
      LocallyRingedSpace.IsOpenImmersion i ∧
      i ≫ (componentObject h c).obj.hom = ambientPointMap n V ∧ x ∈ range i.base := by
  let := connectedSpace_componentObject h c
  exact exists_uniform_smooth_models (componentObject_isSmooth h c)

end Components

end

end Hironaka.Analytic.Unibranch.OriginalSmoothComponents
