import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundAffine
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberDimension
import DeJongAlterations.Geometry.FiberDimensionGenericRestriction

/-!
# Actual component and generic-dimension transport through affine neighborhoods

The topological comparisons use original open immersions and actual scheme
fibers. The field-dimension formula shows that a nonempty affine source-open
generic fiber retains the full actual generic dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundLocality

open FiberDimension FiberDimensionGenericFinite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual homeomorphisms preserve componentwise lower bounds. -/
theorem componentDimension_lowerBound_of_homeomorph
    {T U : Type u} [TopologicalSpace T] [TopologicalSpace U]
    (e : T ≃ₜ U) (d : WithBot ℕ∞)
    (h : ∀ C : Set T, C ∈ irreducibleComponents T → d ≤ topologicalKrullDim C)
    (Z : Set U) (hZ : Z ∈ irreducibleComponents U) : d ≤ topologicalKrullDim Z := by
  let C : Set T := e ⁻¹' Z
  have hC : C ∈ irreducibleComponents T := by
    apply preimage_mem_irreducibleComponents hZ e.isOpenEmbedding
    obtain ⟨z, hz⟩ := hZ.1.nonempty
    exact ⟨z, hz, e.symm z, e.apply_symm_apply z⟩
  let eZ : C ≃ₜ Z := e.isEmbedding.homeomorphOfSubsetRange
    (fun z _ ↦ e.surjective z)
  exact (h C hC).trans (IsHomeomorph.topologicalKrullDim_eq _ eZ.isHomeomorph).le

/-- An actual nonempty affine open immersion into an integral finite-type field
scheme preserves its full dimension. -/
theorem topologicalKrullDim_eq_of_affine_openImmersion
    {k : Type u} [Field k] {X V : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (i : V ⟶ X) [IsOpenImmersion i] [IsAffine V] [Nonempty V] :
    topologicalKrullDim V = topologicalKrullDim X := by
  let U : X.Opens := i.opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange i
  let : Nonempty U := ⟨⟨i (Classical.choice ‹Nonempty V›), _, rfl⟩⟩
  obtain ⟨n, hdim, htr⟩ := FunctionFieldDimension.exists_dimension_and_trdeg p
  have hd := FunctionFieldDimension.affineSections_dimension_eq p ⟨U, hU⟩ n htr
  let e : V ≅ Spec Γ(X, U) := i.isoOpensRange ≪≫ hU.isoSpec
  exact ((IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U))).trans (hd.trans hdim.symm)

/-- The original generic dimension is unchanged on an actual nonempty affine
source chart over an affine integral base. -/
theorem genericFiberDimension_eq_of_affine_openImmersion
    {V X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f]
    (i : V ⟶ X) [IsOpenImmersion i] [IsAffine V] [Nonempty V] :
    fiberDimension (i ≫ f) (genericPoint Y) = fiberDimension f (genericPoint Y) := by
  let : IsIntegral V := isIntegral_of_isOpenImmersion i
  let : IsDominant i := ⟨i.isOpenEmbedding.isOpen_range.dense
    ⟨i (Classical.choice ‹Nonempty V›), _, rfl⟩⟩
  let : IsIntegral (f.fiber (genericPoint Y)) := GenericFiberIntegral.genericFiber_isIntegral f
  let : IsIntegral ((i ≫ f).fiber (genericPoint Y)) :=
    GenericFiberIntegral.genericFiber_isIntegral (i ≫ f)
  let : IsAffineHom (i ≫ f) := isAffineHom_of_isAffine _
  let : IsAffine ((i ≫ f).fiber (genericPoint Y)) := by
    change IsAffine (CategoryTheory.Limits.pullback _ _)
    infer_instance
  let j := fiberProjection i f (genericPoint Y)
  let : IsOpenImmersion j := by
    unfold j fiberProjection
    infer_instance
  let : LocallyOfFiniteType (f.fiberToSpecResidueField (genericPoint Y)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact topologicalKrullDim_eq_of_affine_openImmersion
    (f.fiberToSpecResidueField (genericPoint Y)) j

/-- The actual componentwise lower bound is invariant under an actual arrow isomorphism. -/
theorem everyFiberComponentDimensionGEGeneric_of_arrowIso
    {X Y X' Y' : Scheme.{u}} [IsIntegral Y] [IsIntegral Y']
    {f : X ⟶ Y} {g : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk g)
    (hg : EveryFiberComponentDimensionGEGeneric g) : EveryFiberComponentDimensionGEGeneric f := by
  intro s Z hZ
  let eY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  have hη : eY.hom (genericPoint Y) = genericPoint Y' := genericPoint_map_of_isDominant eY.hom
  have hgen := fiberDimension_eq_of_arrowIso e (genericPoint Y)
  change fiberDimension f (genericPoint Y) = fiberDimension g (eY.hom (genericPoint Y)) at hgen
  rw [hη] at hgen
  rw [hgen]
  exact componentDimension_lowerBound_of_homeomorph (fiberHomeoOfArrowIso e s).symm _
    (hg (eY.hom s)) Z hZ

/-- Source 2.7(c) for arbitrary actual affine integral schemes. -/
theorem everyFiberComponentDimensionGEGeneric_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    EveryFiberComponentDimensionGEGeneric f := by
  let R : Type u := Γ(Y, ⊤)
  let A : Type u := Γ(X, ⊤)
  let : Algebra R A := f.appTop.hom.toAlgebra
  have : IsDomain R := inferInstance
  have : IsDomain A := inferInstance
  have : IsAffineHom f := isAffineHom_of_isAffine f
  have : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have hinj : Function.Injective (algebraMap R A) := by
    change Function.Injective f.appTop.hom
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using f.app_injective ⊤
  have : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance)
  exact everyFiberComponentDimensionGEGeneric_of_arrowIso (arrowIsoSpecΓOfIsAffine f)
    (FiberDimensionComponentLowerBoundAffine.everyFiberComponentDimensionGEGeneric_specMap R A hinj)


/-- Actual affine source neighborhoods prove every fiber-component lower bound
over an affine integral base, without a chosen source cover. -/
theorem everyFiberComponentDimensionGEGeneric_of_isAffine_target
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    EveryFiberComponentDimensionGEGeneric f := by
  intro s Z hZ
  obtain ⟨z, hz⟩ := hZ.1.nonempty
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := f.fiberι s z) (U := (⊤ : X.Opens)) (by trivial)
  let : IsAffine V.toScheme := hV
  let : Nonempty V.toScheme := ⟨⟨f.fiberι s z, hxV⟩⟩
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpen_range.dense
    ⟨V.ι ⟨f.fiberι s z, hxV⟩, ⟨f.fiberι s z, hxV⟩, rfl⟩⟩
  let j := fiberProjection V.ι f s
  let : IsOpenImmersion j := by unfold j fiberProjection; infer_instance
  obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback
    (fiberProjection_isPullback V.ι f s) z (⟨f.fiberι s z, hxV⟩ : V.toScheme) rfl
  let C : Set ((V.ι ≫ f).fiber s) := j ⁻¹' Z
  have hC : C ∈ irreducibleComponents ((V.ι ≫ f).fiber s) :=
    preimage_mem_irreducibleComponents hZ j.isOpenEmbedding ⟨z, hz, w, hw⟩
  have hlocal := everyFiberComponentDimensionGEGeneric_of_isAffine (V.ι ≫ f) s C hC
  rw [genericFiberDimension_eq_of_affine_openImmersion f V.ι] at hlocal
  let c : C → Z := fun w ↦ ⟨j w.val, w.property⟩
  have hc : Topology.IsInducing c :=
    Topology.IsInducing.subtypeVal.of_comp_iff.mp
      (j.isEmbedding.isInducing.comp Topology.IsInducing.subtypeVal)
  exact hlocal.trans hc.topologicalKrullDim_le

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundLocality
