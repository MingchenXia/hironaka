import Hironaka.Resolution.Algebraic.ActualIntegralIntrinsicSmoothDimension

/-!
# Actual component dimensions and genuine smooth generic transport

Source-first proof: `actual-smooth-component-dimension-transport-20261102.tex`.
Actual integral component opens, real cartesian maps and flat generic-point
transport derive the actual component dimension shift needed for J naturality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData
universe u

namespace Hironaka.Resolution.Algebraic.ActualSmoothComponentDimensionTransport

noncomputable section
open ActualIntrinsicComponentDimensions

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsReduced X]

private instance componentOpen_integral (C : irreducibleComponents X) :
    IsIntegral (X.irreducibleComponentOpen C.val) :=
  Hironaka.Resolution.isIntegral_irreducibleComponentOpen_of_isReduced C.val C.property

theorem componentIdeal_open_bot (C : irreducibleComponents X) :
    (componentIdeal C).comap (X.irreducibleComponentOpen C.val).ι = ⊥ := by
  rw [componentIdeal, Hironaka.Smooth.comap_vanishingIdeal_of_smooth]
  have ht : (componentClosed C).preimage (X.irreducibleComponentOpen C.val).ι.continuous = ⊤ := by
    ext x
    change x.val ∈ C.val ↔ True
    exact iff_of_true (Hironaka.Resolution.mem_of_mem_irreducibleComponentOpen x.property) trivial
  rw [ht, vanishingIdeal_top, Scheme.nilradical_eq_bot]

private instance componentRestriction_isIso (C : irreducibleComponents X) :
    IsIso (((componentIdeal C).comap (X.irreducibleComponentOpen C.val).ι).subschemeι) :=
  (Scheme.isIso_subschemeι_iff_eq_bot _).mpr (componentIdeal_open_bot C)

def componentOpenMap (C : irreducibleComponents X) :
    (X.irreducibleComponentOpen C.val).toScheme ⟶ (componentIdeal C).subscheme :=
  inv (((componentIdeal C).comap (X.irreducibleComponentOpen C.val).ι).subschemeι) ≫
    ((componentIdeal C).comapIso (X.irreducibleComponentOpen C.val).ι).hom ≫
      pullback.snd (X.irreducibleComponentOpen C.val).ι (componentIdeal C).subschemeι

instance componentOpenMap_isOpenImmersion (C : irreducibleComponents X) : IsOpenImmersion (componentOpenMap C) := by
  dsimp only [componentOpenMap]
  infer_instance

theorem componentOpenMap_over (C : irreducibleComponents X) :
    componentOpenMap C ≫ (componentIdeal C).subschemeι = (X.irreducibleComponentOpen C.val).ι := by
  rw [componentOpenMap, Category.assoc, Category.assoc, ← pullback.condition,
    ← Category.assoc ((componentIdeal C).comapIso (X.irreducibleComponentOpen C.val).ι).hom,
    comapIso_hom_fst, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

theorem componentOpen_dimension {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (C : irreducibleComponents X) :
    topologicalKrullDim (X.irreducibleComponentOpen C.val) = componentDimension C := by
  have : IsIntegral (componentIdeal C).subscheme := componentIdeal_isIntegral C
  exact Hironaka.Geometry.FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion
    ((componentIdeal C).subschemeι ≫ p) (componentOpenMap C)

def componentGenericPoint (C : irreducibleComponents X) : X :=
  (X.irreducibleComponentOpen C.val).ι (genericPoint (X.irreducibleComponentOpen C.val))

theorem componentGenericPoint_generic (C : irreducibleComponents X) :
    IsGenericPoint (componentGenericPoint C) C.val := by
  have h := (genericPoint_spec (X.irreducibleComponentOpen C.val)).image
    (X.irreducibleComponentOpen C.val).ι.continuous
  rwa [Set.image_univ, Scheme.Opens.range_ι, Hironaka.Resolution.closure_irreducibleComponentOpen C.val C.property] at h

variable [IsNoetherian Y] [IsReduced Y]

omit [AlgebraicGeometry.IsNoetherian X] [IsReduced X] [AlgebraicGeometry.IsNoetherian Y] [IsReduced Y] in
private theorem imageComponentExists (f : Y ⟶ X) (D : irreducibleComponents Y) :
    ∃ C : irreducibleComponents X, f '' D.val ⊆ C.val := by
  obtain ⟨C, hC, hDC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible (f '' D.val)
    (D.property.1.image f f.continuous.continuousOn)
  exact ⟨⟨C, hC⟩, hDC⟩

def imageComponent (f : Y ⟶ X) (D : irreducibleComponents Y) : irreducibleComponents X :=
  (imageComponentExists f D).choose

omit [AlgebraicGeometry.IsNoetherian X] [IsReduced X] [AlgebraicGeometry.IsNoetherian Y] [IsReduced Y] in
theorem imageComponent_image_subset (f : Y ⟶ X) (D : irreducibleComponents Y) :
    f '' D.val ⊆ (imageComponent f D).val := (imageComponentExists f D).choose_spec

theorem imageComponent_genericPoint (f : Y ⟶ X) [Flat f] (D : irreducibleComponents Y) :
    f (componentGenericPoint D) = componentGenericPoint (imageComponent f D) :=
  Hironaka.Resolution.map_genericPoint_eq_of_flat f D.property (imageComponent_image_subset f D)
    (componentGenericPoint_generic (imageComponent f D)) (componentGenericPoint_generic D)

theorem componentDimension_add {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : Y ⟶ X) (r : ℕ)
    [SmoothOfRelativeDimension r f] (D : irreducibleComponents Y) :
    componentDimension D = componentDimension (imageComponent f D) + r := by
  have : Smooth f := SmoothOfRelativeDimension.smooth r f
  let C := imageComponent f D
  let U := X.irreducibleComponentOpen C.val
  let V := Y.irreducibleComponentOpen D.val
  let W : Y.Opens := V ⊓ f ⁻¹ᵁ U
  have hηV : componentGenericPoint D ∈ V := (genericPoint V).property
  have hηU : f (componentGenericPoint D) ∈ U := by
    rw [imageComponent_genericPoint]
    exact (genericPoint U).property
  have : Nonempty W := ⟨⟨componentGenericPoint D, hηV, hηU⟩⟩
  have : IsIntegral W := isIntegral_of_isOpenImmersion (Y.homOfLE (inf_le_left : W ≤ V))
  have hWdim : topologicalKrullDim W = componentDimension D :=
    (Hironaka.Geometry.FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion
      (V.ι ≫ f ≫ p) (Y.homOfLE (inf_le_left : W ≤ V))).trans (componentOpen_dimension (f ≫ p) D)
  have hUdim := componentOpen_dimension p C
  let g := f.resLE U W inf_le_right
  have : SmoothOfRelativeDimension r g := by
    have : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension r) :=
      @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ inferInstance
    have : SmoothOfRelativeDimension r (f ∣_ U) :=
      IsZariskiLocalAtTarget.restrict (inferInstance : SmoothOfRelativeDimension r f) U
    have h : SmoothOfRelativeDimension (0 + r)
        (Y.homOfLE (inf_le_right : W ≤ f ⁻¹ᵁ U) ≫ (f ∣_ U)) := inferInstance
    rw [Nat.zero_add] at h
    exact h
  calc
    componentDimension D = topologicalKrullDim W := hWdim.symm
    _ = topologicalKrullDim U + r := ActualIntegralIntrinsicSmoothDimension.dimension_add_of_smooth (U.ι ≫ p) g r
    _ = componentDimension (imageComponent f D) + r := congrArg (· + (r : WithBot ℕ∞)) hUdim

end
end Hironaka.Resolution.Algebraic.ActualSmoothComponentDimensionTransport
