import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
import Hironaka.Resolution.Algebraic.Smooth.GeometricallyReduced
import Hironaka.Geometry.RationalCoordinateMapGenericFiberOpenDimension

/-!
# Intrinsic dimensions of actual global irreducible components

Source-first proof: `actual-intrinsic-component-dimensions-20261102.tex`.
The actual finite-type field structure proves dimension invariance on open
restrictions.  Global coherent dimension ideals and history gluing remain
separate consumers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u

namespace Hironaka.Resolution.Algebraic.ActualIntrinsicComponentDimensions

noncomputable section

variable {X Y : Scheme.{u}}

def componentClosed (C : irreducibleComponents X) : Closeds X :=
  ⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩

def componentIdeal (C : irreducibleComponents X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (componentClosed C)

def componentDimension (C : irreducibleComponents X) : WithBot ℕ∞ :=
  topologicalKrullDim C.val

def dimensionIndex (X : Scheme.{u}) : Type :=
  ↥(Set.range (componentDimension (X := X)))

theorem componentIdeal_isIntegral (C : irreducibleComponents X) :
    IsIntegral (componentIdeal C).subscheme := by
  have : IsReduced (componentIdeal C).subscheme :=
    Hironaka.Smooth.isReduced_subscheme_of_radical_eq_self _ (by
      rw [componentIdeal, ← Scheme.IdealSheafData.vanishingIdeal_support,
        Hironaka.Sequence.support_vanishingIdeal_eq])
  have : IrreducibleSpace (componentIdeal C).subscheme :=
    Subtype.irreducibleSpace C.property.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def componentRestrict (j : Y ⟶ X) [IsOpenImmersion j]
    (C : irreducibleComponents X) (hC : (C.val ∩ Set.range j).Nonempty) :
    irreducibleComponents Y :=
  ⟨j ⁻¹' C.val, preimage_mem_irreducibleComponents C.property j.isOpenEmbedding hC⟩

theorem componentIdeal_restrict [NoetherianSpace X] (j : Y ⟶ X) [IsOpenImmersion j]
    (C : irreducibleComponents X) (hC : (C.val ∩ Set.range j).Nonempty) :
    (componentIdeal C).comap j = componentIdeal (componentRestrict j C hC) :=
  Hironaka.Smooth.comap_vanishingIdeal_of_smooth j (componentClosed C)

private def closedRestrictionMap (j : Y ⟶ X) (I : X.IdealSheafData) :
    (I.comap j).subscheme ⟶ I.subscheme :=
  (I.comapIso j).hom ≫ pullback.snd j I.subschemeι

private instance closedRestrictionMap_isOpenImmersion (j : Y ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) : IsOpenImmersion (closedRestrictionMap j I) := by
  dsimp [closedRestrictionMap]
  infer_instance

theorem componentDimension_restrict [NoetherianSpace X]
    {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsOpenImmersion j]
    (C : irreducibleComponents X) (hC : (C.val ∩ Set.range j).Nonempty) :
    componentDimension (componentRestrict j C hC) = componentDimension C := by
  have : IsIntegral (componentIdeal C).subscheme := componentIdeal_isIntegral C
  have hI := componentIdeal_restrict j C hC
  obtain ⟨x, hx, y, hxy⟩ := hC
  have hy : y ∈ ((componentIdeal C).comap j).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change j y ∈ C.val
    exact hxy ▸ hx
  let : Nonempty ((componentIdeal C).comap j).subscheme := ⟨⟨y, hy⟩⟩
  have hdim :=
    Hironaka.Geometry.FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion
      ((componentIdeal C).subschemeι ≫ p) (closedRestrictionMap j (componentIdeal C))
  rw [hI] at hdim
  exact hdim

theorem componentRestrict_surjective (j : Y ⟶ X) [IsOpenImmersion j]
    (D : irreducibleComponents Y) :
    ∃ (C : irreducibleComponents X) (hC : (C.val ∩ Set.range j).Nonempty),
      componentRestrict j C hC = D := by
  obtain ⟨C, hC, hD⟩ :=
    Hironaka.Resolution.exists_eq_preimage_of_mem_irreducibleComponents
      j.isOpenEmbedding D.property
  obtain ⟨y, hy⟩ := D.property.1.nonempty
  have hyC : y ∈ j ⁻¹' C := by
    rw [← hD]
    exact hy
  have hmeet : (C ∩ Set.range j).Nonempty :=
    ⟨j y, hyC, y, rfl⟩
  exact ⟨⟨C, hC⟩, hmeet, Subtype.ext hD.symm⟩

theorem dimensionIndex_finite (X : Scheme.{u}) [NoetherianSpace X] :
    Finite (dimensionIndex X) := by
  have : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  exact Set.finite_range (componentDimension (X := X)) |>.to_subtype

theorem componentDimension_nat {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (C : irreducibleComponents X) :
    ∃ n : ℕ, componentDimension C = n := by
  have : IsIntegral (componentIdeal C).subscheme := componentIdeal_isIntegral C
  obtain ⟨n, hn, _⟩ :=
    Hironaka.Geometry.FunctionFieldDimension.exists_dimension_and_trdeg
      ((componentIdeal C).subschemeι ≫ p)
  exact ⟨n, hn⟩

theorem dimension_range_open_subset [NoetherianSpace X]
    {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsOpenImmersion j] :
    Set.range (componentDimension (X := Y)) ⊆ Set.range (componentDimension (X := X)) := by
  rintro _ ⟨D, rfl⟩
  obtain ⟨C, hC, rfl⟩ := componentRestrict_surjective j D
  exact ⟨C, (componentDimension_restrict p j C hC).symm⟩

end
end Hironaka.Resolution.Algebraic.ActualIntrinsicComponentDimensions
