import Hironaka.Geometry.CurveFibrationBaseChangeReduction

/-!
# Actual field-fibre comparisons and all component dimensions

Native Cartesian pasting identifies the whole field-valued fibre with
the original one. The actual reduction comparison gives a canonical
homeomorphism, preserving every native irreducible component dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S Y Q : Scheme.{u}}

/-- Native Cartesian pasting identifies the actual whole fibre with the original fibre. -/
def wholeFieldFiberIso (f : X ⟶ S) (g : Y ⟶ S) {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ Y) :
    pullback (pullback.snd f g) a ≅ pullback f (a ≫ g) :=
  ((IsPullback.of_hasPullback (pullback.snd f g) a).paste_horiz
    (IsPullback.of_hasPullback f g)).isoPullback

/-- The actual whole-reduction field fibre is canonically homeomorphic to the ORIGINAL field fibre. -/
def reducedFieldFiberHomeomorph (f : X ⟶ S) (g : Y ⟶ S) {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ Y) :
    (pullback (reductionι f g ≫ pullback.snd f g) a : Scheme.{u}) ≃ₜ
      (pullback f (a ≫ g) : Scheme.{u}) :=
  ((reductionBaseChangeMap_isHomeomorph f g a).homeomorph (reductionBaseChangeMap f g a)).trans
    (wholeFieldFiberIso f g a).hom.homeomorph

/-- Every actual component dimension transports through an actual homeomorphism. -/
theorem component_dimension_of_homeomorph {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (h : A ≃ₜ B) (d : ℕ)
    (hd : ∀ C ∈ irreducibleComponents B, topologicalKrullDim C = d)
    (C : Set A) (hC : C ∈ irreducibleComponents A) : topologicalKrullDim C = d := by
  let C' := h.symm ⁻¹' C
  have hC' : C' ∈ irreducibleComponents B :=
    preimage_mem_irreducibleComponents hC h.symm.isOpenEmbedding (by
      simpa only [h.symm.surjective.range_eq, Set.inter_univ] using hC.1.nonempty)
  let e : C ≃ₜ C' := h.subtype (by intro x; simp [C'])
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).trans (hd C' hC')

/-- Pure dimension on ALL components of ALL original actual field fibres is preserved. -/
theorem reducedSecond_fieldFiber_components_dimension (f : X ⟶ S) (g : Y ⟶ S) (d : ℕ)
    (hd : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) → topologicalKrullDim C = d)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ Y)
    (C : Set (pullback (reductionι f g ≫ pullback.snd f g) a : Scheme.{u}))
    (hC : C ∈ irreducibleComponents
      (pullback (reductionι f g ≫ pullback.snd f g) a : Scheme.{u})) :
    topologicalKrullDim C = d :=
  component_dimension_of_homeomorph (reducedFieldFiberHomeomorph f g a) d (hd K (a ≫ g)) C hC

end Hironaka.Geometry.CurveFibrationBaseChange
