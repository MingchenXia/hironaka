import Hironaka.Geometry.CartierBoundaryDominance

/-!
# Actual finite reduced boundaries on closed base-change models

The actual inverse boundary is first a closed restriction of the native
finite boundary base change; its radical is then another actual closed
subscheme. No finiteness of the new boundary is supplied as an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CartierBoundaryDominance

open Scheme.IdealSheafData

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S Y T : Scheme.{u}}

/-- The literal ideal pullback square, with its genuine native subscheme map. -/
theorem isPullback_comapSubschemeMap (f : T ⟶ X) (D : X.IdealSheafData) :
    IsPullback (D.comap f).subschemeι (SNCLocality.comapSubschemeMap f D) f D.subschemeι := by
  apply IsPullback.of_iso_pullback
    ⟨(SNCLocality.comapSubschemeMap_ι f D).symm⟩ (D.comapIso f)
  · exact D.comapIso_hom_fst f
  · rfl

/-- The actual comap map is a closed immersion for an original closed immersion. -/
instance comapSubschemeMap_isClosedImmersion (f : T ⟶ X) [IsClosedImmersion f]
    (D : X.IdealSheafData) : IsClosedImmersion (SNCLocality.comapSubschemeMap f D) := by
  delta SNCLocality.comapSubschemeMap
  infer_instance

/-- Passing to the actual reduced subscheme preserves an original finite structure map. -/
theorem radical_subscheme_isFinite (I : T.IdealSheafData) (b : T ⟶ Y)
    [IsFinite (I.subschemeι ≫ b)] : IsFinite (I.radical.subschemeι ≫ b) := by
  let i := Scheme.IdealSheafData.inclusion I.le_radical
  let : IsClosedImmersion (i ≫ I.subschemeι) := by
    rw [Scheme.IdealSheafData.inclusion_subschemeι]
    infer_instance
  let : IsClosedImmersion i := IsClosedImmersion.of_comp i I.subschemeι
  rw [← Scheme.IdealSheafData.inclusion_subschemeι I.le_radical, Category.assoc]
  infer_instance

/-- The actual reduced inverse Cartier support is finite over the new base on every closed model.
This statement needs no Cartier, integral, normality, flatness or field hypothesis. -/
theorem reducedBoundary_isFinite_of_closed_baseChange
    (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData)
    [IsFinite (reducedBoundaryInclusion D ≫ f)]
    (j : T ⟶ pullback f g) [IsClosedImmersion j] :
    IsFinite (reducedBoundaryInclusion (D.comap (j ≫ pullback.fst f g)) ≫
      (j ≫ pullback.snd f g)) := by
  let a := pullback.fst f g
  let b := pullback.snd f g
  let E := vanishingIdeal D.support
  let K := E.comap a
  let J := K.comap j
  have H := (isPullback_comapSubschemeMap a E).paste_horiz
    (IsPullback.of_hasPullback f g).flip
  let : IsFinite (E.subschemeι ≫ f) := inferInstanceAs
    (IsFinite (reducedBoundaryInclusion D ≫ f))
  let : IsFinite (K.subschemeι ≫ b) := MorphismProperty.of_isPullback H.flip inferInstance
  have hcomp : SNCLocality.comapSubschemeMap j K ≫ (K.subschemeι ≫ b) =
      J.subschemeι ≫ (j ≫ b) := by
    rw [← Category.assoc, SNCLocality.comapSubschemeMap_ι, Category.assoc]
  let : IsFinite (J.subschemeι ≫ (j ≫ b)) := by
    rw [← hcomp]
    infer_instance
  have hsupp : J.support = (D.comap (j ≫ a)).support := by
    dsimp only [J, K]
    rw [← comap_comp, support_comap, support_comap]
    rfl
  have hideal : vanishingIdeal (D.comap (j ≫ a)).support = J.radical := by
    rw [← hsupp, vanishingIdeal_support]
  change IsFinite ((vanishingIdeal (D.comap (j ≫ a)).support).subschemeι ≫ (j ≫ b))
  rw [hideal]
  exact radical_subscheme_isFinite J (j ≫ b)

end Hironaka.Geometry.CartierBoundaryDominance
