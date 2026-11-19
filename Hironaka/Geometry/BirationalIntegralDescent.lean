import Hironaka.Geometry.IntegralDenseOpenDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Native birationality descends on the same actual integral flat square
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.BirationalIntegralDescent

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual upstairs native partial isomorphism gives original dominance and a descended open immersion. -/
theorem of_isPullback {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {b : Y' ⟶ Y}
    (H : IsPullback a f' f b) [Surjective b] [Flat b] [IsIntegralHom b]
    [TopologicalSpace.NoetherianSpace X'] (hf' : Scheme.BirationalOver f' (𝟙 Y')) :
    Scheme.BirationalOver f (𝟙 Y) := by
  let : IsIntegralHom a := MorphismProperty.of_isPullback H.flip inferInstance
  obtain ⟨e, he⟩ := hf'
  have heq : e.iso.hom ≫ e.target.ι = e.source.ι ≫ f' := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using he
  let : IsOpenImmersion (e.source.ι ≫ f') := by
    rw [← heq]
    infer_instance
  let : IsDominant e.target.ι := Opens.isDominant_ι e.dense_target
  let : IsDominant (e.source.ι ≫ f') := by
    rw [← heq]
    infer_instance
  let : IsDominant f' := IsDominant.of_comp e.source.ι f'
  let : IsDominant (a ≫ f) := by
    rw [H.w]
    infer_instance
  let : IsDominant f := IsDominant.of_comp a f
  let V := IntegralDenseOpenDescent.descendedOpen a e.source
  have hV := IntegralDenseOpenDescent.descendedOpen_dense a e.source e.dense_source
  have hle : a ⁻¹ᵁ V ≤ e.source :=
    IntegralDenseOpenDescent.preimage_descendedOpen_le a e.source
  let : IsOpenImmersion ((a ⁻¹ᵁ V).ι ≫ f') := by
    have hh : (a ⁻¹ᵁ V).ι ≫ f' = X'.homOfLE hle ≫ (e.source.ι ≫ f') := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [hh]
    infer_instance
  have hs := (isPullback_morphismRestrict a V).paste_vert H
  let : IsOpenImmersion (V.ι ≫ f) := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    hs.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  let : IsDominant V.ι := Opens.isDominant_ι hV
  let g := V.ι ≫ f
  let W := g.opensRange
  have hW : Dense (W : Set Y) := g.denseRange
  have hr : Set.range g = Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rfl
  let i : V.toScheme ≅ W.toScheme := IsOpenImmersion.isoOfRangeEq g W.ι hr
  refine ⟨⟨V, hV, W, hW, i⟩, ?_⟩
  change i.hom ≫ W.ι ≫ 𝟙 Y = V.ι ≫ f
  rw [Category.comp_id]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac g W.ι hr

/-- Native birationality descends from the SAME actual native pullback. -/
theorem of_pullback {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (b : Y' ⟶ Y)
    [Surjective b] [Flat b] [IsIntegralHom b]
    [TopologicalSpace.NoetherianSpace (pullback f b : Scheme.{u})]
    (hf' : Scheme.BirationalOver (pullback.snd f b) (𝟙 Y')) :
    Scheme.BirationalOver f (𝟙 Y) :=
  of_isPullback (IsPullback.of_hasPullback f b) hf'

end Hironaka.Geometry.BirationalIntegralDescent
