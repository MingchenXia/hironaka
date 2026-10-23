/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.AlgebraicScalarStalkDimension
import DeJongAlterations.Geometry.IntegralDenseOpenDescent
import DeJongAlterations.Geometry.SNCLocality

/-!
# Actual pure codimension in a flat integral closed-subscheme square

This proves the codimension part of field/SNC descent, with unchanged
original closed subschemes, ambient maps and component generic points.
Blueprint: `algebraic-scalar-pure-codimension.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.AlgebraicScalarPureCodimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original Cartesian closed-subscheme square and actual flat
integral cover internally transport every component generic point and its
ambient stalk dimension. -/
theorem hasPureCodimension_of_isPullback {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [Flat f] [IsIntegralHom f] [Surjective f]
    (D : Y.IdealSheafData) (E : X.IdealSheafData) (g : E.subscheme ⟶ D.subscheme)
    (H : IsPullback g E.subschemeι D.subschemeι f) {r : ℕ}
    (hE : HasPureCodimension E.support r) : HasPureCodimension D.support r := by
  intro C hC y hy
  have hyD : y ∈ D.support := by
    obtain ⟨z, -, hz⟩ := hy.mem
    exact hz ▸ z.property
  let η : D.subscheme := ⟨y, hyD⟩
  have hη : IsGenericPoint η C := by
    have h := SNCLocality.genericPoint_preimage D.subschemeι.isClosedEmbedding.isEmbedding
      (x := η) (show IsGenericPoint (D.subschemeι η) (Subtype.val '' C) from hy)
    change IsGenericPoint η (Subtype.val ⁻¹' (Subtype.val '' C)) at h
    rwa [Set.preimage_image_eq _ Subtype.val_injective] at h
  let : IsIntegralHom g := MorphismProperty.of_isPullback H.flip inferInstance
  let : Surjective g := MorphismProperty.of_isPullback H.flip inferInstance
  obtain ⟨x, hx⟩ := g.surjective η
  obtain ⟨C', hC', hxgen⟩ :=
    IntegralDenseOpenDescent.exists_component_genericPoint_of_image_generic g hC hη x hx
  have hcl : IsClosed (E.subschemeι '' C') :=
    E.subschemeι.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ hC')
  have hxgen' : IsGenericPoint (E.subschemeι x) (Subtype.val '' C') := by
    have hfun : (fun a : E.subscheme => E.subschemeι a) = Subtype.val :=
      funext E.subschemeι_apply
    have hg := hxgen.image E.subschemeι.continuous
    rw [hcl.closure_eq] at hg
    simpa only [hfun] using hg
  have hxy : f (E.subschemeι x) = y := by
    have h := congrArg (fun a : E.subscheme ⟶ Y => a x) H.w
    simpa only [Scheme.Hom.comp_apply, hx, Scheme.IdealSheafData.subschemeι_apply, η]
      using h.symm
  have hdim := AlgebraicScalarStalkDimension.ringKrullDim_stalk_eq_of_flat_integral
    f (E.subschemeι x)
  rw [hxy] at hdim
  exact hdim.symm.trans (hE C' hC' (E.subschemeι x) hxgen')

end DeJongAlterations.Geometry.AlgebraicScalarPureCodimension
