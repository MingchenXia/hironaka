import DeJongAlterations.Modification
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The native generic-point map of a birational morphism

The field isomorphism is the stalk map of the original morphism, transported
along its actual generic-point equality. It is compatible with every stalk.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.NormalCurveModification

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (hf : Scheme.BirationalOver f (𝟙 Y))

include hf

/-- The original birational morphism maps the actual generic points. -/
theorem genericPoint_map : f (genericPoint X) = genericPoint Y := by
  obtain ⟨e, he⟩ := hf
  let : Nonempty e.source := Set.nonempty_coe_sort.mpr e.dense_source.nonempty
  let : Nonempty e.target := Set.nonempty_coe_sort.mpr e.dense_target.nonempty
  have heq : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using (show e.iso.hom ≫ e.target.ι = e.source.ι ≫ f by
      simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using he).symm
  have hη := congrArg (fun g : e.source.toScheme ⟶ Y =>
    g (genericPoint e.source.toScheme)) heq
  simpa only [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion] using hη

omit [IsIntegral Y] in
/-- The generic stalk map of the original birational morphism is invertible. -/
theorem generic_stalkMap_isIso : IsIso (f.stalkMap (genericPoint X)) := by
  obtain ⟨e, he⟩ := hf
  let : Nonempty e.source := Set.nonempty_coe_sort.mpr e.dense_source.nonempty
  have heq : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using (show e.iso.hom ≫ e.target.ι = e.source.ι ≫ f by
      simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using he).symm
  have : IsOpenImmersion (e.source.ι ≫ f) := by rw [heq]; infer_instance
  have H : IsIso ((e.source.ι ≫ f).stalkMap (genericPoint e.source.toScheme)) :=
    inferInstance
  rw [Scheme.Hom.stalkMap_comp] at H
  have : IsIso (f.stalkMap (e.source.ι (genericPoint e.source.toScheme))) :=
    (isIso_comp_right_iff (f.stalkMap (e.source.ι (genericPoint e.source.toScheme)))
      (e.source.ι.stalkMap (genericPoint e.source.toScheme))).mp H
  have hη : e.source.ι (genericPoint e.source.toScheme) = genericPoint X :=
    genericPoint_eq_of_isOpenImmersion e.source.ι
  rwa [hη] at this

/-- The actual function-field homomorphism induced by the birational morphism. -/
def functionFieldMap : Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (.of_eq (genericPoint_map f hf).symm)).hom ≫
    f.stalkMap (genericPoint X)

/-- The actual induced function-field homomorphism is an isomorphism. -/
theorem functionFieldMap_isIso : IsIso (functionFieldMap f hf) := by
  let := generic_stalkMap_isIso f hf
  dsimp only [functionFieldMap]
  infer_instance

/-- Naturality of the actual function-field map with respect to every local ring. -/
theorem functionFieldMap_stalk (x : X) :
    CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) ≫
      functionFieldMap f hf =
    f.stalkMap x ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
  change Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ (f x))) ≫
      ((Y.presheaf.stalkCongr (.of_eq (genericPoint_map f hf).symm)).hom ≫
        f.stalkMap (genericPoint X)) =
    f.stalkMap x ≫ X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (Set.mem_univ x))
  simpa only [← Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_comp] using
    f.stalkSpecializes_stalkMap (genericPoint X) x
      ((genericPoint_spec X).specializes (Set.mem_univ x))

/-- The same actual function-field map commutes with affine section maps. -/
theorem functionFieldMap_sections (U : Y.Opens) [Nonempty U]
    [hpre : Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ functionFieldMap f hf =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  let x : f ⁻¹ᵁ U := Classical.choice hpre
  have hY : Y.presheaf.germ U (f x) x.2 ≫
      CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) =
      Y.germToFunctionField U := by
    apply CommRingCat.hom_ext
    exact RingHom.ext fun a => Y.algebraMap_germ_eq_germToFunctionField x.2 a
  have hX : X.presheaf.germ (f ⁻¹ᵁ U) x x.2 ≫
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.germToFunctionField (f ⁻¹ᵁ U) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext fun a => X.algebraMap_germ_eq_germToFunctionField x.2 a
  rw [← hY, Category.assoc, functionFieldMap_stalk,
    ← Category.assoc, f.germ_stalkMap, Category.assoc, hX]

end DeJongAlterations.Geometry.NormalCurveModification
