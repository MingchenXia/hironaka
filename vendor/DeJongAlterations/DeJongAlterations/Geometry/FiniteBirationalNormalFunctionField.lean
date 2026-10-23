import DeJongAlterations.Geometry.NormalizationInExtensionFunctionField
import Mathlib.RingTheory.Unramified.Field

/-!
# Actual finite separable function-field extensions from generic etaleness

The scalar map is the native generic stalk map of the original morphism.
Generic etaleness gives actual generic unramifiedness. Essential finite type
and the field unramifiedness theorem then give finiteness and separability.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

omit [IsIntegral Y] in
/-- The actual original generic stalk map is unramified under native generic etaleness. -/
theorem generic_stalkMap_formallyUnramified (f : X ⟶ Y) (hf : IsGenericallyEtale f) :
    (f.stalkMap (genericPoint X)).hom.FormallyUnramified := by
  obtain ⟨U, hU, he⟩ := hf
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU.nonempty)
  let x : U := ⟨genericPoint X, hη⟩
  let : Etale (U.ι ≫ f) := he
  have H := FormallyUnramified.stalkMap (U.ι ≫ f) x
  have H' : (f.stalkMap (genericPoint X) ≫ U.ι.stalkMap x).hom.FormallyUnramified := by
    simpa only [Scheme.Hom.stalkMap_comp, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, x] using H
  exact (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso
    (f.stalkMap (genericPoint X)) (U.ι.stalkMap x)).mp H'

/-- The actual canonical function-field homomorphism defines its scalar structure. -/
abbrev functionFieldAlgebra (f : X ⟶ Y) [IsDominant f] :
    Algebra Y.functionField X.functionField :=
  (NormalizationInExtension.functionFieldMap f).hom.toAlgebra

/-- Local finite type passes through the actual generic-point identification. -/
theorem functionFieldMap_essFiniteType (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f] :
    (NormalizationInExtension.functionFieldMap f).hom.EssFiniteType := by
  let e := Y.presheaf.stalkCongr (.of_eq (genericPoint_map_of_isDominant f).symm)
  exact (RingHom.EssFiniteType.respectsIso.cancel_left_isIso
    e.hom (f.stalkMap (genericPoint X))).mpr (LocallyOfFiniteType.stalkMap f (genericPoint X))

/-- Generic etaleness is retained by the actual canonical generic-stalk comparison. -/
theorem functionFieldMap_formallyUnramified (f : X ⟶ Y) [IsDominant f]
    (hf : IsGenericallyEtale f) :
    (NormalizationInExtension.functionFieldMap f).hom.FormallyUnramified := by
  let e := Y.presheaf.stalkCongr (.of_eq (genericPoint_map_of_isDominant f).symm)
  exact (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso
    e.hom (f.stalkMap (genericPoint X))).mpr (generic_stalkMap_formallyUnramified f hf)

/-- The original canonical function-field extension is finite and separable,
with no supplied extension or field-map compatibility certificate. -/
theorem functionField_finite_separable (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f]
    (hf : IsGenericallyEtale f) :
    letI := functionFieldAlgebra f
    FiniteDimensional Y.functionField X.functionField ∧
      Algebra.IsSeparable Y.functionField X.functionField := by
  let := functionFieldAlgebra f
  let : Algebra.EssFiniteType Y.functionField X.functionField := functionFieldMap_essFiniteType f
  let : Algebra.FormallyUnramified Y.functionField X.functionField :=
    functionFieldMap_formallyUnramified f hf
  exact ⟨Algebra.FormallyUnramified.finite_of_free Y.functionField X.functionField,
    Algebra.FormallyUnramified.isSeparable Y.functionField X.functionField⟩

end DeJongAlterations.Geometry.FiniteBirationalNormal
