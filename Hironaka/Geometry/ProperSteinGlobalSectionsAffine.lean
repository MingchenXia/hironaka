import Hironaka.Geometry.FiniteBirationalNormalFunctionField
import Hironaka.Geometry.NormalCurveModification
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Actual original affine sections of a proper map with no further constants. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace Hironaka.Geometry.ProperSteinGlobalSections
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Universal closedness derives integrality of the ORIGINAL section map on every actual affine open. -/
theorem app_isIntegral {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f]
    (U : S.Opens) (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral := by
  let : IsAffine U := hU
  have ht := isIntegral_appTop_of_universallyClosed (f ∣_ U)
  rw [morphismRestrict_appTop, CommRingCat.hom_comp,
    RingHom.isIntegral_respectsIso.cancel_right_isIso] at ht
  exact (congrArg (fun V => (f.app V).hom.IsIntegral) (Scheme.Opens.ι_image_top U)).mp ht

/-- The actual canonical generic-stalk constants derive bijectivity on every ORIGINAL nonempty affine open. -/
theorem affine_app_bijective {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [IsDominant f] [UniversallyClosed f] (hnormal : IsNormalScheme S)
    (hconstants : letI := FiniteBirationalNormal.functionFieldAlgebra f
      algebraicClosure S.functionField X.functionField = ⊥)
    (U : S.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Function.Bijective (f.app U).hom := by
  let : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := f.denseRange.exists_mem_open U.isOpen (Set.nonempty_coe_sort.mp (inferInstance : Nonempty U))
    exact ⟨⟨x, hx⟩⟩
  let := FiniteBirationalNormal.functionFieldAlgebra f
  let R := Γ(S, U)
  let B := Γ(X, f ⁻¹ᵁ U)
  let : IsDomain R := IsIntegral.component_integral U
  let : IsIntegrallyClosed R := NormalCurveModification.affineSections_isIntegrallyClosed hnormal U hU
  let : IsFractionRing R S.functionField := functionField_isFractionRing_of_isAffineOpen S U hU
  let : Algebra R B := (f.app U).hom.toAlgebra
  let : Algebra R X.functionField :=
    ((algebraMap S.functionField X.functionField).comp (algebraMap R S.functionField)).toAlgebra
  let : IsScalarTower R S.functionField X.functionField := .of_algebraMap_eq' rfl
  have htriangle : (X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom =
      algebraMap R X.functionField := by
    exact (CommRingCat.hom_ext_iff.mp (NormalizationInExtension.functionFieldMap_sections f U)).symm
  let g : B →ₐ[R] X.functionField :=
    { (X.germToFunctionField (f ⁻¹ᵁ U)).hom with
      commutes' := fun r => DFunLike.congr_fun htriangle r }
  have hg : Function.Injective g := X.germToFunctionField_injective (f ⁻¹ᵁ U)
  have hf : Function.Injective (f.app U).hom := by
    intro a b hab
    apply IsFractionRing.injective R S.functionField
    apply (algebraMap S.functionField X.functionField).injective
    change algebraMap R X.functionField a = algebraMap R X.functionField b
    simpa only [← htriangle, RingHom.comp_apply] using
      congrArg (X.germToFunctionField (f ⁻¹ᵁ U)) hab
  refine ⟨hf, ?_⟩
  intro b
  have hb0 : _root_.IsIntegral R b := app_isIntegral f U hU b
  have hb : _root_.IsIntegral R (g b) := hb0.map g
  have hbK : IsAlgebraic S.functionField (g b) := hb.tower_top.isAlgebraic
  have hm : g b ∈ algebraicClosure S.functionField X.functionField :=
    mem_algebraicClosure_iff.mpr hbK
  rw [hconstants] at hm
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hm
  have haI : _root_.IsIntegral R a :=
    (isIntegral_algebraMap_iff (algebraMap S.functionField X.functionField).injective).mp
      (ha.symm ▸ hb)
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral haI
  refine ⟨r, hg ?_⟩
  change g (algebraMap R B r) = g b
  rw [g.commutes, IsScalarTower.algebraMap_apply R S.functionField X.functionField, hr, ha]

end Hironaka.Geometry.ProperSteinGlobalSections
