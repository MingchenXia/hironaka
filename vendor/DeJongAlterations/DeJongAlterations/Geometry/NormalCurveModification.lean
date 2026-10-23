import DeJongAlterations.Algebra.DiscreteValuationOverring
import DeJongAlterations.Geometry.NormalCurveModificationFunctionField
import DeJongAlterations.Geometry.RegularCurve
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Proper birational modifications of normal curves are isomorphisms

The actual local maps are identified using valuation overrings in the actual
function fields. Zariski's Main Theorem yields finiteness, and normality then
makes each finite affine coefficient map bijective.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.NormalCurveModification

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Every actual local map over a normal locally Noetherian curve is an
isomorphism, without properness or a caller quasi-finiteness assumption. -/
theorem stalkMap_isIso (f : X ⟶ Y) (hf : Scheme.BirationalOver f (𝟙 Y))
    [IsLocallyNoetherian Y] (hnormal : IsNormalScheme Y)
    (hdim : topologicalKrullDim Y ≤ 1) (x : X) : IsIso (f.stalkMap x) := by
  let := (hnormal (f x)).2
  let := krullDimLE_stalk_of_topologicalKrullDim_le Y hdim (f x)
  let : ValuationRing (Y.presheaf.stalk (f x)) :=
    Algebra.DiscreteValuationOverring.valuationRing_of_normal_dimLE_one _
  let φ := functionFieldMap f hf
  let : IsIso φ := functionFieldMap_isIso f hf
  let g : X.presheaf.stalk x →+* Y.functionField :=
    (inv φ).hom.comp (algebraMap (X.presheaf.stalk x) X.functionField)
  have hg : Function.Injective g :=
    (ConcreteCategory.bijective_of_isIso (inv φ)).1.comp
      (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
  have h : g.comp (f.stalkMap x).hom =
      algebraMap (Y.presheaf.stalk (f x)) Y.functionField := by
    apply CommRingCat.hom_ext_iff.mp
    change (f.stalkMap x ≫ CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ inv φ = _
    rw [← functionFieldMap_stalk f hf, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rfl
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (Algebra.DiscreteValuationOverring.bijective_of_local_overring
      (f.stalkMap x).hom g hg h)

/-- The actual proper birational map to a normal curve is locally quasi-finite. -/
theorem locallyQuasiFinite_of_normal_curve (f : X ⟶ Y)
    (hf : Scheme.BirationalOver f (𝟙 Y)) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] (hnormal : IsNormalScheme Y)
    (hdim : topologicalKrullDim Y ≤ 1) : LocallyQuasiFinite f := by
  apply (f.quasiFiniteLocus_eq_top_iff).mp
  apply top_le_iff.mp
  intro x hx
  change (f.stalkMap x).hom.QuasiFinite
  let := stalkMap_isIso f hf hnormal hdim x
  exact RingHom.QuasiFinite.of_finite
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).2)

/-- Native Zariski's Main Theorem makes the actual proper modification finite. -/
theorem isFinite_of_normal_curve (f : X ⟶ Y)
    (hf : Scheme.BirationalOver f (𝟙 Y)) [IsProper f]
    [IsLocallyNoetherian Y] (hnormal : IsNormalScheme Y)
    (hdim : topologicalKrullDim Y ≤ 1) : IsFinite f := by
  let := locallyQuasiFinite_of_normal_curve f hf hnormal hdim
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- The actual sections of any nonempty affine open in a normal integral
scheme are integrally closed. -/
theorem affineSections_isIntegrallyClosed (hnormal : IsNormalScheme Y)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(Y, U) := by
  let : IsDomain Γ(Y, U) := IsIntegral.component_integral U
  apply IsIntegrallyClosed.of_localization_maximal
  intro P _ hP
  let p : Spec Γ(Y, U) := ⟨P, inferInstance⟩
  have hx : hU.fromSpec p ∈ U := (hU.isoSpec.inv p).2
  let : Algebra Γ(Y, U) (Y.presheaf.stalk (hU.fromSpec p)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨hU.fromSpec p, hx⟩
  let : IsLocalization.AtPrime (Y.presheaf.stalk (hU.fromSpec p)) P :=
    hU.isLocalization_stalk' p hx
  let := (hnormal (hU.fromSpec p)).2
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl (Y.presheaf.stalk (hU.fromSpec p))
      (Localization.AtPrime P)).toRingEquiv

/-- A finite birational map to a normal integral scheme induces bijections on
its actual nonempty affine coefficient rings, in arbitrary dimension. -/
theorem finite_affine_app_bijective (f : X ⟶ Y)
    (hf : Scheme.BirationalOver f (𝟙 Y)) [IsFinite f]
    (hnormal : IsNormalScheme Y) (U : Y.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] : Function.Bijective (f.app U).hom := by
  let : IsDomain Γ(Y, U) := IsIntegral.component_integral U
  let : IsIntegrallyClosed Γ(Y, U) := affineSections_isIntegrallyClosed hnormal U hU
  let : IsFractionRing Γ(Y, U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  let φ := functionFieldMap f hf
  let : IsIso φ := functionFieldMap_isIso f hf
  let g : Γ(X, f ⁻¹ᵁ U) →+* Y.functionField :=
    (inv φ).hom.comp (X.germToFunctionField (f ⁻¹ᵁ U)).hom
  have hg : Function.Injective g :=
    (ConcreteCategory.bijective_of_isIso (inv φ)).1.comp
      (X.germToFunctionField_injective (f ⁻¹ᵁ U))
  have h : g.comp (f.app U).hom = algebraMap Γ(Y, U) Y.functionField := by
    apply CommRingCat.hom_ext_iff.mp
    change (f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U)) ≫ inv φ = _
    rw [← functionFieldMap_sections f hf, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  let gA : Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Y.functionField :=
    { g with commutes' := fun r => DFunLike.congr_fun h r }
  refine ⟨Function.Injective.of_comp (f := g) ?_, ?_⟩
  · rw [← RingHom.coe_comp, h]
    exact IsFractionRing.injective Γ(Y, U) Y.functionField
  · intro b
    obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff Y.functionField).mp
      (inferInstance : IsIntegrallyClosed Γ(Y, U))
      ((Algebra.IsIntegral.isIntegral b).map gA)
    refine ⟨a, hg ?_⟩
    change (g.comp (f.app U).hom) a = g b
    rwa [h]

/-- Every actual finite birational morphism onto a normal integral scheme is
an isomorphism. This final normality step needs no dimension bound. -/
theorem isIso_of_finite_birational (f : X ⟶ Y)
    (hf : Scheme.BirationalOver f (𝟙 Y)) [IsFinite f]
    (hnormal : IsNormalScheme Y) : IsIso f := by
  let : IsDominant f := isDominant_of_birationalOver_id f hf
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms _)
    (fun U : Y.affineOpens => U.1) (iSup_affineOpens_eq_top Y)).mpr
  intro a
  let U := a.1
  have hU : IsAffineOpen U := a.2
  by_cases hne : Nonempty U
  · let := hne
    have hpre : Nonempty (f ⁻¹ᵁ U) := by
      obtain ⟨x, hx⟩ := f.denseRange.exists_mem_open U.isOpen (Set.nonempty_coe_sort.mp hne)
      exact ⟨⟨x, hx⟩⟩
    let := hpre
    have : IsIso (f.app U) := (ConcreteCategory.isIso_iff_bijective _).mpr
      (finite_affine_app_bijective f hf hnormal U hU)
    have : IsIso (f ∣_ U) := (isIso_morphismRestrict_iff_isIso_app f hU).mpr this
    exact this
  · let : IsEmpty U.toScheme := not_nonempty_iff.mp hne
    exact isIso_of_isEmpty (f ∣_ U)

omit [IsIntegral X] [IsIntegral Y] in
/-- The actual proper birational modification of a normal locally Noetherian
curve is an isomorphism. No finiteness or quasi-finiteness input is supplied. -/
theorem isIso_of_isModification (f : X ⟶ Y) [hf : IsModification f]
    [IsLocallyNoetherian Y] (hnormal : IsNormalScheme Y)
    (hdim : topologicalKrullDim Y ≤ 1) : IsIso f := by
  let := hf.sourceIntegral
  let := hf.targetIntegral
  let : IsFinite f := isFinite_of_normal_curve f hf.birational hnormal hdim
  exact isIso_of_finite_birational f hf.birational hnormal

end DeJongAlterations.Geometry.NormalCurveModification
