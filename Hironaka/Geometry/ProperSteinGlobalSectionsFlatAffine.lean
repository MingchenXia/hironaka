import Hironaka.Geometry.ProperSteinGlobalSectionsFlatBaseChange
import Hironaka.Geometry.ProperSteinGlobalSections
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.Localization

/-! # The SAME intrinsic factor retains ORIGINAL whole coefficients under actual flat local and completed base changes. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace Hironaka.Geometry.ProperSteinFlatSections
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open ProperGeometricGlobalFunctions

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f] [LocallyOfFiniteType f] [AlgebraicGeometry.IsNoetherian X]
  (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)
  {k : Type u} [Field k] (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]
  (hf : IsProper f) (hnormal : IsNormalScheme X)

/-- The SAME factor restricted over the ORIGINAL affine open, with its actual native affine coordinate map. -/
abbrev affineFactor (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V) :
    (SteinCurveFactor.factor f hdim p hnormal ⁻¹ᵁ V).toScheme ⟶
      Spec (.of Γ(SteinCurveFactor.base f, V)) :=
  (SteinCurveFactor.factor f hdim p hnormal ∣_ V) ≫ hV.isoSpec.hom

include hf in
/-- ORIGINAL properness internally gives properness of this SAME actual original affine-coordinate factor. -/
theorem affineFactor_isProper (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V) :
    IsProper (affineFactor f hdim p hnormal V hV) := by
  let := SteinCurveFactor.factor_isProper f hdim p hf hnormal
  dsimp only [affineFactor]
  infer_instance

include hf in
/-- The actual sheaf identity internally derives the ORIGINAL affine-coordinate coefficient map's bijectivity. -/
theorem affineFactor_coefficient_bijective
    (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V) :
    Function.Bijective (coefficientMap (affineFactor f hdim p hnormal V hV)) := by
  let g := SteinCurveFactor.factor f hdim p hnormal
  have ht : IsIso ((g ∣_ V).appTop) := by
    rw [morphismRestrict_appTop]
    let := ProperSteinGlobalSections.factor_isIso_app f hdim p hf hnormal (V.ι ''ᵁ ⊤)
    infer_instance
  let : IsIso (hV.isoSpec.hom.appTop) := by
    change IsIso (hV.isoSpec.hom.app ⊤)
    infer_instance
  let : IsIso (CommRingCat.ofHom (coefficientMap (affineFactor f hdim p hnormal V hV))) := by
    change IsIso ((Scheme.ΓSpecIso (.of Γ(SteinCurveFactor.base f, V))).inv ≫
      (affineFactor f hdim p hnormal V hV).appTop)
    dsimp only [affineFactor]
    rw [Scheme.Hom.comp_appTop]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (coefficientMap (affineFactor f hdim p hnormal V hV)))

/-- The SAME actual affine-coordinate factor has the ORIGINAL whole coefficient equivalence over EVERY genuinely flat algebra. -/
def affineFlatSectionsAlgEquiv (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V)
    (B : Type u) [CommRing B] [Algebra Γ(SteinCurveFactor.base f, V) B]
    [Module.Flat Γ(SteinCurveFactor.base f, V) B] :
    let q := affineFactor f hdim p hnormal V hV
    letI : Algebra B Γ(baseChange (S := B) q, ⊤) := sectionsAlgebra (structureMap (S := B) q)
    B ≃ₐ[B] Γ(baseChange (S := B) q, ⊤) := by
  let q := affineFactor f hdim p hnormal V hV
  let : IsProper q := affineFactor_isProper f hdim p hf hnormal V hV
  exact flatSectionsAlgEquiv q (affineFactor_coefficient_bijective f hdim p hf hnormal V hV)

/-- Its ENTIRE forward map is precisely the ORIGINAL actual whole flat-base-change coefficient map. -/
theorem affineFlatSectionsAlgEquiv_apply (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V)
    (B : Type u) [CommRing B] [Algebra Γ(SteinCurveFactor.base f, V) B]
    [Module.Flat Γ(SteinCurveFactor.base f, V) B] (b : B) :
    let q := affineFactor f hdim p hnormal V hV
    letI : Algebra B Γ(baseChange (S := B) q, ⊤) := sectionsAlgebra (structureMap (S := B) q)
    affineFlatSectionsAlgEquiv f hdim p hf hnormal V hV B b =
      coefficientMap (structureMap (S := B) q) b := by
  let q := affineFactor f hdim p hnormal V hV
  let : Algebra B Γ(baseChange (S := B) q, ⊤) := sectionsAlgebra (structureMap (S := B) q)
  exact (affineFlatSectionsAlgEquiv f hdim p hf hnormal V hV B).commutes b

omit [AlgebraicGeometry.IsNoetherian X] in
include hdim p in
/-- The ORIGINAL finite normalization and ORIGINAL field finite type derive Noetherianity of EVERY actual affine coefficient ring. -/
theorem affineSections_isNoetherianRing (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V) :
    IsNoetherianRing Γ(SteinCurveFactor.base f, V) := by
  let : IsFinite (SteinCurveFactor.baseMap f) := SteinCurveFactor.baseMap_isFinite f hdim p
  let q := SteinCurveFactor.baseMap f ≫ p
  let : LocallyOfFiniteType q := by dsimp only [q]; infer_instance
  let : Algebra k Γ(SteinCurveFactor.base f, V) :=
    (NormalizationFinite.affineCoefficientMap q ⟨V, hV⟩).toAlgebra
  let : Algebra.FiniteType k Γ(SteinCurveFactor.base f, V) :=
    NormalizationFinite.affineSections_finiteType q ⟨V, hV⟩
  exact Algebra.FiniteType.isNoetherianRing k _

/-- The ORIGINAL localization is genuinely flat and retains the SAME original whole coefficient equivalence. -/
def affineLocalizationSectionsAlgEquiv
    (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V)
    (M : Submonoid Γ(SteinCurveFactor.base f, V)) :
    let q := affineFactor f hdim p hnormal V hV
    let B := Localization M
    letI : Algebra B Γ(baseChange (S := B) q, ⊤) := sectionsAlgebra (structureMap (S := B) q)
    B ≃ₐ[B] Γ(baseChange (S := B) q, ⊤) :=
  affineFlatSectionsAlgEquiv f hdim p hf hnormal V hV (Localization M)

/-- ORIGINAL coefficient Noetherianity internally gives completion flatness and the SAME ORIGINAL whole coefficient equivalence. -/
def affineCompletionSectionsAlgEquiv
    (V : (SteinCurveFactor.base f).Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ(SteinCurveFactor.base f, V)) :
    let q := affineFactor f hdim p hnormal V hV
    let B := AdicCompletion I Γ(SteinCurveFactor.base f, V)
    letI : Algebra B Γ(baseChange (S := B) q, ⊤) := sectionsAlgebra (structureMap (S := B) q)
    B ≃ₐ[B] Γ(baseChange (S := B) q, ⊤) := by
  let := affineSections_isNoetherianRing f hdim p V hV
  exact affineFlatSectionsAlgEquiv f hdim p hf hnormal V hV
    (AdicCompletion I Γ(SteinCurveFactor.base f, V))

end Hironaka.Geometry.ProperSteinFlatSections
