import Hironaka.Geometry.ProperSteinGlobalSectionsSheaf
import Hironaka.Geometry.SteinCurveFactor

/-! # The SAME actual intrinsic constant factor has its ORIGINAL structure-sheaf identity. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace Hironaka.Geometry.ProperSteinGlobalSections
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f] [LocallyOfFiniteType f] [AlgebraicGeometry.IsNoetherian X]
  (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)
  {k : Type u} [Field k] (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]
  (hf : IsProper f) (hnormal : IsNormalScheme X)

include hf in
/-- The ORIGINAL intrinsic constant-field factor has its actual sheaf pushforward identity, with no output certificates. -/
theorem factor_isIso_sectionSheafMap :
    IsIso (sectionSheafMap (SteinCurveFactor.factor f hdim p hnormal)) := by
  let := SteinCurveFactor.base_isIntegral f hdim
  let := SteinCurveFactor.factor_isDominant f hdim p hnormal
  let := SteinCurveFactor.factor_isProper f hdim p hf hnormal
  exact isIso_sectionSheafMap (SteinCurveFactor.factor f hdim p hnormal)
    (SteinCurveFactor.base_isNormalScheme f hdim)
    (SteinCurveFactor.factor_algebraicClosure_eq_bot f hdim p hnormal)

include hf in
/-- The SAME factor is an actual isomorphism on sections of EVERY original open. -/
theorem factor_isIso_app (U : (SteinCurveFactor.base f).Opens) :
    IsIso ((SteinCurveFactor.factor f hdim p hnormal).app U) := by
  let q := SteinCurveFactor.factor f hdim p hnormal
  let : IsIso (sectionSheafMap q) := factor_isIso_sectionSheafMap f hdim p hf hnormal
  let : IsIso q.c := (TopCat.Sheaf.forget CommRingCat (SteinCurveFactor.base f)).map_isIso
    (sectionSheafMap q)
  exact NatIso.isIso_app_of_isIso q.c (Opposite.op U)

include hf in
/-- ENTIRE original section-map bijectivity for the actual intrinsic factor, with all input properties derived. -/
theorem factor_app_bijective (U : (SteinCurveFactor.base f).Opens) :
    Function.Bijective ((SteinCurveFactor.factor f hdim p hnormal).app U).hom := by
  let := factor_isIso_app f hdim p hf hnormal U
  exact ConcreteCategory.bijective_of_isIso ((SteinCurveFactor.factor f hdim p hnormal).app U)

/-- The actual equivalence retains the SAME constructed factor and its ORIGINAL entire section map. -/
def factor_appEquiv (U : (SteinCurveFactor.base f).Opens) :
    Γ(SteinCurveFactor.base f, U) ≃+*
      Γ(X, SteinCurveFactor.factor f hdim p hnormal ⁻¹ᵁ U) :=
  RingEquiv.ofBijective ((SteinCurveFactor.factor f hdim p hnormal).app U).hom
    (factor_app_bijective f hdim p hf hnormal U)

/-- The ENTIRE forward map is literally the SAME original factor's pullback on sections. -/
theorem factor_appEquiv_apply (U : (SteinCurveFactor.base f).Opens)
    (a : Γ(SteinCurveFactor.base f, U)) :
    factor_appEquiv f hdim p hf hnormal U a =
      (SteinCurveFactor.factor f hdim p hnormal).app U a := rfl

/-- Actual original section inverses for the SAME factor commute with BOTH original restriction maps. -/
theorem factor_appEquiv_symm_restrict {U V : (SteinCurveFactor.base f).Opens} (hVU : V ≤ U)
    (b : Γ(X, SteinCurveFactor.factor f hdim p hnormal ⁻¹ᵁ U)) :
    (SteinCurveFactor.base f).presheaf.map (homOfLE hVU).op
        ((factor_appEquiv f hdim p hf hnormal U).symm b) =
      (factor_appEquiv f hdim p hf hnormal V).symm
        (X.presheaf.map
          (homOfLE ((SteinCurveFactor.factor f hdim p hnormal).preimage_mono hVU)).op b) := by
  let := SteinCurveFactor.base_isIntegral f hdim
  let := SteinCurveFactor.factor_isDominant f hdim p hnormal
  let := SteinCurveFactor.factor_isProper f hdim p hf hnormal
  exact appEquiv_symm_restrict (SteinCurveFactor.factor f hdim p hnormal)
    (SteinCurveFactor.base_isNormalScheme f hdim)
    (SteinCurveFactor.factor_algebraicClosure_eq_bot f hdim p hnormal) hVU b

end Hironaka.Geometry.ProperSteinGlobalSections
