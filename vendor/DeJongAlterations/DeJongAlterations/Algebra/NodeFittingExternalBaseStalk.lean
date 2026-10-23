import DeJongAlterations.Algebra.NodeFittingOmegaStalk
import DeJongAlterations.Geometry.NodeCompletedLocalAffineBaseChangeUV

/-! # Native external coefficients versus the SAME actual local base in stalk differentials

All coefficient actions are from the original native scheme morphism; these
comparisons hold over any commutative external ring, without Noetherianity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Algebra.NodeFittingExternalBaseStalk

open NodeFittingModule

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (K : Type u) [CommRing K]

/-- The SAME native identity-spectrum coefficient action is the actual prime localization. -/
theorem nativeBaseStalk_localization (t : PrimeSpectrum K) :
    letI := Scheme.stalkAlgebra (𝟙 (Spec (.of K))) t
    IsLocalization t.asIdeal.primeCompl ((Spec (.of K)).presheaf.stalk t) := by
  have hcoeff : Scheme.baseToStalk (𝟙 (Spec (.of K))) t = StructureSheaf.toStalk K t := by
    simp only [Scheme.baseToStalk, Scheme.Modules.baseRingHom, Scheme.Hom.id_appTop,
      Category.comp_id, Scheme.ΓSpecIso_inv]
    rfl
  simpa only [Scheme.stalkAlgebra, hcoeff,
    Geometry.NodeCompletedLocalAffineBaseChangeUV.nativeSpecStalkAlgebra] using
    Geometry.NodeCompletedLocalAffineBaseChangeUV.nativeSpecStalkLocalization K t

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) (y : Y)

/-- The WHOLE actual original coefficient-map naturality produces the SAME native scalar tower. -/
theorem nativeBaseStalk_tower :
    letI := Scheme.stalkAlgebra (𝟙 (Spec (.of K))) (p y)
    letI := NodeFittingOmegaStalk.stalkAlgebra p y
    letI := Scheme.stalkAlgebra p y
    IsScalarTower K ((Spec (.of K)).presheaf.stalk (p y)) (Y.presheaf.stalk y) := by
  let := Scheme.stalkAlgebra (𝟙 (Spec (.of K))) (p y)
  let := NodeFittingOmegaStalk.stalkAlgebra p y
  let := Scheme.stalkAlgebra p y
  apply IsScalarTower.of_algebraMap_eq'
  change (Scheme.baseToStalk p y).hom =
    (p.stalkMap y).hom.comp (Scheme.baseToStalk (𝟙 (Spec (.of K))) (p y)).hom
  have h := Scheme.baseToStalk_comp_stalkMap p (𝟙 (Spec (.of K))) y
  rw [Category.comp_id] at h
  exact (congrArg CommRingCat.Hom.hom h).symm

/-- The actual external-base differential module equals the SAME native original local-base one. -/
def nativeOmegaEquiv :
    letI := Scheme.stalkAlgebra p y
    letI := NodeFittingOmegaStalk.stalkAlgebra p y
    KaehlerDifferential K (Y.presheaf.stalk y) ≃ₗ[Y.presheaf.stalk y]
      KaehlerDifferential ((Spec (.of K)).presheaf.stalk (p y)) (Y.presheaf.stalk y) := by
  letI := Scheme.stalkAlgebra p y
  letI := NodeFittingOmegaStalk.stalkAlgebra p y
  letI := Scheme.stalkAlgebra (𝟙 (Spec (.of K))) (p y)
  letI := nativeBaseStalk_localization K (p y)
  letI := nativeBaseStalk_tower K p y
  letI : Algebra.FormallyEtale K ((Spec (.of K)).presheaf.stalk (p y)) :=
    Algebra.FormallyEtale.of_isLocalization (p y).asIdeal.primeCompl
  exact NodeFittingOmega.baseEquiv K ((Spec (.of K)).presheaf.stalk (p y)) (Y.presheaf.stalk y)

/-- EVERY actual original differential is preserved in the SAME actual coefficient tower. -/
@[simp]
theorem nativeOmegaEquiv_D (r : Y.presheaf.stalk y) :
    letI := Scheme.stalkAlgebra p y
    letI := NodeFittingOmegaStalk.stalkAlgebra p y
    nativeOmegaEquiv K p y (KaehlerDifferential.D K (Y.presheaf.stalk y) r) =
      KaehlerDifferential.D ((Spec (.of K)).presheaf.stalk (p y)) (Y.presheaf.stalk y) r := by
  let := Scheme.stalkAlgebra p y
  let := NodeFittingOmegaStalk.stalkAlgebra p y
  let := Scheme.stalkAlgebra (𝟙 (Spec (.of K))) (p y)
  let := nativeBaseStalk_tower K p y
  change KaehlerDifferential.map K ((Spec (.of K)).presheaf.stalk (p y))
    (Y.presheaf.stalk y) (Y.presheaf.stalk y) (KaehlerDifferential.D K (Y.presheaf.stalk y) r) = _
  simp

variable [LocallyOfFinitePresentation p]

/-- Native external differential finite presentation follows internally from original scheme local finite presentation. -/
theorem nativeOmega_finitePresentation :
    letI := Scheme.stalkAlgebra p y
    Module.FinitePresentation (Y.presheaf.stalk y) (KaehlerDifferential K (Y.presheaf.stalk y)) := by
  let := Scheme.stalkAlgebra p y
  let := NodeFittingOmegaStalk.stalkAlgebra p y
  let := NodeFittingOmegaStalk.differentialFinitePresentation p y
  exact (nativeOmegaEquiv K p y).finitePresentation_iff.mpr inferInstance

/-- The ENTIRE intrinsic actual local-base Fitting ideal is the same native external differential ideal. -/
theorem stalkFittingIdeal_eq_nativeOmega (i : ℕ) :
    letI := Scheme.stalkAlgebra p y
    letI := nativeOmega_finitePresentation K p y
    NodeFittingOmegaStalk.ideal p i y =
      fittingIdeal (R := Y.presheaf.stalk y) (M := KaehlerDifferential K (Y.presheaf.stalk y)) i := by
  let := Scheme.stalkAlgebra p y
  let := NodeFittingOmegaStalk.stalkAlgebra p y
  let := NodeFittingOmegaStalk.differentialFinitePresentation p y
  let := nativeOmega_finitePresentation K p y
  exact (fittingIdeal_equiv (nativeOmegaEquiv K p y) i).symm

end DeJongAlterations.Algebra.NodeFittingExternalBaseStalk
