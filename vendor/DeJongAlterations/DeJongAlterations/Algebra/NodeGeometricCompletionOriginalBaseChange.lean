import DeJongAlterations.Algebra.NodeGeometricCompletionActualUV
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Etale.Kaehler

/-! Native base change and actual localization of the ORIGINAL algebraic coherent Ω.
All maps are from the original algebra and actual tensor product, before completion.
No tensor-of-formal-series or algebraic differential module of a formal completion occurs. -/

noncomputable section

open TensorProduct IsLocalRing

namespace DeJongAlterations.Algebra.NodeGeometricCompletionOriginalBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A R K : Type u) [CommRing A] [CommRing R] [CommRing K]
  [Algebra A R] [Algebra A K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The literal ORIGINAL algebra scalar extension. -/
abbrev ScalarExtension := K ⊗[A] R

variable (L : Type u) [CommRing L]
  [Algebra (ScalarExtension A R K) L] [Algebra R L] [Algebra K L]
  [IsScalarTower R (ScalarExtension A R K) L]
  [IsScalarTower K (ScalarExtension A R K) L]
  (q : Ideal (ScalarExtension A R K)) [q.IsPrime] [IsLocalization q.primeCompl L]

/-- The ORIGINAL relative differential module, pulled to the actual localized scalar
extension, is the actual field-relative differential module of that SAME local algebra. -/
def originalBaseChangeLocalizationEquiv :
    L ⊗[R] KaehlerDifferential A R ≃ₗ[L] KaehlerDifferential K L := by
  letI : Algebra.FormallyEtale (ScalarExtension A R K) L :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R (ScalarExtension A R K) L L
    (KaehlerDifferential A R)).symm.trans
    ((LinearEquiv.baseChange (ScalarExtension A R K) L _ _
      (KaehlerDifferential.tensorKaehlerEquiv A K R (ScalarExtension A R K))).trans
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (ScalarExtension A R K) L))

/-- EVERY original relative differential and every actual localized scalar retain their
actual original value through the native base change and localization. -/
theorem originalBaseChangeLocalizationEquiv_tmul_D (l : L) (r : R) :
    originalBaseChangeLocalizationEquiv A R K L q (l ⊗ₜ[R] KaehlerDifferential.D A R r) =
      l • KaehlerDifferential.D K L (algebraMap R L r) := by
  let : Algebra.FormallyEtale (ScalarExtension A R K) L :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  unfold originalBaseChangeLocalizationEquiv
  simp only [LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_tmul, KaehlerDifferential.tensorKaehlerEquiv_tmul_D,
    one_smul, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
  rw [← IsScalarTower.algebraMap_apply R (ScalarExtension A R K) L]

variable [IsNoetherianRing K] [Algebra.FiniteType A R]

omit [IsNoetherianRing K] [Algebra R L]
  [IsScalarTower R (ScalarExtension A R K) L] in
include A R q in
/-- Original finite type is preserved in the literal scalar extension, then the actual
localization is essentially of finite type over the SAME coefficient ring. -/
theorem localizedScalarExtension_essFiniteType : Algebra.EssFiniteType K L := by
  let : Algebra.FiniteType K (ScalarExtension A R K) := inferInstance
  let : Algebra.EssFiniteType (ScalarExtension A R K) L :=
    Algebra.EssFiniteType.of_isLocalization L q.primeCompl
  exact Algebra.EssFiniteType.comp K (ScalarExtension A R K) L

omit [Algebra R L] [IsScalarTower R (ScalarExtension A R K) L] in
include A R K q in
/-- Original Noetherian coefficients and original finite type imply Noetherianity of
the actual localized scalar extension; no Noetherian hypothesis on A or R is input. -/
theorem localizedScalarExtension_isNoetherianRing : IsNoetherianRing L := by
  let : Algebra.EssFiniteType K L := localizedScalarExtension_essFiniteType A R K L q
  exact Algebra.EssFiniteType.isNoetherianRing K L

/-- The completion of the ACTUAL localized base-change Ω is the pullback of the
ORIGINAL relative Ω, with the SAME actual completed and original scalar maps. -/
def completedOriginalBaseChangeEquiv (I : Ideal L) :
    AdicCompletion I L ⊗[R] KaehlerDifferential A R ≃ₗ[AdicCompletion I L]
      NodeGeometricCompletionCoherentDifferentials.CompletedOmega K L I := by
  letI := localizedScalarExtension_essFiniteType A R K L q
  letI := localizedScalarExtension_isNoetherianRing A R K L q
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R L (AdicCompletion I L)
    (AdicCompletion I L) (KaehlerDifferential A R)).symm.trans
    ((LinearEquiv.baseChange L (AdicCompletion I L) _ _
      (originalBaseChangeLocalizationEquiv A R K L q)).trans
      (NodeGeometricCompletionCoherentDifferentials.completedOmegaTensorEquiv K L I))

/-- Every ORIGINAL family differential and arbitrary completed scalar retain their
actual completed geometric value through the full base-change/localization/completion chain. -/
theorem completedOriginalBaseChangeEquiv_tmul_D (I : Ideal L)
    (l : AdicCompletion I L) (r : R) :
    completedOriginalBaseChangeEquiv A R K L q I (l ⊗ₜ[R] KaehlerDifferential.D A R r) =
      l • AdicCompletion.of I (KaehlerDifferential K L)
        (KaehlerDifferential.D K L (algebraMap R L r)) := by
  let := localizedScalarExtension_essFiniteType A R K L q
  let := localizedScalarExtension_isNoetherianRing A R K L q
  unfold completedOriginalBaseChangeEquiv
  simp only [LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_tmul, originalBaseChangeLocalizationEquiv_tmul_D, one_smul,
    NodeGeometricCompletionCoherentDifferentials.completedOmegaTensorEquiv_tmul]

end DeJongAlterations.Algebra.NodeGeometricCompletionOriginalBaseChange
