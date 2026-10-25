import DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV
import DeJongAlterations.Algebra.NodeGeometricCompletionDifferentialTransport
import Mathlib.RingTheory.Etale.Kaehler

/-! The ACTUAL rational local uv model: completion of its ORIGINAL differential module
compared with the literal formal two-coordinate gradient cokernel, using native localization
of ORIGINAL Kaehler differentials and actual canonical ring completion maps. -/

noncomputable section

open TensorProduct IsLocalRing

namespace DeJongAlterations.Algebra.NodeGeometricCompletionLocalUV

open NodeFittingGeneral NodeGeometricCompletionCoherentDifferentials
  NodeGeometricCompletionFormalModel NodeGeometricCompletionFormalCoordinates
  NodeGeometricCompletionFormalUV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (K : Type u) [Field K]

instance polynomialUV_noetherian : IsNoetherianRing (PolynomialUV K) :=
  isNoetherianRing_of_surjective (MvPolynomial (Fin 2) K) _
    (Ideal.Quotient.mk (polynomialIdeal (uvPolynomial K))) Ideal.Quotient.mk_surjective

instance uvOrigin_isMaximal : (coordinateIdeal K (uvPolynomial K)).IsMaximal :=
  Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by
    simpa using (show polynomialIdeal (uvPolynomial K) ≤ MvPolynomial.idealOfVars (Fin 2) K from by
      rw [NodeCompletion.idealOfVars_eq_ker_constantCoeff]
      apply Ideal.span_le.mpr
      rintro f rfl
      simp [uvPolynomial]))

/-- The literal original localization at the rational node origin. -/
def LocalUV := Localization.AtPrime (coordinateIdeal K (uvPolynomial K))

instance : CommRing (LocalUV K) :=
  inferInstanceAs (CommRing (Localization.AtPrime (coordinateIdeal K (uvPolynomial K))))
instance : _root_.Algebra (PolynomialUV K) (LocalUV K) :=
  inferInstanceAs (_root_.Algebra (PolynomialUV K)
    (Localization.AtPrime (coordinateIdeal K (uvPolynomial K))))
instance : _root_.Algebra K (LocalUV K) :=
  inferInstanceAs (_root_.Algebra K (Localization.AtPrime (coordinateIdeal K (uvPolynomial K))))
instance : IsScalarTower K (PolynomialUV K) (LocalUV K) :=
  inferInstanceAs (IsScalarTower K (PolynomialUV K)
    (Localization.AtPrime (coordinateIdeal K (uvPolynomial K))))
instance : IsLocalRing (LocalUV K) :=
  inferInstanceAs (IsLocalRing (Localization.AtPrime (coordinateIdeal K (uvPolynomial K))))
instance : IsLocalization.AtPrime (LocalUV K) (coordinateIdeal K (uvPolynomial K)) :=
  inferInstanceAs (IsLocalization.AtPrime
    (Localization.AtPrime (coordinateIdeal K (uvPolynomial K))) (coordinateIdeal K (uvPolynomial K)))
instance : IsNoetherianRing (LocalUV K) :=
  inferInstanceAs (IsNoetherianRing (Localization.AtPrime (coordinateIdeal K (uvPolynomial K))))
instance : _root_.Algebra.EssFiniteType K (LocalUV K) :=
  inferInstanceAs (_root_.Algebra.EssFiniteType K
    (Localization.AtPrime (coordinateIdeal K (uvPolynomial K))))

instance : SMulCommClass K (LocalUV K) (LocalUV K) where
  smul_comm a b c := by
    simp only [Algebra.smul_def]
    ring

instance : SMulCommClass K (PolynomialUV K) (LocalUV K) where
  smul_comm a b c := by
    simp only [Algebra.smul_def]
    ring

abbrev LocalUVCompletion := AdicCompletion (R := LocalUV K) (maximalIdeal (LocalUV K)) (LocalUV K)
abbrev LocalUVOmega := CompletedOmega K (LocalUV K) (maximalIdeal (LocalUV K))

local instance localUV_formallyEtale : _root_.Algebra.FormallyEtale (PolynomialUV K) (LocalUV K) :=
  _root_.Algebra.FormallyEtale.of_isLocalization
    (Rₘ := LocalUV K) (coordinateIdeal K (uvPolynomial K)).primeCompl

/-- The SAME canonical completion of the literal actual local node, over the WHOLE original P. -/
def localCompletionEquiv : LocalUVCompletion K ≃ₐ[PolynomialUV K] FormalUV K :=
  (AdicCompletion.localizationAlgEquiv (coordinateIdeal K (uvPolynomial K)) (LocalUV K)).symm.trans
    (completionOriginalAlgEquiv K (uvPolynomial K))

/-- Every original P-element retains its exact original value through the actual local model. -/
theorem localCompletionEquiv_original (p : PolynomialUV K) :
    localCompletionEquiv K (AdicCompletion.of (maximalIdeal (LocalUV K)) (LocalUV K)
      (algebraMap (PolynomialUV K) (LocalUV K) p)) = polynomialToFormal (uvPolynomial K) p := by
  change completionOriginalAlgEquiv K (uvPolynomial K)
    ((AdicCompletion.localizationAlgEquiv _ (LocalUV K)).symm
      (AdicCompletion.of _ _ (algebraMap (PolynomialUV K) (LocalUV K) p))) = _
  rw [← AdicCompletion.localizationAlgEquiv_of (coordinateIdeal K (uvPolynomial K)) (LocalUV K) p,
    AlgEquiv.symm_apply_apply]
  exact completionEquiv_original K (uvPolynomial K) p

/-- Both actual original local coordinate classes become the literal formal coordinates. -/
theorem localCompletionEquiv_coordinate (i : Fin 2) :
    localCompletionEquiv K (AdicCompletion.of (maximalIdeal (LocalUV K)) (LocalUV K)
      (algebraMap (PolynomialUV K) (LocalUV K)
        (Ideal.Quotient.mk (polynomialIdeal (uvPolynomial K)) (MvPolynomial.X i)))) = coordinate K i := by
  rw [localCompletionEquiv_original, polynomialToFormal_coordinate]
  rfl

/-- Native ORIGINAL differential localization, not algebraic differentials of formal series. -/
def originalLocalizationOmegaEquiv :
    LocalUV K ⊗[PolynomialUV K] KaehlerDifferential K (PolynomialUV K) ≃ₗ[LocalUV K]
      KaehlerDifferential K (LocalUV K) :=
  KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (PolynomialUV K) (LocalUV K)

/-- The actual local ORIGINAL coherent completion as a tensor of ORIGINAL polynomial differentials. -/
def localOmegaTensorEquiv :
    LocalUVOmega K ≃ₗ[LocalUVCompletion K]
      LocalUVCompletion K ⊗[PolynomialUV K] KaehlerDifferential K (PolynomialUV K) :=
  (completedOmegaTensorEquiv K (LocalUV K) (maximalIdeal (LocalUV K))).symm.trans
    ((LinearEquiv.baseChange (LocalUV K) (LocalUVCompletion K) _ _
      (originalLocalizationOmegaEquiv K).symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (PolynomialUV K) (LocalUV K)
        (LocalUVCompletion K) (LocalUVCompletion K) (KaehlerDifferential K (PolynomialUV K))))

/-- Every original P-coordinate differential retains its ORIGINAL value through localization and completion. -/
theorem localOmegaTensorEquiv_original (p : PolynomialUV K) :
    localOmegaTensorEquiv K
      (AdicCompletion.of (maximalIdeal (LocalUV K)) (KaehlerDifferential K (LocalUV K))
        (KaehlerDifferential.D K (LocalUV K) (algebraMap (PolynomialUV K) (LocalUV K) p))) =
      1 ⊗ₜ[PolynomialUV K] KaehlerDifferential.D K (PolynomialUV K) p := by
  unfold localOmegaTensorEquiv completedOmegaTensorEquiv originalLocalizationOmegaEquiv
  simp only [LinearEquiv.trans_apply, AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of,
    LinearEquiv.baseChange_tmul]
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

/-- The completed ORIGINAL actual local differential module, along the SAME canonical formal completion map. -/
def localOmegaFormalEquiv : LocalUVOmega K ≃ₗ[PolynomialUV K]
    FormalModelDifferentials (uvPolynomial K) :=
  ((localOmegaTensorEquiv K).restrictScalars (PolynomialUV K)).trans
    (TensorProduct.congr (localCompletionEquiv K).toLinearEquiv (LinearEquiv.refl _ _))

/-- The entire completed local scalar action is carried through the SAME actual formal completion map. -/
theorem localOmegaFormalEquiv_smul (a : LocalUVCompletion K) (ω : LocalUVOmega K) :
    localOmegaFormalEquiv K (a • ω) = localCompletionEquiv K a • localOmegaFormalEquiv K ω := by
  obtain ⟨t, rfl⟩ := (localOmegaTensorEquiv K).symm.surjective ω
  rw [← map_smul]
  simp only [localOmegaFormalEquiv, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.apply_symm_apply]
  induction t using TensorProduct.induction_on with
  | zero => rw [TensorProduct.smul_zero, map_zero, smul_zero]
  | tmul b ω => simp [smul_tmul', map_mul, smul_eq_mul]
  | add t s ht hs => rw [TensorProduct.smul_add, map_add, map_add, ht, hs, smul_add]

/-- Every ORIGINAL local coordinate differential maps to its actual original pulled polynomial value. -/
theorem localOmegaFormalEquiv_original (p : PolynomialUV K) :
    localOmegaFormalEquiv K
      (AdicCompletion.of (maximalIdeal (LocalUV K)) (KaehlerDifferential K (LocalUV K))
        (KaehlerDifferential.D K (LocalUV K) (algebraMap (PolynomialUV K) (LocalUV K) p))) =
      1 ⊗ₜ[PolynomialUV K] KaehlerDifferential.D K (PolynomialUV K) p := by
  unfold localOmegaFormalEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    localOmegaTensorEquiv_original, TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply,
    map_one, LinearEquiv.refl_apply]

/-- The SAME actual canonical local completion is also over the ORIGINAL field. -/
def localCompletionFieldEquiv : LocalUVCompletion K ≃ₐ[K] FormalUV K :=
  (localCompletionEquiv K).restrictScalars K

/-- The literal finite relation (v,u), through the actual original polynomial differential map. -/
def formalDifferentialEquiv :
    FormalModelDifferentials (uvPolynomial K) ≃ₗ[FormalUV K] DifferentialModule K :=
  (gradientCokernelEquiv K (uvPolynomial K)).symm.trans
    (Submodule.quotEquivOfEq _ _ (by rw [gradient_uv]))

theorem formalDifferentialEquiv_coordinate (i : Fin 2) :
    formalDifferentialEquiv K
      (1 ⊗ₜ[PolynomialUV K] KaehlerDifferential.D K (PolynomialUV K)
        (Ideal.Quotient.mk (polynomialIdeal (uvPolynomial K)) (MvPolynomial.X i))) =
      Submodule.Quotient.mk (Pi.single i 1) := by
  rw [← gradientCokernelEquiv_coordinate K (uvPolynomial K) i]
  unfold formalDifferentialEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- The ACTUAL local original coherent completion has the literal uv finite differential relation. -/
def localOmegaGradientEquiv : LocalUVOmega K ≃ₗ[PolynomialUV K] DifferentialModule K :=
  (localOmegaFormalEquiv K).trans ((formalDifferentialEquiv K).restrictScalars (PolynomialUV K))

/-- Both actual ORIGINAL local coordinate differentials are the literal standard classes. -/
theorem localOmegaGradientEquiv_coordinate (i : Fin 2) :
    localOmegaGradientEquiv K
      (AdicCompletion.of (maximalIdeal (LocalUV K)) (KaehlerDifferential K (LocalUV K))
        (KaehlerDifferential.D K (LocalUV K) (algebraMap (PolynomialUV K) (LocalUV K)
          (Ideal.Quotient.mk (polynomialIdeal (uvPolynomial K)) (MvPolynomial.X i))))) =
      Submodule.Quotient.mk (Pi.single i 1) := by
  unfold localOmegaGradientEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    localOmegaFormalEquiv_original, formalDifferentialEquiv_coordinate]

/-- Equivariance retains EVERY actual completed local scalar through the SAME canonical ring map. -/
theorem localOmegaGradientEquiv_smul (a : LocalUVCompletion K) (ω : LocalUVOmega K) :
    localOmegaGradientEquiv K (a • ω) =
      localCompletionFieldEquiv K a • localOmegaGradientEquiv K ω := by
  unfold localOmegaGradientEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [localOmegaFormalEquiv_smul, map_smul]
  rfl

local instance : RingHomInvPair (localCompletionFieldEquiv K).toRingHom
    (localCompletionFieldEquiv K).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (localCompletionFieldEquiv K).toRingEquiv

local instance : RingHomInvPair (localCompletionFieldEquiv K).symm.toRingHom
    (localCompletionFieldEquiv K).toRingHom :=
  RingHomInvPair.of_ringEquiv (localCompletionFieldEquiv K).symm.toRingEquiv

/-- The actual local-to-formal finite coherent comparison, as an honest semilinear map. -/
def localOmegaGradientSemilinearMap :
    LocalUVOmega K →ₛₗ[(localCompletionFieldEquiv K).toRingHom] DifferentialModule K where
  toFun := localOmegaGradientEquiv K
  map_add' := (localOmegaGradientEquiv K).map_add
  map_smul' := localOmegaGradientEquiv_smul K

/-- Honest semilinear equivalence of the ORIGINAL actual local differential completion
with the literal formal finite relation module. -/
def localOmegaGradientSemilinearEquiv :
    LocalUVOmega K ≃ₛₗ[(localCompletionFieldEquiv K).toRingHom] DifferentialModule K :=
  LinearEquiv.ofBijective (localOmegaGradientSemilinearMap K) (localOmegaGradientEquiv K).bijective

end DeJongAlterations.Algebra.NodeGeometricCompletionLocalUV
