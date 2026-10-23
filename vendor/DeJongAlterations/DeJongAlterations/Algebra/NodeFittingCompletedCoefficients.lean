import DeJongAlterations.Algebra.CompletionLocalMap
import DeJongAlterations.Algebra.NodeGeometricCompletionCoherentDifferentials
import Mathlib.RingTheory.Unramified.Basic

/-! # The ORIGINAL relative completed differential kills every completed base coefficient

The coefficient map is the actual native completion of the original local map.
The target is the completion of the ORIGINAL module, not algebraic Omega of a
formal power-series ring. No Noetherian or finite-type hypotheses are needed.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeFittingCompletedCoefficients

open NodeGeometricCompletionDerivation NodeGeometricCompletionCoherentDifferentials

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section CompletedBase

variable (A R M : Type u) [CommRing A] [CommRing R] [Algebra A R]
  [IsLocalRing A] [IsLocalRing R] [IsLocalHom (algebraMap A R)]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M]
  (D : Derivation A R M)

/-- EVERY actual completed original-base coefficient has zero completed original differential. -/
theorem completedDifferential_completedBase (a : AdicCompletion (maximalIdeal A) A) :
    completedDifferential (maximalIdeal R) D
      (CompletionLocalMap.completionMap (algebraMap A R) a) = 0 := by
  apply AdicCompletion.ext
  intro n
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal A) (n + 1) a)
  have heval := CompletionLocalMap.evalₐ_completionMap (algebraMap A R) (n + 1) a
  rw [← ha₀, Ideal.quotientMap_mk] at heval
  have hval := congrArg (Ideal.Quotient.factor
    (show maximalIdeal R ^ (n + 1) ≤ maximalIdeal R ^ (n + 1) • ⊤ from
      le_of_eq (Ideal.mul_top _).symm)) heval
  rw [AdicCompletion.factor_evalₐ_eq_eval] at hval
  change (CompletionLocalMap.completionMap (algebraMap A R) a).val (n + 1) =
    Submodule.Quotient.mk (algebraMap A R a₀) at hval
  rw [completedDifferential_val, AdicCompletion.val_zero_apply, hval,
    differentialLevel_mk, Derivation.map_algebraMap, Submodule.Quotient.mk_zero]

omit [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] in
/-- The SAME actual completed universal differential kills the ENTIRE actual completed base. -/
theorem completedUniversalDerivation_completedBase (a : AdicCompletion (maximalIdeal A) A) :
    completedUniversalDerivation A R (maximalIdeal R)
      (CompletionLocalMap.completionMap (algebraMap A R) a) = 0 :=
  completedDifferential_completedBase A R (KaehlerDifferential A R) (KaehlerDifferential.D A R) a

end CompletedBase

section ScalarEnlargement

variable {K B C P : Type u} [CommRing K] [CommRing B] [CommRing C]
  [Algebra K C] [Algebra B C] [AddCommGroup P] [Module C P] [Module K P]
  [Module B P] [IsScalarTower B C P]

/-- Actual coefficient vanishing upgrades the SAME derivation along the SAME scalar action. -/
@[simps! apply]
def overBase (D : Derivation K C P) (h : ∀ b : B, D (algebraMap B C b) = 0) :
    Derivation B C P where
  toFun := D
  map_add' := D.map_add
  map_smul' b x := by
    rw [Algebra.smul_def, RingHom.id_apply, Derivation.leibniz, h, smul_zero, add_zero,
      IsScalarTower.algebraMap_smul]
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

omit [CommRing K] [Algebra K C] [Module K P] [IsScalarTower B C P] in
/-- Any actual formally unramified coefficient algebra is killed by the enlarged-base derivation. -/
theorem derivation_unramified_coefficient (S : Type u) [CommRing S] [Algebra B S]
    [Algebra S C] [IsScalarTower B S C] [Module S P] [IsScalarTower S C P]
    [IsScalarTower B S P]
    [Algebra.FormallyUnramified B S] (D : Derivation B C P) (s : S) :
    D (algebraMap S C s) = 0 := by
  let E := D.compAlgebraMap S
  have hzero : KaehlerDifferential.D B S s = 0 := Subsingleton.elim _ _
  calc
    D (algebraMap S C s) = E.liftKaehlerDifferential (KaehlerDifferential.D B S s) :=
      (Derivation.liftKaehlerDifferential_comp_D E s).symm
    _ = 0 := by rw [hzero, map_zero]

end ScalarEnlargement

end DeJongAlterations.Algebra.NodeFittingCompletedCoefficients
