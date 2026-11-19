/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Geometry.ProperSteinProjectiveCechSplitResidueCompletion
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Localization

/-! # Actual complete flat Noetherian local lifts of original prescribed-field points

Closed native constructions adapted from same-repository
`EnvelopeProperty/EnvelopeProperty/AlgGeom/FlatLocalFieldLift.lean`,
SHA256 75724287fce1c9c9615cb8748bda1aba65f6c2f85510dfce771a2d1a6f53fd2f,
and `Global/FibreCoefficientField.lean`,
SHA256 1e69ffe3eb8d10eefe611700764c4aba54e981b284029eab606aa4a14b406572.
All completion Noetherianity comes from OWN closed native power-series
surjectivity. No birational, characteristic-zero or other-project import occurs.
-/
open scoped TensorProduct
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.FlatLocalFieldLift
set_option maxHeartbeats 200000
variable {F A K : Type u} [Field F] [CommRing A] [Field K]
  [Algebra F A] [Algebra F K]

/-- The literal ORIGINAL tensor evaluation retains both original field coefficients. -/
def tensorEvaluation (w : A →ₐ[F] K) : A ⊗[F] K →ₐ[F] K :=
  Algebra.TensorProduct.lift w (AlgHom.id F K) fun _ _ => Commute.all _ _

/-- Every original prescribed-field element is the value of its actual original coefficient tensor. -/
theorem tensorEvaluation_surjective (w : A →ₐ[F] K) : Function.Surjective (tensorEvaluation w) := by
  intro k
  refine ⟨1 ⊗ₜ[F] k, ?_⟩
  simp [tensorEvaluation]

/-- The ENTIRE original A coefficient map is retained in the original tensor evaluation. -/
theorem tensorEvaluation_comp (w : A →ₐ[F] K) :
    (tensorEvaluation w).toRingHom.comp (algebraMap A (A ⊗[F] K)) = w.toRingHom := by
  ext a
  simp [tensorEvaluation]

/-- Finite type over the SAME original prescribed field internally derives actual tensor-ring Noetherianity. -/
theorem isNoetherianRing_tensor [Algebra.FiniteType F A] : IsNoetherianRing (A ⊗[F] K) := by
  let : Algebra K (A ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.FiniteType K (A ⊗[F] K) :=
    Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType K (K ⊗[F] A))
      (Algebra.TensorProduct.commRight F K A)
  exact Algebra.FiniteType.isNoetherianRing K (A ⊗[F] K)

private instance tensorEvaluation_ker_prime (w : A →ₐ[F] K) :
    (RingHom.ker (tensorEvaluation w).toRingHom).IsPrime :=
  (RingHom.ker_isMaximal_of_surjective _ (tensorEvaluation_surjective w)).isPrime

/-- The actual ORIGINAL localization at the actual evaluation kernel. -/
abbrev localRing (w : A →ₐ[F] K) :=
  Localization.AtPrime (RingHom.ker (tensorEvaluation w).toRingHom)

/-- The actual localization lift evaluates into the SAME original prescribed field. -/
def localEvaluation (w : A →ₐ[F] K) : localRing w →+* K :=
  IsLocalization.lift (fun s : (RingHom.ker (tensorEvaluation w).toRingHom).primeCompl =>
    isUnit_iff_ne_zero.mpr s.2)

/-- EVERY original tensor element keeps its whole original field value in the actual localization. -/
theorem localEvaluation_algebraMap (w : A →ₐ[F] K) (t : A ⊗[F] K) :
    localEvaluation w (algebraMap (A ⊗[F] K) (localRing w) t) = tensorEvaluation w t :=
  IsLocalization.lift_eq _ t

/-- The original prescribed field has its canonical actual coefficient section. -/
def localCoefficient (w : A →ₐ[F] K) : K →+* localRing w :=
  (algebraMap (A ⊗[F] K) (localRing w)).comp Algebra.TensorProduct.includeRight.toRingHom

/-- Every original field coefficient evaluates to itself through the literal original section. -/
theorem localEvaluation_coefficient (w : A →ₐ[F] K) (k : K) :
    localEvaluation w (localCoefficient w k) = k := by
  change localEvaluation w (algebraMap (A ⊗[F] K) (localRing w) (1 ⊗ₜ[F] k)) = k
  rw [localEvaluation_algebraMap]
  simp [tensorEvaluation]

/-- The WHOLE original section/evaluation composite is the identity on the SAME original field. -/
theorem localEvaluation_comp_coefficient (w : A →ₐ[F] K) :
    (localEvaluation w).comp (localCoefficient w) = RingHom.id K := by
  ext k
  exact localEvaluation_coefficient w k

theorem localEvaluation_surjective (w : A →ₐ[F] K) : Function.Surjective (localEvaluation w) :=
  fun k => ⟨localCoefficient w k, localEvaluation_coefficient w k⟩

/-- The actual original local evaluation has EXACTLY its actual maximal ideal as kernel. -/
theorem localEvaluation_ker (w : A →ₐ[F] K) :
    RingHom.ker (localEvaluation w) = IsLocalRing.maximalIdeal (localRing w) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (localEvaluation_surjective w))

/-- The ENTIRE original coefficient A-to-K triangle is retained, before completion. -/
theorem localEvaluation_comp_original (w : A →ₐ[F] K) :
    (localEvaluation w).comp (algebraMap A (localRing w)) = w.toRingHom := by
  ext a
  change localEvaluation w (algebraMap (A ⊗[F] K) (localRing w)
    (algebraMap A (A ⊗[F] K) a)) = w a
  rw [localEvaluation_algebraMap]
  exact RingHom.congr_fun (tensorEvaluation_comp w) a

/-- ORIGINAL finite type over the original field gives Noetherianity of the SAME actual tensor localization. -/
theorem isNoetherianRing_localRing [Algebra.FiniteType F A] (w : A →ₐ[F] K) :
    IsNoetherianRing (localRing w) := by
  let := isNoetherianRing_tensor (F := F) (A := A) (K := K)
  infer_instance

/-- Actual tensor extension and actual localization internally derive original A-flatness. -/
theorem flat_localRing (w : A →ₐ[F] K) : Module.Flat A (localRing w) :=
  Module.Flat.trans A (A ⊗[F] K) (localRing w)

/-- The actual original maximal-adic completion of the SAME canonical tensor localization. -/
abbrev completedLocalRing (w : A →ₐ[F] K) :=
  AdicCompletion (IsLocalRing.maximalIdeal (localRing w)) (localRing w)

/-- The actual canonical prescribed-field section DERIVES Noetherianity of the SAME original completion in every characteristic. -/
theorem isNoetherianRing_completedLocalRing [Algebra.FiniteType F A] (w : A →ₐ[F] K) :
    IsNoetherianRing (completedLocalRing w) := by
  let := isNoetherianRing_localRing w
  exact SplitResidueCompletion.isNoetherianRing_completion_of_section (localEvaluation w)
    (localEvaluation_ker w) (localCoefficient w) (localEvaluation_comp_coefficient w)

/-- Every ORIGINAL finite-type field point internally produces its actual complete flat Noetherian local coefficient model and EXACT original residue triangle. -/
theorem exists_noetherian_completed_flat_local_lift [Algebra.FiniteType F A] (w : A →ₐ[F] K) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : IsNoetherianRing B)
      (_ : IsLocalRing B), Module.Flat A B ∧
      IsAdicComplete (IsLocalRing.maximalIdeal B) B ∧
      ∃ γ : B →+* K, Function.Surjective γ ∧
        RingHom.ker γ = IsLocalRing.maximalIdeal B ∧ γ.comp (algebraMap A B) = w.toRingHom := by
  let R := localRing w
  let := isNoetherianRing_localRing w
  let := flat_localRing w
  let B := completedLocalRing w
  let := isNoetherianRing_completedLocalRing w
  let β := localEvaluation w
  let γ := SplitResidueCompletion.completionEvaluation β (localEvaluation_ker w)
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.Flat.trans A R B, inferInstance, γ,
    SplitResidueCompletion.completionEvaluation_surjective β (localEvaluation_surjective w)
      (localEvaluation_ker w),
    SplitResidueCompletion.completionEvaluation_ker β (localEvaluation_surjective w)
      (localEvaluation_ker w), ?_⟩
  ext a
  change SplitResidueCompletion.completionEvaluation β (localEvaluation_ker w)
    (algebraMap R B (algebraMap A R a)) = w a
  rw [SplitResidueCompletion.completionEvaluation_algebraMap]
  exact RingHom.congr_fun (localEvaluation_comp_original w) a

end Hironaka.Geometry.ProperSteinProjectiveCech.FlatLocalFieldLift
