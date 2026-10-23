import DeJongAlterations.Algebra.NodeGeometricCompletionOriginalBaseChange

/-! The ORIGINAL family differential module pulled to the ACTUAL localized geometric
scalar extension and its completion, then through the SAME actual field-node model.
The coefficient ring A and original finite-type algebra R need not be Noetherian.
The actual scheme geometric-fibre affine-chart/stalk localization must be supplied by
its native localization theorem; no original relative total-space normal form is assumed. -/

noncomputable section

open TensorProduct IsLocalRing

namespace DeJongAlterations.Algebra.NodeGeometricCompletionOriginalBaseChangeUV

open NodeGeometricCompletionOriginalBaseChange NodeGeometricCompletionCoherentDifferentials
  NodeGeometricCompletionDifferentialTransport NodeGeometricCompletionFormalUV
  NodeGeometricCompletionActualUV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A R K : Type u) [CommRing A] [CommRing R] [Field K]
  [Algebra A R] [Algebra A K] [Algebra.FiniteType A R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (L : Type u) [CommRing L]
  [Algebra (ScalarExtension A R K) L] [Algebra R L] [Algebra K L]
  [IsScalarTower R (ScalarExtension A R K) L]
  [IsScalarTower K (ScalarExtension A R K) L]
  (q : Ideal (ScalarExtension A R K)) [q.IsPrime] [IsLocalization q.primeCompl L]

/-- Actual localization at the original point prime is local; no target-locality
hypothesis is an additional input to the completed field-node comparison. -/
def originalCompletedUVEquiv :
    letI := IsLocalization.AtPrime.isLocalRing L q
    (e : LocalCompletion L ≃ₐ[K] FormalUV K) →
      letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv
      letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm.toRingEquiv
      (LocalCompletion L ⊗[R] KaehlerDifferential A R) ≃ₛₗ[e.toRingHom] DifferentialModule K := by
  letI := IsLocalization.AtPrime.isLocalRing L q
  letI := localizedScalarExtension_essFiniteType A R K L q
  letI := localizedScalarExtension_isNoetherianRing A R K L q
  exact fun e => by
    letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv
    letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm.toRingEquiv
    exact (completedOriginalBaseChangeEquiv A R K L q (maximalIdeal L)).trans
      (actualGradientEquiv K L e)

/-- The pulled ORIGINAL family Ω is finitely presented over the SAME actual completed
geometric stalk; this follows internally from the actual original coherent comparison. -/
theorem originalCompletedOmega_finitePresentation :
    letI := IsLocalization.AtPrime.isLocalRing L q
    Module.FinitePresentation (LocalCompletion L)
      (LocalCompletion L ⊗[R] KaehlerDifferential A R) := by
  let := IsLocalization.AtPrime.isLocalRing L q
  let := localizedScalarExtension_essFiniteType A R K L q
  let := localizedScalarExtension_isNoetherianRing A R K L q
  let := completedOmega_finitePresentation K L (maximalIdeal L)
  exact Module.FinitePresentation.of_equiv
    (completedOriginalBaseChangeEquiv A R K L q (maximalIdeal L)).symm

/-- Every ORIGINAL family differential and every actual completed scalar retain their
actual geometric completed derivative through the SAME coefficient-compatible node model. -/
theorem originalCompletedUVEquiv_original :
    letI := IsLocalization.AtPrime.isLocalRing L q
    ∀ (e : LocalCompletion L ≃ₐ[K] FormalUV K) (a : LocalCompletion L) (r : R),
      originalCompletedUVEquiv A R K L q e (a ⊗ₜ[R] KaehlerDifferential.D A R r) =
        e a • NodeGeometricCompletionLocalUV.localOmegaGradientEquiv K
          (completedUniversalDerivation K (NodeGeometricCompletionLocalUV.LocalUV K)
            (maximalIdeal (NodeGeometricCompletionLocalUV.LocalUV K))
            ((NodeGeometricCompletionLocalUV.localCompletionFieldEquiv K).symm
              (e (algebraMap L (LocalCompletion L) (algebraMap R L r))))) := by
  let := IsLocalization.AtPrime.isLocalRing L q
  let := localizedScalarExtension_essFiniteType A R K L q
  let := localizedScalarExtension_isNoetherianRing A R K L q
  intro e a r
  change actualGradientEquiv K L e
    (completedOriginalBaseChangeEquiv A R K L q (maximalIdeal L)
      (a ⊗ₜ[R] KaehlerDifferential.D A R r)) = _
  rw [completedOriginalBaseChangeEquiv_tmul_D, map_smulₛₗ,
    ← completedUniversalDerivation_original, actualGradientEquiv_derivation]
  rfl

end DeJongAlterations.Algebra.NodeGeometricCompletionOriginalBaseChangeUV
