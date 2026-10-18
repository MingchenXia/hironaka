/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaHolomorphicJetChartInvariance

set_option autoImplicit false
namespace Hironaka.HironakaSmoothCentreRealDomainActualAmbientHS
noncomputable section
open HolGerm HironakaHolomorphicPointJets

section GenuineLocalAlgebras
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
  [IsLocalRing R] [IsLocalRing S]

/-- The genuine original local algebra map retains ALL actual ambient maximal-power quotient classes. -/
def actualLocalAmbientJetAlgEquiv (E : R ≃ₐ[ℂ] S) (I : Ideal R) (s : ℕ) :
    (R ⧸ (I ⊔ IsLocalRing.maximalIdeal R ^ s)) ≃ₐ[ℂ]
      (S ⧸ (Ideal.map E.toRingEquiv.toRingHom I ⊔ IsLocalRing.maximalIdeal S ^ s)) :=
  Ideal.quotientEquivAlg _ _ E (by
    rw [Ideal.map_sup,Ideal.map_pow,
      IsLocalRing.map_maximalIdeal_of_surjective (E : R →+* S) E.surjective]
    rfl)

/-- EVERY original ambient numerator keeps its SAME actual whole algebra image. -/
theorem actualLocalAmbientJetAlgEquiv_mk (E : R ≃ₐ[ℂ] S) (I : Ideal R) (s : ℕ) (g : R) :
    actualLocalAmbientJetAlgEquiv E I s
      (Ideal.Quotient.mk (I ⊔ IsLocalRing.maximalIdeal R ^ s) g) =
        Ideal.Quotient.mk
          (Ideal.map E.toRingEquiv.toRingHom I ⊔ IsLocalRing.maximalIdeal S ^ s) (E g) := rfl

end GenuineLocalAlgebras

/-- The EXISTING original ambient HS is invariant under every genuine original complex germ algebra equivalence. -/
theorem actualAmbientHS_eq_of_genuineAlgEquiv {n : ℕ}
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n))
    (I : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.map E.toRingEquiv.toRingHom I) ℓ = hilbertSamuelValue I ℓ :=
  (actualLocalAmbientJetAlgEquiv E I (ℓ+1)).toLinearEquiv.finrank_eq.symm

end
end Hironaka.HironakaSmoothCentreRealDomainActualAmbientHS
