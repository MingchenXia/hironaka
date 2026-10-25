import DeJongAlterations.Algebra.CompletionRegularityBasics
import DeJongAlterations.Algebra.AdicCompletionTransportQuotient
import Mathlib.RingTheory.LocalRing.Quotient

/-! The actual original local quotient and its literal maximal-adic completion. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.CompletionRegularityQuotient

open CompletionRegularityBasics

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Completion of the actual original local quotient, with its actual maximal ideal. -/
def quotientCompletionEquiv (J : Ideal R) [IsLocalRing (R ⧸ J)] :
    (Completion R ⧸ J.map (algebraMap R (Completion R))) ≃+* Completion (R ⧸ J) :=
  (AdicCompletion.quotientAlgEquiv (maximalIdeal R) J).toRingEquiv.trans
    (AdicCompletion.congrRingEquiv _ _ (RingEquiv.refl (R ⧸ J)) (by
      simpa using (map_maximalIdeal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).symm))

/-- The equivalence preserves every original coefficient class and the literal completion map. -/
theorem quotientCompletionEquiv_coefficient (J : Ideal R) [IsLocalRing (R ⧸ J)] (a : R) :
    quotientCompletionEquiv J
      (Ideal.Quotient.mk _ (AdicCompletion.of (maximalIdeal R) R a)) =
        AdicCompletion.of (maximalIdeal (R ⧸ J)) (R ⧸ J) (Ideal.Quotient.mk J a) := by
  simp only [quotientCompletionEquiv, RingEquiv.trans_apply]
  exact AdicCompletion.congrRingEquiv_of _ _ _ _ _

/-- The literal completion quotient by the original coefficient parameter. -/
def principalQuotientCompletionEquiv (t : R) [IsLocalRing (R ⧸ Ideal.span {t})] :
    (Completion R ⧸ Ideal.span {algebraMap R (Completion R) t}) ≃+*
      Completion (R ⧸ Ideal.span {t}) :=
  (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton] :
    Ideal.span {algebraMap R (Completion R) t} = (Ideal.span {t}).map (algebraMap R (Completion R)))).trans
      (quotientCompletionEquiv (Ideal.span {t}))

end DeJongAlterations.Algebra.CompletionRegularityQuotient
