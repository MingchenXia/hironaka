import DeJongAlterations.Algebra.CompletionLocalMap
import DeJongAlterations.Algebra.CompletionIdealQuotient

/-! The actual closed fibre of the induced map on literal local completions. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.CompletionLocalMap

open CompletionRegularityBasics

universe u
variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  (f : A →+* B) [IsLocalHom f]

/-- The literal induced completed map preserves the full extension of every original ideal. -/
theorem map_completionMap_map (I : Ideal A) :
    (I.map (algebraMap A (Completion A))).map (completionMap f) =
      (I.map f).map (algebraMap B (Completion B)) := by
  rw [Ideal.map_map, Ideal.map_map]
  have hcomp : (completionMap f).comp (algebraMap A (Completion A)) =
      (algebraMap B (Completion B)).comp f :=
    RingHom.ext (completionMap_algebraMap f)
  rw [hcomp]

/-- The actual original closed-fibre ideal in the original target local ring. -/
def closedFiberIdeal : Ideal B := (maximalIdeal A).map f

/-- Original locality supplies the actual proper local quotient, without a quotient certificate. -/
theorem closedFiberIdeal_le_maximalIdeal : closedFiberIdeal f ≤ maximalIdeal B :=
  map_maximalIdeal_le f

variable [IsNoetherianRing A]

/-- The actual maximal-ideal image in the completed target is the extension of the original closed-fibre ideal. -/
theorem closedFiberIdeal_completed :
    (maximalIdeal (Completion A)).map (completionMap f) =
      (closedFiberIdeal f).map (algebraMap B (Completion B)) := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact map_completionMap_map f (maximalIdeal A)

variable [IsNoetherianRing B]

/-- The closed fibre of the literal completed map is the literal maximal-adic completion
of the original closed fibre. Both the quotient structure and comparison are constructed. -/
def closedFiberEquiv :
    letI := CompletionIdealQuotient.quotientLocalRing (closedFiberIdeal f)
      (closedFiberIdeal_le_maximalIdeal f)
    (Completion B ⧸ (maximalIdeal (Completion A)).map (completionMap f)) ≃+*
      Completion (B ⧸ closedFiberIdeal f) := by
  let := CompletionIdealQuotient.quotientLocalRing (closedFiberIdeal f)
    (closedFiberIdeal_le_maximalIdeal f)
  exact (Ideal.quotEquivOfEq (closedFiberIdeal_completed f)).trans
    (CompletionRegularityQuotient.quotientCompletionEquiv (closedFiberIdeal f))

/-- This actual closed-fibre comparison retains every literal original coefficient class. -/
theorem closedFiberEquiv_coefficient (b : B) :
    letI := CompletionIdealQuotient.quotientLocalRing (closedFiberIdeal f)
      (closedFiberIdeal_le_maximalIdeal f)
    closedFiberEquiv f (Ideal.Quotient.mk _ (AdicCompletion.of (maximalIdeal B) B b)) =
      AdicCompletion.of (maximalIdeal (B ⧸ closedFiberIdeal f)) (B ⧸ closedFiberIdeal f)
        (Ideal.Quotient.mk (closedFiberIdeal f) b) := by
  let := CompletionIdealQuotient.quotientLocalRing (closedFiberIdeal f)
    (closedFiberIdeal_le_maximalIdeal f)
  exact CompletionRegularityQuotient.quotientCompletionEquiv_coefficient (closedFiberIdeal f) b

end DeJongAlterations.Algebra.CompletionLocalMap
