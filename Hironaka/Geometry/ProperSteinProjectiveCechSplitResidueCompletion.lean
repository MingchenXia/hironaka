/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Geometry.ProperSteinProjectiveCechCohenSurjective
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # Actual completion evaluations and internally produced Noetherianity

Closed native evaluation proofs adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/FlatLocalFieldLift.lean`,
SHA256 75724287fce1c9c9615cb8748bda1aba65f6c2f85510dfce771a2d1a6f53fd2f.
Noetherianity uses ONLY the own generic explicit power-series producer;
no external project, coefficient-field existence or CohenIso import is used.
-/
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.SplitResidueCompletion
set_option maxHeartbeats 200000
variable {R K : Type u} [CommRing R] [IsLocalRing R] [Field K]

/-- The literal ORIGINAL completion evaluates through its actual order-one quotient into the SAME original field. -/
def completionEvaluation (β : R →+* K) (hβ : RingHom.ker β = IsLocalRing.maximalIdeal R) :
    AdicCompletion (IsLocalRing.maximalIdeal R) R →+* K := by
  have hkill (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) : β r = 0 := by
    change r ∈ RingHom.ker β
    rwa [hβ]
  exact (Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) β hkill).comp
    (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal R)).toRingHom

/-- EVERY original local coefficient retains its entire original prescribed field value. -/
theorem completionEvaluation_algebraMap (β : R →+* K)
    (hβ : RingHom.ker β = IsLocalRing.maximalIdeal R) (r : R) :
    completionEvaluation β hβ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
      β r := rfl

/-- Actual surjectivity is internally transported through the ORIGINAL completion coefficient map. -/
theorem completionEvaluation_surjective (β : R →+* K) (hβs : Function.Surjective β)
    (hβ : RingHom.ker β = IsLocalRing.maximalIdeal R) :
    Function.Surjective (completionEvaluation β hβ) := by
  intro k
  obtain ⟨r, hr⟩ := hβs k
  exact ⟨algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r, hr⟩

/-- The actual completed evaluation has its own genuine completed maximal ideal as EXACT kernel. -/
theorem completionEvaluation_ker [IsNoetherianRing R]
    (β : R →+* K) (hβs : Function.Surjective β)
    (hβ : RingHom.ker β = IsLocalRing.maximalIdeal R) :
    RingHom.ker (completionEvaluation β hβ) =
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _
    (completionEvaluation_surjective β hβs hβ))

/-- The actual ORIGINAL prescribed-field section gives exactly the original completed coefficient action. -/
abbrev completionCoefficientAlgebra (σ : K →+* R) :
    Algebra K (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  ((algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)).comp σ).toAlgebra

/-- The ENTIRE original completed coefficient/evaluation triangle is forced by the actual original section identity. -/
theorem completionEvaluation_comp_coefficient (β : R →+* K)
    (hβ : RingHom.ker β = IsLocalRing.maximalIdeal R) (σ : K →+* R)
    (hσ : β.comp σ = RingHom.id K) :
    letI := completionCoefficientAlgebra σ
    (completionEvaluation β hβ).comp
      (algebraMap K (AdicCompletion (IsLocalRing.maximalIdeal R) R)) = RingHom.id K := by
  let := completionCoefficientAlgebra σ
  ext k
  change completionEvaluation β hβ
    (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) (σ k)) = k
  rw [completionEvaluation_algebraMap]
  exact RingHom.congr_fun hσ k

/-- ORIGINAL Noetherian locality and the actual prescribed-field section DERIVE Noetherianity of the SAME actual completion, in every characteristic. -/
theorem isNoetherianRing_completion_of_section [IsNoetherianRing R]
    (β : R →+* K) (hβ : RingHom.ker β = IsLocalRing.maximalIdeal R)
    (σ : K →+* R) (hσ : β.comp σ = RingHom.id K) :
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  let B := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let : Algebra K B := completionCoefficientAlgebra σ
  have hβs : Function.Surjective β := fun k => ⟨σ k, RingHom.congr_fun hσ k⟩
  have hfg : (IsLocalRing.maximalIdeal B).FG := by
    obtain ⟨d, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R))
    have heq : IsLocalRing.maximalIdeal B =
        Ideal.span (Set.range fun i => algebraMap R B (x i)) := by
      calc
        _ = (IsLocalRing.maximalIdeal R).map (algebraMap R B) :=
          AdicCompletion.maximalIdeal_eq_map
        _ = (Ideal.span (Set.range x)).map (algebraMap R B) :=
          congrArg (Ideal.map (algebraMap R B)) hx.symm
        _ = _ := by rw [Ideal.map_span, ← Set.range_comp]; rfl
    rw [heq]
    exact Submodule.fg_span (Set.finite_range _)
  exact CohenSurjective.isNoetherianRing_of_complete_split_quotient
    (IsLocalRing.maximalIdeal B) (completionEvaluation β hβ)
    (completionEvaluation_comp_coefficient β hβ σ hσ)
    (completionEvaluation_ker β hβs hβ) hfg

end Hironaka.Geometry.ProperSteinProjectiveCech.SplitResidueCompletion
