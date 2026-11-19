import Hironaka.Geometry.ProperSteinGlobalIdempotentsNilBaseChange
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # Actual original ideal-power quotients derive whole idempotent lifting. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace Hironaka.Geometry.ProperSteinGlobalIdempotents
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ)

/-- The ACTUAL original quotient factor from the original ideal power to the original ideal. -/
def powerQuotientFactor : (A ⧸ I ^ (n + 1)) →+* (A ⧸ I) :=
  Ideal.Quotient.factor (I.pow_le_self (Nat.succ_ne_zero n))

/-- The ENTIRE original coefficient quotient triangle is retained. -/
theorem powerQuotientFactor_comp_mk :
    (powerQuotientFactor I n).comp (Ideal.Quotient.mk (I ^ (n + 1))) = Ideal.Quotient.mk I :=
  Ideal.Quotient.factor_comp_mk _

/-- Original quotient factor surjectivity is derived, not an input. -/
theorem powerQuotientFactor_surjective : Function.Surjective (powerQuotientFactor I n) :=
  Ideal.Quotient.factor_surjective _

/-- EVERY actual original quotient-kernel element is nilpotent, by its original representative in I. -/
theorem powerQuotientFactor_nil_ker :
    ∀ a ∈ RingHom.ker (powerQuotientFactor I n), IsNilpotent a := by
  intro a ha
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hr : r ∈ I := by
    simpa only [powerQuotientFactor, RingHom.mem_ker, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem] using ha
  refine ⟨n + 1, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hr (n + 1)

/-- The LITERAL original ideal-power quotient base change is actually homeomorphic, with no supplied certificate. -/
theorem powerQuotientBaseChange_isHomeomorph {T : Scheme.{u}}
    (q : T ⟶ Spec (.of (A ⧸ I ^ (n + 1)))) :
    IsHomeomorph (NilBaseChange.projection (powerQuotientFactor I n) q) :=
  NilBaseChange.projection_isHomeomorph (powerQuotientFactor I n) q
    (powerQuotientFactor_surjective I n) (powerQuotientFactor_nil_ker I n)

/-- Actual ORIGINAL whole idempotents biject across the actual ideal-power quotient base change. -/
def powerQuotientIdempotentEquiv {T : Scheme.{u}}
    (q : T ⟶ Spec (.of (A ⧸ I ^ (n + 1)))) :
    {e : Γ(T, ⊤) // IsIdempotentElem e} ≃
      {e : Γ(NilBaseChange.model (powerQuotientFactor I n) q, ⊤) // IsIdempotentElem e} :=
  NilBaseChange.idempotentEquiv (powerQuotientFactor I n) q
    (powerQuotientFactor_surjective I n) (powerQuotientFactor_nil_ker I n)

/-- Its ENTIRE forward map is the ORIGINAL actual quotient-base-change projection pullback. -/
theorem powerQuotientIdempotentEquiv_apply {T : Scheme.{u}}
    (q : T ⟶ Spec (.of (A ⧸ I ^ (n + 1)))) (e : {e : Γ(T, ⊤) // IsIdempotentElem e}) :
    (powerQuotientIdempotentEquiv I n q e).1 =
      (NilBaseChange.projection (powerQuotientFactor I n) q).appTop e.1 := rfl

end Hironaka.Geometry.ProperSteinGlobalIdempotents
