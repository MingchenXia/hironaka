import Hironaka.Geometry.ProperSteinGlobalIdempotentsThickening

/-! # Every ORIGINAL closed-fibre idempotent has its actual compatible family on ALL original thickenings. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace Hironaka.Geometry.ProperSteinGlobalIdempotents
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The ORIGINAL quotient homomorphism between the actual ORIGINAL ideal-power coefficient rings. -/
def thickeningCoefficientFactor {n m : ℕ} (h : n ≤ m) :
    (A ⧸ I ^ (m + 1)) →+* (A ⧸ I ^ (n + 1)) :=
  Ideal.Quotient.factorPow I (Nat.succ_le_succ h)

/-- The ENTIRE original coefficient triangle for an actual transition. -/
theorem thickeningCoefficientFactor_comp_mk {n m : ℕ} (h : n ≤ m) :
    (thickeningCoefficientFactor I h).comp (Ideal.Quotient.mk (I ^ (m + 1))) =
      Ideal.Quotient.mk (I ^ (n + 1)) :=
  Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (Nat.succ_le_succ h))

/-- Actual original closed-fibre quotient factors commute with ALL original power transitions. -/
theorem powerQuotientFactor_comp_transition {n m : ℕ} (h : n ≤ m) :
    (powerQuotientFactor I n).comp (thickeningCoefficientFactor I h) =
      powerQuotientFactor I m :=
  Ideal.Quotient.factor_comp (Ideal.pow_le_pow_right (Nat.succ_le_succ h))
    (I.pow_le_self (Nat.succ_ne_zero n))

/-- The actual original spectrum transition keeps its full original coefficient structure. -/
theorem thickeningCoefficientSpec_structure {n m : ℕ} (h : n ≤ m) :
    Spec.map (CommRingCat.ofHom (thickeningCoefficientFactor I h)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((thickeningCoefficientFactor I h).comp (Ideal.Quotient.mk (I ^ (m + 1))))) = _
  rw [thickeningCoefficientFactor_comp_mk]

/-- The ORIGINAL closed-fibre maps retain their entire actual spectrum transition triangle. -/
theorem powerQuotientSpec_transition {n m : ℕ} (h : n ≤ m) :
    Spec.map (CommRingCat.ofHom (powerQuotientFactor I n)) ≫
      Spec.map (CommRingCat.ofHom (thickeningCoefficientFactor I h)) =
        Spec.map (CommRingCat.ofHom (powerQuotientFactor I m)) := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((powerQuotientFactor I n).comp (thickeningCoefficientFactor I h))) = _
  rw [powerQuotientFactor_comp_transition]

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of A))

/-- The SAME actual ORIGINAL infinitesimal models have their original Cartesian transition map. -/
def thickeningTransition {n m : ℕ} (h : n ≤ m) : thickening p I n ⟶ thickening p I m :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ≫
      Spec.map (CommRingCat.ofHom (thickeningCoefficientFactor I h)))
    (by rw [Category.assoc, thickeningCoefficientSpec_structure]; exact pullback.condition)

/-- EVERY actual ORIGINAL transition retains the SAME ORIGINAL closed-fibre inclusion. -/
theorem closedToThickening_transition {n m : ℕ} (h : n ≤ m) :
    closedToThickening p I n ≫ thickeningTransition I p h = closedToThickening p I m := by
  apply pullback.hom_ext
  · simp [closedToThickening, thickeningTransition]
  · simp only [Category.assoc, thickeningTransition, pullback.lift_snd,
      closedToThickening, pullback.lift_snd_assoc]
    rw [powerQuotientSpec_transition]

/-- A LITERAL actual original idempotent on EVERY original thickening, constructed from the ORIGINAL closed-fibre idempotent. -/
def infinitesimalIdempotentLift (e : {e : Γ(closedFiber p I, ⊤) // IsIdempotentElem e}) (n : ℕ) :
    {e : Γ(thickening p I n, ⊤) // IsIdempotentElem e} :=
  (closedToThickeningIdempotentEquiv p I n).symm e

/-- The actual original inclusion pulls back EVERY lift to the SAME original closed-fibre idempotent. -/
theorem infinitesimalIdempotentLift_restrict
    (e : {e : Γ(closedFiber p I, ⊤) // IsIdempotentElem e}) (n : ℕ) :
    (closedToThickening p I n).appTop (infinitesimalIdempotentLift I p e n).1 = e.1 :=
  congrArg Subtype.val ((closedToThickeningIdempotentEquiv p I n).apply_symm_apply e)

/-- The SAME ORIGINAL closed-fibre idempotent internally produces compatibility on EVERY actual original transition. -/
theorem infinitesimalIdempotentLift_compatible
    (e : {e : Γ(closedFiber p I, ⊤) // IsIdempotentElem e}) {n m : ℕ} (h : n ≤ m) :
    (thickeningTransition I p h).appTop (infinitesimalIdempotentLift I p e m).1 =
      (infinitesimalIdempotentLift I p e n).1 := by
  have H : idempotentPullback (closedToThickening p I n)
      (idempotentPullback (thickeningTransition I p h) (infinitesimalIdempotentLift I p e m)) =
      idempotentPullback (closedToThickening p I n) (infinitesimalIdempotentLift I p e n) := by
    apply Subtype.ext
    change (closedToThickening p I n ≫ thickeningTransition I p h).appTop
      (infinitesimalIdempotentLift I p e m).1 =
        (closedToThickening p I n).appTop (infinitesimalIdempotentLift I p e n).1
    rw [closedToThickening_transition, infinitesimalIdempotentLift_restrict,
      infinitesimalIdempotentLift_restrict]
  exact congrArg Subtype.val
    ((idempotentPullback_bijective (closedToThickening p I n)
      (closedToThickening_isHomeomorph p I n)).injective H)

end Hironaka.Geometry.ProperSteinGlobalIdempotents
