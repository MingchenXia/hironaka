import DeJongAlterations.Divisor
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! The exact prescribed boundary descends through the original actual scheme scalar square. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlterationBoundaryScalarDescent

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- ALL original boundary support and complement maps descend on the SAME actual scalar diagram. -/
theorem boundary_support_of_isPullback {A' A B' B X : Scheme.{u}}
    {gA : A' ⟶ A} {b' : A' ⟶ B'} {b : A ⟶ B} {gB : B' ⟶ B}
    (H : IsPullback gA b' b gB) [Surjective gB]
    (a' : A' ⟶ X) (a : A ⟶ X) (ha : gA ≫ a = a')
    (Z : Set X) (D : B.IdealSheafData) (D' : B'.IdealSheafData)
    (hD : D.comap gB = D')
    (hsupport : (D'.support : Set B') = b' '' (a' ⁻¹' Z) ∪ (Set.range b')ᶜ) :
    (D.support : Set B) = b '' (a ⁻¹' Z) ∪ (Set.range b)ᶜ := by
  have himage (T : Set A) : gB ⁻¹' (b '' T) = b' '' (gA ⁻¹' T) :=
    (Scheme.image_preimage_eq_of_isPullback H T).symm
  have hrange : gB ⁻¹' Set.range b = Set.range b' := by
    simpa only [Set.image_univ, Set.preimage_univ] using himage Set.univ
  have hpre : gA ⁻¹' (a ⁻¹' Z) = a' ⁻¹' Z := by
    rw [← Set.preimage_comp]
    have hfun : (fun x => a (gA x)) = a' := by
      exact congrArg (fun f : A' ⟶ X => (f : A' → X)) ha
    change (fun x => a (gA x)) ⁻¹' Z = a' ⁻¹' Z
    rw [hfun]
  apply (Set.preimage_injective.mpr gB.surjective)
  have hs : gB ⁻¹' (D.support : Set B) = (D'.support : Set B') := by
    rw [← hD, Scheme.IdealSheafData.support_comap]
    rfl
  rw [hs, Set.preimage_union, himage, hpre, Set.preimage_compl, hrange, hsupport]

end DeJongAlterations.Geometry.AlterationBoundaryScalarDescent
