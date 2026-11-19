/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.Smooth.LocalBlowUp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Stalks of the local blow-up

Hauser's local blow-up at `x' ∈ π⁻¹(x)` is the morphism of germs `(B_Z X, x') → (X, x)`
[Hau14, Definition 4.15], described through the local ring `𝒪_{B_ZX,x'}` in
[Hau14, Definition 4.16]; `Hironaka/Scheme/Smooth/LocalBlowUp.lean` realizes the germ as the base
change of `B_Z X` along `Spec 𝒪_{X,x} → X`. The two readings agree because a base change `φ : Y ⟶ B`
of `X.fromSpecStalk x` does not change the stalks: every `φ^♯_p : 𝒪_{B,φ p} → 𝒪_{Y,p}` is an
isomorphism (`isIso_stalkMap_of_isPullback_fromSpecStalk`).

**Why.** On an affine `U ∋ x` the morphism `Spec 𝒪_{X,x} → X` is `Spec` of the localization
`Γ(X, U) → 𝒪_{X,x}` followed by the open immersion `Spec Γ(X, U) ≅ U ⊆ X`; hence it is flat
(`flat_fromSpecStalk`) and a preimmersion, an embedding of topological spaces that is surjective
on stalks (Mathlib's `IsPreimmersion (X.fromSpecStalk x)`: the stalk map at a prime `𝔮` of
`𝒪_{X,x}` is the localization `𝒪_{X,x} → (𝒪_{X,x})_𝔮`, which is onto). Both properties are
stable under base change (Mathlib's `Flat.isStableUnderBaseChange` and the `IsPreimmersion`
instance, transported through the cartesian square by `property_of_isPullback`), so `φ` is a flat
preimmersion. Its stalk map at `p` is therefore surjective, and it is injective because a flat
local homomorphism of local rings is faithfully flat
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`), hence injective, the argument of Mathlib's
`epi_of_flat_of_surjective`. Not in the sources in this form.

Used to read the stalks of `B_Z X` on the charts of the local blow-up (`LocalBlowUpChart.lean`,
`Hironaka/Scheme/Snc/LocalBlowUpPoint.lean`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A base change of `Spec 𝒪_{X,x} → X` is flat: `flat_fromSpecStalk` transported through the
cartesian square. -/
theorem flat_of_isPullback_fromSpecStalk {x : X} {Y B : Scheme.{u}} {φ : Y ⟶ B}
    {ψ : Y ⟶ Spec (X.presheaf.stalk x)} {π : B ⟶ X}
    (H : IsPullback φ ψ π (X.fromSpecStalk x)) : Flat φ :=
  property_of_isPullback @Flat H (flat_fromSpecStalk x)

/-- A base change of `Spec 𝒪_{X,x} → X` is a preimmersion: Mathlib's instance for
`X.fromSpecStalk x` transported through the cartesian square. -/
theorem isPreimmersion_of_isPullback_fromSpecStalk {x : X} {Y B : Scheme.{u}} {φ : Y ⟶ B}
    {ψ : Y ⟶ Spec (X.presheaf.stalk x)} {π : B ⟶ X}
    (H : IsPullback φ ψ π (X.fromSpecStalk x)) : IsPreimmersion φ :=
  property_of_isPullback @IsPreimmersion H inferInstance

/-- The stalks of the local blow-up are the stalks of `B_Z X` (Hauser's two descriptions of the
local blow-up, [Hau14, Definitions 4.15, 4.16]): a base change `φ` of `Spec 𝒪_{X,x} → X` induces
isomorphisms on stalks, since `φ` is a flat preimmersion, so `φ^♯_p` is surjective, and a flat
local homomorphism of local rings is faithfully flat, hence injective. -/
theorem isIso_stalkMap_of_isPullback_fromSpecStalk {x : X} {Y B : Scheme.{u}} {φ : Y ⟶ B}
    {ψ : Y ⟶ Spec (X.presheaf.stalk x)} {π : B ⟶ X}
    (H : IsPullback φ ψ π (X.fromSpecStalk x)) (p : Y) : IsIso (φ.stalkMap p) := by
  have := flat_of_isPullback_fromSpecStalk H
  have := isPreimmersion_of_isPullback_fromSpecStalk H
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, φ.stalkMap_surjective p⟩
  algebraize [(φ.stalkMap p).hom]
  have : Module.FaithfullyFlat (B.presheaf.stalk (φ p)) (Y.presheaf.stalk p) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ (Flat.stalkMap φ p)
      (φ.toLRSHom.prop p)
  exact ‹RingHom.FaithfullyFlat _›.injective

end AlgebraicGeometry
