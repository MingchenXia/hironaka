/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Transform.Defs
import Hironaka.Scheme.BlowUp.Transform.StrictTransform

/-!
# Colon, saturation and strict transform along an isomorphism

For a trivial blow-up the projection `π : B_Z X ⟶ X` is an isomorphism [Kol07, Warning 20], and
the strict transform `(J.comap π).saturate (Z.comap π)` of a closed subscheme `J` is the inverse
image along `π` of the saturation `J.saturate Z` computed on `X`: inverse images along an
isomorphism commute with colons (the inequality `comap_colon_le` applied to `π` and to `π⁻¹`) and
hence with saturations.  This is used for the total transforms of divisors under trivial
blow-ups and for the order along a trivial blow-up in the resolution sequences.

## Main declarations

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_colon_of_isIso`, `comap_saturate_of_isIso`.
* `AlgebraicGeometry.strictTransformAlong_of_isIso` — `strictTransformAlong π (Z.comap π) J =
  (J.saturate Z).comap π` for an isomorphism `π`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y X : Scheme.{u}} (e : Y ⟶ X) [IsIso e] (I K : X.IdealSheafData)

/-- Inverse image along an isomorphism commutes with the colon. -/
theorem comap_colon_of_isIso : (I.colon K).comap e = (I.comap e).colon (K.comap e) := by
  refine le_antisymm (comap_colon_le I K e) ?_
  have h := comap_colon_le (I.comap e) (K.comap e) (inv e)
  have h1 : (I.comap e).comap (inv e) = I :=
    (comap_comp I (inv e) e).symm.trans (by rw [IsIso.inv_hom_id, comap_id])
  have h2 : (K.comap e).comap (inv e) = K :=
    (comap_comp K (inv e) e).symm.trans (by rw [IsIso.inv_hom_id, comap_id])
  rw [h1, h2] at h
  have h3 : (((I.comap e).colon (K.comap e)).comap (inv e)).comap e ≤ (I.colon K).comap e :=
    comap_mono (f := e) h
  have h4 : (((I.comap e).colon (K.comap e)).comap (inv e)).comap e =
      (I.comap e).colon (K.comap e) :=
    (comap_comp _ e (inv e)).symm.trans (by rw [IsIso.hom_inv_id, comap_id])
  rwa [h4] at h3

/-- Inverse image along an isomorphism commutes with the saturation. -/
theorem comap_saturate_of_isIso : (I.saturate K).comap e = (I.comap e).saturate (K.comap e) := by
  simp only [saturate, comap_iSup, comap_colon_of_isIso, comap_pow]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

/-- For an isomorphism `π`, the strict transform of `J` along `π` with respect to the divisor
`Z.comap π` is the inverse image of the saturation `J.saturate Z` computed on `X`. -/
theorem strictTransformAlong_of_isIso {B X : Scheme.{u}} (π : B ⟶ X) [IsIso π]
    (Z J : X.IdealSheafData) :
    J.strictTransformAlong π (Z.comap π) = (J.saturate Z).comap π :=
  (Scheme.IdealSheafData.comap_saturate_of_isIso π J Z).symm

end AlgebraicGeometry
