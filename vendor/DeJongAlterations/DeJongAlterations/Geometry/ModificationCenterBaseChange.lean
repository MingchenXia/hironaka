import DeJongAlterations.Geometry.ModificationCenterOpen

/-!
# Actual center containment under native scheme base change

The full restriction square remains Cartesian on the actual inverse-image
opens. Isomorphisms are preserved there; maximality of the intrinsic native
isomorphism open gives center containment, without integrality hypotheses
or a claim that arbitrary base changes are modifications.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ModificationCenter

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y X' Y' Z : Scheme.{u}}

/-- An actual Cartesian square restricts isomorphisms over the actual inverse-image target open. -/
theorem isIso_restrict_of_isPullback {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {iX : X' ⟶ X} {iY : Y' ⟶ Y} (H : IsPullback iX f' f iY)
    (U : Y.Opens) [IsIso (f ∣_ U)] : IsIso (f' ∣_ iY ⁻¹ᵁ U) := by
  have hpre : iX ⁻¹ᵁ (f ⁻¹ᵁ U) = f' ⁻¹ᵁ (iY ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  have Hr := Scheme.Hom.isPullback_resLE H (US := U) (UT := iY ⁻¹ᵁ U)
    (UX := f ⁻¹ᵁ U) le_rfl le_rfl (UY := f' ⁻¹ᵁ (iY ⁻¹ᵁ U)) (by rw [hpre, inf_idem])
  have : IsIso (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using Hr.isIso_snd_of_isIso

/-- The actual closed inverse image of the original nonisomorphism center. -/
def inverseImageCenter (f : X ⟶ Y) (g : Z ⟶ Y) : Closeds Z :=
  ⟨g ⁻¹' (center f : Set Y), (center f).isClosed.preimage g.continuous⟩

/-- The native base-change center is contained in the actual closed inverse image of the original center. -/
theorem center_pullback_le (f : X ⟶ Y) (g : Z ⟶ Y) :
    center (pullback.snd f g) ≤ inverseImageCenter f g := by
  apply (center_le_iff _ _).mpr
  exact isIso_restrict_of_isPullback (IsPullback.of_hasPullback f g) (center f).compl

/-- Explicit set-theoretic form of the actual center base-change containment. -/
theorem center_pullback_subset (f : X ⟶ Y) (g : Z ⟶ Y) :
    (center (pullback.snd f g) : Set Z) ⊆ g ⁻¹' (center f : Set Y) :=
  center_pullback_le f g

end DeJongAlterations.Geometry.ModificationCenter
