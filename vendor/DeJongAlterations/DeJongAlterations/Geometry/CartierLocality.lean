import DeJongAlterations.Divisor
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Effective Cartier equations on open covers

Non-zero-divisor equations transport through actual open-immersion section
isomorphisms. Thus effective Cartier divisors glue on arbitrary open covers.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace DeJongAlterations.Geometry.CartierLocality

universe u

theorem isRegular_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {t : R} (ht : IsRegular t) : IsRegular (e t) := by
  constructor
  · intro a b hab
    apply e.symm.injective
    apply ht.left
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hab
  · intro a b hab
    apply e.symm.injective
    apply ht.right
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hab

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A local Cartier equation on an open subscheme gives an actual affine equation in its image. -/
theorem exists_affine_neighborhood_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f]
    (D : Y.IdealSheafData) (hD : IsEffectiveCartierDivisor (D.comap f)) (x : X) :
    ∃ U : Y.affineOpens, f x ∈ U.1 ∧
      ∃ t : Γ(Y, U.1), IsRegular t ∧ D.ideal U = Ideal.span {t} := by
  obtain ⟨V, hxV, t, ht, hV⟩ := hD x
  let U : Y.affineOpens := ⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩
  let e := (f.appIso V.1).commRingCatIsoToRingEquiv
  let φ : Γ(X, V.1) →+* Γ(Y, U.1) := (f.appIso V.1).inv.hom
  refine ⟨U, ?_, φ t, isRegular_ringEquiv e.symm ht, ?_⟩
  · exact ⟨x, hxV, rfl⟩
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hV
    change Ideal.comap φ (D.ideal U) = Ideal.span {t} at hV
    have h := congrArg (Ideal.map φ) hV
    rw [Ideal.map_comap_of_surjective φ e.symm.surjective (D.ideal U),
      Ideal.map_span, Set.image_singleton] at h
    exact h

/-- Effective Cartier divisors glue on an arbitrary native scheme open cover. -/
theorem of_openCover (D : Y.IdealSheafData) (𝒰 : Y.OpenCover)
    (hD : ∀ i, IsEffectiveCartierDivisor (D.comap (𝒰.f i))) :
    IsEffectiveCartierDivisor D := by
  intro y
  obtain ⟨x, hx⟩ := 𝒰.covers y
  simpa only [hx] using
    exists_affine_neighborhood_of_isOpenImmersion (𝒰.f (𝒰.idx y)) D (hD _) x

end DeJongAlterations.Geometry.CartierLocality
