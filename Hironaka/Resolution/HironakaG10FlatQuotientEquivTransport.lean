import Hironaka.Resolution.HironakaG10HirFlatQuotient

/-! # Flatness over a quotient under ring equivalences -/

set_option autoImplicit false

namespace Hironaka.HironakaG10FlatQuotientEquivTransport

open HironakaG10HirFlatQuotient

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Postcomposition by a target ring equivalence preserves flatness over
each fixed quotient of the base. -/
theorem flat_quotMap_ringEquiv_comp {B' : Type*} [CommRing B']
    (φ : A →+* B) (e : B ≃+* B') (J : Ideal A) :
    (quotMap (e.toRingHom.comp φ) J).Flat ↔ (quotMap φ J).Flat := by
  have hJ : J.map (e.toRingHom.comp φ) = (J.map φ).map e.toRingHom := by
    rw [Ideal.map_map]
  let e' := Ideal.quotientEquiv (J.map φ) (J.map (e.toRingHom.comp φ)) e hJ
  have hsq : e'.toRingHom.comp (quotMap φ J) = quotMap (e.toRingHom.comp φ) J := by
    refine Ideal.Quotient.ringHom_ext ?_
    ext a
    rfl
  rw [← hsq, RingHom.Flat.comp_iff_of_bijective_left (g := e'.toRingHom) e'.bijective]

/-- Precomposition by a base ring equivalence transports flatness over a
fixed quotient to the image ideal in the original base. -/
theorem flat_quotMap_comp_ringEquiv {A' : Type*} [CommRing A']
    (φ : A →+* B) (e : A' ≃+* A) (J : Ideal A') :
    (quotMap (φ.comp e.toRingHom) J).Flat ↔ (quotMap φ (J.map e.toRingHom)).Flat := by
  have hJ : J.map (φ.comp e.toRingHom) = (J.map e.toRingHom).map φ := by
    rw [Ideal.map_map]
  let e₁ := Ideal.quotientEquiv J (J.map e.toRingHom) e rfl
  let e₂ := Ideal.quotEquivOfEq hJ
  have hsq : e₂.symm.toRingHom.comp ((quotMap φ (J.map e.toRingHom)).comp e₁.toRingHom) =
      quotMap (φ.comp e.toRingHom) J := by
    refine Ideal.Quotient.ringHom_ext ?_
    ext a
    rfl
  rw [← hsq, RingHom.Flat.comp_iff_of_bijective_left (g := e₂.symm.toRingHom) e₂.symm.bijective,
    RingHom.Flat.comp_iff_of_bijective_right (g := e₁.toRingHom) e₁.bijective]

end Hironaka.HironakaG10FlatQuotientEquivTransport
