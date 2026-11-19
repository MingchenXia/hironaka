import Hironaka.Resolution.HironakaG10FlatQuotientEquivTransport

/-! # Whole-family flattener transport through equivalent fibres -/

set_option autoImplicit false

namespace Hironaka.HironakaG10FlatFamilyEquivTransport

open HironakaG10HirFlatQuotient HironakaG10FlatQuotientEquivTransport

variable {A A' : Type*} [CommRing A] [CommRing A']

/-- A whole-family flattener transports along a base isomorphism when
an onto map of index sets identifies every new target with its corresponding
old target by a compatible ring equivalence. -/
theorem wholeFamilyFlattener_equiv {ι κ : Type*} {B : ι → Type*} {C : κ → Type*}
    [∀ i, CommRing (B i)] [∀ j, CommRing (C j)]
    (φ : ∀ i, A →+* B i) (ψ : ∀ j, A' →+* C j)
    (g : κ → ι) (hg : Function.Surjective g)
    (e : A ≃+* A') (d : ∀ j, B (g j) ≃+* C j)
    (hsq : ∀ j, (ψ j).comp e.toRingHom = (d j).toRingHom.comp (φ (g j)))
    (I : Ideal A) (hI : ∀ J : Ideal A, (∀ i, (quotMap (φ i) J).Flat) ↔ I ≤ J) :
    ∀ J' : Ideal A', (∀ j, (quotMap (ψ j) J').Flat) ↔ I.map e.toRingHom ≤ J' := by
  intro J'
  let J := J'.comap e.toRingHom
  have hJJ : J.map e.toRingHom = J' := Ideal.map_comap_of_surjective _ e.surjective J'
  have hpair (j : κ) : (quotMap (φ (g j)) J).Flat ↔ (quotMap (ψ j) J').Flat := by
    have hh := flat_quotMap_comp_ringEquiv (ψ j) e J
    rw [hsq j, flat_quotMap_ringEquiv_comp, hJJ] at hh
    exact hh
  have hall : (∀ j, (quotMap (ψ j) J').Flat) ↔ (∀ i, (quotMap (φ i) J).Flat) := by
    constructor
    · intro h i
      obtain ⟨j,rfl⟩ := hg i
      exact (hpair j).mpr (h j)
    · intro h j
      exact (hpair j).mp (h (g j))
  rw [hall, hI]
  exact (Ideal.map_le_iff_le_comap).symm

end Hironaka.HironakaG10FlatFamilyEquivTransport
