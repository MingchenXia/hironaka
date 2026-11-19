import Hironaka.Resolution.HironakaG10ChowArtinReesCentre

/-! # Positive source thickening preserves strict-transform radicals -/
set_option autoImplicit false
namespace Hironaka.HironakaG10StrictIdealRadical
open HironakaG10ChowArtinReesCentre
variable {A R : Type*} [CommRing A] [CommRing R]

/-- Raising a source witness to a power puts the corresponding power of
its strict-transform generator in the strict ideal of the source power. -/
theorem strictIdeal_le_radical_source_pow (φ : A →+* R) (I D : Ideal A)
    (G : R) (β : ℕ) :
    strictIdeal φ I D G ≤ (strictIdeal φ (I ^ β) D G).radical := by
  apply Ideal.span_le.mpr
  rintro z ⟨k, h, hh, heq⟩
  apply Ideal.mem_radical_iff.mpr
  refine ⟨β, Ideal.subset_span ?_⟩
  refine ⟨k * β, h ^ β, ⟨Ideal.pow_mem_pow hh.1 β, ?_⟩, ?_⟩
  · change h ^ β ∈ D ^ (k * β)
    rw [pow_mul]
    exact Ideal.pow_mem_pow hh.2 β
  · rw [map_pow, heq, mul_pow, ← pow_mul]

/-- The whole algebraic strict-transform ideals of a source and any
positive thickening have equal radicals, for every exceptional equation. -/
theorem radical_strictIdeal_source_pow (φ : A →+* R) (I D : Ideal A)
    (G : R) {β : ℕ} (hβ : β ≠ 0) :
    (strictIdeal φ (I ^ β) D G).radical = (strictIdeal φ I D G).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_mono
    rintro z ⟨k, h, hh, heq⟩
    exact ⟨k, h, ⟨Ideal.pow_le_self hβ hh.1, hh.2⟩, heq⟩
  · have h := Ideal.radical_mono (strictIdeal_le_radical_source_pow φ I D G β)
    simpa only [Ideal.radical_idem] using h

/-- Unit-ideal/properness tests for strict transforms are unchanged by a
positive power of the source ideal, with the centre held fixed. -/
theorem strictIdeal_source_pow_eq_top_iff (φ : A →+* R) (I D : Ideal A)
    (G : R) {β : ℕ} (hβ : β ≠ 0) :
    strictIdeal φ (I ^ β) D G = ⊤ ↔ strictIdeal φ I D G = ⊤ := by
  rw [← Ideal.radical_eq_top, radical_strictIdeal_source_pow φ I D G hβ,
    Ideal.radical_eq_top]

end Hironaka.HironakaG10StrictIdealRadical
