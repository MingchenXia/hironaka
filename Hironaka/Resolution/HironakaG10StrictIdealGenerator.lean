import Hironaka.Resolution.HironakaG10ChowArtinReesCentre

/-! # Independence of the regular exceptional equation in a strict ideal -/
set_option autoImplicit false
namespace Hironaka.HironakaG10StrictIdealGenerator
open HironakaG10ChowArtinReesCentre

variable {A R : Type*} [CommRing A] [CommRing R]

private theorem strictIdeal_mul_unit_le (φ : A →+* R) (I D : Ideal A)
    (G : R) (u : Rˣ) :
    strictIdeal φ I D ((u : R) * G) ≤ strictIdeal φ I D G := by
  apply Ideal.span_le.mpr
  rintro z ⟨k, h, hh, heq⟩
  have hmem : (u : R) ^ k * z ∈ strictIdeal φ I D G := by
    apply Ideal.subset_span
    refine ⟨k, h, hh, ?_⟩
    calc
      φ h = ((u : R) * G) ^ k * z := heq
      _ = G ^ k * ((u : R) ^ k * z) := by rw [mul_pow]; ring
  have hinv := (strictIdeal φ I D G).mul_mem_left ((↑(u⁻¹) : R) ^ k) hmem
  change z ∈ strictIdeal φ I D G
  simpa only [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul] using hinv

/-- The algebraic strict-transform ideal is unchanged by unit-rescaling
its exceptional equation, without a regularity assumption. -/
theorem strictIdeal_mul_unit (φ : A →+* R) (I D : Ideal A) (G : R) (u : Rˣ) :
    strictIdeal φ I D ((u : R) * G) = strictIdeal φ I D G := by
  apply le_antisymm (strictIdeal_mul_unit_le φ I D G u)
  have h := strictIdeal_mul_unit_le φ I D ((u : R) * G) u⁻¹
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using h

/-- Regular generators of the same principal ideal differ by a unit in
an arbitrary commutative ring. -/
theorem exists_unit_mul_of_regular_span_eq {G H : R} (hG : IsRegular G)
    (hspan : Ideal.span {G} = Ideal.span {H}) :
    ∃ u : Rˣ, H = (u : R) * G := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp
    (hspan.symm ▸ (Ideal.subset_span (Set.mem_singleton H)))
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp
    (hspan ▸ (Ideal.subset_span (Set.mem_singleton G)))
  have hba : b * a = 1 := by
    apply hG.left
    calc
      G * (b * a) = b * (a * G) := by ring
      _ = b * H := by rw [ha]
      _ = G := hb
      _ = G * 1 := (mul_one G).symm
  let u : Rˣ := ⟨a, b, by simpa only [mul_comm] using hba, hba⟩
  exact ⟨u, ha.symm⟩

/-- Changing to any other generator of the same regular principal ideal
preserves the whole algebraic strict-transform ideal. -/
theorem strictIdeal_eq_of_regular_span_eq (φ : A →+* R) (I D : Ideal A)
    {G H : R} (hG : IsRegular G) (hspan : Ideal.span {G} = Ideal.span {H}) :
    strictIdeal φ I D G = strictIdeal φ I D H := by
  obtain ⟨u, hu⟩ := exists_unit_mul_of_regular_span_eq hG hspan
  rw [hu, strictIdeal_mul_unit]

end Hironaka.HironakaG10StrictIdealGenerator
