import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Literal finite jets at an actual maximal point are unchanged by its actual
localization. The original localization map is retained on EVERY representative. -/

noncomputable section

namespace Hironaka.Algebra.NodeGeometricCompletionLocalizedJets

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsMaximal]

/-- Every element outside the ACTUAL maximal ideal is already a unit in EVERY finite jet. -/
theorem isUnit_mk_pow (n : ℕ) (a : R) (ha : a ∉ p) :
    IsUnit (Ideal.Quotient.mk (p ^ n) a) := by
  let := Ideal.Quotient.field p
  have ha0 : Ideal.Quotient.mk p a ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using ha
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk p a)⁻¹)
  have hab : a * b - 1 ∈ p := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, map_one, hb, mul_inv_cancel₀ ha0, sub_self]
  have hp : (a * b - 1) ^ n ∈ p ^ n := Ideal.pow_mem_pow hab n
  have hn : IsNilpotent (Ideal.Quotient.mk (p ^ n) (a * b - 1)) :=
    ⟨n, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hp⟩
  have hu := hn.isUnit_add_one
  rw [map_sub, map_mul, map_one, sub_add_cancel] at hu
  exact isUnit_of_dvd_unit (dvd_mul_right _ _) hu

variable (T : Type v) [CommRing T] [Algebra R T] [IsLocalization p.primeCompl T]

/-- Actual localization preserves EVERY maximal-point jet, over the SAME original ring. -/
def powerQuotientEquiv (n : ℕ) :
    (R ⧸ p ^ n) ≃ₐ[R] (T ⧸ (p ^ n).map (algebraMap R T)) := by
  let M := Algebra.algebraMapSubmonoid (R ⧸ p ^ n) p.primeCompl
  have hM : M ≤ IsUnit.submonoid (R ⧸ p ^ n) := by
    rintro _ ⟨a, ha, rfl⟩
    exact isUnit_mk_pow p n a ha
  exact (IsLocalization.atUnits (R ⧸ p ^ n) M
    (S := T ⧸ (p ^ n).map (algebraMap R T)) hM).restrictScalars R

/-- EVERY original representative has its canonical ACTUAL localization image. -/
theorem powerQuotientEquiv_mk (n : ℕ) (r : R) :
    powerQuotientEquiv p T n (Ideal.Quotient.mk (p ^ n) r) =
      Ideal.Quotient.mk ((p ^ n).map (algebraMap R T)) (algebraMap R T r) := rfl

end Hironaka.Algebra.NodeGeometricCompletionLocalizedJets
