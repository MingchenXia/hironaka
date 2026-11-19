import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Actual module finiteness after inverting a common integral multiplier

If a finite original algebra-generating family becomes integral after
multiplication by a base element, the native coefficient-localization map is
finite. The proof constructs the localized algebra structures and proves
integrality of every actual localized element.
-/

noncomputable section

namespace Hironaka.Algebra.RelativeNoetherNormalizationSpreading

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R P A : Type u} [CommRing R] [CommRing P] [CommRing A]
  [Algebra R P] [Algebra R A]

/-- Cleared monic equations on actual finite generators make the literal localization map finite. -/
theorem awayMap_finite_of_integral_scaled_generators (f : P →ₐ[R] A) (b : R)
    (s : Finset A) (hs : Algebra.adjoin R (s : Set A) = ⊤)
    (hint : ∀ a ∈ s, f.toRingHom.IsIntegralElem (b • a)) :
    (Localization.awayMap f.toRingHom (algebraMap R P b)).Finite := by
  classical
  let : Algebra P A := f.toRingHom.toAlgebra
  have : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let p := algebraMap R P b
  let Q := Localization.Away p
  let B := Localization.Away (f p)
  have : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers p)) B := by
    change IsLocalization ((Submonoid.powers p).map f.toRingHom) B
    rw [Submonoid.map_powers]
    infer_instance
  let : Algebra Q B := (Localization.awayMap f.toRingHom p).toAlgebra
  have : IsScalarTower P Q B := by
    apply IsScalarTower.of_algebraMap_eq'
    have hmap : Submonoid.powers p ≤ (Submonoid.powers (f p)).comap f.toRingHom := by
      rintro x ⟨n, rfl⟩
      exact ⟨n, (map_pow f p n).symm⟩
    exact (IsLocalization.map_comp (S := Q) (Q := B) (g := f.toRingHom)
      (hy := hmap)).symm
  have hb : algebraMap A B (algebraMap R A b) = algebraMap Q B (algebraMap P Q p) := by
    rw [← f.commutes b]
    change algebraMap A B (algebraMap P A p) = algebraMap Q B (algebraMap P Q p)
    rw [← IsScalarTower.algebraMap_apply P A B, ← IsScalarTower.algebraMap_apply P Q B]
  obtain ⟨q, hq⟩ := isUnit_iff_exists_inv.mp (IsLocalization.Away.algebraMap_isUnit (S := Q) p)
  have hqB : algebraMap Q B q * algebraMap A B (algebraMap R A b) = 1 := by
    rw [hb, ← map_mul, mul_comm q]
    simpa only [map_one] using congrArg (algebraMap Q B) hq
  have hgen (a : A) (ha : a ∈ s) : IsIntegral Q (algebraMap A B a) := by
    have hm : IsIntegral P (b • a) := hint a ha
    have hmB : IsIntegral Q (algebraMap A B (b • a)) := hm.algebraMap.tower_top
    apply IsIntegral.of_mul_unit hqB
    simpa only [Algebra.smul_def, map_mul, mul_comm] using hmB
  have hA (a : A) : IsIntegral Q (algebraMap A B a) := by
    have ha : a ∈ Algebra.adjoin R (s : Set A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap r =>
      have hr : IsIntegral P (algebraMap R A r) := by
        rw [← f.commutes r]
        exact isIntegral_algebraMap
      exact hr.algebraMap.tower_top
    | add x y hx hy hix hiy => simpa only [map_add] using hix.add hiy
    | mul x y hx hy hix hiy => simpa only [map_mul] using hix.mul hiy
  have : Algebra.IsIntegral Q B := by
    constructor
    intro z
    obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers (f p)) z
    obtain ⟨n, hn⟩ := m.property
    have hden : algebraMap A B (m : A) = algebraMap Q B (algebraMap P Q p ^ n) := by
      rw [← hn, map_pow, map_pow, ← IsScalarTower.algebraMap_apply P Q B,
        IsScalarTower.algebraMap_apply P A B]
      rfl
    have hinv : algebraMap Q B (q ^ n) * algebraMap A B (m : A) = 1 := by
      rw [hden, ← map_mul, ← mul_pow, mul_comm q, hq]
      simp
    apply IsIntegral.of_mul_unit hinv
    rw [hm]
    exact hA a
  have : Algebra.FiniteType R A := ⟨⟨s, hs⟩⟩
  have : Algebra.FiniteType P A := Algebra.FiniteType.of_restrictScalars_finiteType R P A
  have hft : f.toRingHom.FiniteType := inferInstanceAs (Algebra.FiniteType P A)
  have hlocft := RingHom.localization_away_map_finiteType P A Q B f.toRingHom p hft
  have : Algebra.FiniteType Q B := hlocft
  exact Algebra.IsIntegral.finite

end Hironaka.Algebra.RelativeNoetherNormalizationSpreading
