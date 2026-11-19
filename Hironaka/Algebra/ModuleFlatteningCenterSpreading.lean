import Hironaka.Algebra.ModuleFlatteningCenterMatrix
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# An exact principal original minor ideal spreads from the actual local ring

Finitely many original minors supply actual denominators outside the
original prime. Their single product spreads equality of the same whole
ideal to an actual original principal neighborhood.
-/

noncomputable section

open scoped BigOperators

namespace Hironaka.Algebra.ModuleFlatteningCenter

open ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {n r : ℕ}

/-- Equality of the same original minor ideal with one original principal minor
in the local ring spreads to an actual original principal neighborhood. -/
theorem exists_away_minorIdeal_eq_span_of_atPrime
    (V : Matrix (Fin r) (Fin n) R) (p : Ideal R) [p.IsPrime]
    (s : Fin r → Fin n)
    (hI : (minorIdeal V).map (algebraMap R (Localization.AtPrime p)) =
      Ideal.span ({algebraMap R (Localization.AtPrime p) (columnMinor V s)} :
        Set (Localization.AtPrime p))) :
    ∃ a : R, a ∉ p ∧
      (minorIdeal V).map (algebraMap R (Localization.Away a)) =
        Ideal.span ({algebraMap R (Localization.Away a) (columnMinor V s)} :
          Set (Localization.Away a)) := by
  classical
  let J : Ideal R := Ideal.span ({columnMinor V s} : Set R)
  have hden (t : Fin r → Fin n) :
      ∃ d : R, d ∉ p ∧ d * columnMinor V t ∈ J := by
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
      (Localization.AtPrime p) J (columnMinor V t)).mp
    have hmem := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p))
      (columnMinor_mem_minorIdeal V t)
    simpa only [J, hI, Ideal.map_span, Set.image_singleton] using hmem
  choose d hdp hd using hden
  let a : R := ∏ t : Fin r → Fin n, d t
  have hap : a ∉ p := by
    exact p.primeCompl.prod_mem fun t _ ↦ hdp t
  refine ⟨a, hap, le_antisymm ?_ ?_⟩
  · rw [minorIdeal, Ideal.map_span, ← Set.range_comp]
    apply Ideal.span_le.mpr
    rintro _ ⟨t, rfl⟩
    let J' : Ideal (Localization.Away a) :=
      Ideal.span ({algebraMap R (Localization.Away a) (columnMinor V s)} :
        Set (Localization.Away a))
    apply (J'.unit_mul_mem_iff_mem (IsLocalization.Away.algebraMap_isUnit a)).mp
    have hdiv : d t ∣ a := Finset.dvd_prod_of_mem d (Finset.mem_univ t)
    obtain ⟨c, hc⟩ := hdiv
    have hamem : a * columnMinor V t ∈ J := by
      rw [hc, mul_right_comm]
      exact J.mul_mem_right c (hd t)
    have hmap := Ideal.mem_map_of_mem (algebraMap R (Localization.Away a)) hamem
    simpa only [J', J, Ideal.map_span, Set.image_singleton, map_mul, Function.comp_apply] using hmap
  · apply Ideal.span_le.mpr
    rintro _ rfl
    exact Ideal.mem_map_of_mem _ (columnMinor_mem_minorIdeal V s)

end Hironaka.Algebra.ModuleFlatteningCenter
