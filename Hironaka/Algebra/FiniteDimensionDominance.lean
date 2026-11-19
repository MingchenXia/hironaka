import Hironaka.Algebra.FunctionFieldDimension
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Actual full-dimensional integral algebras have injective coefficient maps

A nonzero kernel forces a strict dimension drop through its genuine
quotient. Thus an integral domain algebra whose dimension is at least
the original finite base dimension has the original injective scalar map.
-/

noncomputable section

namespace Hironaka.Algebra.FiniteDimensionDominance

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native integral dimension and the nonzero-divisor quotient inequality rule out any kernel. -/
theorem algebraMap_injective_of_dimension_le
    (R B : Type*) [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra R B] [Algebra.IsIntegral R B] (d : ℕ)
    (hR : ringKrullDim R = d) (hB : (d : WithBot ℕ∞) ≤ ringKrullDim B) :
    Function.Injective (algebraMap R B) := by
  by_contra hinj
  let J := RingHom.ker (algebraMap R B)
  have hJ : J ≠ ⊥ := by
    intro heq
    exact hinj ((RingHom.injective_iff_ker_eq_bot _).mpr heq)
  obtain ⟨r, hr, hr0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hJ)
  have hrne : r ≠ 0 := by simpa only [Ideal.mem_bot] using hr0
  let φ : R ⧸ J →+* B := Ideal.Quotient.lift J (algebraMap R B) (fun _ ha => ha)
  have hcomp : φ.comp (Ideal.Quotient.mk J) = algebraMap R B := rfl
  have hi : φ.IsIntegral := by
    have hcompint : (φ.comp (Ideal.Quotient.mk J)).IsIntegral := by
      rw [hcomp]
      exact algebraMap_isIntegral_iff.mpr inferInstance
    exact fun b => (hcompint b).of_comp
  have hd := FunctionFieldDimension.ringKrullDim_le_of_isIntegral φ hi
  have hquot := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_iff_ne_zero.mpr hrne) (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hbad : (d : WithBot ℕ∞) + 1 ≤ d := by
    exact ((add_le_add hB le_rfl).trans ((add_le_add hd le_rfl).trans hquot)).trans_eq hR
  have hstrict : (d : WithBot ℕ∞) < (d : WithBot ℕ∞) + 1 := by
    exact_mod_cast Nat.lt_succ_self d
  exact (not_le_of_gt hstrict) hbad

end Hironaka.Algebra.FiniteDimensionDominance
