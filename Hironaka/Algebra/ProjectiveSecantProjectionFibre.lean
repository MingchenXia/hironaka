import Hironaka.Algebra.ProjectiveSecantLine

/-!
# Whole original line kernels from actual remaining-coordinate fibre minors
-/

noncomputable section

open MvPolynomial AlgebraicGeometry

namespace Hironaka.Algebra.ProjectiveSecant

open Geometry.ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- Actual original minors make the whole original quotient map cancel the literal line section followed by line substitution. -/
theorem quotient_lineSection_lineMap_eq (v : Fin (n + 2) → k)
    (j : Fin (n + 1)) (hj : v j.succ ≠ 0) (P : Ideal (MvPolynomial (Fin (n + 2)) k))
    (hminor : ∀ a : Fin (n + 1), C (v j.succ) * X a.succ - C (v a.succ) * X j.succ ∈ P) :
    (Ideal.Quotient.mk P).comp ((linePolynomialSection k n v j).toRingHom.comp
      (lineGradedMap k n v).toRingHom) = Ideal.Quotient.mk P := by
  let φ := Ideal.Quotient.mk P
  have hinv : φ (C ((v j.succ)⁻¹)) * φ (C (v j.succ)) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hj, map_one, map_one]
  have hrel (a : Fin (n + 1)) :
      φ (C (v j.succ)) * φ (X a.succ) = φ (C (v a.succ)) * φ (X j.succ) := by
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr (hminor a)
    simpa only [map_sub, map_mul, sub_eq_zero] using he
  have hnorm (a : Fin (n + 1)) :
      φ (C (v a.succ)) * (φ (C ((v j.succ)⁻¹)) * φ (X j.succ)) = φ (X a.succ) := by
    calc
      _ = φ (C ((v j.succ)⁻¹)) * (φ (C (v a.succ)) * φ (X j.succ)) := by ring
      _ = φ (C ((v j.succ)⁻¹)) * (φ (C (v j.succ)) * φ (X a.succ)) := by rw [hrel]
      _ = φ (X a.succ) := by rw [← mul_assoc, hinv, one_mul]
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [linePolynomialSection, lineGradedMap]
  · intro a
    refine Fin.cases ?_ (fun a => ?_) a
    · simp [linePolynomialSection, lineGradedMap, lineCoordinates]
    · change φ (linePolynomialSection k n v j (lineGradedMap k n v (X a.succ))) = φ (X a.succ)
      rw [lineGradedMap_X_succ, map_mul]
      simpa [linePolynomialSection] using hnorm a

/-- The entire original line kernel is internally contained in the actual original ideal as soon as its genuine remaining-coordinate minors vanish. -/
theorem lineGradedMap_ker_le_of_minors (v : Fin (n + 2) → k)
    (j : Fin (n + 1)) (hj : v j.succ ≠ 0) (P : Ideal (MvPolynomial (Fin (n + 2)) k))
    (hminor : ∀ a : Fin (n + 1), C (v j.succ) * X a.succ - C (v a.succ) * X j.succ ∈ P) :
    RingHom.ker (lineGradedMap k n v).toRingHom ≤ P := by
  intro F hF
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := RingHom.congr_fun (quotient_lineSection_lineMap_eq k n v j hj P hminor) F
  change Ideal.Quotient.mk P (linePolynomialSection k n v j (lineGradedMap k n v F)) =
    Ideal.Quotient.mk P F at h
  change lineGradedMap k n v F = 0 at hF
  rw [hF, map_zero, map_zero] at h
  exact h.symm

end Hironaka.Algebra.ProjectiveSecant
