import Hironaka.Algebra.PluckerQuotTransitionContraction

/-!
# Literal original contraction identities for the actual pivot projection

Both factor matrices are extracted from the SAME original contraction itself.
These whole-ring identities internally produce the scalar factorization used
by the original native over-site maps, without a factorization input.
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuot

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {ι κ η : Type u} {σ : Type v}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  (β : σ ≃ (ι → η)) (e : (ι ⊕ κ) ≃ η) (a : Matrix ι κ R)

/-- The original pivot columns of the SAME contraction are exactly its actual adjugate factor. -/
theorem originalContractionMatrix_pivot_columns :
    (originalContractionMatrix β (splitNormalizedMatrix e a)).submatrix id (e ∘ Sum.inl) =
      originalContractionFactor β (splitNormalizedMatrix e a) := by
  classical
  rw [originalContractionMatrix_eq_factor_mul]
  ext row i
  change ∑ j : ι, originalContractionFactor β (splitNormalizedMatrix e a) row j *
    splitNormalizedMatrix e a j (e (Sum.inl i)) = _
  simp [splitNormalizedMatrix_apply, normalizedMatrix_inl, Matrix.one_apply]

/-- The original pivot rows of the SAME contraction are the original normalized quotient matrix. -/
theorem originalContractionMatrix_pivot_rows :
    (originalContractionMatrix β (splitNormalizedMatrix e a)).submatrix
      (fun i => (β.symm (e ∘ Sum.inl), i)) id = splitNormalizedMatrix e a := by
  classical
  rw [originalContractionMatrix_eq_factor_mul]
  have hp := originalContractionFactor_pivot_rows β e a
  ext i j
  change ∑ h : ι, originalContractionFactor β (splitNormalizedMatrix e a)
    (β.symm (e ∘ Sum.inl), i) h * splitNormalizedMatrix e a h j = _
  have hi (h : ι) : originalContractionFactor β (splitNormalizedMatrix e a)
      (β.symm (e ∘ Sum.inl), i) h = (1 : Matrix ι ι R) i h :=
    congrArg (fun M : Matrix ι ι R => M i h) hp
  simp_rw [hi]
  simp [Matrix.one_apply]

/-- The SAME entire contraction factors through its SAME actual original pivot columns and rows. -/
theorem originalContractionMatrix_pivot_factor :
    originalContractionMatrix β (splitNormalizedMatrix e a) =
      (originalContractionMatrix β (splitNormalizedMatrix e a)).submatrix id (e ∘ Sum.inl) *
      (originalContractionMatrix β (splitNormalizedMatrix e a)).submatrix
        (fun i => (β.symm (e ∘ Sum.inl), i)) id := by
  rw [originalContractionMatrix_pivot_columns, originalContractionMatrix_pivot_rows]
  exact originalContractionMatrix_eq_factor_mul β (splitNormalizedMatrix e a)

/-- The literal original pivot intersection block of the SAME contraction is the actual identity. -/
theorem originalContractionMatrix_pivot_block :
    (originalContractionMatrix β (splitNormalizedMatrix e a)).submatrix
      (fun i => (β.symm (e ∘ Sum.inl), i)) (e ∘ Sum.inl) = 1 := by
  have hp := originalContractionMatrix_pivot_rows β e a
  have hm := congrArg (fun M : Matrix ι η R => M.submatrix id (e ∘ Sum.inl)) hp
  exact hm.trans (selectedMatrix_splitNormalized_pivot e a)

end Hironaka.Algebra.PluckerQuot
