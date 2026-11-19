import Hironaka.Resolution.HironakaG4MonomialTopStratum

/-!
# Zero residual order under a retained-count native transform

The existing mark-one family transform and arbitrary incidence restriction
cannot increase the actual current proper-row count. If that count is retained,
an internally attained original gcd row remains proper and attains every actual
new gcd column. This proves zero residual persistence on the retained branch.
No geometric history, strict pair decrease or lower-count residual claim occurs.
Blueprint: `hironaka-g4-zero-residual-top-transform.tex`.
-/

set_option autoImplicit false

open Finset

namespace Hironaka.HironakaG4ZeroResidualTopTransform

open HironakaG4MonomialFamilyInvariant HironakaG4MonomialMaximalContact
  HironakaG4MonomialTopStratum

noncomputable section

private theorem zero_of_not_proper {r b : ℕ} (A : Fin r → Fin b → ℕ)
    {i : Fin r} (hi : i ∉ properRows A) : ∀ j, A i j = 0 := by
  have hn : ¬0 < rowOrder A i := by simpa [properRows] using hi
  have ho : rowOrder A i = 0 := by omega
  intro j
  have hle := Finset.single_le_sum (fun k (_hk : k ∈ (univ : Finset (Fin b))) =>
    Nat.zero_le (A i k)) (mem_univ j)
  change A i j ≤ rowOrder A i at hle
  omega

private theorem transformed_proper_subset {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (S R : Finset (Fin b))
    (K : Finset (Fin (b+1))) :
    properRows (restrictIncidence (transformFamily 1 S R A) K) ⊆ properRows A := by
  classical
  intro i hi
  by_contra hnot
  have hz := zero_of_not_proper A hnot
  have hB : ∀ j, transformFamily 1 S R A i j = 0 := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j <;>
      simp [transformFamily, transformRow, rowWeight, hz]
  have hC : ∀ j, restrictIncidence (transformFamily 1 S R A) K i j = 0 := by
    intro j
    simp [restrictIncidence, hB]
  have hzero : rowOrder (restrictIncidence (transformFamily 1 S R A) K) i = 0 := by
    simp [rowOrder, hC]
  have hpos := (mem_filter.mp hi).2
  omega

private theorem transformed_least_row {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (S R : Finset (Fin b))
    (K : Finset (Fin (b+1))) (w : Fin r)
    (hle : ∀ i ∈ properRows A, ∀ j, A w j ≤ A i j) :
    ∀ i ∈ properRows A, ∀ j,
      restrictIncidence (transformFamily 1 S R A) K w j ≤
        restrictIncidence (transformFamily 1 S R A) K i j := by
  classical
  intro i hi j
  by_cases hj : j ∈ K
  · simp only [restrictIncidence, if_pos hj]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [transformFamily, transformRow, Fin.lastCases_last]
      apply Nat.sub_le_sub_right
      exact Finset.sum_le_sum (fun k _hk => hle i hi k)
    · simp only [transformFamily, transformRow, Fin.lastCases_castSucc]
      by_cases hk : k ∈ R
      · simpa only [if_pos hk] using hle i hi k
      · simp only [if_neg hk, le_refl]
  · simp only [restrictIncidence, if_neg hj, le_refl]

/-- Arbitrary native selected/retained mark-one transformation and endpoint
incidence restriction cannot create a proper row from an original zero row. -/
theorem actual_transform_incidence_tau_le {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (S R : Finset (Fin b))
    (K : Finset (Fin (b+1))) :
    tauD (restrictIncidence (transformFamily 1 S R A) K) ≤ tauD A := by
  exact Finset.card_le_card (transformed_proper_subset A S R K)

/-- Only original current nonempty proper rows, zero residual order and actual
retained endpoint count imply literal proper-set equality and recomputed nu zero.
The attaining original and endpoint gcd row is constructed internally. -/
theorem actual_transform_incidence_nu_zero_of_tau_eq {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (S R : Finset (Fin b))
    (K : Finset (Fin (b+1))) (hact : (properRows A).Nonempty)
    (hnu : nuOne A = 0)
    (htau : tauD (restrictIncidence (transformFamily 1 S R A) K) = tauD A) :
    properRows (restrictIncidence (transformFamily 1 S R A) K) = properRows A ∧
      nuOne (restrictIncidence (transformFamily 1 S R A) K) = 0 := by
  classical
  let C := restrictIncidence (transformFamily 1 S R A) K
  have hP : properRows C = properRows A :=
    Finset.eq_of_subset_of_card_le (transformed_proper_subset A S R K) htau.ge
  have hactC : (properRows C).Nonempty := by rwa [hP]
  obtain ⟨w, hw, hrow⟩ := (nuOne_eq_zero_iff_exists_gcd_row A hact).mp hnu
  have hleast : ∀ i ∈ properRows A, ∀ j, A w j ≤ A i j := by
    intro i hi j
    rw [hrow j, gcdColumn, dif_pos hact]
    exact Finset.inf'_le _ hi
  have hwC : w ∈ properRows C := by rwa [hP]
  refine ⟨hP, (nuOne_eq_zero_iff_exists_gcd_row C hactC).mpr ⟨w, hwC, ?_⟩⟩
  intro j
  apply le_antisymm
  · rw [gcdColumn, dif_pos hactC]
    apply Finset.le_inf'
    intro i hi
    exact transformed_least_row A S R K w hleast i (by rwa [← hP]) j
  · rw [gcdColumn, dif_pos hactC]
    exact Finset.inf'_le _ hwC

end
end Hironaka.HironakaG4ZeroResidualTopTransform
