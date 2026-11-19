import Hironaka.Resolution.HironakaG4MonomialMaximalContact
set_option autoImplicit false
open Set Finset Classical
open scoped BigOperators
namespace Hironaka.HironakaG4MonomialRowChain
noncomputable section
open HironakaG4MonomialFamilyInvariant HironakaG4MonomialMaximalContact

def RowsChain {ι : Type} {b : ℕ} (A : ι → Fin b → ℕ) : Prop :=
  ∀ i k, (∀ j,A i j ≤ A k j) ∨ (∀ j,A k j ≤ A i j)

/-- Relabeling columns transports the same pairwise comparison. -/
theorem rowsChain_of_column_equiv {ι : Type} {b c : ℕ}
    (A : ι → Fin b → ℕ) (B : ι → Fin c → ℕ) (e : Fin c ≃ Fin b)
    (h : ∀ i j,B i j=A i (e j)) (hChain : RowsChain A) : RowsChain B := by
  intro i k
  rcases hChain i k with hle | hle
  · left
    intro j
    rw [h i j,h k j]
    exact hle (e j)
  · right
    intro j
    rw [h k j,h i j]
    exact hle (e j)

/-- Relabeling rows also preserves their componentwise comparability. -/
theorem rowsChain_of_row_equiv {ι κ : Type} {b : ℕ}
    (A : ι → Fin b → ℕ) (B : κ → Fin b → ℕ) (e : κ ≃ ι)
    (h : ∀ i j,B i j=A (e i) j) (hChain : RowsChain A) : RowsChain B := by
  intro i k
  rcases hChain (e i) (e k) with hle | hle
  · left
    intro j
    rw [h i j,h k j]
    exact hle j
  · right
    intro j
    rw [h k j,h i j]
    exact hle j

/-- A finite componentwise chain of proper rows has an actual gcd row. -/
theorem nuOne_eq_zero_of_rowsChain {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (hChain : RowsChain A) : nuOne A=0 := by
  classical
  by_cases hAct : (properRows A).Nonempty
  · obtain ⟨i,hi,hMin⟩ := Finset.exists_min_image (properRows A) (rowOrder A) hAct
    apply (nuOne_eq_zero_iff_exists_gcd_row A hAct).mpr
    refine ⟨i,hi,?_⟩
    intro j
    have hLeast (k : ι) (hk : k ∈ properRows A) : ∀ j,A i j ≤ A k j := by
      rcases hChain i k with h | h
      · exact h
      · by_contra hnot
        push Not at hnot
        obtain ⟨j,hj⟩ := hnot
        have hlt : rowOrder A k < rowOrder A i := by
          unfold rowOrder
          exact Finset.sum_lt_sum (fun j _ => h j) ⟨j,Finset.mem_univ _,by omega⟩
        exact (not_lt_of_ge (hMin k hk)) hlt
    unfold gcdColumn
    rw [dif_pos hAct]
    apply le_antisymm
    · exact Finset.le_inf' hAct (fun k => A k j) (fun k hk => hLeast k hk j)
    · exact Finset.inf'_le _ hi
  · simp [nuOne,hAct]

/-- Every controlled chart transform preserves componentwise row order. -/
theorem transformFamily_rowsChain {ι : Type} {b : ℕ} (A : ι → Fin b → ℕ)
    (S R : Finset (Fin b)) (m : ℕ) (hChain : RowsChain A) :
    RowsChain (transformFamily m S R A) := by
  have hMono (i k : ι) (h : ∀ j,A i j ≤ A k j) :
      ∀ j,transformFamily m S R A i j ≤ transformFamily m S R A k j := by
    intro j
    induction j using Fin.lastCases with
    | last =>
        simp only [transformFamily,transformRow,Fin.lastCases_last,rowWeight]
        exact Nat.sub_le_sub_right (Finset.sum_le_sum (fun j _ => h j)) m
    | cast j =>
        simp only [transformFamily,transformRow,Fin.lastCases_castSucc]
        split <;> simp_all
  intro i k
  rcases hChain i k with h | h
  · exact Or.inl (hMono i k h)
  · exact Or.inr (hMono k i h)

/-- Adding an absent born column also preserves componentwise row order. -/
theorem appendAbsentFamily_rowsChain {ι : Type} {b : ℕ} (A : ι → Fin b → ℕ)
    (hChain : RowsChain A) : RowsChain (appendAbsentFamily A) := by
  have hMono (i k : ι) (h : ∀ j,A i j ≤ A k j) :
      ∀ j,appendAbsentFamily A i j ≤ appendAbsentFamily A k j := by
    intro j
    induction j using Fin.lastCases with
    | last => simp [appendAbsentFamily,appendAbsentRow]
    | cast j => simpa [appendAbsentFamily,appendAbsentRow] using h j
  intro i k
  rcases hChain i k with h | h
  · exact Or.inl (hMono i k h)
  · exact Or.inr (hMono k i h)
end
end Hironaka.HironakaG4MonomialRowChain
