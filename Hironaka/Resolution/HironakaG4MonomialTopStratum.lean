import Hironaka.Resolution.HironakaG4MonomialMaximalContact

/-!
# The actual active top (tauD, nuOne) incidence stratum

Source BM97 Lemma12.8. No whole-cosupport normalization or history
termination is asserted. Blueprint: `hironaka-g4-monomial-top-stratum.tex`.
-/

set_option autoImplicit false

open Finset

namespace Hironaka.HironakaG4MonomialTopStratum

open HironakaG4MonomialFamilyInvariant HironakaG4MonomialMaximalContact

noncomputable section

def restrictIncidence {ι : Type} {b : ℕ} (A : ι → Fin b → ℕ) (K : Finset (Fin b)) :
    ι → Fin b → ℕ := fun i j => if j ∈ K then A i j else 0

def residualWeight {ι : Type} [Fintype ι] {b : ℕ} (A : ι → Fin b → ℕ)
    (i : ι) (K : Finset (Fin b)) : ℕ := rowWeight (fun j => A i j - gcdColumn A j) K

/-- Minimum on the INITIAL actual proper set; not a recomputed invariant. -/
def fixedResidualMinimum {ι : Type} [Fintype ι] {b : ℕ} (A : ι → Fin b → ℕ)
    (K : Finset (Fin b)) : ℕ :=
  if h : (properRows A).Nonempty then (properRows A).inf' h (fun i => residualWeight A i K) else 0

/-- Original common-mark cosupport on the INITIAL active positions only. -/
def trackedCosupport {ι : Type} [Fintype ι] {b : ℕ} (A : ι → Fin b → ℕ)
    (D : ℕ) (K : Finset (Fin b)) : Prop := ∀ i ∈ properRows A, D ≤ rowWeight (A i) K

/-- Actual active top companion: zero residual uses only the gcd row;
positive residual uses its marked rows and a gcd row only if its mark is positive. -/
def TopCompanionCosupport {ι : Type} [Fintype ι] {b : ℕ} (A : ι → Fin b → ℕ)
    (D : ℕ) (K : Finset (Fin b)) : Prop :=
  (properRows A).Nonempty ∧
    if nuOne A = 0 then D ≤ rowWeight (gcdColumn A) K else
      (∀ i ∈ properRows A, nuOne A ≤ residualWeight A i K) ∧
      (nuOne A < D → D-nuOne A ≤ rowWeight (gcdColumn A) K)

private theorem gcd_le {ι : Type} [Fintype ι] {b : ℕ} (A : ι → Fin b → ℕ)
    {i : ι} (hi : i ∈ properRows A) (j : Fin b) : gcdColumn A j ≤ A i j := by
  rw [gcdColumn, dif_pos ⟨i,hi⟩]
  exact Finset.inf'_le _ hi

private theorem row_weight_split {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) {i : ι} (hi : i ∈ properRows A) (K : Finset (Fin b)) :
    rowWeight (A i) K = rowWeight (gcdColumn A) K + residualWeight A i K := by
  simp only [rowWeight, residualWeight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  exact (Nat.add_sub_of_le (gcd_le A hi j)).symm

private theorem fixed_min_le {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) {i : ι} (hi : i ∈ properRows A) (K : Finset (Fin b)) :
    fixedResidualMinimum A K ≤ residualWeight A i K := by
  rw [fixedResidualMinimum, dif_pos ⟨i,hi⟩]
  exact Finset.inf'_le _ hi

private theorem fixed_min_attained {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (hact : (properRows A).Nonempty) (K : Finset (Fin b)) :
    ∃ i ∈ properRows A, fixedResidualMinimum A K = residualWeight A i K := by
  rw [fixedResidualMinimum, dif_pos hact]
  exact Finset.exists_mem_eq_inf' hact _

private theorem residual_lower_iff {ι : Type} [Fintype ι] {b L : ℕ}
    (A : ι → Fin b → ℕ) (hact : (properRows A).Nonempty) (K : Finset (Fin b)) :
    (∀ i ∈ properRows A, L ≤ residualWeight A i K) ↔ L ≤ fixedResidualMinimum A K := by
  rw [fixedResidualMinimum, dif_pos hact, Finset.le_inf'_iff]

private theorem fixed_min_le_nu {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (K : Finset (Fin b)) : fixedResidualMinimum A K ≤ nuOne A := by
  classical
  by_cases hact : (properRows A).Nonempty
  · obtain ⟨i,hi,hmin⟩ := Finset.exists_mem_eq_inf' hact
      (fun i => ∑ j, (A i j-gcdColumn A j))
    have hnu : nuOne A = ∑ j, (A i j-gcdColumn A j) := by
      rw [nuOne, dif_pos hact]
      exact hmin
    calc
      fixedResidualMinimum A K ≤ residualWeight A i K := fixed_min_le A hi K
      _ ≤ ∑ j, (A i j-gcdColumn A j) := Finset.sum_le_sum_of_subset (subset_univ K)
      _ = nuOne A := hnu.symm
  · simp [fixedResidualMinimum, nuOne, hact]

private theorem tracked_cosupport_iff {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (D : ℕ) (K : Finset (Fin b)) (hact : (properRows A).Nonempty) :
    trackedCosupport A D K ↔ D ≤ rowWeight (gcdColumn A) K + fixedResidualMinimum A K := by
  constructor
  · intro h
    obtain ⟨i,hi,hmin⟩ := fixed_min_attained A hact K
    have hx := h i hi
    rwa [row_weight_split A hi K, ←hmin] at hx
  · intro h i hi
    rw [row_weight_split A hi K]
    exact h.trans (Nat.add_le_add_left (fixed_min_le A hi K) _)

/-- The actual companion is exactly original TRACKED marked cosupport
intersected with the top fixed residual level, including empty/zero branches. -/
theorem top_companion_iff_tracked_cosupport_residual_minimum {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (D : ℕ) (_hD : 0 < D) (K : Finset (Fin b)) :
    TopCompanionCosupport A D K ↔ (properRows A).Nonempty ∧
      trackedCosupport A D K ∧ fixedResidualMinimum A K = nuOne A := by
  classical
  by_cases hact : (properRows A).Nonempty
  · have hbound := fixed_min_le_nu A K
    simp only [TopCompanionCosupport, hact, true_and]
    rw [tracked_cosupport_iff A D K hact]
    by_cases hz : nuOne A = 0
    · have hm : fixedResidualMinimum A K = 0 := by omega
      simp [hz, hm]
    · simp only [hz, if_false]
      constructor
      · rintro ⟨hres,hgcd⟩
        have hlow := (residual_lower_iff A hact K).mp hres
        have hm : fixedResidualMinimum A K = nuOne A := by omega
        refine ⟨?_,hm⟩
        by_cases hLD : nuOne A < D
        · have h := hgcd hLD
          omega
        · omega
      · rintro ⟨horig,hm⟩
        refine ⟨(residual_lower_iff A hact K).mpr (by omega),fun hLD => ?_⟩
        omega
  · simp [TopCompanionCosupport, hact]

private theorem restricted_order {ι : Type} {b : ℕ} (A : ι → Fin b → ℕ)
    (K : Finset (Fin b)) (i : ι) : rowOrder (restrictIncidence A K) i = rowWeight (A i) K := by
  simp [rowOrder, restrictIncidence, rowWeight]

private theorem restricted_proper_subset {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (K : Finset (Fin b)) : properRows (restrictIncidence A K) ⊆ properRows A := by
  intro i hi
  have hpos := (mem_filter.mp hi).2
  rw [restricted_order] at hpos
  have hle : rowWeight (A i) K ≤ rowOrder A i := Finset.sum_le_sum_of_subset (subset_univ K)
  exact mem_filter.mpr ⟨mem_univ i,lt_of_lt_of_le hpos hle⟩

theorem restricted_proper_eq {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (K : Finset (Fin b))
    (htau : tauD (restrictIncidence A K) = tauD A) :
    properRows (restrictIncidence A K) = properRows A := by
  apply Finset.eq_of_subset_of_card_le (restricted_proper_subset A K)
  exact htau.ge

/-- Native recomputed nuOne equals the tracked incidence minimum ONLY on
the genuine retained-tau stratum; actual proper sets and gcds are derived. -/
theorem nuOne_restrictIncidence_of_tau_eq {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (K : Finset (Fin b))
    (htau : tauD (restrictIncidence A K) = tauD A) :
    nuOne (restrictIncidence A K) = fixedResidualMinimum A K := by
  classical
  have hp := restricted_proper_eq A K htau
  have hgcd : ∀ j, gcdColumn (restrictIncidence A K) j = if j ∈ K then gcdColumn A j else 0 := by
    intro j
    by_cases hj : j ∈ K <;> simp [gcdColumn, hp, restrictIncidence, hj]
  have hsum : ∀ i, (∑ j, (restrictIncidence A K i j - gcdColumn (restrictIncidence A K) j)) =
      residualWeight A i K := by
    intro i
    calc
      (∑ j, (restrictIncidence A K i j - gcdColumn (restrictIncidence A K) j)) =
          ∑ j, if j ∈ K then A i j-gcdColumn A j else 0 := by
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hj : j ∈ K <;> simp [hgcd, restrictIncidence, hj]
      _ = residualWeight A i K := by simp [residualWeight, rowWeight]
  simp only [nuOne, fixedResidualMinimum, hp, hsum]

private theorem tracked_one_iff_retained_tau {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (K : Finset (Fin b)) :
    trackedCosupport A 1 K ↔ tauD (restrictIncidence A K) = tauD A := by
  constructor
  · intro hcos
    have hp : properRows (restrictIncidence A K) = properRows A := by
      apply subset_antisymm (restricted_proper_subset A K)
      intro i hi
      refine mem_filter.mpr ⟨mem_univ i,?_⟩
      rw [restricted_order]
      exact hcos i hi
    exact congrArg Finset.card hp
  · intro htau i hi
    have hp := restricted_proper_eq A K htau
    have himem : i ∈ properRows (restrictIncidence A K) := by rwa [hp]
    have hpos := (mem_filter.mp himem).2
    rwa [restricted_order] at hpos

/-- The source mark-one companion is EXACTLY the active top pair of the
actual native tauD and recomputed nuOne, not the entire original cosupport. -/
theorem top_companion_iff_retained_tau_nu {ι : Type} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (K : Finset (Fin b)) :
    TopCompanionCosupport A 1 K ↔ 0 < tauD A ∧
      tauD (restrictIncidence A K) = tauD A ∧ nuOne (restrictIncidence A K) = nuOne A := by
  classical
  rw [top_companion_iff_tracked_cosupport_residual_minimum A 1 (by decide) K]
  constructor
  · rintro ⟨hact,hcos,hmin⟩
    have htau := (tracked_one_iff_retained_tau A K).mp hcos
    refine ⟨Finset.card_pos.mpr hact,htau,?_⟩
    exact (nuOne_restrictIncidence_of_tau_eq A K htau).trans hmin
  · rintro ⟨hpos,htau,hnu⟩
    refine ⟨Finset.card_pos.mp hpos,(tracked_one_iff_retained_tau A K).mpr htau,?_⟩
    exact (nuOne_restrictIncidence_of_tau_eq A K htau).symm.trans hnu

end
end Hironaka.HironakaG4MonomialTopStratum
