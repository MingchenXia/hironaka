import Hironaka.Resolution.HironakaG4MonomialTopStratum

/-!
# Exact one-step positive top-phase arithmetic

Source BM97 Lemma12.8. Actual native proper sets/gcd/residuals are derived;
no multi-step phase or global termination is asserted.
Blueprint: `hironaka-g4-monomial-top-phase-transform.tex`.
-/

set_option autoImplicit false

open Finset

namespace Hironaka.HironakaG4MonomialTopPhaseTransform

open HironakaG4MonomialFamilyInvariant HironakaG4MonomialMaximalContact
open HironakaG4MonomialTopStratum

noncomputable section

def originalTopTransform {r b : ℕ} (A : Fin r → Fin b → ℕ) (S R : Finset (Fin b)) :
    Fin r → Fin (b+1) → ℕ := transformFamily 1 S R A

def proposedGcd {r b : ℕ} (A : Fin r → Fin b → ℕ) (S R : Finset (Fin b)) :
    Fin (b+1) → ℕ := Fin.lastCases (rowWeight (gcdColumn A) S + nuOne A - 1)
      (fun j => if j ∈ R then gcdColumn A j else 0)

/-- Independent controlled marking-L transforms of the INITIAL active residuals. -/
def transportedResidualFamily {r b : ℕ} (A : Fin r → Fin b → ℕ)
    (S R : Finset (Fin b)) : properRows A → Fin (b+1) → ℕ :=
  transformFamily (nuOne A) S R (residualFamily A)

private theorem row_weight_split {r b : ℕ} (A : Fin r → Fin b → ℕ)
    {i : Fin r} (hi : i ∈ properRows A) (S : Finset (Fin b)) :
    rowWeight (A i) S = rowWeight (gcdColumn A) S + residualWeight A i S := by
  simp only [rowWeight, residualWeight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  have hle : gcdColumn A j ≤ A i j := by
    rw [gcdColumn, dif_pos ⟨i,hi⟩]
    exact Finset.inf'_le _ hi
  omega

private theorem top_witness {r b : ℕ} (A : Fin r → Fin b → ℕ) (S : Finset (Fin b))
    (hL : 0 < nuOne A) (hTop : TopCompanionCosupport A 1 S) :
    ∃ w ∈ properRows A,
      (∑ j, (A w j-gcdColumn A j)) = nuOne A ∧ residualWeight A w S = nuOne A ∧
      (∀ i ∈ properRows A, nuOne A ≤ residualWeight A i S) := by
  have hres := hTop.2
  rw [if_neg (Nat.ne_of_gt hL)] at hres
  obtain ⟨w,hw,hmin⟩ := Finset.exists_mem_eq_inf' hTop.1
    (fun i => ∑ j, (A i j-gcdColumn A j))
  have htotal : (∑ j, (A w j-gcdColumn A j)) = nuOne A := by
    rw [nuOne, dif_pos hTop.1]
    exact hmin.symm
  have hle : residualWeight A w S ≤ ∑ j, (A w j-gcdColumn A j) :=
    Finset.sum_le_sum_of_subset (subset_univ S)
  have hge := hres.1 w hw
  exact ⟨w,hw,htotal,by omega,hres.1⟩

private theorem transformed_proper_subset {r b : ℕ} (A : Fin r → Fin b → ℕ)
    (S R : Finset (Fin b)) : properRows (originalTopTransform A S R) ⊆ properRows A := by
  intro i hi
  by_contra hnot
  have horder : rowOrder A i = 0 := by
    have hn : ¬0 < rowOrder A i := by simpa [properRows] using hnot
    omega
  have hz : ∀ j, A i j = 0 := by
    intro j
    have hle := Finset.single_le_sum (fun k (_hk : k ∈ (univ : Finset (Fin b))) =>
      Nat.zero_le (A i k)) (mem_univ j)
    change A i j ≤ rowOrder A i at hle
    omega
  have hnewzero : rowOrder (originalTopTransform A S R) i = 0 := by
    simp [rowOrder, originalTopTransform, transformFamily, transformRow, rowWeight,
      Fin.sum_univ_castSucc, hz]
  have hpos := (mem_filter.mp hi).2
  omega

private theorem gcd_and_residual_of_same_proper {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (S R : Finset (Fin b))
    (hL : 0 < nuOne A) (hTop : TopCompanionCosupport A 1 S)
    (hP : properRows (originalTopTransform A S R) = properRows A) :
    gcdColumn (originalTopTransform A S R) = proposedGcd A S R ∧
      ∀ (i : Fin r) (hi : i ∈ properRows A),
        (fun j => originalTopTransform A S R i j - gcdColumn (originalTopTransform A S R) j) =
          transportedResidualFamily A S R ⟨i,hi⟩ := by
  obtain ⟨w,hw,_htotal,hselected,hfeas⟩ := top_witness A S hL hTop
  have hact' : (properRows (originalTopTransform A S R)).Nonempty := by
    rw [hP]
    exact hTop.1
  have hw' : w ∈ properRows (originalTopTransform A S R) := by rwa [hP]
  have hG : gcdColumn (originalTopTransform A S R) = proposedGcd A S R := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [proposedGcd, Fin.lastCases_last]
      rw [gcdColumn, dif_pos hact']
      apply le_antisymm
      · have hle := Finset.inf'_le
          (fun i => originalTopTransform A S R i (Fin.last b)) hw'
        have hsplit := row_weight_split A hw S
        have hval : originalTopTransform A S R w (Fin.last b) = rowWeight (A w) S - 1 := by
          simp [originalTopTransform, transformFamily, transformRow]
        rw [hval] at hle
        omega
      · apply Finset.le_inf'
        intro i hi
        have hip : i ∈ properRows A := by rwa [hP] at hi
        have hsplit := row_weight_split A hip S
        have hbound := hfeas i hip
        simp only [originalTopTransform, transformFamily, transformRow, Fin.lastCases_last]
        omega
    · simp only [proposedGcd, Fin.lastCases_castSucc]
      rw [gcdColumn, dif_pos hact']
      simp only [hP]
      by_cases hk : k ∈ R <;>
        simp [originalTopTransform, transformFamily, transformRow, gcdColumn, hTop.1, hk]
  refine ⟨hG,fun i hi => ?_⟩
  funext j
  rw [hG]
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hsplit := row_weight_split A hi S
    have hbound := hfeas i hi
    simp only [originalTopTransform, transformFamily, transformRow, proposedGcd,
      transportedResidualFamily, Fin.lastCases_last]
    change (rowWeight (A i) S - 1) - (rowWeight (gcdColumn A) S + nuOne A - 1) =
      residualWeight A i S - nuOne A
    omega
  · by_cases hk : k ∈ R <;>
      simp [originalTopTransform, transformFamily, transformRow, proposedGcd,
        transportedResidualFamily, residualFamily, hk]

private theorem nu_bound_of_same_proper {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (S R : Finset (Fin b))
    (hL : 0 < nuOne A) (hTop : TopCompanionCosupport A 1 S)
    (hP : properRows (originalTopTransform A S R) = properRows A)
    (hres : ∀ (i : Fin r) (hi : i ∈ properRows A),
      (fun j => originalTopTransform A S R i j - gcdColumn (originalTopTransform A S R) j) =
        transportedResidualFamily A S R ⟨i,hi⟩) :
    nuOne (originalTopTransform A S R) ≤ nuOne A := by
  obtain ⟨w,hw,htotal,hselected,_hfeas⟩ := top_witness A S hL hTop
  have hw' : w ∈ properRows (originalTopTransform A S R) := by rwa [hP]
  have hle : nuOne (originalTopTransform A S R) ≤
      ∑ j, (originalTopTransform A S R w j-gcdColumn (originalTopTransform A S R) j) := by
    rw [nuOne, dif_pos ⟨w,hw'⟩]
    exact Finset.inf'_le _ hw'
  have hsum := congrArg (fun f : Fin (b+1) → ℕ => ∑ j, f j) (hres w hw)
  rw [hsum] at hle
  have hdegree : (∑ j, transportedResidualFamily A S R ⟨w,hw⟩ j) = residualWeight A w R := by
    change (∑ j, transformRow (nuOne A) S R (fun k => A w k-gcdColumn A k) j) = _
    simp only [Fin.sum_univ_castSucc, transformRow, Fin.lastCases_castSucc, Fin.lastCases_last]
    change (∑ j, if j ∈ R then A w j-gcdColumn A j else 0) +
      (residualWeight A w S-nuOne A) = _
    rw [hselected, Nat.sub_self, Nat.add_zero]
    simp [residualWeight, rowWeight]
  have hsubset : residualWeight A w R ≤ ∑ j, (A w j-gcdColumn A j) :=
    Finset.sum_le_sum_of_subset (subset_univ R)
  omega

private theorem tau_restriction_le {r b : ℕ} (A : Fin r → Fin b → ℕ)
    (K : Finset (Fin b)) : tauD (restrictIncidence A K) ≤ tauD A := by
  apply Finset.card_le_card
  intro i hi
  have hpos := (mem_filter.mp hi).2
  have hle : rowOrder (restrictIncidence A K) i ≤ rowOrder A i := by
    apply Finset.sum_le_sum
    intro j _hj
    by_cases hj : j ∈ K <;> simp [restrictIncidence, hj]
  exact mem_filter.mpr ⟨mem_univ i,lt_of_lt_of_le hpos hle⟩

/-- Genuine original top-companion selection internally gives either an
actual tau drop or exact native gcd/residual persistence and nu nonincrease.
No supplied min witness, proper-set identity or comparison certificate. -/
theorem actual_top_transform_persistence_or_tau_drop {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (S R : Finset (Fin b)) (p : Fin b)
    (_hp : p ∈ S) (_hpR : p ∉ R) (hL : 0 < nuOne A)
    (hTop : TopCompanionCosupport A 1 S) :
    tauD (originalTopTransform A S R) < tauD A ∨
      (tauD (originalTopTransform A S R) = tauD A ∧
        properRows (originalTopTransform A S R) = properRows A ∧
        gcdColumn (originalTopTransform A S R) = proposedGcd A S R ∧
        (∀ (i : Fin r) (hi : i ∈ properRows A),
          (fun j => originalTopTransform A S R i j-gcdColumn (originalTopTransform A S R) j) =
            transportedResidualFamily A S R ⟨i,hi⟩) ∧
        nuOne (originalTopTransform A S R) ≤ nuOne A) := by
  have hle : tauD (originalTopTransform A S R) ≤ tauD A :=
    Finset.card_le_card (transformed_proper_subset A S R)
  by_cases htau : tauD (originalTopTransform A S R) = tauD A
  · have hP : properRows (originalTopTransform A S R) = properRows A :=
      Finset.eq_of_subset_of_card_le (transformed_proper_subset A S R) htau.ge
    obtain ⟨hG,hres⟩ := gcd_and_residual_of_same_proper A S R hL hTop hP
    exact Or.inr ⟨htau,hP,hG,hres,nu_bound_of_same_proper A S R hL hTop hP hres⟩
  · exact Or.inl (by omega)

/-- Failure of the actually transported mark-L residual family at ANY
endpoint incidence K forces strict exit of the genuine native top pair.
This does NOT claim the original marked cosupport is empty. -/
theorem actual_top_transform_exit_of_residual_failure {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (S R : Finset (Fin b)) (p : Fin b)
    (hp : p ∈ S) (hpR : p ∉ R) (hL : 0 < nuOne A)
    (hTop : TopCompanionCosupport A 1 S) (K : Finset (Fin (b+1)))
    (hfailure : ¬familyCosupport (transportedResidualFamily A S R) (nuOne A) K) :
    tauD (restrictIncidence (originalTopTransform A S R) K) < tauD A ∨
      (tauD (restrictIncidence (originalTopTransform A S R) K) = tauD A ∧
        nuOne (restrictIncidence (originalTopTransform A S R) K) < nuOne A) := by
  have hRestr := tau_restriction_le (originalTopTransform A S R) K
  rcases actual_top_transform_persistence_or_tau_drop A S R p hp hpR hL hTop with
    hdrop | ⟨htau,hP,_hG,hres,_hnu⟩
  · exact Or.inl (lt_of_le_of_lt hRestr hdrop)
  · by_cases heq : tauD (restrictIncidence (originalTopTransform A S R) K) = tauD A
    · right
      refine ⟨heq,?_⟩
      have htauK : tauD (restrictIncidence (originalTopTransform A S R) K) =
          tauD (originalTopTransform A S R) := heq.trans htau.symm
      rw [nuOne_restrictIncidence_of_tau_eq _ K htauK]
      have hfail : ¬∀ i : properRows A, nuOne A ≤ rowWeight (transportedResidualFamily A S R i) K :=
        hfailure
      obtain ⟨i,hbad⟩ := not_forall.mp hfail
      have hi' : i.val ∈ properRows (originalTopTransform A S R) := by rw [hP]; exact i.property
      have hminle : fixedResidualMinimum (originalTopTransform A S R) K ≤
          residualWeight (originalTopTransform A S R) i.val K := by
        rw [fixedResidualMinimum, dif_pos ⟨i.val,hi'⟩]
        exact Finset.inf'_le _ hi'
      have hrow : residualWeight (originalTopTransform A S R) i.val K =
          rowWeight (transportedResidualFamily A S R i) K :=
        congrArg (fun f : Fin (b+1) → ℕ => rowWeight f K) (hres i.val i.property)
      rw [hrow] at hminle
      exact lt_of_le_of_lt hminle (Nat.lt_of_not_ge hbad)
    · exact Or.inl (by omega)

end
end Hironaka.HironakaG4MonomialTopPhaseTransform
