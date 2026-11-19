import Hironaka.Invariant.MonomialInvariant
import Mathlib.Algebra.BigOperators.Fin

/-!
# The source nuOne=0 common-gcd branch for simultaneous monomial rows

Current proper rows define the gcd and residual minimum. The actual common
Cartier transform retains the old pivot at zero and appends the new born
column. The finite producer stops when a tracked row becomes a unit.
No geometry or termination of the nuOne>0 recursive branch is asserted.
Blueprint: `hironaka-g4-monomial-family-invariant.tex`.
-/

set_option autoImplicit false

open Finset

universe u

namespace Hironaka.HironakaG4MonomialFamilyInvariant

noncomputable section

/-- Actual ordinary order of one monomial row. -/
def rowOrder {ι : Type u} {b : ℕ} (A : ι → Fin b → ℕ) (i : ι) : ℕ :=
  ∑ j, A i j

/-- Current proper rows; unit rows are excluded from the source presentation. -/
def properRows {ι : Type u} [Fintype ι] {b : ℕ} (A : ι → Fin b → ℕ) : Finset ι :=
  univ.filter fun i => 0 < rowOrder A i

def tauD {ι : Type u} [Fintype ι] {b : ℕ} (A : ι → Fin b → ℕ) : ℕ :=
  (properRows A).card

/-- The true gcd exponent, minimized over CURRENT proper rows. -/
def gcdColumn {ι : Type u} [Fintype ι] {b : ℕ} (A : ι → Fin b → ℕ) (j : Fin b) : ℕ :=
  if h : (properRows A).Nonempty then (properRows A).inf' h (fun i => A i j) else 0

def gcdOrder {ι : Type u} [Fintype ι] {b : ℕ} (A : ι → Fin b → ℕ) : ℕ :=
  ∑ j, gcdColumn A j

/-- BM97 Lemma12.8's first residual order, using the actual current proper set. -/
def nuOne {ι : Type u} [Fintype ι] {b : ℕ} (A : ι → Fin b → ℕ) : ℕ :=
  if h : (properRows A).Nonempty then
    (properRows A).inf' h (fun i => ∑ j, (A i j - gcdColumn A j)) else 0

private theorem gcdColumn_le {ι : Type u} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) {i : ι} (hi : i ∈ properRows A) (j : Fin b) :
    gcdColumn A j ≤ A i j := by
  rw [gcdColumn, dif_pos ⟨i,hi⟩]
  exact Finset.inf'_le _ hi

/-- A source zero residual is recognized by an actual proper row equal to
the componentwise gcd, with no supplied row or invariant dictionary. -/
theorem nuOne_eq_zero_iff_exists_gcd_row {ι : Type u} [Fintype ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (hact : (properRows A).Nonempty) :
    nuOne A = 0 ↔ ∃ i ∈ properRows A, ∀ j, A i j = gcdColumn A j := by
  classical
  rw [nuOne, dif_pos hact]
  constructor
  · intro hzero
    obtain ⟨i,hi,hmin⟩ := Finset.exists_mem_eq_inf' hact
      (fun i => ∑ j, (A i j - gcdColumn A j))
    have hsum : (∑ j, (A i j - gcdColumn A j)) = 0 := hmin.symm.trans hzero
    refine ⟨i,hi,fun j => ?_⟩
    have hle := gcdColumn_le A hi j
    have hj := Finset.single_le_sum (fun k (_hk : k ∈ (univ : Finset (Fin b))) =>
      Nat.zero_le (A i k - gcdColumn A k)) (mem_univ j)
    rw [hsum] at hj
    omega
  · rintro ⟨i,hi,hrow⟩
    have hz : (∑ j, (A i j - gcdColumn A j)) = 0 := by simp only [hrow, Nat.sub_self, sum_const_zero]
    have hle := Finset.inf'_le (fun i => ∑ j, (A i j - gcdColumn A j)) hi
    rw [hz] at hle
    exact Nat.eq_zero_of_le_zero hle

/-- Literal chronological Cartier row law: retain the old pivot slot at zero,
retain the other old exponents, append the new born exponent minus one. -/
def cartierTransform {ι : Type u} {b : ℕ} (A : ι → Fin b → ℕ) (j : Fin b) :
    ι → Fin (b+1) → ℕ :=
  fun i => Fin.lastCases (A i j - 1) (fun k => if k = j then 0 else A i k)

/-- An actual finite sequence of common Cartier row transformations. Each
selected born column hits EVERY tracked row; no decrease premise occurs. -/
inductive CommonCartierPhase {ι : Type u} :
    {b c : ℕ} → (ι → Fin b → ℕ) → (ι → Fin c → ℕ) → ℕ → Prop
  | nil {b : ℕ} (A : ι → Fin b → ℕ) : CommonCartierPhase A A 0
  | cons {b c : ℕ} {A : ι → Fin b → ℕ} {B : ι → Fin c → ℕ} {l : ℕ}
      (j : Fin b) (hpos : ∀ i, 0 < A i j)
      (tail : CommonCartierPhase (cartierTransform A j) B l) :
      CommonCartierPhase A B (l+1)

private theorem rowOrder_cartierTransform_add_one {ι : Type u} {b : ℕ}
    (A : ι → Fin b → ℕ) (i : ι) (j : Fin b) (hpos : 0 < A i j) :
    rowOrder (cartierTransform A j) i + 1 = rowOrder A i := by
  classical
  have hsum : (∑ k : Fin b, if k = j then 0 else A i k) + A i j = rowOrder A i := by
    calc
      (∑ k : Fin b, if k = j then 0 else A i k) + A i j =
          (∑ k : Fin b, if k = j then 0 else A i k) +
            (∑ k : Fin b, if k = j then A i k else 0) := by simp
      _ = ∑ k : Fin b, ((if k = j then 0 else A i k) +
          (if k = j then A i k else 0)) := (Finset.sum_add_distrib).symm
      _ = rowOrder A i := by
        apply Finset.sum_congr rfl
        intro k _hk
        by_cases h : k = j <;> simp [h]
  have hnew : rowOrder (cartierTransform A j) i =
      (∑ k : Fin b, if k = j then 0 else A i k) + (A i j - 1) := by
    simp only [rowOrder, Fin.sum_univ_castSucc, cartierTransform,
      Fin.lastCases_castSucc, Fin.lastCases_last]
  omega

private theorem least_row_cartierTransform {ι : Type u} {b : ℕ}
    (A : ι → Fin b → ℕ) (w : ι) (hle : ∀ i j, A w j ≤ A i j) (j : Fin b) :
    ∀ i k, cartierTransform A j w k ≤ cartierTransform A j i k := by
  intro i k
  refine Fin.lastCases ?_ (fun a => ?_) k
  · simpa only [cartierTransform, Fin.lastCases_last] using Nat.sub_le_sub_right (hle i j) 1
  · simp only [cartierTransform, Fin.lastCases_castSucc]
    by_cases h : a = j
    · simp only [h, if_true, le_refl]
    · simp only [h, if_false]
      exact hle i a

private theorem phase_slots {ι : Type u} {b c l : ℕ}
    {A : ι → Fin b → ℕ} {B : ι → Fin c → ℕ} (h : CommonCartierPhase A B l) :
    c = b + l := by
  induction h with
  | nil A => omega
  | cons j hpos tail ih => omega

private theorem exists_phase_of_least_row {ι : Type u} (w : ι) :
    ∀ (r b : ℕ) (A : ι → Fin b → ℕ), rowOrder A w = r →
      (∀ i j, A w j ≤ A i j) →
      ∃ (c : ℕ) (B : ι → Fin c → ℕ), CommonCartierPhase A B r ∧ rowOrder B w = 0 := by
  intro r
  induction r with
  | zero =>
    intro b A hr _hle
    exact ⟨b,A,CommonCartierPhase.nil A,hr⟩
  | succ r ih =>
    intro b A hr hle
    have hpos : 0 < ∑ j, A w j := by change 0 < rowOrder A w; omega
    obtain ⟨j,_hj,hj⟩ := Finset.sum_pos_iff.mp hpos
    have hall : ∀ i, 0 < A i j := fun i => lt_of_lt_of_le hj (hle i j)
    have hnew : rowOrder (cartierTransform A j) w = r := by
      have h := rowOrder_cartierTransform_add_one A w j hj
      omega
    obtain ⟨c,B,hphase,hzero⟩ := ih (b+1) (cartierTransform A j) hnew
      (least_row_cartierTransform A w hle j)
    exact ⟨c,B,CommonCartierPhase.cons j hall hphase,hzero⟩

/-- Original finite active monomial rows in the source nuOne=0 branch
INTERNALLY produce an exact-length genuine chronological Cartier phase
ending in a strict tauD drop. No terminal residual-invariant claim is made. -/
theorem exists_common_gcd_cartier_phase {ι : Type u} [Fintype ι] [Nonempty ι] {b : ℕ}
    (A : ι → Fin b → ℕ) (hall : ∀ i, 0 < rowOrder A i) (hnu : nuOne A = 0) :
    ∃ (c : ℕ) (B : ι → Fin c → ℕ),
      CommonCartierPhase A B (gcdOrder A) ∧ c = b + gcdOrder A ∧
        0 < gcdOrder A ∧ tauD B < tauD A := by
  classical
  have hproper : properRows A = univ := by
    ext i
    simp only [properRows, mem_filter, mem_univ, true_and, hall i]
  have hact : (properRows A).Nonempty := by rw [hproper]; exact univ_nonempty
  obtain ⟨w,hw,hgcd⟩ := (nuOne_eq_zero_iff_exists_gcd_row A hact).mp hnu
  have hleast : ∀ i j, A w j ≤ A i j := by
    intro i j
    rw [hgcd j]
    exact gcdColumn_le A (by rw [hproper]; exact mem_univ i) j
  have horder : rowOrder A w = gcdOrder A := by
    simp only [rowOrder, gcdOrder, hgcd]
  obtain ⟨c,B,hphase,hzero⟩ := exists_phase_of_least_row w (rowOrder A w) b A rfl hleast
  rw [horder] at hphase
  refine ⟨c,B,hphase,phase_slots hphase,by rw [←horder]; exact hall w,?_⟩
  have hlt : (properRows B).card < (univ : Finset ι).card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,?_⟩
    intro heq
    have hwB : w ∈ properRows B := by rw [heq]; exact mem_univ w
    have hwpos : 0 < rowOrder B w := (mem_filter.mp hwB).2
    omega
  simpa only [tauD, hproper] using hlt

end
end Hironaka.HironakaG4MonomialFamilyInvariant
