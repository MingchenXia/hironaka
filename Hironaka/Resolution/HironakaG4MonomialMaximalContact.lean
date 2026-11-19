import Hironaka.Resolution.HironakaG4MonomialFamilyInvariant

/-!
# Blowup-only finite coordinate equivalence of source positive residual rows

Original current proper rows and the genuine positive residual minimum
internally supply the residual family and least supported coordinate.
All transforms and histories below are literal exponent arithmetic;
no analytic GeoTestTower or nuOne>0 termination is claimed.
Blueprint: `hironaka-g4-monomial-maximal-contact.tex`.
-/

set_option autoImplicit false

open Finset

namespace Hironaka.HironakaG4MonomialMaximalContact

noncomputable section

open HironakaG4MonomialFamilyInvariant

/-- The original gcd-divided rows, on the ACTUAL current proper old positions. -/
def residualFamily {r b : ℕ} (A : Fin r → Fin b → ℕ) : properRows A → Fin b → ℕ :=
  fun i j => A i.val j - gcdColumn A j

def rowWeight {b : ℕ} (a : Fin b → ℕ) (S : Finset (Fin b)) : ℕ := ∑ j ∈ S, a j

def coordinateRow {b : ℕ} (h : Fin b) : Fin b → ℕ := fun j => if j = h then 1 else 0

/-- Literal controlled monomial row in a chart with retained old incidences R.
The pivot is absent from R in every actual history constructor below. -/
def transformRow {b : ℕ} (d : ℕ) (S R : Finset (Fin b)) (a : Fin b → ℕ) : Fin (b+1) → ℕ :=
  Fin.lastCases (rowWeight a S - d) (fun j => if j ∈ R then a j else 0)

def appendAbsentRow {b : ℕ} (a : Fin b → ℕ) : Fin (b+1) → ℕ := Fin.lastCases 0 a

def transformFamily {ι : Type} {b : ℕ} (m : ℕ) (S R : Finset (Fin b))
    (F : ι → Fin b → ℕ) : ι → Fin (b+1) → ℕ := fun i => transformRow m S R (F i)

def appendAbsentFamily {ι : Type} {b : ℕ} (F : ι → Fin b → ℕ) :
    ι → Fin (b+1) → ℕ := fun i => appendAbsentRow (F i)

/-- Finite genuine exponent-chart tests. The only step premise is the actual
selected-row feasibility, with its actual pivot/old incidence bookkeeping. -/
inductive MonomialChartHistory {ι : Type} (m : ℕ) :
    {b : ℕ} → (ι → Fin b → ℕ) → Type
  | stop {b : ℕ} (F : ι → Fin b → ℕ) : MonomialChartHistory m F
  | over {b : ℕ} {F : ι → Fin b → ℕ} (S : Finset (Fin b)) (p : Fin b)
      (R : Finset (Fin b)) (hp : p ∈ S) (hpR : p ∉ R)
      (feasible : ∀ i, m ≤ rowWeight (F i) S)
      (tail : MonomialChartHistory m (transformFamily m S R F)) : MonomialChartHistory m F
  | off {b : ℕ} {F : ι → Fin b → ℕ}
      (tail : MonomialChartHistory m (appendAbsentFamily F)) : MonomialChartHistory m F

structure ChartState (ι : Type) where
  slots : ℕ
  rows : ι → Fin slots → ℕ
  coordinate : Fin slots → ℕ

/-- Every actual prefix, with saturation at the true finite endpoint.
The coordinate is independently computed using marking one on the SAME steps. -/
def readPrefix {ι : Type} {m : ℕ} :
    {b : ℕ} → {F : ι → Fin b → ℕ} → MonomialChartHistory m F →
      (Fin b → ℕ) → ℕ → ChartState ι
  | b,F,_,v,0 => ⟨b,F,v⟩
  | b,F,.stop _,v,_+1 => ⟨b,F,v⟩
  | _,_,.over S _ R _ _ _ T,v,k+1 => readPrefix T (transformRow 1 S R v) k
  | _,_,.off T,v,k+1 => readPrefix T (appendAbsentRow v) k

/-- Actual marking-one feasibility at every recorded through-centre step. -/
def IsCoordinateTest {ι : Type} {m : ℕ} :
    {b : ℕ} → {F : ι → Fin b → ℕ} → MonomialChartHistory m F → (Fin b → ℕ) → Prop
  | _,_,.stop _,_ => True
  | _,_,.over S _ R _ _ _ T,v => 1 ≤ rowWeight v S ∧ IsCoordinateTest T (transformRow 1 S R v)
  | _,_,.off T,v => IsCoordinateTest T (appendAbsentRow v)

def familyCosupport {ι : Type} {b : ℕ} (F : ι → Fin b → ℕ) (m : ℕ)
    (K : Finset (Fin b)) : Prop := ∀ i, m ≤ rowWeight (F i) K

private theorem weight_le_total {b : ℕ} (a : Fin b → ℕ) (S : Finset (Fin b)) :
    rowWeight a S ≤ ∑ j, a j := Finset.sum_le_sum_of_subset (subset_univ S)

private theorem positive_mem_of_full_weight {b : ℕ} (a : Fin b → ℕ)
    (S : Finset (Fin b)) (h : Fin b) (hh : 0 < a h)
    (hfull : (∑ j, a j) ≤ rowWeight a S) : h ∈ S := by
  by_contra hnot
  have hsum : rowWeight a S + a h ≤ ∑ j, a j := by
    calc
      rowWeight a S + a h = rowWeight a (insert h S) := by simp [rowWeight, hnot, Nat.add_comm]
      _ ≤ ∑ j, a j := weight_le_total a _
  omega

private theorem no_feasible_step_of_deficient {ι : Type} {b m : ℕ}
    (F : ι → Fin b → ℕ) (w : ι) (hsmall : rowOrder F w < m) (S : Finset (Fin b)) :
    ¬ (∀ i, m ≤ rowWeight (F i) S) := by
  intro hf
  have hle := weight_le_total (F w) S
  have hw := hf w
  change rowWeight (F w) S ≤ rowOrder F w at hle
  omega

private def ContactData {ι : Type} {b : ℕ} (F : ι → Fin b → ℕ)
    (v : Fin b → ℕ) (w : ι) (m : ℕ) : Prop :=
  rowOrder F w < m ∨
    (rowOrder F w = m ∧ ∃ h, v = coordinateRow h ∧ 0 < F w h)

private theorem coordinate_transform {b : ℕ} (S R : Finset (Fin b)) (h : Fin b)
    (hS : h ∈ S) (hR : h ∈ R) :
    transformRow 1 S R (coordinateRow h) = coordinateRow h.castSucc := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [transformRow, coordinateRow, rowWeight, hS, Ne.symm (Fin.castSucc_ne_last h)]
  · by_cases hj : j = h
    · subst j
      simp [transformRow, coordinateRow, hR]
    · simp [transformRow, coordinateRow, hj]

private theorem append_coordinate {b : ℕ} (h : Fin b) :
    appendAbsentRow (coordinateRow h) = coordinateRow h.castSucc := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k <;>
    simp [appendAbsentRow, coordinateRow, Ne.symm (Fin.castSucc_ne_last h)]

private theorem transformed_degree {ι : Type} {b m : ℕ} (F : ι → Fin b → ℕ)
    (w : ι) (S R : Finset (Fin b)) (hS : rowWeight (F w) S = m) :
    rowOrder (transformFamily m S R F) w = rowWeight (F w) R := by
  change (∑ j ∈ S, F w j) = m at hS
  simp [rowOrder, transformFamily, transformRow, Fin.sum_univ_castSucc, hS, rowWeight]

private theorem append_degree {ι : Type} {b : ℕ} (F : ι → Fin b → ℕ) (w : ι) :
    rowOrder (appendAbsentFamily F) w = rowOrder F w := by
  simp [rowOrder, appendAbsentFamily, appendAbsentRow, Fin.sum_univ_castSucc]

private theorem contact_over {ι : Type} {b m : ℕ} {F : ι → Fin b → ℕ}
    {v : Fin b → ℕ} {w : ι} (hd : ContactData F v w m) (S R : Finset (Fin b))
    (hf : ∀ i, m ≤ rowWeight (F i) S) :
    1 ≤ rowWeight v S ∧ ContactData (transformFamily m S R F) (transformRow 1 S R v) w m := by
  rcases hd with hsmall | ⟨heq,h,hv,hh⟩
  · exact (no_feasible_step_of_deficient F w hsmall S hf).elim
  · subst v
    have hselected : rowWeight (F w) S = m := by
      have hle := weight_le_total (F w) S
      change rowWeight (F w) S ≤ rowOrder F w at hle
      have hw := hf w
      omega
    have hS : h ∈ S := positive_mem_of_full_weight (F w) S h hh (by
      change rowOrder F w ≤ rowWeight (F w) S
      omega)
    refine ⟨by simp [rowWeight, coordinateRow, hS], ?_⟩
    have hdegree := transformed_degree F w S R hselected
    have hle : rowOrder (transformFamily m S R F) w ≤ m := by
      rw [hdegree]
      have h := weight_le_total (F w) R
      change rowWeight (F w) R ≤ rowOrder F w at h
      omega
    by_cases heq' : rowOrder (transformFamily m S R F) w = m
    · have hR : h ∈ R := positive_mem_of_full_weight (F w) R h hh (by
        change rowOrder F w ≤ rowWeight (F w) R
        omega)
      right
      refine ⟨heq',h.castSucc,coordinate_transform S R h hS hR,?_⟩
      simpa [transformFamily, transformRow, hR] using hh
    · left
      omega

private theorem contact_off {ι : Type} {b m : ℕ} {F : ι → Fin b → ℕ}
    {v : Fin b → ℕ} {w : ι} (hd : ContactData F v w m) :
    ContactData (appendAbsentFamily F) (appendAbsentRow v) w m := by
  rcases hd with hsmall | ⟨heq,h,hv,hh⟩
  · left
    rwa [append_degree]
  · right
    refine ⟨(append_degree F w).trans heq,h.castSucc,?_,?_⟩
    · rw [hv]
      exact append_coordinate h
    · simpa [appendAbsentFamily, appendAbsentRow] using hh

private theorem contact_cosupport {ι : Type} {b m : ℕ} {F : ι → Fin b → ℕ}
    {v : Fin b → ℕ} {w : ι} (hd : ContactData F v w m) (K : Finset (Fin b)) :
    familyCosupport F m K ↔ familyCosupport F m K ∧ 1 ≤ rowWeight v K := by
  constructor
  · intro hF
    refine ⟨hF,?_⟩
    rcases hd with hsmall | ⟨heq,h,hv,hh⟩
    · have hle := weight_le_total (F w) K
      change rowWeight (F w) K ≤ rowOrder F w at hle
      have hw := hF w
      omega
    · have hK : h ∈ K := positive_mem_of_full_weight (F w) K h hh (by
        change rowOrder F w ≤ rowWeight (F w) K
        rw [heq]
        exact hF w)
      rw [hv]
      simp [rowWeight, coordinateRow, hK]
  · exact And.left

private theorem contact_history {ι : Type} {m : ℕ} (w : ι) :
    ∀ {b : ℕ} {F : ι → Fin b → ℕ} (T : MonomialChartHistory m F) (v : Fin b → ℕ),
      ContactData F v w m → IsCoordinateTest T v ∧
        ∀ k, let P := readPrefix T v k; ContactData P.rows P.coordinate w m := by
  intro b F T
  induction T with
  | stop F =>
    intro v hd
    refine ⟨trivial,fun k => ?_⟩
    cases k <;> exact hd
  | over S p R hp hpR hf T ih =>
    intro v hd
    obtain ⟨hcoord,hnew⟩ := contact_over hd S R hf
    obtain ⟨hTest,hPrefix⟩ := ih (transformRow 1 S R v) hnew
    refine ⟨⟨hcoord,hTest⟩,fun k => ?_⟩
    cases k with
    | zero => exact hd
    | succ k => exact hPrefix k
  | off T ih =>
    intro v hd
    obtain ⟨hTest,hPrefix⟩ := ih (appendAbsentRow v) (contact_off hd)
    refine ⟨hTest,fun k => ?_⟩
    cases k with
    | zero => exact hd
    | succ k => exact hPrefix k

/-- ONLY original matrix/current-proper-row data and the genuine positive
residual minimum internally supply minimum row, least coordinate and its
same-history marking-one tests with ALL-prefix literal cosupport equality. -/
theorem exists_original_residual_coordinate_test_equivalence {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (hnu : 0 < nuOne A) :
    ∃ (w : properRows A) (h : Fin b),
      rowOrder (residualFamily A) w = nuOne A ∧ 0 < residualFamily A w h ∧
      (∀ j, 0 < residualFamily A w j → h ≤ j) ∧
      (∀ i, nuOne A ≤ rowOrder (residualFamily A) i) ∧
      ∀ T : MonomialChartHistory (nuOne A) (residualFamily A),
        IsCoordinateTest T (coordinateRow h) ∧
        ∀ k, let P := readPrefix T (coordinateRow h) k;
          ∀ K : Finset (Fin P.slots),
            familyCosupport P.rows (nuOne A) K ↔
              familyCosupport P.rows (nuOne A) K ∧ 1 ≤ rowWeight P.coordinate K := by
  classical
  have hact : (properRows A).Nonempty := by
    by_contra he
    have hz : nuOne A = 0 := by simp [nuOne, he]
    omega
  have hdef : nuOne A = (properRows A).inf' hact
      (fun i => ∑ j, (A i j - gcdColumn A j)) := by rw [nuOne, dif_pos hact]
  obtain ⟨i,hi,hmin⟩ := Finset.exists_mem_eq_inf' hact
    (fun i => ∑ j, (A i j - gcdColumn A j))
  let w : properRows A := ⟨i,hi⟩
  have hw : rowOrder (residualFamily A) w = nuOne A := hmin.symm.trans hdef.symm
  have hpos : 0 < ∑ j, residualFamily A w j := by
    change 0 < rowOrder (residualFamily A) w
    omega
  let S : Finset (Fin b) := univ.filter fun j => 0 < residualFamily A w j
  have hS : S.Nonempty := by
    obtain ⟨j,_hj,hj⟩ := Finset.sum_pos_iff.mp hpos
    exact ⟨j,mem_filter.mpr ⟨mem_univ j,hj⟩⟩
  let h := S.min' hS
  have hh : 0 < residualFamily A w h := (mem_filter.mp (Finset.min'_mem S hS)).2
  refine ⟨w,h,hw,hh,?_,?_,?_⟩
  · intro j hj
    exact Finset.min'_le S j (mem_filter.mpr ⟨mem_univ j,hj⟩)
  · intro j
    rw [hdef]
    exact Finset.inf'_le _ j.property
  · intro T
    have hd : ContactData (residualFamily A) (coordinateRow h) w (nuOne A) :=
      Or.inr ⟨hw,h,rfl,hh⟩
    obtain ⟨hTest,hPrefix⟩ := contact_history w T (coordinateRow h) hd
    refine ⟨hTest,fun k K => ?_⟩
    exact contact_cosupport (hPrefix k) K

end
end Hironaka.HironakaG4MonomialMaximalContact
