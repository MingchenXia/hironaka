import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Lex
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Digits.Defs

/-! Arithmetic for comparing ordered defect stamps with common empty slots. -/

set_option autoImplicit false

open scoped BigOperators

namespace Hironaka.HironakaG4OrderedRowCode

private theorem digit_block_lt {place a b lo hi : ℕ} (hlo : lo < place) (hab : a < b) :
    lo + place * a < hi + place * b :=
  calc
    lo + place * a < place + place * a := Nat.add_lt_add_right hlo _
    _ = place * (a + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ place * b := Nat.mul_le_mul_left _ hab
    _ ≤ hi + place * b := Nat.le_add_left _ _

private theorem digit_block_lt_iff {place a b lo hi : ℕ} (hlo : lo < place) (hhi : hi < place) :
    lo + place * a < hi + place * b ↔ a < b ∨ a = b ∧ lo < hi := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact iff_of_true (digit_block_lt hlo hab) (Or.inl hab)
  · simp
  · have h := digit_block_lt (hi := lo) hhi hba
    exact iff_of_false (by omega) (by omega)

/-- Equal-length bounded digit lists, with the most significant digit first, compare
numerically exactly in lexicographic order. -/
private theorem ofDigits_reverse_lt_iff_lex {base : ℕ} (hBase : 1 < base) {as bs : List ℕ}
    (hlen : as.length = bs.length) (ha : ∀ a ∈ as, a < base) (hb : ∀ b ∈ bs, b < base) :
    Nat.ofDigits base as.reverse < Nat.ofDigits base bs.reverse ↔ List.Lex (· < ·) as bs := by
  induction as generalizing bs with
  | nil =>
      have hbs : bs = [] := List.length_eq_zero_iff.mp hlen.symm
      subst bs
      simp
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          have hlen' : as.length = bs.length := by simpa using hlen
          have ha' : ∀ d ∈ as.reverse, d < base :=
            fun d hd => ha d (List.mem_cons_of_mem a (List.mem_reverse.mp hd))
          have hb' : ∀ d ∈ bs.reverse, d < base :=
            fun d hd => hb d (List.mem_cons_of_mem b (List.mem_reverse.mp hd))
          have hlow : Nat.ofDigits base as.reverse < base ^ bs.length := by
            simpa only [List.length_reverse, hlen'] using Nat.ofDigits_lt_base_pow_length hBase ha'
          have hhigh : Nat.ofDigits base bs.reverse < base ^ bs.length := by
            simpa only [List.length_reverse] using Nat.ofDigits_lt_base_pow_length hBase hb'
          rw [Nat.ofDigits_reverse_cons, Nat.ofDigits_reverse_cons, hlen',
              digit_block_lt_iff hlow hhigh, List.cons_lex_cons_iff]
          rw [ih hlen' (fun d hd => ha' d (List.mem_reverse.mpr hd))
              (fun d hd => hb' d (List.mem_reverse.mpr hd))]

private theorem lex_insertIdx_iff {α : Type*} {rel : α → α → Prop} [Std.Irrefl rel]
    {as bs : List α} (hlen : as.length = bs.length) (j : ℕ) (a : α) :
    List.Lex rel (as.insertIdx j a) (bs.insertIdx j a) ↔ List.Lex rel as bs := by
  induction as generalizing bs j with
  | nil =>
      have hbs : bs = [] := List.length_eq_zero_iff.mp hlen.symm
      subst bs
      cases j <;> simp [List.lex_cons_iff]
  | cons d as ih =>
      cases bs with
      | nil => simp at hlen
      | cons e bs =>
          have hlen' : as.length = bs.length := by simpa using hlen
          cases j with
          | zero => simp [List.lex_cons_iff]
          | succ j => simp only [List.insertIdx_succ_cons, List.cons_lex_cons_iff, ih hlen' j]

private theorem ofFn_insertNth {α : Type*} {m : ℕ} (j : Fin (m + 1)) (a : α) (f : Fin m → α) :
    List.ofFn (j.insertNth a f) = (List.ofFn f).insertIdx j.val a := by
  induction m with
  | zero =>
      have hj : j = 0 := Fin.fin_one_eq_zero j
      subst j
      simp [Fin.insertNth_zero']
  | succ m ih =>
      induction j using Fin.cases with
      | zero => simp [Fin.insertNth_zero']
      | succ j =>
          obtain ⟨d, g, rfl⟩ := Fin.exists_cons f
          rw [Fin.insertNth_succ_cons, List.ofFn_cons, List.ofFn_cons]
          simp only [Fin.val_succ, List.insertIdx_succ_cons, ih]

private def rowDigit {m : ℕ} (r : Fin m → ℕ) (P : Finset (Fin m)) (i : Fin m) : ℕ :=
  2 * r i + if i ∈ P then 1 else 0

/-- The row orders with their inactive-membership bits in literal row order. -/
def orderedRowDigits {m : ℕ} (r : Fin m → ℕ) (P : Finset (Fin m)) : List ℕ :=
  List.ofFn (rowDigit r P)

/-- Earliest-row tie priority. The radix is fixed over all stamps of the same total. -/
def orderedRowTieCode {m : ℕ} (r : Fin m → ℕ) (P : Finset (Fin m)) : ℕ :=
  Nat.ofDigits (2 * ((∑ i, r i) + 1)) (orderedRowDigits r P).reverse

private theorem rowDigit_lt_radix {m : ℕ} (r : Fin m → ℕ) (P : Finset (Fin m))
    {d : ℕ} (hd : d ∈ (orderedRowDigits r P).reverse) : d < 2 * ((∑ i, r i) + 1) := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hd)
  have hi : r i ≤ ∑ j, r j := Finset.single_le_sum (fun j _ => Nat.zero_le (r j)) (Finset.mem_univ i)
  by_cases hP : i ∈ P <;> simp [rowDigit, hP] <;> omega

private theorem rowDigit_eq_iff {m : ℕ} {r s : Fin m → ℕ} {P Q : Finset (Fin m)} {i : Fin m} :
    rowDigit r P i = rowDigit s Q i ↔ r i = s i ∧ (i ∈ P ↔ i ∈ Q) := by
  by_cases hP : i ∈ P <;> by_cases hQ : i ∈ Q <;> simp [rowDigit, hP, hQ] <;> omega

/-- At fixed length and total, the tie code determines every row order and inactive slot. -/
theorem orderedRowTieCode_inj {m : ℕ} {r s : Fin m → ℕ} {P Q : Finset (Fin m)}
    (hTotal : (∑ i, r i) = ∑ i, s i) (hCode : orderedRowTieCode r P = orderedRowTieCode s Q) :
    r = s ∧ P = Q := by
  unfold orderedRowTieCode at hCode
  rw [← hTotal] at hCode
  have hd := Nat.ofDigits_inj_of_len_eq (by omega : 1 < 2 * ((∑ i, r i) + 1))
    (by simp [orderedRowDigits]) (fun _ h => rowDigit_lt_radix r P h)
    (fun _ h => hTotal.symm ▸ rowDigit_lt_radix s Q h) hCode
  have hFunctions := List.ofFn_injective (List.reverse_inj.mp hd)
  have hRows (i : Fin m) := rowDigit_eq_iff.mp (congrFun hFunctions i)
  exact ⟨funext (fun i => (hRows i).1), Finset.ext (fun i => (hRows i).2)⟩

/-- At fixed length and total, the tie code compares the literal row data from the
earliest slot, breaking each row-order tie by its inactive-membership bit. -/
theorem orderedRowTieCode_lt_iff_lex {m : ℕ} {r s : Fin m → ℕ} {P Q : Finset (Fin m)}
    (hTotal : (∑ i, r i) = ∑ i, s i) :
    orderedRowTieCode r P < orderedRowTieCode s Q ↔
      List.Lex (· < ·) (orderedRowDigits r P) (orderedRowDigits s Q) := by
  unfold orderedRowTieCode
  rw [← hTotal]
  exact ofDigits_reverse_lt_iff_lex (by omega) (by simp [orderedRowDigits])
    (fun d hd => rowDigit_lt_radix r P (List.mem_reverse.mpr hd))
    (fun d hd => hTotal.symm ▸ rowDigit_lt_radix s Q (List.mem_reverse.mpr hd))

/-- Inserting one trivial old row inserts exactly a zero digit in that position. -/
theorem orderedRowDigits_insert_zero {m : ℕ} (j : Fin (m + 1)) (r : Fin m → ℕ)
    (P : Finset (Fin m)) :
    orderedRowDigits (j.insertNth 0 r) (P.map j.succAboveEmb) =
      (orderedRowDigits r P).insertIdx j.val 0 := by
  unfold orderedRowDigits
  rw [← ofFn_insertNth]
  congr 1
  funext i
  refine Fin.succAboveCases j ?_ (fun k => ?_) i
  · have hj : j ∉ P.map j.succAboveEmb := by
      rintro h
      obtain ⟨k, _, hk⟩ := Finset.mem_map.mp h
      exact j.succAbove_ne k hk
    simp [rowDigit, Fin.insertNth_apply_same, hj]
  · have hk : j.succAbove k ∈ P.map j.succAboveEmb ↔ k ∈ P :=
      Finset.mem_map' j.succAboveEmb
    simp [rowDigit, Fin.insertNth_apply_succAbove, hk]

/-- Inserting or deleting the same trivial old slot preserves and reflects strict
tie priority. The original row total stays unchanged. -/
theorem orderedRowTieCode_lt_insert_zero_iff {m : ℕ} (j : Fin (m + 1))
    {r s : Fin m → ℕ} {P Q : Finset (Fin m)} (hTotal : (∑ i, r i) = ∑ i, s i) :
    orderedRowTieCode (j.insertNth 0 r) (P.map j.succAboveEmb) <
      orderedRowTieCode (j.insertNth 0 s) (Q.map j.succAboveEmb) ↔
    orderedRowTieCode r P < orderedRowTieCode s Q := by
  have hTotal' : (∑ i, j.insertNth 0 r i) = ∑ i, j.insertNth 0 s i := by simpa using hTotal
  rw [orderedRowTieCode_lt_iff_lex hTotal', orderedRowTieCode_lt_iff_lex hTotal,
      orderedRowDigits_insert_zero, orderedRowDigits_insert_zero]
  exact lex_insertIdx_iff (by simp [orderedRowDigits]) _ _

/-- Pairwise weak priority is preserved as well, for comparing actual maxima. -/
theorem orderedRowTieCode_le_insert_zero_iff {m : ℕ} (j : Fin (m + 1))
    {r s : Fin m → ℕ} {P Q : Finset (Fin m)} (hTotal : (∑ i, r i) = ∑ i, s i) :
    orderedRowTieCode (j.insertNth 0 r) (P.map j.succAboveEmb) ≤
      orderedRowTieCode (j.insertNth 0 s) (Q.map j.succAboveEmb) ↔
    orderedRowTieCode r P ≤ orderedRowTieCode s Q := by
  simpa only [Nat.not_lt] using
    not_congr (orderedRowTieCode_lt_insert_zero_iff j (P := Q) (Q := P) hTotal.symm)

end Hironaka.HironakaG4OrderedRowCode
