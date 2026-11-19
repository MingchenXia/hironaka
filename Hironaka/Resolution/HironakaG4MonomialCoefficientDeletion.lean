import Hironaka.Resolution.HironakaG4MonomialMaximalContact

/-!
# Same-history positive-mark coefficient deletion

Source: BM97 Lemma12.8 and Construction4.18. This is a literal finite
exponent-chart law; analytic realization and recursive termination are separate.
Blueprint: `hironaka-g4-monomial-coefficient-deletion.tex`.
-/

set_option autoImplicit false

open Finset

namespace Hironaka.HironakaG4MonomialCoefficientDeletion

open HironakaG4MonomialMaximalContact

noncomputable section

/-- Exactly the earlier chart operations, factored from any choice of row marks. -/
inductive MonomialTrace : ℕ → Type
  | stop (b : ℕ) : MonomialTrace b
  | over {b : ℕ} (S : Finset (Fin b)) (p : Fin b) (R : Finset (Fin b))
      (hp : p ∈ S) (hpR : p ∉ R) (tail : MonomialTrace (b+1)) : MonomialTrace b
  | off {b : ℕ} (tail : MonomialTrace (b+1)) : MonomialTrace b

def transformMarkedRows {ι : Type} {b : ℕ} (d : ι → ℕ)
    (S R : Finset (Fin b)) (F : ι → Fin b → ℕ) : ι → Fin (b+1) → ℕ :=
  fun i => transformRow (d i) S R (F i)

/-- Genuine selected-row inequalities, permitting distinct positive row marks. -/
def TraceFeasible {ι : Type} (d : ι → ℕ) :
    {b : ℕ} → (ι → Fin b → ℕ) → MonomialTrace b → Prop
  | _,_,.stop _ => True
  | _,F,.over S _ R _ _ T =>
      (∀ i, d i ≤ rowWeight (F i) S) ∧ TraceFeasible d (transformMarkedRows d S R F) T
  | _,F,.off T => TraceFeasible d (appendAbsentFamily F) T

/-- A direct compatible embedding of the prior common-mark histories. -/
def fromCommonHistory {ι : Type} {m b : ℕ} {F : ι → Fin b → ℕ}
    (T : MonomialChartHistory m F) : {U : MonomialTrace b // TraceFeasible (fun _ => m) F U} := by
  induction T with
  | stop F => exact ⟨.stop _,trivial⟩
  | over S p R hp hpR hf T ih =>
    exact ⟨.over S p R hp hpR ih.val, hf, ih.property⟩
  | off T ih => exact ⟨.off ih.val,ih.property⟩

/-- Live means actual selected and retained incidence of the current h label. -/
def TraceLives : {b : ℕ} → MonomialTrace b → Fin b → Prop
  | _,.stop _,_ => True
  | _,.over S _ R _ _ T,h => h ∈ S ∧ h ∈ R ∧ TraceLives T h.castSucc
  | _,.off T,h => TraceLives T h.castSucc

/-- The SAME chronological trace with h erased from selected/retained sets.
The same actual pivot remains valid because it was not retained but h was. -/
def eraseTrace : {b : ℕ} → (T : MonomialTrace b) → (h : Fin b) → TraceLives T h → MonomialTrace b
  | _,.stop b,_,_ => .stop b
  | _,.over S p R hp hpR T,h,hl =>
      .over (S.erase h) p (R.erase h)
        (mem_erase.mpr ⟨by intro he; exact hpR (he.symm ▸ hl.2.1),hp⟩)
        (fun hmem => hpR (mem_of_mem_erase hmem)) (eraseTrace T h.castSucc hl.2.2)
  | _,.off T,h,hl => .off (eraseTrace T h.castSucc hl)

def eraseRow {b : ℕ} (h : Fin b) (a : Fin b → ℕ) : Fin b → ℕ :=
  fun j => if j = h then 0 else a j

def CoefficientPositions {ι : Type} {b : ℕ} (F : ι → Fin b → ℕ) (d : ι → ℕ)
    (h : Fin b) := {i : ι // F i h < d i}

def coefficientMarks {ι : Type} {b : ℕ} (F : ι → Fin b → ℕ) (d : ι → ℕ)
    (h : Fin b) : CoefficientPositions F d h → ℕ := fun i => d i.val - F i.val h

def coefficientRows {ι : Type} {b : ℕ} (F : ι → Fin b → ℕ) (d : ι → ℕ)
    (h : Fin b) : CoefficientPositions F d h → Fin b → ℕ := fun i => eraseRow h (F i.val)

structure PrefixPair (ι κ : Type) where
  slots : ℕ
  label : Fin slots
  main : ι → Fin slots → ℕ
  coefficient : κ → Fin slots → ℕ

/-- Independent controlled prefix computations on the original and erased trace.
The second component applies its own marks to S.erase h and R.erase h. -/
def readPrefixPair {ι κ : Type} (d : ι → ℕ) (e : κ → ℕ) :
    {b : ℕ} → MonomialTrace b → Fin b → (ι → Fin b → ℕ) →
      (κ → Fin b → ℕ) → ℕ → PrefixPair ι κ
  | b,_,h,F,G,0 => ⟨b,h,F,G⟩
  | b,.stop _,h,F,G,_+1 => ⟨b,h,F,G⟩
  | _,.over S _ R _ _ T,h,F,G,k+1 => readPrefixPair d e T h.castSucc
      (transformMarkedRows d S R F) (transformMarkedRows e (S.erase h) (R.erase h) G) k
  | _,.off T,h,F,G,k+1 => readPrefixPair d e T h.castSucc
      (appendAbsentFamily F) (appendAbsentFamily G) k

def markedCosupport {ι : Type} {b : ℕ} (F : ι → Fin b → ℕ) (d : ι → ℕ)
    (K : Finset (Fin b)) : Prop := ∀ i, d i ≤ rowWeight (F i) K

private theorem weight_erase {b : ℕ} (a : Fin b → ℕ) (h : Fin b) (S : Finset (Fin b)) :
    rowWeight (eraseRow h a) S = rowWeight a (S.erase h) := by
  calc
    rowWeight (eraseRow h a) S = rowWeight (eraseRow h a) (S.erase h) := by
      symm
      apply Finset.sum_subset (erase_subset h S)
      intro j hj hjnot
      have he : j = h := by simpa [mem_erase, hj] using hjnot
      simp [eraseRow, he]
    _ = rowWeight a (S.erase h) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [eraseRow, ne_of_mem_erase hj]

private theorem weight_split {b : ℕ} (a : Fin b → ℕ) (h : Fin b)
    (S : Finset (Fin b)) (hh : h ∈ S) :
    rowWeight a S = a h + rowWeight (eraseRow h a) S := by
  rw [weight_erase]
  exact (Finset.add_sum_erase S a hh).symm

private theorem selected_split {b : ℕ} (a : Fin b → ℕ) (h : Fin b)
    (S : Finset (Fin b)) (hh : h ∈ S) :
    rowWeight a S = a h + rowWeight (eraseRow h a) (S.erase h) := by
  rw [weight_erase]
  simpa [rowWeight] using (Finset.add_sum_erase S a hh).symm

private theorem erase_transform {b d : ℕ} (a : Fin b → ℕ) (h : Fin b)
    (S R : Finset (Fin b)) (hh : h ∈ S) (hsmall : a h < d)
    (hf : d ≤ rowWeight a S) :
    transformRow (d-a h) (S.erase h) (R.erase h) (eraseRow h a) =
      eraseRow h.castSucc (transformRow d S R a) := by
  have hs := selected_split a h S hh
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp only [transformRow, Fin.lastCases_last, eraseRow,
      if_neg (Ne.symm (Fin.castSucc_ne_last h))]
    omega
  · by_cases hj : j = h
    · subst j
      simp [transformRow, eraseRow]
    · simp [transformRow, eraseRow, hj]

private theorem erase_append {b : ℕ} (a : Fin b → ℕ) (h : Fin b) :
    appendAbsentRow (eraseRow h a) = eraseRow h.castSucc (appendAbsentRow a) := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [appendAbsentRow, eraseRow, Ne.symm (Fin.castSucc_ne_last h)]
  · simp [appendAbsentRow, eraseRow]

private theorem deletion_history {ι κ : Type} (d : ι → ℕ) (s : κ → ι)
    (α : ι → ℕ) (hsmall : ∀ i, α (s i) < d (s i)) :
    ∀ {b : ℕ} (T : MonomialTrace b) (h : Fin b) (F : ι → Fin b → ℕ)
      (_hα : ∀ i, F i h = α i) (_hf : TraceFeasible d F T) (hl : TraceLives T h),
      TraceFeasible (fun i => d (s i)-α (s i)) (fun i => eraseRow h (F (s i))) (eraseTrace T h hl) ∧
      ∀ k, let P := (readPrefixPair d (fun i => d (s i)-α (s i)) T h F
        (fun i => eraseRow h (F (s i))) k);
        (∀ i, P.main i P.label = α i) ∧
        (∀ i, P.coefficient i = eraseRow P.label (P.main (s i))) := by
  intro b T
  induction T with
  | stop b =>
    intro h F hα hf hl
    refine ⟨trivial,fun k => ?_⟩
    cases k <;> exact ⟨hα,fun _ => rfl⟩
  | over S p R hp hpR T ih =>
    intro h F hα hf hl
    have hα' : ∀ i, transformMarkedRows d S R F i h.castSucc = α i := by
      intro i
      simp [transformMarkedRows, transformRow, hl.2.1, hα]
    have hG : transformMarkedRows (fun i => d (s i)-α (s i)) (S.erase h) (R.erase h)
        (fun i => eraseRow h (F (s i))) =
        fun i => eraseRow h.castSucc (transformMarkedRows d S R F (s i)) := by
      funext i
      simpa [transformMarkedRows, hα] using
        erase_transform (F (s i)) h S R hl.1 (by simpa [hα] using hsmall i) (hf.1 (s i))
    obtain ⟨hTail,hPrefix⟩ := ih h.castSucc (transformMarkedRows d S R F) hα' hf.2 hl.2.2
    refine ⟨?_,fun k => ?_⟩
    · change (∀ i, d (s i)-α (s i) ≤ rowWeight (eraseRow h (F (s i))) (S.erase h)) ∧ _
      constructor
      · intro i
        have hs := selected_split (F (s i)) h S hl.1
        have hi := hf.1 (s i)
        have ha := hα (s i)
        omega
      · rw [hG]
        exact hTail
    · cases k with
      | zero => exact ⟨hα,fun _ => rfl⟩
      | succ k =>
        dsimp only [readPrefixPair]
        rw [hG]
        exact hPrefix k
  | off T ih =>
    intro h F hα hf hl
    have hα' : ∀ i, appendAbsentFamily F i h.castSucc = α i := by
      intro i
      simpa [appendAbsentFamily, appendAbsentRow] using hα i
    have hG : appendAbsentFamily (fun i => eraseRow h (F (s i))) =
        fun i => eraseRow h.castSucc (appendAbsentFamily F (s i)) := by
      funext i
      exact erase_append (F (s i)) h
    obtain ⟨hTail,hPrefix⟩ := ih h.castSucc (appendAbsentFamily F) hα' hf hl
    refine ⟨?_,fun k => ?_⟩
    · change TraceFeasible _ (appendAbsentFamily _) _
      rw [hG]
      exact hTail
    · cases k with
      | zero => exact ⟨hα,fun _ => rfl⟩
      | succ k =>
        dsimp only [readPrefixPair]
        rw [hG]
        exact hPrefix k

private theorem cosupport_of_prefix {ι : Type} {b : ℕ}
    (F : ι → Fin b → ℕ) (d : ι → ℕ) (h : Fin b)
    (P : PrefixPair ι (CoefficientPositions F d h))
    (hα : ∀ i, P.main i P.label = F i h)
    (hG : ∀ i, P.coefficient i = eraseRow P.label (P.main i.val))
    (K : Finset (Fin P.slots)) (hK : P.label ∈ K) :
    markedCosupport P.main d K ↔ markedCosupport P.coefficient (coefficientMarks F d h) K := by
  constructor
  · intro hmain i
    have hi := hmain i.val
    have hs := weight_split (P.main i.val) P.label K hK
    rw [hG i]
    change d i.val - F i.val h ≤ rowWeight (eraseRow P.label (P.main i.val)) K
    rw [hα] at hs
    omega
  · intro hcoeff i
    have hs := weight_split (P.main i) P.label K hK
    rw [hα] at hs
    by_cases hi : F i h < d i
    · let q : CoefficientPositions F d h := ⟨i,hi⟩
      have hq := hcoeff q
      change d i - F i h ≤ rowWeight (P.coefficient q) K at hq
      rw [hG q] at hq
      change d i ≤ rowWeight (P.main i) K
      change d i - F i h ≤ rowWeight (eraseRow P.label (P.main i)) K at hq
      omega
    · change d i ≤ rowWeight (P.main i) K
      omega

/-- Actual varying-mark rows INTERNALLY produce their positive coefficient
family and SAME erased feasible history, with exact ALL-prefix row laws
and full cosupport equality on every incident subset containing current h.
The erased h slot is a zero placeholder retaining chronological labels. -/
theorem coefficient_deletion_finite_history {ι : Type} [Fintype ι] {b : ℕ}
    (F : ι → Fin b → ℕ) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (h : Fin b) (T : MonomialTrace b) (hf : TraceFeasible d F T) (hl : TraceLives T h) :
    (∀ i, 0 < coefficientMarks F d h i) ∧
    TraceFeasible (coefficientMarks F d h) (coefficientRows F d h) (eraseTrace T h hl) ∧
    ∀ k, let P := readPrefixPair d (coefficientMarks F d h) T h F (coefficientRows F d h) k;
      (∀ i, P.main i P.label = F i h) ∧
      (∀ i, P.coefficient i = eraseRow P.label (P.main i.val)) ∧
      ∀ K : Finset (Fin P.slots), P.label ∈ K →
        (markedCosupport P.main d K ↔
          markedCosupport P.coefficient (coefficientMarks F d h) K) := by
  obtain ⟨hTest,hPrefix⟩ := deletion_history d (fun i : CoefficientPositions F d h => i.val)
    (fun i => F i h) (fun i => i.property) T h F (fun _ => rfl) hf hl
  refine ⟨?_,hTest,fun k => ?_⟩
  · intro i
    have hi := i.property
    have hdi := hd i.val
    change 0 < d i.val - F i.val h
    omega
  · obtain ⟨hα,hG⟩ := hPrefix k
    exact ⟨hα,hG,fun K hK => cosupport_of_prefix F d h _ hα hG K hK⟩

end
end Hironaka.HironakaG4MonomialCoefficientDeletion
