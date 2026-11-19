import Hironaka.Resolution.HironakaG4MonomialTopPhaseTransform

/-!
# Exact native top-pair dictionary along genuine finite residual histories

Source BM97 Lemma12.8. Original/common/residual rows are independently read
from the same existing literal history. No phase existence or termination
is claimed. Blueprint: `hironaka-g4-monomial-finite-top-phase.tex`.
-/

set_option autoImplicit false

open Finset

namespace Hironaka.HironakaG4MonomialFiniteTopPhase

open HironakaG4MonomialFamilyInvariant HironakaG4MonomialMaximalContact
open HironakaG4MonomialTopStratum

noncomputable section

structure PhaseState (r : ℕ) (κ : Type) where
  slots : ℕ
  original : Fin r → Fin slots → ℕ
  residual : κ → Fin slots → ℕ
  common : Fin slots → ℕ

private def transformCommon {b : ℕ} (L : ℕ) (S R : Finset (Fin b))
    (c : Fin b → ℕ) : Fin (b+1) → ℕ :=
  Fin.lastCases (rowWeight c S+L-1) (fun j => if j ∈ R then c j else 0)

/-- Original/common rows are independently read; residual rows are the
actual controlled family already in the SAME existing finite history. -/
def readPhasePrefix {r : ℕ} {κ : Type} {L : ℕ} :
    {b : ℕ} → {F : κ → Fin b → ℕ} → MonomialChartHistory L F →
      (Fin r → Fin b → ℕ) → (Fin b → ℕ) → ℕ → PhaseState r κ
  | b,F,_,A,c,0 => ⟨b,A,F,c⟩
  | b,F,.stop _,A,c,_+1 => ⟨b,A,F,c⟩
  | _,_,.over S _ R _ _ _ T,A,c,k+1 =>
      readPhasePrefix T (transformFamily 1 S R A) (transformCommon L S R c) k
  | _,_,.off T,A,c,k+1 => readPhasePrefix T (appendAbsentFamily A) (appendAbsentRow c) k

private def PhaseInvariant {r b : ℕ} (P : Finset (Fin r)) (w : P) (L : ℕ)
    (A : Fin r → Fin b → ℕ) (F : P → Fin b → ℕ) (c : Fin b → ℕ) : Prop :=
  (∀ i, i ∉ P → ∀ j, A i j = 0) ∧
  (∀ i : P, ∀ j, A i.val j = c j + F i j) ∧
  (∀ j, ∃ i : P, F i j = 0) ∧ rowOrder F w ≤ L

private theorem selected_eq_of_degree_le {κ : Type} {b L : ℕ}
    (F : κ → Fin b → ℕ) (w : κ) (hdeg : rowOrder F w ≤ L)
    (S : Finset (Fin b)) (hf : ∀ i, L ≤ rowWeight (F i) S) : rowWeight (F w) S = L := by
  have hle : rowWeight (F w) S ≤ rowOrder F w := Finset.sum_le_sum_of_subset (subset_univ S)
  have hge := hf w
  omega

private theorem transformed_degree {κ : Type} {b L : ℕ} (F : κ → Fin b → ℕ)
    (w : κ) (S R : Finset (Fin b)) (hS : rowWeight (F w) S = L) :
    rowOrder (transformFamily L S R F) w = rowWeight (F w) R := by
  change (∑ j ∈ S, F w j) = L at hS
  simp [rowOrder, transformFamily, transformRow, Fin.sum_univ_castSucc, hS, rowWeight]

private theorem invariant_over {r b L : ℕ} {P : Finset (Fin r)} {w : P}
    {A : Fin r → Fin b → ℕ} {F : P → Fin b → ℕ} {c : Fin b → ℕ}
    (hL : 0 < L) (hi : PhaseInvariant P w L A F c) (S R : Finset (Fin b))
    (hf : ∀ i, L ≤ rowWeight (F i) S) :
    PhaseInvariant P w L (transformFamily 1 S R A) (transformFamily L S R F)
      (transformCommon L S R c) := by
  obtain ⟨hout,hfac,hzero,hdeg⟩ := hi
  have hselected := selected_eq_of_degree_le F w hdeg S hf
  refine ⟨?_,?_,?_,?_⟩
  · intro i hip j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [transformFamily, transformRow, rowWeight, hout i hip]
    · simp [transformFamily, transformRow, hout i hip]
  · intro i j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · have hsplit : rowWeight (A i.val) S = rowWeight c S + rowWeight (F i) S := by
        simp only [rowWeight, hfac i, Finset.sum_add_distrib]
      have hbound := hf i
      simp only [transformFamily, transformRow, transformCommon, Fin.lastCases_last]
      omega
    · by_cases hk : k ∈ R <;> simp [transformFamily, transformRow, transformCommon, hk, hfac i k]
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · refine ⟨w,?_⟩
      simp [transformFamily, transformRow, hselected]
    · by_cases hk : k ∈ R
      · obtain ⟨i,hiz⟩ := hzero k
        exact ⟨i,by simpa [transformFamily, transformRow, hk] using hiz⟩
      · exact ⟨w,by simp [transformFamily, transformRow, hk]⟩
  · rw [transformed_degree F w S R hselected]
    exact (Finset.sum_le_sum_of_subset (subset_univ R)).trans hdeg

private theorem invariant_off {r b L : ℕ} {P : Finset (Fin r)} {w : P}
    {A : Fin r → Fin b → ℕ} {F : P → Fin b → ℕ} {c : Fin b → ℕ}
    (hi : PhaseInvariant P w L A F c) :
    PhaseInvariant P w L (appendAbsentFamily A) (appendAbsentFamily F) (appendAbsentRow c) := by
  obtain ⟨hout,hfac,hzero,hdeg⟩ := hi
  refine ⟨?_,?_,?_,?_⟩
  · intro i hip j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [appendAbsentFamily, appendAbsentRow, hout i hip]
  · intro i j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [appendAbsentFamily, appendAbsentRow, hfac i]
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · exact ⟨w,by simp [appendAbsentFamily, appendAbsentRow]⟩
    · obtain ⟨i,hiz⟩ := hzero k
      exact ⟨i,by simpa [appendAbsentFamily, appendAbsentRow] using hiz⟩
  · simpa [rowOrder, appendAbsentFamily, appendAbsentRow, Fin.sum_univ_castSucc] using hdeg

private theorem invariant_history {r L : ℕ} (P : Finset (Fin r)) (w : P) (hL : 0 < L) :
    ∀ {b : ℕ} {F : P → Fin b → ℕ} (T : MonomialChartHistory L F)
      (A : Fin r → Fin b → ℕ) (c : Fin b → ℕ), PhaseInvariant P w L A F c →
      ∀ k, let Q := readPhasePrefix T A c k;
        PhaseInvariant P w L Q.original Q.residual Q.common := by
  intro b F T
  induction T with
  | stop F =>
    intro A c hi k
    cases k <;> exact hi
  | over S p R hp hpR hf T ih =>
    intro A c hi k
    cases k with
    | zero => exact hi
    | succ k => exact ih _ _ (invariant_over hL hi S R hf) k
  | off T ih =>
    intro A c hi k
    cases k with
    | zero => exact hi
    | succ k => exact ih _ _ (invariant_off hi) k

private theorem exists_initial_invariant {r b : ℕ} (A : Fin r → Fin b → ℕ)
    (hL : 0 < nuOne A) : ∃ w : properRows A,
      PhaseInvariant (properRows A) w (nuOne A) A (residualFamily A) (gcdColumn A) := by
  classical
  have hact : (properRows A).Nonempty := by
    by_contra he
    have hz : nuOne A = 0 := by simp [nuOne, he]
    omega
  obtain ⟨w,hw,hmin⟩ := Finset.exists_mem_eq_inf' hact
    (fun i => ∑ j, (A i j-gcdColumn A j))
  let q : properRows A := ⟨w,hw⟩
  refine ⟨q,?_,?_,?_,?_⟩
  · intro i hip j
    have horder : rowOrder A i = 0 := by
      have hn : ¬0 < rowOrder A i := by simpa [properRows] using hip
      omega
    have hle := Finset.single_le_sum (fun k (_hk : k ∈ (univ : Finset (Fin b))) =>
      Nat.zero_le (A i k)) (mem_univ j)
    change A i j ≤ rowOrder A i at hle
    omega
  · intro i j
    have hle : gcdColumn A j ≤ A i.val j := by
      rw [gcdColumn, dif_pos hact]
      exact Finset.inf'_le _ i.property
    change A i.val j = gcdColumn A j + (A i.val j-gcdColumn A j)
    omega
  · intro j
    obtain ⟨i,hi,hcol⟩ := Finset.exists_mem_eq_inf' hact (fun i => A i j)
    have hc : gcdColumn A j = A i j := by rw [gcdColumn, dif_pos hact]; exact hcol
    refine ⟨⟨i,hi⟩,?_⟩
    change A i j-gcdColumn A j = 0
    rw [hc, Nat.sub_self]
  · change (∑ j, (A w j-gcdColumn A j)) ≤ nuOne A
    rw [nuOne, dif_pos hact]
    exact hmin.symm.le

private theorem outside_proper_subset {r b : ℕ} (P : Finset (Fin r))
    (A : Fin r → Fin b → ℕ) (hout : ∀ i, i ∉ P → ∀ j, A i j = 0)
    (K : Finset (Fin b)) : properRows (restrictIncidence A K) ⊆ P := by
  intro i hi
  by_contra hip
  have hzero : rowOrder (restrictIncidence A K) i = 0 := by
    simp [rowOrder, restrictIncidence, hout i hip]
  have hpos := (mem_filter.mp hi).2
  omega

private theorem native_data {r b L : ℕ} {P : Finset (Fin r)} {w : P}
    {A : Fin r → Fin b → ℕ} {F : P → Fin b → ℕ} {c : Fin b → ℕ}
    (hi : PhaseInvariant P w L A F c) (K : Finset (Fin b))
    (hcard : tauD (restrictIncidence A K) = P.card) :
    properRows (restrictIncidence A K) = P ∧
      gcdColumn (restrictIncidence A K) = (fun j => if j ∈ K then c j else 0) ∧
      (∀ i : P, (fun j => restrictIncidence A K i.val j-gcdColumn (restrictIncidence A K) j) =
        fun j => if j ∈ K then F i j else 0) ∧
      nuOne (restrictIncidence A K) ≤ L ∧
      (∀ i : P, nuOne (restrictIncidence A K) ≤ rowWeight (F i) K) ∧
      (familyCosupport F L K → L ≤ nuOne (restrictIncidence A K)) := by
  obtain ⟨hout,hfac,hzero,hdeg⟩ := hi
  have hP : properRows (restrictIncidence A K) = P :=
    Finset.eq_of_subset_of_card_le (outside_proper_subset P A hout K) hcard.ge
  have hw' : w.val ∈ properRows (restrictIncidence A K) := by rw [hP]; exact w.property
  have hact' : (properRows (restrictIncidence A K)).Nonempty := ⟨w.val,hw'⟩
  have hG : gcdColumn (restrictIncidence A K) = (fun j => if j ∈ K then c j else 0) := by
    funext j
    by_cases hj : j ∈ K
    · simp only [if_pos hj]
      rw [gcdColumn, dif_pos hact']
      apply le_antisymm
      · obtain ⟨i,hiz⟩ := hzero j
        have hi' : i.val ∈ properRows (restrictIncidence A K) := by rw [hP]; exact i.property
        have hle := Finset.inf'_le (fun i => restrictIncidence A K i j) hi'
        have hval : restrictIncidence A K i.val j = c j := by
          simp [restrictIncidence, hj, hfac i j, hiz]
        rwa [hval] at hle
      · apply Finset.le_inf'
        intro i hip
        have hipP : i ∈ P := by rwa [hP] at hip
        simp only [restrictIncidence, if_pos hj]
        calc
          c j ≤ c j + F ⟨i,hipP⟩ j := Nat.le_add_right _ _
          _ = A i j := (hfac ⟨i,hipP⟩ j).symm
    · simp [gcdColumn, restrictIncidence, hj]
  have hres : ∀ i : P,
      (fun j => restrictIncidence A K i.val j-gcdColumn (restrictIncidence A K) j) =
        fun j => if j ∈ K then F i j else 0 := by
    intro i
    funext j
    rw [hG]
    by_cases hj : j ∈ K <;> simp [restrictIncidence, hj, hfac i j]
  have hweight : ∀ i : P, (∑ j,
      (restrictIncidence A K i.val j-gcdColumn (restrictIncidence A K) j)) = rowWeight (F i) K := by
    intro i
    simpa [rowWeight] using congrArg (fun f : Fin b → ℕ => ∑ j, f j) (hres i)
  have hle : ∀ i : P, nuOne (restrictIncidence A K) ≤ rowWeight (F i) K := by
    intro i
    have himem : i.val ∈ properRows (restrictIncidence A K) := by rw [hP]; exact i.property
    have hle' : nuOne (restrictIncidence A K) ≤ ∑ j,
        (restrictIncidence A K i.val j-gcdColumn (restrictIncidence A K) j) := by
      rw [nuOne, dif_pos hact']
      exact Finset.inf'_le _ himem
    rwa [hweight i] at hle'
  have hnu : nuOne (restrictIncidence A K) ≤ L := by
    have hs : rowWeight (F w) K ≤ rowOrder F w := Finset.sum_le_sum_of_subset (subset_univ K)
    exact (hle w).trans (hs.trans hdeg)
  refine ⟨hP,hG,hres,hnu,hle,?_⟩
  intro hcos
  rw [nuOne, dif_pos hact']
  apply Finset.le_inf'
  intro i hip
  have hipP : i ∈ P := by rwa [hP] at hip
  let q : P := ⟨i,hipP⟩
  have hq := hcos q
  rwa [←hweight q] at hq

/-- ONLY original A and its actual positive native residual minimum give
the native dictionary and exact top-pair presentation at EVERY prefix of
EVERY same existing finite residual history, for EVERY incidence subset. -/
theorem actual_finite_top_phase_dictionary {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (hL : 0 < nuOne A) :
    ∀ (T : MonomialChartHistory (nuOne A) (residualFamily A)) (k : ℕ),
      let Q := readPhasePrefix T A (gcdColumn A) k;
      tauD Q.original ≤ tauD A ∧
      (tauD Q.original = tauD A →
        properRows Q.original = properRows A ∧ gcdColumn Q.original = Q.common ∧
        (∀ i : properRows A, (fun j => Q.original i.val j-gcdColumn Q.original j) = Q.residual i) ∧
        nuOne Q.original ≤ nuOne A) ∧
      ∀ K : Finset (Fin Q.slots),
        (familyCosupport Q.residual (nuOne A) K ↔
          tauD (restrictIncidence Q.original K) = tauD A ∧
          nuOne (restrictIncidence Q.original K) = nuOne A) ∧
        (¬familyCosupport Q.residual (nuOne A) K →
          tauD (restrictIncidence Q.original K) < tauD A ∨
          (tauD (restrictIncidence Q.original K) = tauD A ∧
            nuOne (restrictIncidence Q.original K) < nuOne A)) := by
  obtain ⟨w,hinit⟩ := exists_initial_invariant A hL
  intro T k
  let Q := readPhasePrefix T A (gcdColumn A) k
  have hi : PhaseInvariant (properRows A) w (nuOne A) Q.original Q.residual Q.common :=
    invariant_history (properRows A) w hL T A (gcdColumn A) hinit k
  have hUniv : restrictIncidence Q.original univ = Q.original := by
    funext i j
    simp [restrictIncidence]
  have hsub : properRows Q.original ⊆ properRows A := by
    simpa only [hUniv] using outside_proper_subset (properRows A) Q.original hi.1 univ
  refine ⟨Finset.card_le_card hsub,?_,fun K => ?_⟩
  · intro htau
    have hc : tauD (restrictIncidence Q.original univ) = (properRows A).card := by
      rw [hUniv]
      exact htau
    obtain ⟨hP,hG,hres,hnu,_hle,_hlow⟩ := native_data hi univ hc
    have hdata := And.intro hP (And.intro hG (And.intro hres hnu))
    simpa only [hUniv, Finset.mem_univ, if_true] using hdata
  · have hsubK := outside_proper_subset (properRows A) Q.original hi.1 K
    have htauKle : tauD (restrictIncidence Q.original K) ≤ tauD A := Finset.card_le_card hsubK
    have hiff : familyCosupport Q.residual (nuOne A) K ↔
        tauD (restrictIncidence Q.original K) = tauD A ∧
        nuOne (restrictIncidence Q.original K) = nuOne A := by
      constructor
      · intro hcos
        have hPsub : properRows A ⊆ properRows (restrictIncidence Q.original K) := by
          intro i hip
          let q : properRows A := ⟨i,hip⟩
          have hrow : Q.original i = (fun j => Q.common j + Q.residual q j) := by
            funext j
            exact hi.2.1 q j
          have hweight : rowWeight (Q.original i) K =
              rowWeight Q.common K + rowWeight (Q.residual q) K := by
            rw [hrow]
            simp [rowWeight, Finset.sum_add_distrib]
          have hq := hcos q
          refine mem_filter.mpr ⟨mem_univ i,?_⟩
          have horder : rowOrder (restrictIncidence Q.original K) i = rowWeight (Q.original i) K := by
            simp [rowOrder, restrictIncidence, rowWeight]
          rw [horder]
          omega
        have hP : properRows (restrictIncidence Q.original K) = properRows A :=
          subset_antisymm hsubK hPsub
        have htau : tauD (restrictIncidence Q.original K) = tauD A := congrArg Finset.card hP
        obtain ⟨_hP,_hG,_hres,hnu,_hle,hlow⟩ := native_data hi K htau
        exact ⟨htau,le_antisymm hnu (hlow hcos)⟩
      · rintro ⟨htau,hnu⟩
        obtain ⟨_hP,_hG,_hres,_hbound,hle,_hlow⟩ := native_data hi K htau
        intro i
        have hiLe := hle i
        rwa [hnu] at hiLe
    refine ⟨hiff,fun hfail => ?_⟩
    by_cases htau : tauD (restrictIncidence Q.original K) = tauD A
    · obtain ⟨_hP,_hG,_hres,hbound,_hle,_hlow⟩ := native_data hi K htau
      have hne : nuOne (restrictIncidence Q.original K) ≠ nuOne A := by
        intro heq
        exact hfail (hiff.mpr ⟨htau,heq⟩)
      right
      refine ⟨htau,?_⟩
      change nuOne (restrictIncidence Q.original K) < nuOne A
      omega
    · left
      change tauD (restrictIncidence Q.original K) < tauD A
      omega

end
end Hironaka.HironakaG4MonomialFiniteTopPhase
