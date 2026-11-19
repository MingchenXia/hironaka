import Hironaka.Resolution.HironakaG4MonomialInternalSelector

/-!
# Internal strategy reification into fixed-original finite history forests

BM97 Lemma12.8, literal over-centre arithmetic. The forest contains the SAME
existing finite chart histories, with complete all-pivot/retained coverage.
No incoming future history, leaf failure or comparison certificate is supplied.
Blueprint: `hironaka-g4-monomial-strategy-reification.tex`.
-/
set_option autoImplicit false
open Finset

namespace Hironaka.HironakaG4MonomialStrategyReification

open HironakaG4MonomialFamilyInvariant HironakaG4MonomialMaximalContact
open HironakaG4MonomialInternalSelector HironakaG4MonomialFiniteTopPhase
open HironakaG4MonomialTopStratum

noncomputable section

/-- The actual number of recorded operations, including off-centre operations. -/
def historyLength {ι : Type} {m : ℕ} :
    {b : ℕ} → {F : ι → Fin b → ℕ} → MonomialChartHistory m F → ℕ
  | _,_,.stop _ => 0
  | _,_,.over _ _ _ _ _ _ T => historyLength T+1
  | _,_,.off T => historyLength T+1

/-- The actual terminal family already in the existing chronological history. -/
def terminalRows {ι : Type} {m : ℕ} :
    {b : ℕ} → {F : ι → Fin b → ℕ} → MonomialChartHistory m F →
      Σ b : ℕ, ι → Fin b → ℕ
  | b,F,.stop _ => ⟨b,F⟩
  | _,_,.over _ _ _ _ _ _ T => terminalRows T
  | _,_,.off T => terminalRows T

private theorem pivot_not_retained {b : ℕ} {J R : Finset (Fin b)} {p : Fin b}
    (hR : R ⊆ J.erase p) : p ∉ R := by
  intro hp
  exact (ne_of_mem_erase (hR hp)) rfl

/-- Prepend the true SAME over-step to ALL histories in ALL valid child forests. -/
def prependForest {ι : Type} {b m : ℕ} {F : ι → Fin b → ℕ}
    (J S : Finset (Fin b)) (hf : ∀ i, m ≤ rowWeight (F i) S)
    (forests : (p : S) → (R : (J.erase p.val).powerset) →
      Finset (MonomialChartHistory m (transformFamily m S R.val F))) :
    Finset (MonomialChartHistory m F) := by
  classical
  exact S.attach.biUnion fun p => (J.erase p.val).powerset.attach.biUnion fun R =>
    (forests p R).image fun T =>
      .over S p.val R.val p.property
        (pivot_not_retained (Finset.mem_powerset.mp R.property)) hf T

/-- Literal coverage by a finite forest with one current selected centre and
EVERY valid pivot/retained-incidence child. Its leaves have actual row failures. -/
inductive CompleteHistoryForest {ι : Type} (m : ℕ) :
    {b : ℕ} → (F : ι → Fin b → ℕ) → Finset (Fin b) →
      Finset (MonomialChartHistory m F) → Prop
  | done {b : ℕ} {F : ι → Fin b → ℕ} {J : Finset (Fin b)}
      (i : ι) (failure : rowWeight (F i) J<m) :
      CompleteHistoryForest m F J {.stop F}
  | step {b : ℕ} {F : ι → Fin b → ℕ} {J : Finset (Fin b)}
      (S : Finset (Fin b)) (hSJ : S ⊆ J) (hne : S.Nonempty)
      (hf : ∀ i, m ≤ rowWeight (F i) S)
      (forests : (p : S) → (R : (J.erase p.val).powerset) →
        Finset (MonomialChartHistory m (transformFamily m S R.val F)))
      (children : ∀ p R, CompleteHistoryForest m (transformFamily m S R.val F)
        (insert (Fin.last b) (R.val.image Fin.castSucc)) (forests p R)) :
      CompleteHistoryForest m F J (prependForest J S hf forests)

private def Supported {ι : Type} {b : ℕ} (F : ι → Fin b → ℕ)
    (J : Finset (Fin b)) : Prop := ∀ i j, j ∉ J → F i j=0

private def Deficient {ι : Type} (m : ℕ) (E : Σ b : ℕ, ι → Fin b → ℕ) : Prop :=
  ∃ i, rowWeight (E.2 i) Finset.univ<m

private theorem weight_supported {ι : Type} {b : ℕ} {F : ι → Fin b → ℕ}
    {J : Finset (Fin b)} (hs : Supported F J) (i : ι) :
    rowWeight (F i) J=rowWeight (F i) Finset.univ := by
  apply Finset.sum_subset (Finset.subset_univ J)
  intro j _ hj
  exact hs i j hj

private theorem transform_supported {ι : Type} {b m : ℕ}
    (F : ι → Fin b → ℕ) (S R : Finset (Fin b)) :
    Supported (transformFamily m S R F)
      (insert (Fin.last b) (R.image Fin.castSucc)) := by
  intro i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · intro hj
    exact False.elim (hj (Finset.mem_insert_self _ _))
  · intro hj
    have hk : k ∉ R := by
      intro hk
      exact hj (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k,hk,rfl⟩))
    simp [transformFamily,transformRow,hk]

private theorem extract_forest {ι : Type} {m : ℕ} :
    ∀ {b : ℕ} (F : ι → Fin b → ℕ) (J : Finset (Fin b)),
      FiniteStrategy (fun _ => m) F J → Supported F J →
      ∃ H : Finset (MonomialChartHistory m F), H.Nonempty ∧
        CompleteHistoryForest m F J H ∧ ∀ T ∈ H, Deficient m (terminalRows T) := by
  classical
  intro b F J T
  induction T with
  | @done b F J i failure =>
    intro hs
    refine ⟨{.stop F},by simp,CompleteHistoryForest.done i failure,?_⟩
    intro U hU
    have heq : U=.stop F := Finset.mem_singleton.mp hU
    subst U
    refine ⟨i,?_⟩
    change rowWeight (F i) Finset.univ<m
    rw [← weight_supported hs i]
    exact failure
  | @step b F J S hSJ hne hf children ih =>
    intro _hs
    have hchild (p : S) (R : (J.erase p.val).powerset) :
        ∃ H : Finset (MonomialChartHistory m (transformFamily m S R.val F)),
          H.Nonempty ∧ CompleteHistoryForest m (transformFamily m S R.val F)
            (insert (Fin.last b) (R.val.image Fin.castSucc)) H ∧
          ∀ T ∈ H, Deficient m (terminalRows T) :=
      ih p.val p.property R.val (Finset.mem_powerset.mp R.property)
        (transform_supported F S R.val)
    let forests := fun (p : S) (R : (J.erase p.val).powerset) => Classical.choose (hchild p R)
    have spec (p : S) (R : (J.erase p.val).powerset) :
        (forests p R).Nonempty ∧ CompleteHistoryForest m (transformFamily m S R.val F)
          (insert (Fin.last b) (R.val.image Fin.castSucc)) (forests p R) ∧
        ∀ T ∈ forests p R, Deficient m (terminalRows T) := Classical.choose_spec (hchild p R)
    refine ⟨prependForest J S hf forests,?_,
      CompleteHistoryForest.step S hSJ hne hf forests (fun p R => (spec p R).2.1),?_⟩
    · obtain ⟨p,hp⟩ := hne
      let pS : S := ⟨p,hp⟩
      let R0 : (J.erase pS.val).powerset := ⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
      obtain ⟨U,hU⟩ := (spec pS R0).1
      refine ⟨.over S pS.val R0.val pS.property
        (pivot_not_retained (Finset.mem_powerset.mp R0.property)) hf U,?_⟩
      unfold prependForest
      apply Finset.mem_biUnion.mpr
      refine ⟨pS,by simp,?_⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨R0,by simp,Finset.mem_image.mpr ⟨U,hU,rfl⟩⟩
    · intro U hU
      unfold prependForest at hU
      obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hU
      obtain ⟨R,_,hR⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨V,hV,heq⟩ := Finset.mem_image.mp hR
      subst U
      exact (spec p R).2.2 V hV

/-- Public factor of the existing finite-strategy forest extraction. -/
theorem finite_strategy_forest {ι : Type} {m b : ℕ}
    (F : ι → Fin b → ℕ) (J : Finset (Fin b))
    (h : FiniteStrategy (fun _ => m) F J)
    (hs : ∀ i j, j ∉ J → F i j=0) :
    ∃ H : Finset (MonomialChartHistory m F), H.Nonempty ∧
      CompleteHistoryForest m F J H ∧
      ∀ T ∈ H, ∃ i, rowWeight ((terminalRows T).2 i) Finset.univ<m :=
  extract_forest F J h hs

private theorem terminalRows_readPhasePrefix {r : ℕ} {ι : Type} {m : ℕ} :
    ∀ {b : ℕ} {F : ι → Fin b → ℕ} (T : MonomialChartHistory m F)
      (A : Fin r → Fin b → ℕ) (c : Fin b → ℕ),
      let Q := readPhasePrefix T A c (historyLength T);
      (⟨Q.slots,Q.residual⟩ : Σ b : ℕ, ι → Fin b → ℕ)=terminalRows T := by
  intro b F T
  induction T with
  | stop F => intro A c; rfl
  | over S p R hp hpR hf T ih =>
    intro A c
    dsimp only [historyLength,readPhasePrefix,terminalRows]
    exact ih _ _
  | off T ih =>
    intro A c
    dsimp only [historyLength,readPhasePrefix,terminalRows]
    exact ih _ _

/-- ONLY original A and its actual positive nuOne internally produce a
NONEMPTY COMPLETE finite forest of actual fixed-original histories. EVERY
terminal history has true native pair exit at EVERY endpoint incidence set. -/
theorem exists_original_positive_residual_history_forest {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (hL : 0<nuOne A) :
    ∃ H : Finset (MonomialChartHistory (nuOne A) (residualFamily A)), H.Nonempty ∧
      CompleteHistoryForest (nuOne A) (residualFamily A) Finset.univ H ∧
      ∀ T ∈ H, let Q := readPhasePrefix T A (gcdColumn A) (historyLength T);
        ∀ K : Finset (Fin Q.slots),
          tauD (restrictIncidence Q.original K)<tauD A ∨
          tauD (restrictIncidence Q.original K)=tauD A ∧
            nuOne (restrictIncidence Q.original K)<nuOne A := by
  obtain ⟨H,hne,hcover,hdef⟩ := extract_forest (residualFamily A) Finset.univ
    (exists_original_positive_residual_strategy A hL)
    (by intro i j hj; exact False.elim (hj (Finset.mem_univ j)))
  refine ⟨H,hne,hcover,?_⟩
  intro T hT
  let Q := readPhasePrefix T A (gcdColumn A) (historyLength T)
  change ∀ K : Finset (Fin Q.slots),
    tauD (restrictIncidence Q.original K)<tauD A ∨
      tauD (restrictIncidence Q.original K)=tauD A ∧
        nuOne (restrictIncidence Q.original K)<nuOne A
  have hrows := terminalRows_readPhasePrefix T A (gcdColumn A)
  have hsmall : Deficient (nuOne A) (⟨Q.slots,Q.residual⟩ : Σ b : ℕ, properRows A → Fin b → ℕ) := by
    rw [hrows]
    exact hdef T hT
  obtain ⟨i,hi⟩ := hsmall
  change rowWeight (Q.residual i) Finset.univ<nuOne A at hi
  intro K
  have hnot : ¬familyCosupport Q.residual (nuOne A) K := by
    intro hf
    have hb := hf i
    have hle : rowWeight (Q.residual i) K ≤ rowWeight (Q.residual i) Finset.univ :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ K)
    omega
  exact ((actual_finite_top_phase_dictionary A hL T (historyLength T)).2.2 K).2 hnot

end
end Hironaka.HironakaG4MonomialStrategyReification
