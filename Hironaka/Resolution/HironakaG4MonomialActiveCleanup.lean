import Hironaka.Resolution.HironakaG4MonomialStrategyReification

/-!
# Internally constructed cleanup with actual recomputed active row masks

BM97 Lemma12.8, arithmetic over-centre scope only. The output is a finite
complete forest in the existing mark-free trace alphabet. No future history,
phase exit, selector, or residual-minimum premise is supplied.
Blueprint: `hironaka-g4-monomial-active-cleanup.tex`.
-/
set_option autoImplicit false
open Finset

namespace Hironaka.HironakaG4MonomialActiveCleanup

open HironakaG4MonomialFamilyInvariant HironakaG4MonomialMaximalContact
open HironakaG4MonomialCoefficientDeletion HironakaG4MonomialInternalSelector
open HironakaG4MonomialFiniteTopPhase HironakaG4MonomialTopStratum

noncomputable section

/-- Actual length in the existing mark-free trace alphabet. -/
def traceLength : {b : ℕ} → MonomialTrace b → ℕ
  | _,.stop _ => 0
  | _,.over _ _ _ _ _ T => traceLength T+1
  | _,.off T => traceLength T+1

private def emptyHistory : {b : ℕ} → (T : MonomialTrace b) →
    (F : Empty → Fin b → ℕ) → MonomialChartHistory 1 F
  | _,.stop _,F => .stop F
  | _,.over S p R hp hpR T,F =>
      .over S p R hp hpR (fun i => Empty.elim i)
        (emptyHistory T (transformFamily 1 S R F))
  | _,.off T,F => .off (emptyHistory T (appendAbsentFamily F))

/-- The actual original component of the existing native reader, using the
empty-row embedding of the SAME trace. This asserts no original feasibility. -/
def readOriginalTracePrefix {r b : ℕ} (T : MonomialTrace b)
    (A : Fin r → Fin b → ℕ) (k : ℕ) : Σ c : ℕ, Fin r → Fin c → ℕ :=
  let Q := readPhasePrefix (emptyHistory T (fun i => Empty.elim i)) A (fun _ => 0) k
  ⟨Q.slots,Q.original⟩

private theorem pivot_not_retained {b : ℕ} {J R : Finset (Fin b)} {p : Fin b}
    (hR : R ⊆ J.erase p) : p ∉ R := by
  intro hp
  exact (ne_of_mem_erase (hR hp)) rfl

/-- Finite union of the same over constructor over ALL allowed pivot/R pairs. -/
def prependActiveForest {b : ℕ} (J S : Finset (Fin b))
    (forests : (p : S) → (R : (J.erase p.val).powerset) →
      Finset (MonomialTrace (b+1))) : Finset (MonomialTrace b) := by
  classical
  exact S.attach.biUnion fun p => (J.erase p.val).powerset.attach.biUnion fun R =>
    (forests p R).image fun T => .over S p.val R.val p.property
      (pivot_not_retained (Finset.mem_powerset.mp R.property)) T

/-- Actual current proper-row feasibility and full over-centre chart coverage,
ending only when the actual current proper-row count is zero. -/
inductive CompleteActiveTraceForest {r : ℕ} :
    {b : ℕ} → (Fin r → Fin b → ℕ) → Finset (Fin b) →
      Finset (MonomialTrace b) → Prop
  | done {b : ℕ} {A : Fin r → Fin b → ℕ} {J : Finset (Fin b)}
      (hzero : tauD A=0) : CompleteActiveTraceForest A J {.stop b}
  | step {b : ℕ} {A : Fin r → Fin b → ℕ} {J : Finset (Fin b)}
      (S : Finset (Fin b)) (hSJ : S ⊆ J) (hne : S.Nonempty)
      (hf : ∀ i ∈ properRows A, 1 ≤ rowWeight (A i) S)
      (forests : (p : S) → (R : (J.erase p.val).powerset) →
        Finset (MonomialTrace (b+1)))
      (children : ∀ p R, CompleteActiveTraceForest (transformFamily 1 S R.val A)
        (insert (Fin.last b) (R.val.image Fin.castSucc)) (forests p R)) :
      CompleteActiveTraceForest A J (prependActiveForest J S forests)

private theorem zero_of_not_proper {r b : ℕ} (A : Fin r → Fin b → ℕ)
    {i : Fin r} (hi : i ∉ properRows A) : ∀ j, A i j=0 := by
  have hn : ¬0<rowOrder A i := by simpa [properRows] using hi
  have ho : rowOrder A i=0 := by omega
  intro j
  have hle := Finset.single_le_sum (fun k (_hk : k ∈ (univ : Finset (Fin b))) =>
    Nat.zero_le (A i k)) (mem_univ j)
  change A i j ≤ rowOrder A i at hle
  omega

/-- Genuine current proper->mark1 and unit->mark0 agree with native all-slot
mark-one arithmetic. This is not geometric admissibility of a unit ideal. -/
theorem current_mark_mask_transform_eq_native {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (S R : Finset (Fin b)) :
    transformMarkedRows (fun i => if i ∈ properRows A then 1 else 0) S R A =
      transformFamily 1 S R A := by
  classical
  funext i j
  by_cases hi : i ∈ properRows A
  · simp [transformMarkedRows,transformFamily,hi]
  · have hz := zero_of_not_proper A hi
    refine Fin.lastCases ?_ (fun k => ?_) j <;>
      simp [transformMarkedRows,transformFamily,transformRow,hi,rowWeight,hz]

private def Supported {ι : Type} {b : ℕ} (A : ι → Fin b → ℕ)
    (J : Finset (Fin b)) : Prop := ∀ i j, j ∉ J → A i j=0

private theorem weight_supported {ι : Type} {b : ℕ} {A : ι → Fin b → ℕ}
    {J : Finset (Fin b)} (hs : Supported A J) (i : ι) :
    rowWeight (A i) J=rowOrder A i := by
  apply Finset.sum_subset (Finset.subset_univ J)
  intro j _ hj
  exact hs i j hj

private theorem transform_supported {ι : Type} {b : ℕ}
    (A : ι → Fin b → ℕ) (S R : Finset (Fin b)) :
    Supported (transformFamily 1 S R A)
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

private def Tracked {r b : ℕ} (P : Finset (Fin r))
    (A : Fin r → Fin b → ℕ) (F : P → Fin b → ℕ) : Prop :=
  (∀ i, i ∉ P → ∀ j, A i j=0) ∧ ∀ i : P, ∀ j, A i.val j=F i j

private theorem tracked_proper_subset {r b : ℕ} {P : Finset (Fin r)}
    {A : Fin r → Fin b → ℕ} {F : P → Fin b → ℕ} (ht : Tracked P A F) :
    properRows A ⊆ P := by
  intro i hi
  by_contra hip
  have hz : rowOrder A i=0 := by simp [rowOrder,ht.1 i hip]
  have hp := (Finset.mem_filter.mp hi).2
  omega

private theorem tracked_over {r b : ℕ} {P : Finset (Fin r)}
    {A : Fin r → Fin b → ℕ} {F : P → Fin b → ℕ}
    (ht : Tracked P A F) (S R : Finset (Fin b)) :
    Tracked P (transformFamily 1 S R A) (transformMarkedRows (fun _ => 1) S R F) := by
  constructor
  · intro i hip j
    refine Fin.lastCases ?_ (fun k => ?_) j <;>
      simp [transformFamily,transformRow,rowWeight,ht.1 i hip]
  · intro i j
    refine Fin.lastCases ?_ (fun k => ?_) j <;>
      simp [transformFamily,transformMarkedRows,transformRow,rowWeight,ht.2 i]

private def CleanupExists {r b : ℕ} (A : Fin r → Fin b → ℕ)
    (J : Finset (Fin b)) : Prop :=
  ∃ H : Finset (MonomialTrace b), H.Nonempty ∧ CompleteActiveTraceForest A J H

private theorem lift_strategy {r q : ℕ} (P : Finset (Fin r)) (hcard : P.card=q)
    (recurse : ∀ {b : ℕ} (A : Fin r → Fin b → ℕ) (J : Finset (Fin b)),
      Supported A J → tauD A<q → CleanupExists A J) :
    ∀ {b : ℕ} (F : P → Fin b → ℕ) (J : Finset (Fin b)),
      FiniteStrategy (fun _ => 1) F J →
      ∀ A : Fin r → Fin b → ℕ, Tracked P A F → Supported A J → CleanupExists A J := by
  classical
  intro b F J T
  induction T with
  | @done b F J i failure =>
    intro A ht hs
    have hsub := tracked_proper_subset ht
    have hsmall : rowOrder A i.val<1 := by
      rw [← weight_supported hs i.val]
      simpa only [rowWeight,ht.2 i] using failure
    have hnot : i.val ∉ properRows A := by
      intro hp
      have hpos := (Finset.mem_filter.mp hp).2
      omega
    have hstrict : properRows A ⊂ P := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub,?_⟩
      intro heq
      exact hnot (heq.symm ▸ i.property)
    apply recurse A J hs
    simpa only [tauD,hcard] using Finset.card_lt_card hstrict
  | @step b F J S hSJ hne hf children ih =>
    intro A ht _hs
    have hchild (p : S) (R : (J.erase p.val).powerset) :
        CleanupExists (transformFamily 1 S R.val A)
          (insert (Fin.last b) (R.val.image Fin.castSucc)) :=
      ih p.val p.property R.val (Finset.mem_powerset.mp R.property)
        (transformFamily 1 S R.val A) (tracked_over ht S R.val)
        (transform_supported A S R.val)
    let forests := fun (p : S) (R : (J.erase p.val).powerset) => Classical.choose (hchild p R)
    have spec (p : S) (R : (J.erase p.val).powerset) :
        (forests p R).Nonempty ∧ CompleteActiveTraceForest (transformFamily 1 S R.val A)
          (insert (Fin.last b) (R.val.image Fin.castSucc)) (forests p R) :=
      Classical.choose_spec (hchild p R)
    refine ⟨prependActiveForest J S forests,?_,?_⟩
    · obtain ⟨p,hp⟩ := hne
      let pS : S := ⟨p,hp⟩
      let R0 : (J.erase pS.val).powerset := ⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
      obtain ⟨T,hT⟩ := (spec pS R0).1
      refine ⟨.over S pS.val R0.val pS.property
        (pivot_not_retained (Finset.mem_powerset.mp R0.property)) T,?_⟩
      unfold prependActiveForest
      apply Finset.mem_biUnion.mpr
      refine ⟨pS,by simp,?_⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨R0,by simp,Finset.mem_image.mpr ⟨T,hT,rfl⟩⟩
    · apply CompleteActiveTraceForest.step S hSJ hne
      · intro i hi
        have hip : i ∈ P := tracked_proper_subset ht hi
        simpa only [rowWeight,← ht.2 ⟨i,hip⟩] using hf ⟨i,hip⟩
      · exact fun p R => (spec p R).2

private theorem cleanup_by_tau (q : ℕ) :
    ∀ {r b : ℕ} (A : Fin r → Fin b → ℕ) (J : Finset (Fin b)),
      tauD A=q → Supported A J → CleanupExists A J := by
  classical
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro r b A J hq hs
    by_cases hz : q=0
    · exact ⟨{.stop b},by simp,CompleteActiveTraceForest.done (hq.trans hz)⟩
    · let P := properRows A
      have hP : P.Nonempty := by
        by_contra he
        have heq : tauD A=0 := by simp [tauD,P,Finset.not_nonempty_iff_eq_empty.mp he]
        omega
      obtain ⟨i,hi⟩ := hP
      have : Nonempty P := ⟨⟨i,hi⟩⟩
      let F : P → Fin b → ℕ := fun i => A i.val
      have hF : Supported F J := by intro i j hj; exact hs i.val j hj
      have hstrategy := exists_finite_marked_monomial_strategy F (fun _ => 1)
        (fun _ => Nat.zero_lt_one) J hF
      apply lift_strategy P (show P.card=q from hq)
        (fun {c} B K hB hlt => ih (tauD B) hlt B K rfl hB) F J hstrategy A
      · exact ⟨fun i hip => zero_of_not_proper A hip,fun _ _ => rfl⟩
      · exact hs

private def directOriginalPrefix {r : ℕ} :
    {b : ℕ} → MonomialTrace b → (Fin r → Fin b → ℕ) → ℕ →
      Σ c : ℕ, Fin r → Fin c → ℕ
  | b,_,A,0 => ⟨b,A⟩
  | b,.stop _,A,_+1 => ⟨b,A⟩
  | _,.over S _ R _ _ T,A,k+1 => directOriginalPrefix T (transformFamily 1 S R A) k
  | _,.off T,A,k+1 => directOriginalPrefix T (appendAbsentFamily A) k

private theorem native_reader_eq {r : ℕ} :
    ∀ {b : ℕ} (T : MonomialTrace b) (F : Empty → Fin b → ℕ)
      (A : Fin r → Fin b → ℕ) (c : Fin b → ℕ) (k : ℕ),
      let Q := readPhasePrefix (emptyHistory T F) A c k;
      (⟨Q.slots,Q.original⟩ : Σ c : ℕ, Fin r → Fin c → ℕ)=directOriginalPrefix T A k := by
  intro b T
  induction T with
  | stop b => intro F A c k; cases k <;> rfl
  | over S p R hp hpR T ih =>
    intro F A c k
    cases k with
    | zero => rfl
    | succ k =>
      dsimp only [emptyHistory,readPhasePrefix,directOriginalPrefix]
      exact ih _ _ _ k
  | off T ih =>
    intro F A c k
    cases k with
    | zero => rfl
    | succ k =>
      dsimp only [emptyHistory,readPhasePrefix,directOriginalPrefix]
      exact ih _ _ _ k

private theorem forest_terminal_zero {r b : ℕ} {A : Fin r → Fin b → ℕ}
    {J : Finset (Fin b)} {H : Finset (MonomialTrace b)}
    (h : CompleteActiveTraceForest A J H) :
    ∀ T ∈ H, tauD (directOriginalPrefix T A (traceLength T)).2=0 := by
  classical
  induction h with
  | @done b A J hzero =>
    intro T hT
    have heq : T=.stop b := Finset.mem_singleton.mp hT
    subst T
    exact hzero
  | @step b A J S hSJ hne hf forests children ih =>
    intro T hT
    unfold prependActiveForest at hT
    obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hT
    obtain ⟨R,_,hR⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨U,hU,heq⟩ := Finset.mem_image.mp hR
    subst T
    exact ih p R U hU

private theorem restricted_tau_zero {r b : ℕ} (A : Fin r → Fin b → ℕ)
    (hz : tauD A=0) (K : Finset (Fin b)) : tauD (restrictIncidence A K)=0 := by
  have hsub : properRows (restrictIncidence A K) ⊆ properRows A := by
    intro i hi
    have hp := (Finset.mem_filter.mp hi).2
    have heq : rowOrder (restrictIncidence A K) i=rowWeight (A i) K := by
      simp [rowOrder,restrictIncidence,rowWeight]
    rw [heq] at hp
    have hle : rowWeight (A i) K ≤ rowOrder A i :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ K)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,lt_of_lt_of_le hp hle⟩
  have hle := Finset.card_le_card hsub
  change tauD (restrictIncidence A K) ≤ tauD A at hle
  omega

/-- ONLY the actual original matrix internally produces a NONEMPTY COMPLETE
finite existing-trace forest, with actual current proper-row feasibility and
native tauD=0 on EVERY terminal incidence subset. -/
theorem exists_original_complete_active_cleanup_forest {r b : ℕ}
    (A : Fin r → Fin b → ℕ) :
    ∃ H : Finset (MonomialTrace b), H.Nonempty ∧
      CompleteActiveTraceForest A Finset.univ H ∧
      ∀ T ∈ H, let Q := readOriginalTracePrefix T A (traceLength T);
        ∀ K : Finset (Fin Q.1), tauD (restrictIncidence Q.2 K)=0 := by
  obtain ⟨H,hne,hcover⟩ := cleanup_by_tau (tauD A) A Finset.univ rfl
    (by intro i j hj; exact False.elim (hj (Finset.mem_univ j)))
  refine ⟨H,hne,hcover,?_⟩
  intro T hT
  dsimp only
  unfold readOriginalTracePrefix
  rw [native_reader_eq]
  intro K
  exact restricted_tau_zero _ (forest_terminal_zero hcover T hT) K

end
end Hironaka.HironakaG4MonomialActiveCleanup
