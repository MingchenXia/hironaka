import Hironaka.Invariant.NonmonomialOrderGlobalPhase
import Hironaka.Invariant.ResolutionInvariantSeq

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The phases of the general value in the count of centres; the monomial phase is finite along growing sequences

Hironaka phase H2 (TN3), for the per-sequence local finiteness (8') of the general step's value (human decision I-1139 (b));
claim I-0977 C-0215.  Blueprint `bcalc:general-phase-count` (chapter `blowup-calculus.tex`).  Sources: Włodarczyk 2005
(`wlodarczyk05-hironaka`), Step 2 of Proposition `pr:resol`; Bierstone--Milman 2008 (`bierstone-milman08-functoriality`),
Step II.

Along a canonical segment `T` of TN-CLASSICAL's general value `genInv M 𝔪`, `StepOnePhase.centreValues (genInv M 𝔪) T` lists the
values of the nonempty centres; their first entries are the orders `ν` of the nonmonomial part (the phases).  This module splits
the count of (8') by phases and settles the phase of order `0`:

* **`countCentresMeeting_le_length_filter`**, `countCentresMeeting_le_sum_phases`: if every point of every nonempty canonical
  centre meeting the preimage of `K` has order `≤ q` (`NonmonomialOrderGlobalPhase.exists_centre_nmOrd_le_of_isCompact` gives such
  a `q` for compact `K`), the centres meeting `K` are at most the entries of order `≤ q`, i.e. the sum over the phases
  `o = 0, …, q` of the numbers of entries of order `o`;
* `exists_bound_of_isPrefix`: prefix-growing lists, each strictly decreasing, with entries in a set on which no sequence strictly
  decreases forever, have bounded lengths;
* **`exists_bound_phase_zero`**: along every growing sequence of canonical segments of `genInv M 𝔪`
  (`ResolutionInvariantSeq.GrowingSeq`) the numbers of entries of order `0` are bounded -- the monomial phase is finite (its
  values `(0, inl γ)` strictly decrease and `γ`'s values are well-founded);
* **`exists_bound_of_phases`**: so (8') along such a sequence follows from bounds for the phases `o = 1, …, q`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralPhaseCount

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MonomialInvariant Hironaka.BlowupTowers
  Hironaka.BlowupTowerTransforms Hironaka.StepOnePhase
  Hironaka.NonmonomialOrderLocal Hironaka.MaxOrderValue
  Hironaka.GeneralValue
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
open Hironaka.ResolutionInvariantSeq (GrowingSeq)

noncomputable section

variable {n : ℕ}

/-! ### Bounded lengths of prefix-growing strictly decreasing lists -/

section Lists

variable {β : Type*} [Preorder β]

/-- **Prefix-growing strictly decreasing lists with entries in a set on which no sequence decreases strictly forever have bounded
lengths** (otherwise the entries at the positions `0, 1, 2, …` of long enough lists form such a sequence). -/
theorem exists_bound_of_isPrefix (F : ℕ → List β) (hmono : ∀ i, F i <+: F (i + 1))
    (hpw : ∀ i, (F i).Pairwise (fun a b => b < a)) (P : β → Prop) (hP : ∀ i, ∀ b ∈ F i, P b)
    (hwf : ∀ g : ℕ → β, (∀ k, P (g k)) → ¬ StrictAnti g) : ∃ m : ℕ, ∀ i, (F i).length ≤ m := by
  classical
  by_contra hcon
  simp only [not_exists, not_forall, not_le] at hcon
  have hpre : ∀ i j, i ≤ j → F i <+: F j := by
    intro i j hij
    induction hij with
    | refl => exact List.prefix_refl _
    | step _ ih => exact ih.trans (hmono _)
  let idx : ℕ → ℕ := fun k => Nat.find (hcon k)
  have hidx : ∀ k, k < (F (idx k)).length := fun k => Nat.find_spec (hcon k)
  let g : ℕ → β := fun k => (F (idx k))[k]'(hidx k)
  refine hwf g (fun k => hP _ _ (List.getElem_mem _)) fun k k' hkk' => ?_
  have hj1 : idx k ≤ max (idx k) (idx k') := le_max_left _ _
  have hj2 : idx k' ≤ max (idx k) (idx k') := le_max_right _ _
  have e1 : g k = (F (max (idx k) (idx k')))[k]'(Nat.lt_of_lt_of_le (hidx k) (hpre _ _ hj1).length_le) :=
    (hpre _ _ hj1).getElem (hidx k)
  have e2 : g k' = (F (max (idx k) (idx k')))[k']'(Nat.lt_of_lt_of_le (hidx k') (hpre _ _ hj2).length_le) :=
    (hpre _ _ hj2).getElem (hidx k')
  rw [e1, e2]
  exact List.pairwise_iff_getElem.mp (hpw _) k k' _ _ hkk'

end Lists

/-! ### The count of centres meeting `K`, by phases -/

section Count

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ} {𝔪 : MarkedIdeal n X}

/-- **The centres meeting `K` are counted in the phases `≤ q`**: along a canonical segment of the general value (`M` a value
function for the marked ideals of maximal order, `𝔪` in the domain, `n > 0`), if every point of every nonempty canonical centre
meeting the preimage of `K` has order `≤ q`, the number of centres meeting `K` is at most the number of entries of
`centreValues (genInv M 𝔪) T` with first entry `≤ q`. -/
theorem countCentresMeeting_le_length_filter (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) {K : Set X}
    {q : ℕ} (hq : ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower 𝔪 (.step T C π hπ) → IsCanonical 𝔪 (genInv M 𝔪) (.step T C π hπ) →
        (C ∩ T.proj ⁻¹' K).Nonempty → ∀ c ∈ C, nmOrd (geoTransformAlong 𝔪 T) c ≤ q) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (genInv M 𝔪) T →
      countCentresMeeting K T ≤ ((centreValues (genInv M 𝔪) T).filter fun v => (ofLex v).1 ≤ q).length
  | _, .refl, _ => Nat.zero_le _
  | _, .step T C π hπ, hcan => by
      classical
      have hcanT : IsCanonical 𝔪 (genInv M 𝔪) T := hcan.1
      have hT : IsGeoTestTower 𝔪 (.step T C π hπ) :=
        GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h _ hcan
      have ih := countCentresMeeting_le_length_filter hM hn h hq T hcanT
      show countCentresMeeting K T + (if (C ∩ T.proj ⁻¹' K).Nonempty then 1 else 0) ≤ _
      by_cases hne : C.Nonempty
      · rw [centreValues_step_of_nonempty _ T C π hπ hne, List.filter_append, List.length_append]
        by_cases hK : (C ∩ T.proj ⁻¹' K).Nonempty
        · have hle : (ofLex (genInv M 𝔪 T hne.some)).1 ≤ q := hq T C π hπ hT hcan hK _ hne.some_mem
          rw [if_pos hK, List.filter_singleton, decide_eq_true hle]
          simp only [cond_true, List.length_singleton]
          omega
        · rw [if_neg hK]
          omega
      · have hK : ¬ (C ∩ T.proj ⁻¹' K).Nonempty := fun hK => hne (hK.mono inter_subset_left)
        rw [centreValues_step_of_eq_empty _ T C π hπ (not_nonempty_iff_eq_empty.mp hne), if_neg hK]
        omega

/-- **The entries of order `≤ q` are the sum of the phases `o = 0, …, q`.** -/
theorem length_filter_le_eq_sum (l : List (ℕ ×ₗ (WithBot Val ⊕ₗ WithTop Λ))) (q : ℕ) :
    (l.filter fun v => (ofLex v).1 ≤ q).length =
      ∑ o ∈ Finset.range (q + 1), (l.filter fun v => (ofLex v).1 = o).length := by
  rw [length_eq_sum_filter_fst (fun v : ℕ ×ₗ (WithBot Val ⊕ₗ WithTop Λ) => (ofLex v).1) (q + 1) _
    (fun a ha => Nat.lt_succ_of_le (by simpa using (List.mem_filter.mp ha).2))]
  refine Finset.sum_congr rfl fun o ho => ?_
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro v _
  have hoq : o ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp ho)
  by_cases hv : (ofLex v).1 = o
  · simp [hv, hoq]
  · simp [hv]

/-- **The count of (8') by phases**: under the hypothesis of `countCentresMeeting_le_length_filter`, the number of centres
meeting `K` is at most the sum over the phases `o = 0, …, q` of the numbers of entries of order `o`. -/
theorem countCentresMeeting_le_sum_phases (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) {K : Set X}
    {q : ℕ} (hq : ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower 𝔪 (.step T C π hπ) → IsCanonical 𝔪 (genInv M 𝔪) (.step T C π hπ) →
        (C ∩ T.proj ⁻¹' K).Nonempty → ∀ c ∈ C, nmOrd (geoTransformAlong 𝔪 T) c ≤ q)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔪 (genInv M 𝔪) T) :
    countCentresMeeting K T ≤
      ∑ o ∈ Finset.range (q + 1), ((centreValues (genInv M 𝔪) T).filter fun v => (ofLex v).1 = o).length := by
  rw [← length_filter_le_eq_sum]
  exact countCentresMeeting_le_length_filter hM hn h hq T hcan

end Count

/-! ### Along growing sequences -/

section Seq

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ} {𝔪 : MarkedIdeal n X}

/-- Along a growing sequence the lists of centre values grow by prefixes. -/
theorem centreValues_isPrefix_succ {Λ' : Type v} [LinearOrder Λ'] (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ') (s : GrowingSeq X)
    (i : ℕ) : centreValues inv (s.stage i).2 <+: centreValues inv (s.stage (i + 1)).2 := by
  obtain ⟨C, π, hπ, heq⟩ := s.succ i
  rw [heq]
  by_cases hne : C.Nonempty
  · rw [centreValues_step_of_nonempty _ _ C π hπ hne]
    exact List.prefix_append _ _
  · rw [centreValues_step_of_eq_empty _ _ C π hπ (not_nonempty_iff_eq_empty.mp hne)]

/-- **The monomial phase is finite along every growing sequence**: along a growing sequence of canonical segments of the general
value (`M` a value function for the marked ideals of maximal order, `𝔪` in the domain, `n > 0`), the numbers of nonempty centres
of order `0` (entries of `centreValues (genInv M 𝔪)` with first entry `0`) are bounded.  Their values `(0, inl γ)` strictly
decrease along the prefix-growing lists (`StepOnePhase.pairwise_centreValues` with `GeneralAdmissible.stepDrop_genInv`), and no
sequence of such values decreases strictly forever (`NonmonomialOrderGlobalPhase.not_strictAnti_zero_inl`). -/
theorem exists_bound_phase_zero (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) (s : GrowingSeq X)
    (hs : ∀ i, IsCanonical 𝔪 (genInv M 𝔪) (s.stage i).2) :
    ∃ m : ℕ, ∀ i, ((centreValues (genInv M 𝔪) (s.stage i).2).filter fun v => (ofLex v).1 = 0).length ≤ m := by
  classical
  refine exists_bound_of_isPrefix (fun i => (centreValues (genInv M 𝔪) (s.stage i).2).filter fun v => (ofLex v).1 = 0)
    (fun i => (centreValues_isPrefix_succ _ s i).filter _)
    (fun i => (pairwise_centreValues (GeneralAdmissible.stepDrop_genInv hM hn h) _ (hs i)).filter _)
    (fun v => ∃ w : WithBot Val, v = toLex ((0 : ℕ), (toLex (Sum.inl w) : WithBot Val ⊕ₗ WithTop Λ))) ?_ ?_
  · intro i v hv
    obtain ⟨hvmem, hv0⟩ := List.mem_filter.mp hv
    obtain ⟨Y', T', x, rfl⟩ := exists_eq_of_mem_centreValues _ _ hvmem
    exact ⟨_, NonmonomialOrderGlobalPhase.genInv_snd_of_fst_eq_zero M 𝔪 T' (by simpa using hv0)⟩
  · intro g hg hanti
    choose w hw using hg
    refine NonmonomialOrderGlobalPhase.not_strictAnti_zero_inl (Λ := Λ) w ?_
    intro a b hab
    have := hanti hab
    rwa [hw a, hw b] at this

/-- **(8') of the general value from its phases of positive order**: along a growing sequence of canonical segments of the general
value, with `q` as in `countCentresMeeting_le_length_filter` for `K`, if for each `o = 1, …, q` the numbers of entries of order
`o` are bounded, then the numbers of centres meeting `K` are bounded. -/
theorem exists_bound_of_phases (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) {K : Set X} {q : ℕ}
    (hq : ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower 𝔪 (.step T C π hπ) → IsCanonical 𝔪 (genInv M 𝔪) (.step T C π hπ) →
        (C ∩ T.proj ⁻¹' K).Nonempty → ∀ c ∈ C, nmOrd (geoTransformAlong 𝔪 T) c ≤ q)
    (s : GrowingSeq X) (hs : ∀ i, IsCanonical 𝔪 (genInv M 𝔪) (s.stage i).2)
    (hpos : ∀ o ∈ Finset.range (q + 1), o ≠ 0 →
      ∃ m : ℕ, ∀ i, ((centreValues (genInv M 𝔪) (s.stage i).2).filter fun v => (ofLex v).1 = o).length ≤ m) :
    ∃ m : ℕ, ∀ i, countCentresMeeting K (s.stage i).2 ≤ m := by
  classical
  have hall : ∀ o ∈ Finset.range (q + 1),
      ∃ m : ℕ, ∀ i, ((centreValues (genInv M 𝔪) (s.stage i).2).filter fun v => (ofLex v).1 = o).length ≤ m := by
    intro o ho
    by_cases ho0 : o = 0
    · subst ho0
      exact exists_bound_phase_zero hM hn h s hs
    · exact hpos o ho ho0
  choose! m hm using hall
  refine ⟨∑ o ∈ Finset.range (q + 1), m o, fun i => ?_⟩
  exact (countCentresMeeting_le_sum_phases hM hn h hq _ (hs i)).trans
    (Finset.sum_le_sum fun o ho => hm o ho i)

end Seq

end

end Hironaka.GeneralPhaseCount
