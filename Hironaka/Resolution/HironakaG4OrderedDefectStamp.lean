import Hironaka.Resolution.HironakaG4RetainedDefectCompactRank
import Hironaka.Resolution.HironakaG4OrderedRowCode
import Mathlib.Data.Fintype.Pi

/-! Deterministic comparisons of tied retained defect profiles. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4OrderedDefectStamp

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings HironakaActualRetainedBoundaryJointStep
  HironakaActualRetainedBornResidualSeed HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaG4PointwiseJointProfile
  HironakaG4RetainedDefectCompactRank HironakaG4PreparedCentreCoordinates HironakaG4OrderedRowCode

variable {n : ℕ} {X : CMfd.{u} n}

/-- The ordered old row orders and the inactive nonunit old positions. -/
def retainedDefectStamp (N : Set X) (old born : List (Set X)) (x : X) :
    (Fin old.length → ℕ) × Finset (Fin old.length) :=
  let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
  (r, inactiveCanonicalRows N old born r x)

/-- Lexicographic rank of a complete ordered stamp. The old residual
total and inactive count take priority over the ordered row digits. -/
def orderedDefectStampRank {m : ℕ} (r : Fin m → ℕ) (P : Finset (Fin m)) :
    (ℕ ×ₗ ℕ) ×ₗ ℕ :=
  toLex (toLex (∑ i, r i, P.card), orderedRowTieCode r P)

/-- The refinement determines the whole ordered old-row stamp. -/
theorem orderedDefectStamp_eq_of_rank_eq {m : ℕ}
    {r s : Fin m → ℕ} {P Q : Finset (Fin m)}
    (h : orderedDefectStampRank r P = orderedDefectStampRank s Q) :
    (r, P) = (s, Q) := by
  have hTotal : (∑ i, r i) = ∑ i, s i := congrArg (fun k => (ofLex (ofLex k).1).1) h
  have hCode : orderedRowTieCode r P = orderedRowTieCode s Q := congrArg (fun k => (ofLex k).2) h
  obtain ⟨hr,hP⟩ := orderedRowTieCode_inj hTotal hCode
  exact Prod.ext hr hP

/-- A common trivial row leaves the strict priority of two ordered stamps
unchanged. The two leading coordinates and the order of the other rows
are preserved. -/
theorem orderedDefectStampRank_lt_insert_zero_iff {m : ℕ} (j : Fin (m + 1))
    {r s : Fin m → ℕ} {P Q : Finset (Fin m)} :
    orderedDefectStampRank (j.insertNth 0 r) (P.map j.succAboveEmb) <
      orderedDefectStampRank (j.insertNth 0 s) (Q.map j.succAboveEmb) ↔
    orderedDefectStampRank r P < orderedDefectStampRank s Q := by
  simp only [orderedDefectStampRank, Prod.Lex.toLex_lt_toLex, Fin.sum_insertNth, zero_add,
    Finset.card_map]
  constructor <;> rintro (h | ⟨hPair,hTie⟩)
  · exact Or.inl h
  · have hTotal : (∑ i, r i) = ∑ i, s i := congrArg (fun k => (ofLex k).1) hPair
    exact Or.inr ⟨hPair,(orderedRowTieCode_lt_insert_zero_iff j hTotal).mp hTie⟩
  · exact Or.inl h
  · have hTotal : (∑ i, r i) = ∑ i, s i := congrArg (fun k => (ofLex k).1) hPair
    exact Or.inr ⟨hPair,(orderedRowTieCode_lt_insert_zero_iff j hTotal).mpr hTie⟩

/-- The same insertion leaves weak priority unchanged. -/
theorem orderedDefectStampRank_le_insert_zero_iff {m : ℕ} (j : Fin (m + 1))
    {r s : Fin m → ℕ} {P Q : Finset (Fin m)} :
    orderedDefectStampRank (j.insertNth 0 r) (P.map j.succAboveEmb) ≤
      orderedDefectStampRank (j.insertNth 0 s) (Q.map j.succAboveEmb) ↔
    orderedDefectStampRank r P ≤ orderedDefectStampRank s Q := by
  simpa only [not_lt] using
    not_congr (orderedDefectStampRank_lt_insert_zero_iff j (r := s) (s := r) (P := Q) (Q := P))

/-- Updating the length index by the equality from an ordered boundary
transport leaves the rank of the same row data unchanged. -/
theorem orderedDefectStampRank_eq_of_ordered_cast {m k : ℕ} (h : m = k)
    (r : Fin m → ℕ) (s : Fin k → ℕ) (P : Finset (Fin m)) (Q : Finset (Fin k))
    (hRows : ∀ i, s (finCongr h i) = r i)
    (hMask : Q = P.map (finCongr h).toEmbedding) :
    orderedDefectStampRank s Q = orderedDefectStampRank r P := by
  subst k
  have hr : s = r := funext fun i => hRows i
  have hp : Q = P := by simpa using hMask
  rw [hr, hp]

/-- A strict drop of the original two coordinates gives a strict drop of
the refined rank, regardless of the two stamp codes. -/
theorem orderedDefectStampRank_lt_of_pair_lt {m k : ℕ}
    (r : Fin m → ℕ) (s : Fin k → ℕ) (P : Finset (Fin m)) (Q : Finset (Fin k))
    (h : toLex (∑ i, s i, Q.card) < toLex (∑ i, r i, P.card)) :
    orderedDefectStampRank s Q < orderedDefectStampRank r P :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- Refine the total-order and inactive-count rank by a fixed code
of the actual ordered stamp. The code is only used for ties. -/
def retainedDefectOrderedRank (N : Set X) (old born : List (Set X)) (x : X) :
    (ℕ ×ₗ ℕ) ×ₗ ℕ :=
  let stamp := retainedDefectStamp N old born x
  orderedDefectStampRank stamp.1 stamp.2

/-- Equality of refined ranks determines the entire ordered stamp. -/
theorem retainedDefectStamp_eq_of_orderedRank_eq (N : Set X) (old born : List (Set X))
    {x y : X} (h : retainedDefectOrderedRank N old born x = retainedDefectOrderedRank N old born y) :
    retainedDefectStamp N old born x = retainedDefectStamp N old born y := by
  exact orderedDefectStamp_eq_of_rank_eq h

/-- The tie refinement preserves the local upper bound of the actual defect
rank. When both original rank coordinates are equal, the entire stamp is
equal by componentwise control and inclusion of the inactive set. -/
theorem eventually_retainedDefectOrderedRank_le (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ G ∈ old ++ born, G))
    {x : X} (hx : x ∈ actualFamilyDistinctDefect N (oldResidualPart N old born)) :
    ∀ᶠ y in 𝓝 x, retainedDefectOrderedRank N old born y ≤ retainedDefectOrderedRank N old born x := by
  have hControl := (retained_joint_profile_controls_near_defect hn hN hE hTr hDense hx).2.2
  have hRank := eventually_retainedDefectRank_le hn hN hE hTr hDense hx
  let r (y : X) := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) y
  filter_upwards [hRank, hControl] with y hyRank hyControl
  obtain ⟨hOrd, _, hMask⟩ := hyControl
  apply Prod.Lex.toLex_le_toLex.mpr
  rcases hyRank.eq_or_lt with hEq | hLt
  · have hRankEq := congrArg ofLex hEq
    have hSum : ∑ i, r y i = ∑ i, r x i := congrArg Prod.fst hRankEq
    have hRows : r y = r x := funext fun i =>
      (Finset.sum_eq_sum_iff_of_le (fun i _ => hOrd i)).mp hSum i (Finset.mem_univ i)
    have hCard : (inactiveCanonicalRows N old born (r y) y).card =
        (inactiveCanonicalRows N old born (r x) x).card := congrArg Prod.snd hRankEq
    rw [hRows] at hCard
    have hMasks : inactiveCanonicalRows N old born (r x) y =
        inactiveCanonicalRows N old born (r x) x :=
      Finset.eq_of_subset_of_card_le hMask hCard.ge
    have hStamp : retainedDefectStamp N old born y = retainedDefectStamp N old born x := by
      change (r y, inactiveCanonicalRows N old born (r y) y) =
        (r x, inactiveCanonicalRows N old born (r x) x)
      rw [hRows, hMasks]
    exact Or.inr ⟨hEq, (congrArg (fun s => orderedRowTieCode s.1 s.2) hStamp).le⟩
  · exact Or.inl hLt

/-- The refined rank has an actual maximizer near any compact enclosure of
part of the closed defect. The first two coordinates keep their priority. -/
theorem exists_ordered_retained_defect_rank_max_near_compact (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ G ∈ old ++ born, G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (hNonempty : (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty) :
    ∃ x ∈ K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born),
      ∃ U : Opens X, K ⊆ U ∧
        ∀ y ∈ U, y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
          retainedDefectOrderedRank N old born y ≤ retainedDefectOrderedRank N old born x :=
  exists_rank_max_near_compact (retainedDefectOrderedRank N old born) hK hClosed hNonempty
    (fun _ hx => eventually_retainedDefectOrderedRank_le hn hN hE hTr hDense hx)

/-- A bound on the refined rank is a bound on the total-order and
inactive-count rank used by the closed crest construction. -/
theorem retainedDefectRank_le_of_orderedRank_le (N : Set X) (old born : List (Set X))
    {x y : X} (h : retainedDefectOrderedRank N old born y ≤ retainedDefectOrderedRank N old born x) :
    retainedDefectRank N old born y ≤ retainedDefectRank N old born x := by
  rcases Prod.Lex.toLex_le_toLex.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

/-- The refined numerical maximum identifies exactly the same defect stamp
independently of how a maximizing point is chosen. -/
theorem retainedDefectOrderedRank_eq_iff_stamp_eq (N : Set X) (old born : List (Set X))
    {x y : X} :
    retainedDefectOrderedRank N old born x = retainedDefectOrderedRank N old born y ↔
      retainedDefectStamp N old born x = retainedDefectStamp N old born y := by
  refine ⟨retainedDefectStamp_eq_of_orderedRank_eq N old born, ?_⟩
  intro h
  exact congrArg (fun s : (Fin old.length → ℕ) × Finset (Fin old.length) =>
    orderedDefectStampRank s.1 s.2) h

/-- Select the actual whole maximal stamp near a compact enclosure. Every
point of its selected closed crest has exactly the same refined rank, and
no other defect of the same rank is left outside that crest. -/
theorem exists_ordered_retained_defect_crest_near_compact (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ G ∈ old ++ born, G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (hNonempty : (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty) :
    ∃ x ∈ K, ∃ U V : Opens X, K ⊆ U ∧ V ≤ U ∧
      let r := (retainedDefectStamp N old born x).1
      let P := (retainedDefectStamp N old born x).2
      let C := retainedDefectCrest N old born r P
      1 ≤ ∑ i,r i ∧ IsClosed C ∧ x ∈ C ∧ C ∩ (U : Set X) ⊆ V ∧
      (∀ y ∈ U, y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) →
        retainedDefectOrderedRank N old born y ≤ retainedDefectOrderedRank N old born x) ∧
      (∀ y ∈ V, (∀ i, ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ r i) ∧
        actualDistinctProperCount (oldResidualPart N old born) y < ∑ i,r i ∧
        inactiveCanonicalRows N old born r y ⊆ P) ∧
      ∀ y ∈ U, y ∈ C ↔ y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
        retainedDefectOrderedRank N old born y = retainedDefectOrderedRank N old born x := by
  obtain ⟨x, hx, U, hKU, hMax⟩ :=
    exists_ordered_retained_defect_rank_max_near_compact hn hN hE hTr hDense hK hClosed hNonempty
  have hPair := fun y hy hyD => retainedDefectRank_le_of_orderedRank_le N old born (hMax y hy hyD)
  obtain ⟨V, hVU, hq, hC, hxC, hIn, _, hControls, hExact⟩ :=
    exists_retained_defect_crest_of_rank_bound hn hN hE hTr hDense hClosed U hx.2 hPair
  refine ⟨x, hx.1, U, V, hKU, hVU, hq, hC, hxC, hIn, hMax, hControls, fun y hy => ?_⟩
  change y ∈ retainedDefectCrest N old born
    (fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x)
    (inactiveCanonicalRows N old born (fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x) x) ↔ _
  rw [hExact y hy, retainedDefectOrderedRank_eq_iff_stamp_eq]
  refine ⟨fun ⟨hyD, hRows, hMask⟩ => ⟨hyD, ?_⟩, fun ⟨hyD, hStamp⟩ => ⟨hyD, ?_⟩⟩
  · have he : (fun i => ordinaryTraceOrder N (oldResidualPart N old born i) y) =
        fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x := funext hRows
    unfold retainedDefectStamp
    dsimp only
    rw [he, hMask]
  · have he := congrArg Prod.fst hStamp
    have hm := congrArg Prod.snd hStamp
    change inactiveCanonicalRows N old born
      (fun i => ordinaryTraceOrder N (oldResidualPart N old born i) y) y =
      inactiveCanonicalRows N old born (fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x) x at hm
    rw [show (fun i => ordinaryTraceOrder N (oldResidualPart N old born i) y) =
      (fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x) from he] at hm
    exact ⟨fun i => congrFun he i, hm⟩

end
end Hironaka.HironakaG4OrderedDefectStamp
