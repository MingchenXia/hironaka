import Hironaka.Analytic.GrowingSeqTail
import Hironaka.Resolution.HironakaLocallyFiniteResolutionSequence

set_option autoImplicit false

open Set TopologicalSpace
open scoped BigOperators

universe u v w

namespace Hironaka.HironakaG8FiniteWindowCount

open Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals
open HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq ResolutionInvariantSpec

noncomputable section

variable {n k : ℕ} {X : CMfd.{u} n}

/-- The number of actual nonempty centres in each prefix is bounded when every such
centre meets a compact footprint in one of finitely many literally restricted
canonical histories. The footprints need only meet the centres. -/
theorem exists_bound_of_compact_footprints
    {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {ι : Type w} [Finite ι] (s : GrowingSeq X) (U : ι → Opens X)
    (Q : (i : ι) → MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hQ : ∀ i, IsInvDomain k (Q i)) (K : (i : ι) → Set (U i))
    (hK : ∀ i, IsCompact (K i))
    (hCan : ∀ i j, IsCanonical (Q i) (R.inv (Q i)) (restrict (U i) (s.stage j).2))
    (hHit : ∀ j, (stepCentre s j).Nonempty →
      ∃ i, (centreImage s j ∩ ((Subtype.val : U i → X) '' K i)).Nonempty) :
    ∃ b : ℕ, ∀ j, countCentresMeeting univ (s.stage j).2 ≤ b := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let footprint (i : ι) : Set X := (Subtype.val : U i → X) '' K i
  let covered : Set X := ⋃ i ∈ (Finset.univ : Finset ι), footprint i
  have hLocal : ∀ i, ∃ b : ℕ, ∀ j, countCentresMeeting (footprint i) (s.stage j).2 ≤ b := by
    intro i
    obtain ⟨b, hb⟩ := R.seqLocallyFinite (Q i) (hQ i) (K i) (hK i)
      (s.restrict (U i)) (hCan i)
    have hSub : footprint i ⊆ U i := by
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    refine ⟨b, fun j => ?_⟩
    rw [← s.count_restrict (U i) hSub j]
    simpa only [footprint, Set.preimage_image_eq _ Subtype.val_injective] using hb j
  choose b hb using hLocal
  have hMeet : ∀ j,
      (centreImage s j ∩ (univ : Set X)).Nonempty ↔ (centreImage s j ∩ covered).Nonempty := by
    intro j
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, _⟩
      obtain ⟨i, x, hx, hxK⟩ := hHit j ⟨y, hy⟩
      exact ⟨x, hx, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_univ i, hxK⟩⟩⟩
    · rintro ⟨x, hx, _⟩
      exact ⟨x, hx, mem_univ x⟩
  have hCount : ∀ j,
      countCentresMeeting univ (s.stage j).2 = countCentresMeeting covered (s.stage j).2 := by
    intro j
    induction j with
    | zero => rw [s.zero]; rfl
    | succ j ih => rw [countCentresMeeting_step, countCentresMeeting_step, ih, hMeet j]
  refine ⟨∑ i, b i, fun j => ?_⟩
  rw [hCount j]
  exact (ResolutionInvariantSegments.countCentresMeeting_biUnion_le
    Finset.univ footprint (s.stage j).2).trans (Finset.sum_le_sum fun i _ => hb i j)

/-- A uniform count of actual nonempty centres forces an actual empty next centre
by the given bound. -/
theorem exists_empty_stepCentre_of_bound (s : GrowingSeq X) {b : ℕ}
    (hBound : ∀ j, countCentresMeeting univ (s.stage j).2 ≤ b) :
    ∃ j ≤ b, stepCentre s j = ∅ := by
  classical
  by_contra! h
  have hCount : ∀ j ≤ b + 1, countCentresMeeting univ (s.stage j).2 = j := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [s.zero]
        rfl
    | succ j ih =>
        intro hj
        have hjb : j ≤ b := Nat.le_of_succ_le_succ hj
        obtain ⟨y, hy⟩ := h j hjb
        have hMeet : (centreImage s j ∩ (univ : Set X)).Nonempty :=
          ⟨(s.stage j).2.proj y, ⟨y, hy, rfl⟩, mem_univ _⟩
        rw [countCentresMeeting_step, if_pos hMeet, ih (Nat.le_succ_of_le hjb)]
  have hLast := hBound (b + 1)
  rw [hCount (b + 1) le_rfl] at hLast
  exact Nat.not_succ_le_self b hLast

/-- If each actual nonempty centre before the first empty step hits a compact set,
a finite open cover with literally restricted canonical histories forces an actual
empty step. -/
theorem exists_empty_stepCentre_of_finite_compact_cover
    {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {ι : Type w} [Finite ι] (s : GrowingSeq X) (U : ι → Opens X)
    (Q : (i : ι) → MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hQ : ∀ i, IsInvDomain k (Q i)) {L : Set X} (hL : IsCompact L)
    (hCover : L ⊆ ⋃ i, (U i : Set X))
    (hCan : ∀ i j, (∀ a < j, (stepCentre s a).Nonempty) →
      IsCanonical (Q i) (R.inv (Q i)) (restrict (U i) (s.stage j).2))
    (hHit : ∀ j, (∀ a ≤ j, (stepCentre s a).Nonempty) →
      (centreImage s j ∩ L).Nonempty) :
    ∃ j, stepCentre s j = ∅ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hFiniteCover : L ⊆ ⋃ i ∈ (Finset.univ : Finset ι), (U i : Set X) := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hCover hx)
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_univ i, hxi⟩⟩
  obtain ⟨F, hF, hFU, hUnion⟩ := hL.finite_compact_cover Finset.univ
    (fun i => (U i : Set X)) (fun i _ => (U i).isOpen) hFiniteCover
  let K (i : ι) : Set (U i) := (Subtype.val : U i → X) ⁻¹' F i
  have hImage (i : ι) : (Subtype.val : U i → X) '' K i = F i :=
    Set.image_preimage_eq_of_subset fun x hx => ⟨⟨x, hFU i hx⟩, rfl⟩
  have hK (i : ι) : IsCompact (K i) := Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    (hImage i ▸ hF i)
  by_contra! hAll
  have hFootprints (j : ℕ) (_ : (stepCentre s j).Nonempty) :
      ∃ i, (centreImage s j ∩ ((Subtype.val : U i → X) '' K i)).Nonempty := by
    obtain ⟨x, hx, hxL⟩ := hHit j (fun a _ => hAll a)
    rw [hUnion] at hxL
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxL
    obtain ⟨_, hxF⟩ := mem_iUnion.mp hi
    exact ⟨i, x, hx, (hImage i).symm ▸ hxF⟩
  obtain ⟨b, hb⟩ := exists_bound_of_compact_footprints R s U Q hQ K hK
    (fun i j => hCan i j (fun a _ => hAll a)) hFootprints
  obtain ⟨j, _, hj⟩ := exists_empty_stepCentre_of_bound s hb
  exact (hAll j).ne_empty hj

end

end Hironaka.HironakaG8FiniteWindowCount
