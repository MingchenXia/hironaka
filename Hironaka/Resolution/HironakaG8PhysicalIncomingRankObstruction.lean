import Hironaka.Resolution.HironakaG8RankedEmptyPadding

/-! # Incoming length bounds for actual occupied chart comparisons -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8PhysicalIncomingRankObstruction
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism BlowupTowerTransforms
  HironakaG8RankedEmptyPadding ResolutionInvariantSpec

/-- Every actual chronological step of a ranked finite tower consumes
one slot, even when other scheduled slots were skipped. -/
theorem RankedTower.length_le_index {n : ℕ} {X Y : CMfd.{0} n}
    {T : BlowupTower X Y} {k : ℕ} (D : RankedTower X T k) : T.length ≤ k := by
  induction D with
  | refl => exact Nat.zero_le _
  | step D h _ ih => exact Nat.succ_le_succ (ih.trans h)

/-- If both terminal centres in an actual comparison are occupied,
neither can be discarded by the empty-aware alignment. Their assigned
slots coincide and bound both actual incoming prefix lengths. -/
theorem occupied_terminal_slots_and_prefix_lengths
    {n : ℕ} {X A Y B Z W : CMfd.{0} n} {T : BlowupTower X Y} {S : BlowupTower A B}
    {i j k l : ℕ} (D : RankedTower X T i) (F : RankedTower A S j)
    (hi : i ≤ k) (hj : j ≤ l)
    {C : Set Y} {C' : Set B} {π : Z → Y} {ρ : W → B}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n C' ρ)
    (hC : C.Nonempty) (hC' : C'.Nonempty)
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ W}
    (hCmp : OccupiedComparison φ (.step D hi hπ) (.step F hj hρ) χ) :
    k = l ∧ T.length ≤ k ∧ S.length ≤ k := by
  have he : k = l := by
    cases hCmp with
    | pair _ _ _ _ _ _ _ _ hSlot => exact hSlot hC
    | left => exact False.elim (Set.not_nonempty_empty hC)
    | right => exact False.elim (Set.not_nonempty_empty hC')
  exact ⟨he, (RankedTower.length_le_index D).trans hi,
    he.symm ▸ (RankedTower.length_le_index F).trans hj⟩

/-- Synchronizing the last occupied stage of a family of literal
physical towers forces a uniform bound on the number of its incoming
chart stages. The test uses actual ranked towers with their genuine
blowup maps and includes different ambient charts and targets. -/
theorem no_common_terminal_rank_of_unbounded_physical_prefixes
    {n : ℕ} {X Y : ℕ → CMfd.{0} n} (T : ∀ a, BlowupTower (X a) (Y a))
    (hUnbounded : ∀ k, ∃ a, k ≤ (T a).length) :
    ¬ ∃ k, ∀ a, Nonempty (RankedTower (X a) (T a) k) := by
  rintro ⟨k,h⟩
  obtain ⟨a,ha⟩ := hUnbounded (k+1)
  obtain ⟨D⟩ := h a
  have hb := RankedTower.length_le_index D
  omega

/-- In an actual chain of restricted chart comparisons, a matched
occupied terminal event has a single assigned slot throughout the chain.
Unbounded numbers of actual occupied predecessors therefore obstruct a
common natural clock on those charts. Each overlap is a literal open
restriction, and its nonempty terminal-centre trace is explicit. -/
theorem no_synchronized_clock_on_unbounded_terminal_overlap_chain
    {n : ℕ} {X Y Z : ℕ → CMfd.{0} n}
    (T : ∀ a, BlowupTower (X a) (Y a))
    (C : ∀ a, Set (Y a)) (π : ∀ a, Z a → Y a)
    (hπ : ∀ a, IsBlowupAlong n (C a) (π a))
    (U : ∀ a, Opens (X a)) (V : ∀ a, Opens (X (a+1)))
    (hU : ∀ a, ((Subtype.val : openPreimage (T a) (U a) → Y a) ⁻¹' C a).Nonempty)
    (hV : ∀ a, ((Subtype.val : openPreimage (T (a+1)) (V a) → Y (a+1)) ⁻¹' C (a+1)).Nonempty)
    (hUnbounded : ∀ k, ∃ a, k ≤ countCentresMeeting univ (T a)) :
    ¬ ∃ (i r : ℕ → ℕ) (D : ∀ a, RankedTower (X a) (T a) (i a)) (hr : ∀ a, i a ≤ r a),
      ∀ a, ∃ φ : CMfd.of (n := n) (U a)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (V a),
        ∃ χ : CMfd.of (n := n) (openPreimage (.step (T a) (C a) (π a) (hπ a)) (U a))
            ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
              CMfd.of (n := n) (openPreimage (.step (T (a+1)) (C (a+1)) (π (a+1)) (hπ (a+1))) (V a)),
          OccupiedComparison φ
            ((RankedTower.step (D a) (hr a) (hπ a)).restrict (U a))
            ((RankedTower.step (D (a+1)) (hr (a+1)) (hπ (a+1))).restrict (V a)) χ := by
  rintro ⟨i,r,D,hr,hCmp⟩
  have hEq (a : ℕ) : r a = r (a+1) := by
    obtain ⟨φ,χ,h⟩ := hCmp a
    exact (occupied_terminal_slots_and_prefix_lengths ((D a).restrict (U a))
      ((D (a+1)).restrict (V a)) (hr a) (hr (a+1)) _ _ (hU a) (hV a) h).1
  have hConst (a : ℕ) : r a = r 0 := by
    induction a with
    | zero => rfl
    | succ a ih => exact (hEq a).symm.trans ih
  have hCount {A B : CMfd.{0} n} (S : BlowupTower A B) :
      countCentresMeeting univ S ≤ S.length := by
    induction S with
    | refl => exact Nat.zero_le _
    | step S C π hπ ih =>
      simp only [countCentresMeeting,BlowupTower.length_step]
      split <;> omega
  obtain ⟨a,ha⟩ := hUnbounded (r 0 + 1)
  have hLen := ha.trans (hCount (T a))
  have hb := (RankedTower.length_le_index (D a)).trans (hr a)
  rw [hConst a] at hb
  omega

end
end Hironaka.HironakaG8PhysicalIncomingRankObstruction
