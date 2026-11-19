import Hironaka.Resolution.HironakaSmoothSubmersionOriginalLocallyFiniteHistory
import Hironaka.Resolution.HironakaExhaustionBlockLocalFiniteness
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8LocallyFiniteCountBridge
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaLocallyFiniteResolutionSequence HironakaExhaustionBlockLocalFiniteness
  HironakaSmoothSubmersionOriginalLocallyFiniteHistory HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionCartesianTower
open ResolutionInvariantSeq (GrowingSeq)
open ResolutionInvariantSpec (countCentresMeeting)

/-- Actual local finiteness implies a uniform count bound on each compact set. -/
theorem locallyFinite_compact_count_bound {n : ℕ} {X : CMfd.{u} n}
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (K : Set X) (hK : IsCompact K) :
    ∃ m, ∀ i, countCentresMeeting K (s.stage i).2 ≤ m := by
  have hFinite : {i | (centreImage s i ∩ K).Nonempty}.Finite := hLF.finite_nonempty_inter_compact hK
  obtain ⟨N,hN⟩ := hFinite.bddAbove
  have hEmpty : ∀ i, N+1 ≤ i → ¬ (centreImage s i ∩ K).Nonempty := by
    intro i hi hhit
    have hle := hN hhit
    omega
  have hConst : ∀ i, N+1 ≤ i → countCentresMeeting K (s.stage i).2 = countCentresMeeting K (s.stage (N+1)).2 := by
    intro i hi
    induction i,hi using Nat.le_induction with
    | base => rfl
    | succ i hi ih =>
      rw [countCentresMeeting_step,if_neg (hEmpty i hi),Nat.add_zero,ih]
  refine ⟨countCentresMeeting K (s.stage (N+1)).2,fun i => ?_⟩
  rcases le_total i (N+1) with hi|hi
  · exact monotone_countCentresMeeting s K hi
  · exact (hConst i hi).le
/-- The actual chosen pullback of any locally finite growing history remains
locally finite, without assuming canonicality or invariant-domain hypotheses. -/
theorem actualSourceGrowing_locallyFinite {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m}
    {f : Y → X} (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    LocallyFinite (centreImage (actualSourceGrowing β hf s)) := by
  let : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace (ComplexModel m) Y
  let J := CompactExhaustion.choice Y
  let U : ℕ → Opens Y := fun j => ⟨interior (J (j+1)),isOpen_interior⟩
  have hCover : ∀ y : Y, ∃ j, y ∈ U j := by
    intro y
    obtain ⟨j,hj⟩ := J.exists_mem y
    exact ⟨j,J.subset_interior_succ j hj⟩
  apply locallyFinite_of_open_cover_count_bounds (actualSourceGrowing β hf s) U hCover
  intro j
  have hCompact : IsCompact (f '' J (j+1)) := (J.isCompact (j+1)).image hf.contMDiff.continuous
  obtain ⟨b,hb⟩ := locallyFinite_compact_count_bound s hLF (f '' J (j+1)) hCompact
  refine ⟨b,fun i => ?_⟩
  have hp := (chosenActualTower β hf (s.stage i).2).2.2.property
  have hLe := HironakaSmoothSubmersionOriginalLocallyFiniteHistory.IsActualTowerPullback.countCentresMeeting_le_image
    hp (U j : Set Y)
  have hMono := ResolutionInvariantSegments.countCentresMeeting_mono
    (image_mono (f := f) (show (U j : Set Y) ⊆ J (j+1) from interior_subset)) (s.stage i).2
  exact hLe.trans (hMono.trans (hb i))

end
end Hironaka.HironakaG8LocallyFiniteCountBridge
