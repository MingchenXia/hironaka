import Hironaka.Resolution.HironakaG8IndexedSwapTraceLift
import Hironaka.Resolution.HironakaG8IndexedDisjointSwap

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8GeometricIndexedWord

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowerIsomorphism HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8OccupiedSlotComparison
  HironakaG8FirstFootprintOrder HironakaG8IndexedDisjointSwap HironakaG8DisjointSwapFullHistory
  HironakaG8NestedVisibleWordLift HironakaG8IndexedSwapTraceLift HironakaG3EmptyAwareHistory

variable {n : ℕ} {B : CMfd.{0} n}

abbrev IntrinsicStage (W : Set B) (T : TowerAt B) : Prop :=
  StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T.2

abbrev OccupiedFootprints (T : TowerAt B) : Prop :=
  ∀ j < T.2.length, (slotFootprint T.2 j).Nonempty

/-- A physical larger move retains its literal exchange geometry, the
footprint dictionary, and the comparison on opens seeing at most one slot. -/
def GeometricIndexedMove (W : Set B) (M : MarkedIdeal n B) (i : ℕ)
    (L R : TowerAt B) : Prop :=
  IndexedOccupiedReadback i L R ∧ IsGeoTestTower M L.2 ∧ IsGeoTestTower M R.2 ∧
  IntrinsicStage W L ∧ IntrinsicStage W R ∧
  ∃ (e : L.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R.1),
    R.2.proj ∘ e = L.2.proj ∧ Nonempty (AdjacentSwapGeometry L.2 R.2 e i) ∧
    ∀ U : Opens B,
      Disjoint (U : Set B) (slotFootprint L.2 i) ∨
        Disjoint (U : Set B) (slotFootprint L.2 (i+1)) →
      ∃ χ : CMfd.of (n := n) (openPreimage L.2 U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R.2 U),
        (∀ z, (χ z).val = e z.val) ∧
        EmptyAwareTowerIso
          (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
          (restrict U L.2) (restrict U R.2) χ

/-- Realize one requested move using the existing indexed geometric producer.
The two actual suffixes in its witness have the same length. -/
theorem exists_geometric_indexed_move (W : Set B) (M : MarkedIdeal n B)
    (hM : M.IsWellFormed) (hN : M.N = univ) (L : TowerAt B) (i : ℕ)
    (hi : i+1 < L.2.length)
    (hDisj : Disjoint (slotFootprint L.2 i) (slotFootprint L.2 (i+1)))
    (hTest : IsGeoTestTower M L.2) (hStage : IntrinsicStage W L)
    (hOcc : OccupiedFootprints L) :
    ∃ R : TowerAt B, GeometricIndexedMove W M i L R := by
  obtain ⟨G,R,e,hRT,hProj,hRS,hFoot,hOpen,⟨w⟩⟩ :=
    swap_adjacent_at_index_with_geometry L.2 i hi hDisj W M hM hN hTest hStage
  have hLen : R.length = L.2.length := by
    have hBefore := congrArg BlowupTower.length w.before
    have hAfter := congrArg BlowupTower.length w.after
    simp only [BlowupTower.length_append,BlowupTower.length_step,BlowupTower.length_refl,w.carry.length_eq] at hBefore hAfter
    exact hAfter.symm.trans hBefore
  have hROcc : OccupiedFootprints ⟨G,R⟩ := by
    intro j hj
    rw [hFoot]
    have hj' : j < L.2.length := hLen ▸ hj
    apply hOcc
    by_cases h₀ : j = i
    · simpa [h₀]
    by_cases h₁ : j = i+1
    · simp [h₁]; omega
    · simpa only [Equiv.swap_apply_of_ne_of_ne h₀ h₁]
  exact ⟨⟨G,R⟩,⟨hi,hDisj,hOcc,hROcc,hFoot⟩,hTest,hRT,hStage,hRS,e,hProj,⟨w⟩,hOpen⟩

/-- The actual indexed producer now retains every geometric move of the
realized word. The endpoint still has exact reindexed original footprints. -/
theorem realize_geometric_indexed_word (A : ℕ → Set B)
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : M.N = univ)
    (word : List ℕ) (L : TowerAt B) (σ : ℕ ≃ ℕ)
    (hWord : IsDisjointSwapWord A σ word)
    (hFoot : ∀ j, slotFootprint L.2 j = A (σ j))
    (hTest : IsGeoTestTower M L.2) (hStage : IntrinsicStage W L)
    (hOcc : OccupiedFootprints L) :
    ∃ R : TowerAt B, RealizedWord (GeometricIndexedMove W M) word L R ∧
      IsGeoTestTower M R.2 ∧ IntrinsicStage W R ∧ OccupiedFootprints R ∧
      ∀ j, slotFootprint R.2 j = A (reordering σ word j) := by
  induction word generalizing L σ with
  | nil =>
      exact ⟨L, .nil _, hTest, hStage, hOcc, hFoot⟩
  | cons i rest ih =>
      obtain ⟨hHit,hDisj,hNext⟩ := hWord
      have hi : i+1 < L.2.length := by
        obtain ⟨x,hx⟩ := hHit
        exact hit_slot_lt_length L.2 (by rwa [hFoot])
      have hD : Disjoint (slotFootprint L.2 i) (slotFootprint L.2 (i+1)) := by
        simpa only [hFoot]
      obtain ⟨S,hStep⟩ := exists_geometric_indexed_move W M hM hN L i
        hi hD hTest hStage hOcc
      have hSF : ∀ j, slotFootprint S.2 j = A (((Equiv.swap i (i+1)).trans σ) j) :=
        fun j => (hStep.1.2.2.2.2 j).trans (hFoot _)
      obtain ⟨R,hTail,hRT,hRS,hRO,hRF⟩ := ih S _ hNext hSF
        hStep.2.2.1 hStep.2.2.2.2.1 hStep.1.2.2.2.1
      exact ⟨R,.cons hStep hTail,hRT,hRS,hRO,hRF⟩

/-- The source footprints themselves supply the initial dictionary. -/
theorem realize_geometric_indexed_word_from_source
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : M.N = univ)
    (L : TowerAt B) (word : List ℕ)
    (hWord : IsDisjointSwapWord (slotFootprint L.2) (Equiv.refl ℕ) word)
    (hTest : IsGeoTestTower M L.2) (hStage : IntrinsicStage W L)
    (hOcc : OccupiedFootprints L) :
    ∃ R : TowerAt B, RealizedWord (GeometricIndexedMove W M) word L R ∧
      IsGeoTestTower M R.2 ∧ IntrinsicStage W R ∧ OccupiedFootprints R ∧
      ∀ j, slotFootprint R.2 j = slotFootprint L.2 (reordering (Equiv.refl ℕ) word j) :=
  realize_geometric_indexed_word _ W M hM hN word L _ hWord (fun _ => rfl) hTest hStage hOcc

end
end Hironaka.HironakaG8GeometricIndexedWord
