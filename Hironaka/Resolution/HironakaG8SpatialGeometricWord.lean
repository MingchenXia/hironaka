import Hironaka.Resolution.HironakaG8FiniteSpatialRealization
import Hironaka.Resolution.HironakaG8GeometricIndexedWord

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8SpatialGeometricWord

noncomputable section

open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG8OccupiedSlotComparison HironakaG8FirstFootprintOrder HironakaG8IndexedDisjointSwap
  HironakaG8FiniteSpatialRealization HironakaG8NestedVisibleWordLift HironakaG8GeometricIndexedWord

variable {n : ℕ} {B : CMfd.{0} n}

/-- The successive geometric witnesses compose over the original source. -/
theorem geometric_word_endpoint_equiv (W : Set B) (M : MarkedIdeal n B)
    {w : List ℕ} {L R : TowerAt B} (h : RealizedWord (GeometricIndexedMove W M) w L R) :
    ∃ e : L.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R.1,
      R.2.proj ∘ e = L.2.proj := by
  induction h with
  | nil => exact ⟨Diffeomorph.refl _ _ _,rfl⟩
  | @cons i w L S R hMove _ ih =>
      obtain ⟨e,he,_,_⟩ := hMove.2.2.2.2.2
      obtain ⟨f,hf⟩ := ih
      refine ⟨e.trans f,?_⟩
      change R.2.proj ∘ (f ∘ e) = L.2.proj
      rw [← Function.comp_assoc,hf,he]

/-- Use the archived spatial sorting witness to select the larger physical
word, keeping every realized geometric move and the literal target list. -/
theorem realize_spatial_target_geometrically (L : TowerAt B) (target : List ℕ)
    (hPerm : (List.range L.2.length).Perm target)
    (hOcc : OccupiedFootprints L)
    (hPreserve : ∀ i j : ℕ, i < j → j < L.2.length →
      (slotFootprint L.2 i ∩ slotFootprint L.2 j).Nonempty → target.idxOf i < target.idxOf j)
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M L.2) (hStage : IntrinsicStage W L) :
    ∃ (word : List ℕ) (R : TowerAt B),
      IsDisjointSwapWord (slotFootprint L.2) (Equiv.refl ℕ) word ∧
      RealizedWord (GeometricIndexedMove W M) word L R ∧
      IsGeoTestTower M R.2 ∧ IntrinsicStage W R ∧ OccupiedFootprints R ∧
      (∀ j a, target[j]? = some a → slotFootprint R.2 j = slotFootprint L.2 a) ∧
      footprints R = target.map (slotFootprint L.2) ∧
      ∃ e : L.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R.1,
        R.2.proj ∘ e = L.2.proj := by
  obtain ⟨word,hWord,hOrder⟩ := exists_disjoint_swap_word_of_intersection_order
    (slotFootprint L.2) L.2.length target hPerm hOcc hPreserve
  obtain ⟨R,hPhysical,hRT,hRS,hRO,hFoot⟩ :=
    realize_geometric_indexed_word_from_source W M hM hN L word hWord hTest hStage hOcc
  let σ := reordering (Equiv.refl ℕ) word
  have hListed j a (ha : target[j]? = some a) : slotFootprint R.2 j = slotFootprint L.2 a :=
    (hFoot j).trans (congrArg (slotFootprint L.2) (hOrder j a ha))
  have hActive (j : ℕ) : (slotFootprint R.2 j).Nonempty ↔ j < target.length := by
    constructor
    · rintro ⟨x,hx⟩
      have hxL : x ∈ slotFootprint L.2 (σ j) := (hFoot j) ▸ hx
      have ha : σ j ∈ target := hPerm.mem_iff.mp (List.mem_range.mpr (hit_slot_lt_length L.2 hxL))
      let k := target.idxOf (σ j)
      have hk : k < target.length := List.idxOf_lt_length_iff.mpr ha
      have hka : target[k]? = some (σ j) := List.getElem?_idxOf ha
      have he : σ k = σ j := hOrder k (σ j) hka
      rwa [σ.injective he] at hk
    · intro hj
      rw [hListed j _ (List.getElem?_eq_getElem hj)]
      exact hOcc _ (List.mem_range.mp (hPerm.mem_iff.mpr (List.getElem_mem hj)))
  have hLen : R.2.length = target.length := by
    apply Nat.le_antisymm
    · by_contra! h
      exact Nat.lt_irrefl _ ((hActive _).mp (hRO _ h))
    · by_contra! h
      obtain ⟨x,hx⟩ := (hActive _).mpr h
      exact Nat.lt_irrefl _ (hit_slot_lt_length R.2 hx)
  refine ⟨word,R,hWord,hPhysical,hRT,hRS,hRO,hListed,?_,geometric_word_endpoint_equiv W M hPhysical⟩
  apply List.ext_getElem (by simpa [footprints])
  intro j hj hk
  have hTarget : j < target.length := by simpa using hk
  simpa [footprints] using hListed j (target[j]'hTarget) (List.getElem?_eq_getElem hTarget)

end
end Hironaka.HironakaG8SpatialGeometricWord
