import Hironaka.Resolution.HironakaG8LabelledNativeOverlap
import Hironaka.Resolution.HironakaG8OccupiedSlotComparison

/-! Footprint invariance along a full labelled native history. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NativeOccupiedFootprintSymmetry
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  HironakaG3EmptyAwareHistory HironakaG8CofinalOccupiedAncestry
  HironakaG8OccupiedSlotComparison HironakaG8LabelledNativeHistory
  HironakaG8LabelledNativeOverlap

variable {n : ℕ} {X Y : CMfd.{0} n} {W : Set X}
  {E : List (Set X)} {T : BlowupTower X Y} {L : List (ℕ → ℕ)}

private theorem footprint_of_self_emptyAware
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : EmptyAwareTowerIso φ T T χ) (i : ℕ) :
    slotFootprint T i = φ ⁻¹' slotFootprint T i := by
  classical
  by_cases hi : Occupied T i
  · have he : occupiedComparison h = OrderIso.refl {j // Occupied T j} :=
      occupied_orderIso_unique _ _
    simpa only [he,OrderIso.refl_apply] using
      (slotFootprint_occupiedComparison h (⟨i,hi⟩ : {j // Occupied T j}))
  · have hz : slotFootprint T i = ∅ := eq_empty_iff_forall_notMem.mpr
      (fun x hx => hi ((slotFootprint_nonempty_iff T i).mp ⟨x,hx⟩))
    rw [hz,preimage_empty]

theorem native_whole_boundary_footprint_symmetry (hn : 0<n)
    (hT : LabelledNativeTower n W E univ T L)
    (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (hW : φ ⁻¹' W = W)
    (hE : E.filter (fun B => decide B.Nonempty) =
      (E.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty)) (i : ℕ) :
    slotFootprint T i = φ ⁻¹' slotFootprint T i := by
  obtain ⟨χ,hCompare⟩ := labelled_native_history_overlap hn φ hW.symm hE hDense hDense hT hT
  exact footprint_of_self_emptyAware hCompare i

theorem native_empty_boundary_footprint_symmetry (hn : 0<n)
    (hT : LabelledNativeTower n W [] univ T L)
    (φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (hW : φ ⁻¹' W = W) (i : ℕ) :
    slotFootprint T i = φ ⁻¹' slotFootprint T i := by
  have hDense : W ⊆ closure (W \ ⋃ B ∈ ([] : List (Set X)), B) := by
    simpa using (subset_closure : W ⊆ closure W)
  exact native_whole_boundary_footprint_symmetry hn hT hDense φ hW (by simp) i

end
end Hironaka.HironakaG8NativeOccupiedFootprintSymmetry
