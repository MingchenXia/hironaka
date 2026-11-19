import Hironaka.Resolution.HironakaG34MaskFoldEquivariance
import Hironaka.Resolution.HironakaG4OrderedRetainedDefectTrace

/-! Equivariance of a native retained lower tail for the whole upper tuple. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedLowerEquivariance
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers NormalCrossings HomogenizedGlueingTower MarkedIdeals.MarkedIdeal
  HironakaG4PreparedCentreCoordinates HironakaG4ResidualInductionInputs
  HironakaG34JointMaskEquivariance HironakaG34MaskFoldEquivariance
  HironakaG4OrderedRetainedDefectTrace HironakaActualRetainedBornResidualHistory
  HironakaSharpActualFiniteChronologicalHistory

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- A local symmetry preserving the upper carrier and every old and born
slot preserves the actual selected retained residual support. -/
theorem retained_selected_support_preserved (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (i : Fin old.length) {U V : Opens X}
    (φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V)
    (hCarrier : ∀ p : U, ((φ p : V) : X) ∈ N ↔ (p : X) ∈ N)
    (hBoundary : ∀ D ∈ old ++ born, ∀ p : U, ((φ p : V) : X) ∈ D ↔ (p : X) ∈ D) :
    ∀ p : U, ((φ p : V) : X) ∈ N ∩ (oldResidualPart N old born i).zeroLocus ↔
      (p : X) ∈ N ∩ (oldResidualPart N old born i).zeroLocus := by
  let f : CMfd.of (n := n) U → X := fun p => ((φ p : V) : X)
  let v : CMfd.of (n := n) U → X := Subtype.val
  have hf : HironakaBaseChange.IsOpenHoloEmbedding n f := ⟨V,φ,fun _ => rfl⟩
  have hv : HironakaBaseChange.IsOpenHoloEmbedding n v :=
    HironakaBaseChange.isOpenHoloEmbedding_val (n := n) U
  have hN : f ⁻¹' N = v ⁻¹' N := Set.ext hCarrier
  have hH : f ⁻¹' old.get i = v ⁻¹' old.get i :=
    Set.ext (hBoundary _ (List.mem_append_left born (List.get_mem old i)))
  have hB : born.map (f ⁻¹' ·) = born.map (v ⁻¹' ·) :=
    List.map_congr_left fun D hD => Set.ext (hBoundary D (List.mem_append_right old hD))
  have hZ := retained_residual_zeroLocus_preimage_eq_of_compatible_open_embeddings
    hn g.carrier g.full g.born_transverse g.dense i hf hv hN hH hB
  intro p
  exact and_congr (hCarrier p) (Set.ext_iff.mp hZ p)

/-- A tail equivariant for the selected lower data is equivariant for the
full upper data, carrying along any common extra ordered labels. -/
theorem isEquivariant_upper_of_retained_selected_lower_with_labels (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (i : Fin old.length) (extra : List (Set X)) (R : BlowupTower X Y)
    (hLower : IsEquivariant (N ∩ (oldResidualPart N old born i).zeroLocus)
      (extra ++ remainingBoundary old born i) R) :
    IsEquivariant N (extra ++ (old ++ born)) R := by
  intro U V φ hφN hφBoundary
  have hφFull (D : Set X) (hD : D ∈ old ++ born) (p : U) :
      ((φ p : V) : X) ∈ D ↔ (p : X) ∈ D :=
    hφBoundary D (List.mem_append_right extra hD) p
  apply hLower U V φ (retained_selected_support_preserved hn g i φ hφN hφFull)
  intro D hD p
  have hSub : (extra ++ remainingBoundary old born i).Sublist (extra ++ (old ++ born)) :=
    (List.Sublist.refl extra).append ((List.eraseIdx_sublist old i.val).append (List.Sublist.refl born))
  exact hφBoundary D (hSub.subset hD) p

/-- The native lower tail is equivariant for the actual upper carrier and
full retained boundary, on the same physical tower. -/
theorem isEquivariant_upper_of_retained_selected_lower (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (i : Fin old.length) (R : BlowupTower X Y)
    (hLower : IsEquivariant (N ∩ (oldResidualPart N old born i).zeroLocus)
      (remainingBoundary old born i) R) :
    IsEquivariant N (old ++ born) R :=
  isEquivariant_upper_of_retained_selected_lower_with_labels hn g i [] R hLower

/-- Appending a lower-equivariant tail of the actual selected current
row preserves upper equivariance of the whole native history. -/
theorem isEquivariant_append_retained_selected_lower (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (i : Fin old.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (hEq : IsEquivariant N (old ++ born) T) (R : BlowupTower Y Z)
    (hLower : let A := geoTransformAlong (geometricTemplate N born) T
      let O := old.map (strictAlong T)
      let j : Fin O.length := Fin.cast (List.length_map _).symm i
      IsEquivariant (A.N ∩ (oldResidualPart A.N O A.E j).zeroLocus)
        (remainingBoundary O A.E j) R) :
    IsEquivariant N (old ++ born) (T.append R) := by
  obtain ⟨hN,hE,hTr,hDense,_⟩ :=
    actual_retained_born_recorded_residual_dictionary hn g.carrier g.full g.born_transverse g.dense T hT hFull
  exact IsEquivariant.append_of_current g.carrier T hT hFull hEq R
    (isEquivariant_upper_of_retained_selected_lower hn ⟨hN,hE,hTr,hDense⟩ _ R hLower)

end
end Hironaka.HironakaG4RetainedLowerEquivariance
