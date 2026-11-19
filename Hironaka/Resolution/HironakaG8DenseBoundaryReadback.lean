import Hironaka.Resolution.HironakaG8DenseBoundaryRestart
import Hironaka.Resolution.HironakaNormalCrossingsTransversality

/-! Read back dense complement, transversality and the exact carrier image
from a finite admissible embedded history with simultaneous normal crossings. -/

set_option autoImplicit false
open Set Function
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8DenseBoundaryReadback

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaEmbeddedAnalytic
  HironakaEmbeddedBoundary HironakaAdmissibleSequence HironakaAdmissibleCalculus HironakaG8DenseBoundaryRestart

/-- Full normal crossings, actual admissibility and original density imply
final density, transversality and non-erasure of the strict carrier. -/
theorem terminal_dense_transverse_image {n : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hAdm : IsAdmissibleBlowupSequence n X E (singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H))
      Y T.proj (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).E)
    (hNC : HasNormalCrossings n (strictTransform n T.proj W)
      (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).E) :
    let A := strictTransform n T.proj W
    let B := (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).E
    A ⊆ closure (A \ ⋃ H ∈ B, H) ∧ IsTransverse n A B ∧ T.proj '' A = W := by
  let B := ⋃ H ∈ E, H
  let D := singularSet (n := n) W
  let F := D ∪ (W ∩ B)
  let W' := strictTransform n T.proj W
  let E' := (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).E
  have hProper := HironakaLocalPrincipalization.isProperMap_proj T
  have hSurj := HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence
  have hIso : IsIsomorphismOver n T.proj Fᶜ := IsAdmissibleBlowupSequence.isIsomorphismOver_compl hAdm
  have hJoint : W ⊆ closure (W \ (B ∪ D)) :=
    dense_off_original_boundary_and_singular hW (isClosed_biUnion_of_forall_isClosed hE.1) hDense
  have hBound : (⋃ H ∈ E', H) ⊆ T.proj ⁻¹' (B ∪ D) :=
    (IsAdmissibleBlowupSequence.biUnion_subset hAdm hE.1).trans
      (preimage_mono (fun _ h => h.elim Or.inl (fun h => h.elim Or.inr (fun h => Or.inl h.2))))
  have hDensity : W' ⊆ closure (W' \ ⋃ H ∈ E', H) :=
    (strictTransform_subset_closure_diff T.contMDiff_proj hW.isClosed hJoint).trans
      (closure_mono (sdiff_subset_sdiff_right hBound))
  have hTrans := HironakaNormalCrossingsTransversality.isTransverse_of_hasNormalCrossings_of_subset_closure_diff
    hNC hDensity
  have hImage : T.proj '' W' = W := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact strictTransform_subset_preimage T.contMDiff_proj.continuous hW.isClosed hz
    · refine hJoint.trans (closure_minimal ?_ (hProper.isClosedMap _ isClosed_closure))
      rintro x ⟨hxW, hxGood⟩
      obtain ⟨z, hz⟩ := hSurj x
      have hzF : z ∈ T.proj ⁻¹' Fᶜ := by
        change T.proj z ∉ F
        rw [hz]
        exact fun h => hxGood (h.elim Or.inr (fun h => Or.inl h.2))
      have hzW : z ∈ T.proj ⁻¹' W := by
        change T.proj z ∈ W
        rwa [hz]
      exact ⟨z, subset_closure ⟨hzW, fun h => disjoint_left.mp hIso.2 hzF h⟩, hz⟩
  exact ⟨hDensity, hTrans, hImage⟩

end Hironaka.HironakaG8DenseBoundaryReadback
