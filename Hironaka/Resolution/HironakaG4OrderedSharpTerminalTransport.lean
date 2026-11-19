import Hironaka.Resolution.HironakaG4OrderedProcessedMaskRestriction
import Hironaka.Resolution.HironakaG4SharpTerminalAtlas
import Hironaka.Resolution.HironakaCompactFootprintSharpExtension

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4OrderedSharpTerminalTransport

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  HomogenizedGlueingTower NormalCrossings NormalCrossingsInvariance
  HironakaG34NonPureLowDim HironakaSharpActualFiniteChronologicalHistory
  HironakaG4SharpTerminalAtlas HironakaCompactFootprintSharpExtension IdealWeightPowers
  HironakaG4OrderedProcessedMaskHistory

variable {n : ℕ} {X X' Y Y' : CMfd.{u} n} {ι : Type v}

/-- Transport the full sharp endpoint by the actual tower isomorphism. -/
theorem sharp_terminal_of_isTowerIso {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W)
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T χ) (h : IsSharpTerminalTower W E T) :
    IsSharpTerminalTower (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) T' := by
  let WO := φ ⁻¹' W
  let EO := E.map (φ ⁻¹' ·)
  have hTest := (IsTowerIso.isGeoTestTower_iff φ hW isCoherent_unitIdeal hIso).mpr h.carrierTest
  rw [template_pullback,List.map_nil] at hTest
  have hFull := (IsTowerIso.isGeoTestTower_iff φ isClosedSubmanifold_univ isCoherent_unitIdeal hIso).mpr h.boundaryTest
  rw [template_pullback,preimage_univ] at hFull
  have hSharp : HironakaG4CompactWholeMonomialMaskPhase.CurrentSharpCentres WO EO T' := by
    apply currentSharp_of_isTowerIso WO EO φ.symm hIso.symm hFull
    have hW₀ : φ.symm ⁻¹' WO = W := by
      ext x
      change φ (φ.symm x) ∈ W ↔ x ∈ W
      rw [φ.apply_symm_apply]
    have hE₀ : EO.map (φ.symm ⁻¹' ·) = E := by
      unfold EO
      rw [List.map_map]
      have hId : (fun H : Set X => φ.symm ⁻¹' (φ ⁻¹' H)) = id := by
        funext H
        ext x
        change φ (φ.symm x) ∈ H ↔ x ∈ H
        rw [φ.apply_symm_apply]
      change List.map (fun H : Set X => φ.symm ⁻¹' (φ ⁻¹' H)) E = E
      rw [hId,List.map_id]
    rw [hW₀,hE₀]
    exact h.sharp
  have hList := IsTowerIso.geoTransformAlong_eq φ isClosedSubmanifold_univ isCoherent_unitIdeal hIso h.boundaryTest
  rw [template_pullback,preimage_univ] at hList
  refine ⟨hTest,hFull,hSharp,?_⟩
  rw [hIso.strictAlong_eq,congrArg MarkedIdeal.E hList]
  exact hasNormalCrossings_preimage (pullsBackCoordinates χ) h.normalCrossings

/-- Reindexing the same original list by its length equality changes no
actual phase. -/
theorem ordered_processed_change_boundary (hn : 0 < n) (W : Set X)
    {E F : List (Set X)} (hEF : E = F) (T : BlowupTower X Y)
    {Z : CMfd.{u} n} (Q : BlowupTower Y Z) (L : List ι)
    (mask : ι → Finset (Fin E.length)) :
    OrderedProcessedMaskHistory hn W E T mask Q L →
    OrderedProcessedMaskHistory hn W F T
      (fun a => (mask a).map (finCongr (congrArg List.length hEF)).toEmbedding) Q L := by
  subst F
  simp

end
end Hironaka.HironakaG4OrderedSharpTerminalTransport
