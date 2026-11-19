import Hironaka.Resolution.HironakaG4IncidencePairedEmptyRowsComparison
import Hironaka.Resolution.HironakaG4LiveBoundaryIndices

/-! The ordered live old lists are enough to compare two complete Γ
histories, even when the literal lists have different empty slots. -/

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4IncidenceLiveBoundaryComparison

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaG3EmptyAwareHistory
  HironakaG4OrderedProcessedMaskHistory HironakaG4ProcessedMaskIncidenceOrder
  HironakaG4RelativeOrderedProcessedFinish HironakaG4IncidencePairedEmptyRowsComparison
  HironakaG4LiveBoundaryIndices

variable {n : ℕ} {X X' Y Y' Z Z' : CMfd.{u} n}

/-- Equality of the live old lists under the base biholomorphism gives
the comparison of the two actual incidence-ordered Γ histories. -/
theorem incidence_processed_live_boundary_comparison (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (E' : List (Set X')) (hE' : IsSNCDivisor n E')
    (hdense' : φ ⁻¹' W ⊆ closure (φ ⁻¹' W \ ⋃ H ∈ E',H))
    (hLive : E'.filter (fun H => decide H.Nonempty) =
      (E.filter (fun H => decide H.Nonempty)).map (φ ⁻¹' ·))
    (T : BlowupTower X Y) (T' : BlowupTower X' Y')
    {ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : EmptyAwareTowerIso φ T' T ψ)
    (q q' : ℕ) (hCap : E.length ≤ q) (hCap' : E'.length ≤ q')
    (Q : BlowupTower Y Z) (Q' : BlowupTower Y' Z')
    (hTest : IsGeoTestTower (geometricTemplate W []) (T.append Q))
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q))
    (hTest' : IsGeoTestTower (geometricTemplate (φ ⁻¹' W) []) (T'.append Q'))
    (hFull' : IsGeoTestTower (geometricTemplate (univ : Set X') E') (T'.append Q'))
    (hQ : OrderedProcessedMaskHistory hn W E T id Q
      (descendingMaskLabels (orderedMaskLevel E.length) q).reverse)
    (hQ' : OrderedProcessedMaskHistory hn (φ ⁻¹' W) E' T' id Q'
      (descendingMaskLabels (orderedMaskLevel E'.length) q').reverse) :
    ∃ χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      EmptyAwareTowerIso φ (T'.append Q') (T.append Q) χ := by
  let H := E.filter (fun B => decide B.Nonempty)
  let H' := E'.filter (fun B => decide B.Nonempty)
  obtain ⟨e,hMono,hSlots,hAbsent⟩ := exists_live_boundary_embedding E
  obtain ⟨e₀',hMono₀',hSlots₀',hAbsent₀'⟩ := exists_live_boundary_embedding E'
  have hList : H' = H.map (φ ⁻¹' ·) := hLive
  have hLen : H.length = H'.length := by rw [hList,List.length_map]
  let a := finCongr hLen
  let e' := a.toEmbedding.trans e₀'
  have hMono' : StrictMono e' := hMono₀'.comp (Fin.cast_strictMono hLen)
  have hSlots' (i : Fin H.length) : E'.get (e' i) = φ ⁻¹' H.get i := by
    change E'.get (e₀' (a i)) = _
    rw [hSlots₀' (a i),List.get_of_eq hList]
    simp [a,List.get_eq_getElem]
  have hAbsent' (j : Fin E'.length) (hj : ∀ i,e' i ≠ j) : E'.get j = ∅ := by
    apply hAbsent₀' j
    intro i hi
    apply hj (a.symm i)
    change e₀' (a (a.symm i)) = j
    rwa [a.apply_symm_apply]
  exact incidence_processed_paired_empty_rows_comparison hn hW hE hdense E' hE' hdense'
    H e e' hMono hMono' hSlots hSlots' hAbsent hAbsent' T T' hIso
    q q' hCap hCap' Q Q' hTest hFull hTest' hFull' hQ hQ'

end
end Hironaka.HironakaG4IncidenceLiveBoundaryComparison
