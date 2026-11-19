import Hironaka.Resolution.HironakaG4PairedProcessedMaskHistory
import Hironaka.Resolution.HironakaG4MaskScheduleEmptyRows

/-! The common live row list aligns two independently padded incidence
schedules, with independent count caps and no common resolving choice. -/

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4IncidencePairedEmptyRowsComparison

noncomputable section

open Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaG3EmptyAwareHistory
  HironakaG4OrderedProcessedMaskHistory HironakaG4ProcessedMaskIncidenceOrder
  HironakaG4RelativeOrderedProcessedFinish HironakaG4MaskScheduleEmptyRows
  HironakaG4PairedProcessedMaskHistory

variable {n : ℕ} {X X' Y Y' Z Z' : CMfd.{u} n}

/-- The same ordered live rows in two independently padded original old
lists give an actual comparison of their entire incidence histories. Each
starting cap is bounded below by its own old length. -/
theorem incidence_processed_paired_empty_rows_comparison (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (E' : List (Set X')) (hE' : IsSNCDivisor n E')
    (hdense' : φ ⁻¹' W ⊆ closure (φ ⁻¹' W \ ⋃ H ∈ E',H))
    (H : List (Set X)) (e : Fin H.length ↪ Fin E.length) (e' : Fin H.length ↪ Fin E'.length)
    (hMono : StrictMono e) (hMono' : StrictMono e')
    (hSlots : ∀ i,E.get (e i) = H.get i)
    (hSlots' : ∀ i,E'.get (e' i) = φ ⁻¹' H.get i)
    (hAbsent : ∀ j,(∀ i,e i ≠ j) → E.get j = ∅)
    (hAbsent' : ∀ j,(∀ i,e' i ≠ j) → E'.get j = ∅)
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
  obtain ⟨p⟩ := OldRowInsertion.of_strictMono hMono
  obtain ⟨p'⟩ := OldRowInsertion.of_strictMono hMono'
  let L := (descendingMaskLabels (orderedMaskLevel E.length) q).reverse
  let L' := (descendingMaskLabels (orderedMaskLevel E'.length) q').reverse
  have hJoin (i : Fin H.length) : E'.get (e' i) = φ ⁻¹' E.get (e i) := by
    rw [hSlots i,hSlots' i]
  have hSame : L.filterMap p.project = L'.filterMap p'.project := by
    simp only [L,L',List.filterMap_reverse,p.descendingMaskLabels_project_of_caps le_rfl hCap,
      p'.descendingMaskLabels_project_of_caps le_rfl hCap']
  refine paired_processed_histories_emptyAware hn hW hE hdense E' hE' hdense' T T' hIso
    e e' hJoin id id p.project p'.project ?_ ?_ L L' hSame Q Q'
    hTest hFull hTest' hFull' hQ hQ'
  · intro P
    cases hP : p.project P with
    | none =>
      obtain ⟨j,hj,hMissing⟩ := p.exists_unmatched_of_project_eq_none hP
      exact ⟨j,hj,hAbsent j hMissing⟩
    | some R => exact (p.map_of_project_eq_some hP).symm
  · intro P
    cases hP : p'.project P with
    | none =>
      obtain ⟨j,hj,hMissing⟩ := p'.exists_unmatched_of_project_eq_none hP
      exact ⟨j,hj,hAbsent' j hMissing⟩
    | some R => exact (p'.map_of_project_eq_some hP).symm

end
end Hironaka.HironakaG4IncidencePairedEmptyRowsComparison
