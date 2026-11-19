import Hironaka.Resolution.HironakaG4SelectedLowerOverlapData

/-! Compare one retained row, including its actual re-preparation trace. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4SelectedRetainedRowOverlap

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals.MarkedIdeal HomogenizedGlueingTower
  HironakaSharpActualFiniteChronologicalHistory HironakaActualRetainedBornResidualHistory
  HironakaG4OrderedRetainedDefectTrace HironakaG4PreparedCentreCoordinates
  HironakaG4SelectedLowerOverlapData HironakaG4RetainedTraceComparison
  HironakaG3EmptyAwareHistory HironakaG8DisjointPhaseMerge

/-- Corresponding selected rows on two actual retained inputs give
comparable lower problems even when either old list contains extra
empty slots. Compare their actual immediate defect reruns on the same
lower endpoint maps and append the two physical comparisons. -/
theorem compare_matched_retained_row_and_preparation {n : ℕ} (hn : 0 < n)
    {X X' A A' Z Z' : CMfd.{u} n}
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {N' : Set X'} {old' born' : List (Set X')} (g' : NativeRetainedGeometry N' old' born')
    (hN : N' = φ ⁻¹' N) (hOld : liveBorn old' = (liveBorn old).map (φ ⁻¹' ·))
    (hBorn : liveBorn born' = (liveBorn born).map (φ ⁻¹' ·))
    (j : Fin old.length) (j' : Fin old'.length)
    (hRow : old'.get j' = φ ⁻¹' old.get j)
    (hRest : liveBorn (old'.eraseIdx j'.val) = (liveBorn (old.eraseIdx j.val)).map (φ ⁻¹' ·))
    {R : BlowupTower X A} {R' : BlowupTower X' A'}
    (compareLower :
      let L := N ∩ (oldResidualPart N old born j).zeroLocus
      let L' := N' ∩ (oldResidualPart N' old' born' j').zeroLocus
      let F := old.eraseIdx j.val ++ born
      let F' := old'.eraseIdx j'.val ++ born'
      L' = φ ⁻¹' L → liveBorn F' = (liveBorn F).map (φ ⁻¹' ·) →
      ∃ β : A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A, EmptyAwareTowerIso φ R' R β)
    (hR : IsGeoTestTower (geometricTemplate N born) R)
    (hFullR : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) R)
    (hR' : IsGeoTestTower (geometricTemplate N' born') R')
    (hFullR' : IsGeoTestTower (geometricTemplate (univ : Set X') (old' ++ born')) R')
    {S : BlowupTower A Z} {S' : BlowupTower A' Z'} {μ μ' : WithTop RetainedStampRank}
    (prepare : let C := geoTransformAlong (geometricTemplate N born) R
      OrderedRetainedDefectTrace hn C.N (old.map (strictAlong R)) C.E μ S)
    (prepare' : let C' := geoTransformAlong (geometricTemplate N' born') R'
      OrderedRetainedDefectTrace hn C'.N (old'.map (strictAlong R')) C'.E μ' S') :
    ∃ χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      EmptyAwareTowerIso φ (R'.append S') (R.append S) χ := by
  obtain ⟨_,hL,hF⟩ := selected_lower_data_of_matched_old_rows hn φ g hN hBorn j j' hRow hRest
  obtain ⟨β,hβ⟩ := compareLower hL hF
  obtain ⟨hNextN,hNextOld,hNextBorn⟩ := retained_filtered_inputs_of_emptyAware g hN hOld hBorn hβ
  have hNext := actual_retained_born_recorded_residual_dictionary hn g.carrier g.full
    g.born_transverse g.dense R hR hFullR
  have hNext' := actual_retained_born_recorded_residual_dictionary hn g'.carrier g'.full
    g'.born_transverse g'.dense R' hR' hFullR'
  obtain ⟨χ,hχ⟩ := compare_aligned_filtered_ordered_retained_traces
    ⟨hNext.1,hNext.2.1,hNext.2.2.1,hNext.2.2.2.1⟩
    ⟨hNext'.1,hNext'.2.1,hNext'.2.2.1,hNext'.2.2.2.1⟩
    β hNextN hNextOld hNextBorn prepare' prepare
  exact ⟨χ,emptyAware_append hβ hχ⟩

/-- With the upper prefixes already matched over `φ`, the two literal
selected lower histories compare by the smaller-dimensional service.
Compare the actual retained re-preparation traces on their endpoints
and concatenate on those same physical towers. -/
theorem compare_selected_retained_row_and_preparation {n : ℕ} (hn : 0 < n)
    {X X' A A' Z Z' : CMfd.{u} n}
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {N' : Set X'} {old' born' : List (Set X')} (g' : NativeRetainedGeometry N' old' born')
    (hN : N' = φ ⁻¹' N) (hOld : old' = old.map (φ ⁻¹' ·))
    (hBorn : liveBorn born' = (liveBorn born).map (φ ⁻¹' ·))
    (j : Fin old.length) (j' : Fin old'.length) (hIndex : j'.val = j.val)
    {R : BlowupTower X A} {R' : BlowupTower X' A'}
    (compareLower :
      let L := N ∩ (oldResidualPart N old born j).zeroLocus
      let L' := N' ∩ (oldResidualPart N' old' born' j').zeroLocus
      let F := old.eraseIdx j.val ++ born
      let F' := old'.eraseIdx j'.val ++ born'
      L' = φ ⁻¹' L → liveBorn F' = (liveBorn F).map (φ ⁻¹' ·) →
      ∃ β : A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A, EmptyAwareTowerIso φ R' R β)
    (hR : IsGeoTestTower (geometricTemplate N born) R)
    (hFullR : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) R)
    (hR' : IsGeoTestTower (geometricTemplate N' born') R')
    (hFullR' : IsGeoTestTower (geometricTemplate (univ : Set X') (old' ++ born')) R')
    {S : BlowupTower A Z} {S' : BlowupTower A' Z'} {μ μ' : WithTop RetainedStampRank}
    (prepare : let C := geoTransformAlong (geometricTemplate N born) R
      OrderedRetainedDefectTrace hn C.N (old.map (strictAlong R)) C.E μ S)
    (prepare' : let C' := geoTransformAlong (geometricTemplate N' born') R'
      OrderedRetainedDefectTrace hn C'.N (old'.map (strictAlong R')) C'.E μ' S') :
    ∃ χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      EmptyAwareTowerIso φ (R'.append S') (R.append S) χ := by
  obtain ⟨hRow,hRest⟩ := matched_old_rows_of_literal φ hOld j j' hIndex
  have hOldLive : liveBorn old' = (liveBorn old).map (φ ⁻¹' ·) := by
    rw [hOld]
    exact HironakaG3EmptyAwareBornSlots.filter_map_bijection φ φ.surjective _
  exact compare_matched_retained_row_and_preparation hn φ g g' hN hOldLive hBorn j j' hRow hRest
    compareLower hR hFullR hR' hFullR' prepare prepare'

end
end Hironaka.HironakaG4SelectedRetainedRowOverlap
