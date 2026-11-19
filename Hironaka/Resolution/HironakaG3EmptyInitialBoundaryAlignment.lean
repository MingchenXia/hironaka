import Hironaka.Resolution.HironakaG3BiholomorphicFirstMeeting
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison

/-!
# Actual stopped-history alignment across empty initial boundary slots

Filtering initial empty boundary positions preserves the stopped predicate
on the same physical tower. Actual whole-record pullback identities and
filtered-boundary agreement therefore reduce to the existing structural
stopped comparison. Nonempty centres and actual prefix commutation remain
in the resulting `EmptyAwareTowerIso`; no endpoint isomorphism is promoted
to an ambient-history comparison.

Blueprint: `hironaka-g3-empty-initial-boundary-alignment.tex`.
-/

set_option autoImplicit false

open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG3EmptyInitialBoundaryAlignment

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms
  HironakaG3RStoppedOverlap HironakaG3BiholomorphicFirstMeeting
  HironakaG3EmptyAwareHistory HironakaOriginalBoundaryEmptyBaseComparison
  HironakaOriginalBoundaryEmptyFilterComparison

open ResolutionInvariantSpec (IsInvDomain)

/-- Filtering original empty slots preserves stoppedness of the unchanged
actual finite history and the unchanged avoided open. -/
theorem isStopped_nonemptyBoundary_iff {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (O : Opens X) (T : BlowupTower X Y) :
    IsStopped (nonemptyBoundary M) O T ↔ IsStopped M O T := by
  unfold IsStopped
  rw [isCanonical_nonemptyBoundary_iff,cosupp_nonemptyBoundary_along,
    maxLocus_nonemptyBoundary,isGeoResolution_nonemptyBoundary_iff]

private theorem nonemptyBoundary_eq_pullback {n : ℕ} {X X' : CMfd.{0} n}
    (M : MarkedIdeal n X) (M' : MarkedIdeal n X')
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (hN : M'.N = Φ ⁻¹' M.N) (hI : M'.ideal = GermIdeal.pullback (m := n) Φ M.ideal)
    (hd : M'.d = M.d)
    (hE : M'.E.filter (fun H => decide H.Nonempty) =
      (M.E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty)) :
    nonemptyBoundary M' = MarkedIdeal.pullback Φ (nonemptyBoundary M) := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact hN
  · change M'.E.filter (fun H => decide H.Nonempty) =
      (M.E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·)
    have hpred : ((fun H : Set X' => decide H.Nonempty) ∘ (fun H : Set X => Φ ⁻¹' H)) =
        (fun H : Set X => decide H.Nonempty) := by
      funext H
      have hh : (Φ ⁻¹' H).Nonempty ↔ H.Nonempty :=
        ⟨fun ⟨x,hx⟩ => ⟨Φ x,hx⟩,fun h => h.preimage Φ.surjective⟩
      simp only [Function.comp_apply,hh]
    rw [hE,List.filter_map,hpred]
  · exact hI
  · exact hd

/-- Actual stopped canonical histories over a base biholomorphism admit a
structural empty-aware comparison when only original empty slots differ. -/
theorem stopped_emptyAware_over_base_across_empty_initial_boundaries
    {n : ℕ} (hn : 0 < n) {X X' Y Y' : CMfd.{0} n}
    (M : MarkedIdeal n X) (M' : MarkedIdeal n X') (hM : IsInvDomain n M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (hN : M'.N = Φ ⁻¹' M.N) (hI : M'.ideal = GermIdeal.pullback (m := n) Φ M.ideal)
    (hd : M'.d = M.d)
    (hE : M'.E.filter (fun H => decide H.Nonempty) =
      (M.E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty))
    (O : Opens X) (hcases : (M.cosupp ∩ O).Nonempty ∨ M.cosupp = ∅)
    (S : BlowupTower X' Y') (T : BlowupTower X Y)
    (hS : IsStopped M' (baseOpen Φ O) S) (hT : IsStopped M O T) :
    ∃ ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      EmptyAwareTowerIso Φ S T ψ := by
  have heq := nonemptyBoundary_eq_pullback M M' Φ hN hI hd hE
  have hSf := (isStopped_nonemptyBoundary_iff M' (baseOpen Φ O) S).mpr hS
  have hTf := (isStopped_nonemptyBoundary_iff M O T).mpr hT
  rw [heq] at hSf
  have hcos : (nonemptyBoundary M).cosupp = M.cosupp := by
    simpa only [geoTransformAlong_refl] using
      cosupp_nonemptyBoundary_along M (.refl : BlowupTower X X)
  have hcasesf : ((nonemptyBoundary M).cosupp ∩ O).Nonempty ∨
      (nonemptyBoundary M).cosupp = ∅ := by
    rwa [hcos]
  exact stopped_emptyAware_over_base hn (nonemptyBoundary M)
    (isInvDomain_nonemptyBoundary M hM) Φ O hcasesf S T hSf hTf

end

end Hironaka.HironakaG3EmptyInitialBoundaryAlignment
