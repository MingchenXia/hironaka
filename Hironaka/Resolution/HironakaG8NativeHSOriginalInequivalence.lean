import Hironaka.Resolution.HironakaActualHistoricalOriginalSingularReference
import Hironaka.Resolution.HironakaG8NativeHSOriginalTestBridge
import Hironaka.Resolution.HironakaG8LocalHistory
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8NativeHSOriginalInequivalence
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG11PresLineState HironakaG11PresTowerState
  HironakaG8LocalHistory HomogenizedGlueingTower

/-- An actual native singular-HS state has cosupport in the singular locus. -/
theorem native_hs_cosupp_subset_singular {n : ℕ} {X : CMfd.{0} n}
    (Q : MarkedIdeal n X) {W : Set X} {H : ℕ → ℕ} (h : NativeHSState Q W H) :
    Q.cosupp ⊆ singularSet (n := n) W := by
  obtain ⟨m,X₀,W₀,a₀,hW₀,ha₀,hH⟩ := h.1
  rw [h.cosupp_eq, ← hH]
  exact HironakaActualHistoricalOriginalSingularReference.actual_original_singular_profile_locus_subset_current_singular W₀ hW₀ a₀ ha₀ W h.2.1

/-- For a nonempty analytic set, the native singular-HS record cannot be
weak-projection equivalent to its original mark-one vanishing record. -/
theorem native_hs_not_locWPEquiv_original {n : ℕ} {X : CMfd.{0} n}
    (Q : MarkedIdeal n X) {W : Set X} {H : ℕ → ℕ}
    (hW : IsComplexAnalyticSubset (n := n) W) (hne : W.Nonempty)
    (h : NativeHSState Q W H) :
    ¬ LocWPEquiv Q (⟨univ,Q.E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) := by
  have hdense := HironakaResolutionSpace.subset_closure_diff_singularSet hW
  have hreg : (W \ singularSet (n := n) W).Nonempty := by
    by_contra hnone
    have he : W \ singularSet (n := n) W = ∅ := Set.not_nonempty_iff_eq_empty.mp hnone
    obtain ⟨x,hx⟩ := hne
    have hx' := hdense hx
    rw [he, closure_empty] at hx'
    exact hx'
  obtain ⟨x,hxW,hxS⟩ := hreg
  intro hEq
  have heq := hEq.cosupp_eq_base
  have hcos : (⟨univ,Q.E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).cosupp = W :=
    HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW.isClosed Q.E
  have hxQ : x ∈ Q.cosupp := by rw [heq,hcos]; exact hxW
  exact hxS (native_hs_cosupp_subset_singular Q h hxQ)
end
end Hironaka.HironakaG8NativeHSOriginalInequivalence
