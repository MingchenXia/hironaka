import Hironaka.Resolution.HironakaG8CompatibleLocalCentres
import Hironaka.Resolution.HironakaG8NativeHSOriginalInequivalence
import Hironaka.Resolution.HironakaResolutionSpaceLocal
set_option autoImplicit false
namespace Hironaka.HironakaG8CompatibleNativeFirstCentre
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  NormalCrossings HironakaEmbeddedAnalytic HironakaG11PresLineState
  HironakaG8NativeHSOriginalInequivalence HironakaEmbeddedBoundary HironakaResolutionSpaceLocal
  HironakaG8CompatibleLocalCentres
noncomputable section

/-- Compatible admissible native HS centres glue to an actual original
mark-one test blowup, with global centre in the actual singular set. -/
theorem compatible_native_initial_centres {n : ℕ} {X : CMfd.{0} n} {J : Type}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (hint : interior W = ∅)
    (U : J → Opens X) (Q : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (C : ∀ i, Set (U i)) (H : J → ℕ → ℕ)
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hcompat : ∀ (i j : J) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (⟨x,hi⟩ : U i) ∈ C i ↔ (⟨x,hj⟩ : U j) ∈ C j)
    (hE : ∀ i, (Q i).E = [])
    (hState : ∀ i, NativeHSState (Q i) ((Subtype.val : U i → X) ⁻¹' W) (H i))
    (hC : ∀ i, (Q i).IsAdmissibleCentre (C i)) :
    let P : MarkedIdeal n X := ⟨univ,[],vanishingIdeal (n := n) W,1⟩
    ∃ (Y : CMfd.{0} n) (π : Y → X) (hπ : IsBlowupAlong n (compatibleCentre U C) π),
      IsProperMap π ∧ IsGeoTestTower P (.step .refl (compatibleCentre U C) π hπ) ∧
      compatibleCentre U C ⊆ singularSet (n := n) W ∧
      ∀ i, (Subtype.val : U i → X) ⁻¹' compatibleCentre U C = C i := by
  let P : MarkedIdeal n X := ⟨univ,[],vanishingIdeal (n := n) W,1⟩
  have hP : ResolutionInvariantSpec.IsInvDomain n P :=
    isInvDomain_boundary hW hint isSNCDivisor_nil
  have hLocal : ∀ i, (MarkedIdeal.pullback (Subtype.val : U i → X) P).IsAdmissibleCentre (C i) := by
    intro i
    rw [show P = (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) from rfl,
      pullback_val_mk_vanishingIdeal]
    simp only [List.map_nil]
    refine ⟨(hC i).1, ?_, ?_⟩
    · rw [cosupp_mk_vanishingIdeal (hW.isClosed.preimage continuous_subtype_val) []]
      exact (hC i).2.1.trans ((native_hs_cosupp_subset_singular (Q i) (hState i)).trans (singularSet_subset _))
    · simpa only [hE i] using (hC i).2.2
  obtain ⟨Y,π,hπ,hproper,hAdm,hTrace⟩ := exists_blowup_compatibleCentre P hP U C hcover hcompat hLocal
  refine ⟨Y,π,hπ,hproper,⟨trivial,hAdm⟩,?_,hTrace⟩
  intro x hx
  obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
  have hs := native_hs_cosupp_subset_singular (Q i) (hState i) ((hC i).2.1 hy)
  rw [singularSet_preimage_val] at hs
  exact hs
end
end Hironaka.HironakaG8CompatibleNativeFirstCentre
