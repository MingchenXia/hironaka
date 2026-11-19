import Hironaka.Resolution.HironakaG3BoundaryContainedOriginalInputs
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BoundaryContainedOriginalGlobalLift
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeReferenceWindow HironakaDisjointNativeOpenLift
  HironakaDisjointFiniteControlledHistory HironakaG3RStoppedOverlap HironakaG3RBoundaryEmbedded
  HironakaG3BoundaryContainedOriginalInputs HironakaG3BoundaryContainedGlobalLift
open ResolutionInvariantSpec (IsInvDomain)

/-- Original analytic data in one smooth containing contact construct and
glue the actual stopped ambient lifts. -/
theorem original_contained_global_lift
    {d t : ℕ} (hd : 0 < d) (ht : 0 < t) {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (V : Set (nativeManifold (Nat.le_add_right d t) N hN))
      (_hVa : IsComplexAnalyticSubset (n := d) V)
      (_hWa : IsComplexAnalyticSubset (n := d+t) ((Subtype.val : N → X) '' V))
      {r : ℕ} (_hr : r < d) (_hpure : V ⊆ closure (regularLocus (n := d) V r))
      (_hAvoid : V ⊆ closure (V \ ⋃ H ∈ B.map ((Subtype.val : N → X) ⁻¹' ·), H)),
    let J := vanishingIdeal (n := d+t) ((Subtype.val : N → X) '' V)
    let O := bdryOpen V r (B.map ((Subtype.val : N → X) ⁻¹' ·))
    ∃ (U : X → Opens X) (Y : X → CMfd.{0} (d+t))
      (A : ∀ x, BlowupTower (CMfd.of (n := d+t) (U x)) (Y x))
      (Z : CMfd.{0} (d+t)) (P : Z → X),
      (∀ x, x ∈ U x) ∧ ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ P ∧
      IsProperMap P ∧ Surjective P ∧
      (∀ x,
        letI := chartedSpace (Nat.le_add_right d t) (openSection_regular hN (U x))
        letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) (openSection_regular hN (U x))
        ∃ (R : CMfd.{0} d)
          (T : BlowupTower (nativeManifold (Nat.le_add_right d t) (openSection N (U x))
            (openSection_regular hN (U x))) R) (η : R → Y x),
          let Jx := GermIdeal.pullback (m := d+t) (Subtype.val : U x → X) J
          let Bx := B.map ((Subtype.val : U x → X) ⁻¹' ·)
          let Mx := fullMarked (Bx.map ((Subtype.val : openSection N (U x) → U x) ⁻¹' ·))
            (GermIdeal.pullback (m := d) (Subtype.val : openSection N (U x) → U x) Jx)
          IsInvDomain d Mx ∧ IsGeoTestTower Mx T ∧ IsGeoTestTower (fullMarked Bx Jx) (A x) ∧
          CoupledHistory (openSection N (U x)) Bx Jx (Subtype.val : openSection N (U x) → U x) Mx T (A x) η ∧
          HironakaG3RStoppedOverlap.stoppedClass
            (⟨univ, B.map ((Subtype.val : N → X) ⁻¹' ·), vanishingIdeal (n := d) V, 1⟩ :
              MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) O
            (nativeWindow (Nat.le_add_right d t) N hN (U x)) _
            (MarkedIdealTowerTransport.transport (windowEquiv (Nat.le_add_right d t) N hN hNc (U x)).symm T).tower) ∧
      ∀ x, ∃ W : Opens Z, (W : Set Z) = P ⁻¹' (U x : Set X) ∧
        ∃ φ : Y x ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ CMfd.of (n := d+t) W,
          ∀ y, P (φ y : Z) = (((A x).proj y : U x) : X) := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro V hVa hWa r hr hpure hAvoid
  dsimp only
  obtain ⟨hJ,hNorm,hTrace,hdom,hEO,hreg,hdense⟩ :=
    original_contained_input_data hd N hNc hN B hB hTrans V hVa hWa hr hpure hAvoid
  exact exists_global_stopped_contact_lift hd ht N hNc hN B hB hTrans _ hJ hNorm
    V hVa.isClosed hTrace hdom _ hEO hreg hdense

end
end Hironaka.HironakaG3BoundaryContainedOriginalGlobalLift
