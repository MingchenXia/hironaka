import Hironaka.Resolution.HironakaG3FixedContactHeadClass
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaEmbeddedBoundary
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3FixedHeadTargetFootprint
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaG3RTowerClass HironakaG3FixedContactHeadClass
  HironakaAdmissibleSequence RestrictEmptyTower HironakaEmbeddedBoundary

/-- Every actual centre of a fixed-contact head maps into the original
target, irrespective of how many boundary members contain it. -/
theorem fixed_head_centres_over_target {d t : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W)
    (r : ℕ) (U : Opens X) (Y : CMfd.{0} (d+t))
    (A : BlowupTower (CMfd.of (n := d+t) U) Y) (hHead : fixedContactHead N hNc hN B W r U Y A) :
    CentresOver ((Subtype.val : U → X) ⁻¹' W) A := by
  obtain ⟨R,T,η,hM,hT,hTest,hC,hStop⟩ := hHead
  let Bx := B.map ((Subtype.val : U → X) ⁻¹' ·)
  let Jx := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) (vanishingIdeal (n := d+t) W)
  let Mx := fullMarked Bx Jx
  have hJ : Jx.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
    (CartanIrreducible.cartanCoherence _ hWa)
  have hCos : Mx.cosupp = (Subtype.val : U → X) ⁻¹' W := by
    dsimp [Mx,fullMarked,Jx]
    rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal]
    exact cosupp_mk_vanishingIdeal (hWa.isClosed.preimage continuous_subtype_val) Bx
  have hOver := centresOver_cosupp Mx HomogenizedGlueingTower.isClosedSubmanifold_univ hJ A hTest
  rwa [hCos] at hOver
end
end Hironaka.HironakaG3FixedHeadTargetFootprint
