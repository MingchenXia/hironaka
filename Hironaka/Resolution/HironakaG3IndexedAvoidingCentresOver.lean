import Hironaka.Resolution.HironakaG3IndexedAvoidingBoundaryClass
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedAvoidingCentresOver
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaActualLocallyFiniteBoundary
  HironakaG3RTowerClass HironakaG3RBoundaryEmbedded HironakaG3OrderedFiniteWindows
  HironakaG3IndexedAvoidingBoundaryClass HironakaAdmissibleSequence HironakaFromSeqInvariant
  RestrictEmptyTower EmbeddedFromResolution CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain)

theorem indexed_avoiding_centres_over {n : ℕ} {X : CMfd.{0} n} {ι : Type*} [LinearOrder ι]
    (C : Set X) (D : ι → Set X) (hCa : IsComplexAnalyticSubset (n := n) C)
    (hD : IsLocallyFiniteSNCDivisor n D) {r : ℕ} (hr : r < n)
    (hpure : C ⊆ closure (regularLocus (n := n) C r))
    (U : Opens X) (Y : CMfd.{0} n) (A : BlowupTower (CMfd.of (n := n) U) Y)
    (hA : indexedAvoidingBoundaryClass C r D U Y A) :
    CentresOver ((Subtype.val : U → X) ⁻¹' C) A := by
  obtain ⟨R,hVis,hStop⟩ := hA
  let E := (R.sort (· ≤ ·)).map D
  let M : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) C,1⟩
  have hdom : IsInvDomain n M := isInvDomain_bdry hCa hr hpure (sorted_boundary_snc D hD R)
  have hdom₀ := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)
  have hT := hF.isGeoTestTower_of_isCanonical hdom₀ A hStop.1
  have hOver := centresOver_cosupp (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M)
    hdom₀.isWellFormed.isClosedSubmanifold_N hdom₀.isWellFormed.isCoherent A hT
  have hC₀ : IsClosed ((Subtype.val : U → X) ⁻¹' C) := hCa.isClosed.preimage continuous_subtype_val
  have hEq := HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal U E C
  change CentresOver (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M).cosupp A at hOver
  rw [show MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M = _ from hEq,
    HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hC₀] at hOver
  exact hOver
end
end Hironaka.HironakaG3IndexedAvoidingCentresOver
