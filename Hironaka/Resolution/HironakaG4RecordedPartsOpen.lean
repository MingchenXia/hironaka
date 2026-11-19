import Hironaka.Resolution.HironakaActualProtectedOtherRowLocalStep

/-! The actual normalized old-member parts commute with open restriction. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4RecordedPartsOpen
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings NormalCrossingsComparison HironakaG4PreparedCentreCoordinates
  HironakaG4RecordedTowerResidualCompatibility HironakaG4LowerPreparedNeighborhood
  HironakaActualProtectedOtherRowLocalStep HironakaSharpActualAccumulatedTraceResidual
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualTraceIncidence HironakaSharpActualStrictTraceOpenNonmonomial
  MonomialPartEtale RelativePrincipalizationSpan RestrictedIdealExtension
  NonmonomialTransformAlong MonomialPartAlong DivisorExponentAlong MarkedIdeals
  BlowupRestrictOpen GermIdealPullbackCalculus DerivativeIdealAlongEtale

variable {n : ℕ} {X : CMfd.{u} n}

/-- For the actual normalized old-member ideal, both the born monomial part
and the residual part pull back exactly to any open source window. -/
theorem actual_old_parts_pullback_open (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X) (i : Fin old.length) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let IU := restrictOn n NU (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
    monomialPartAlong n NU IU bornU = GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (oldMonomialPart N old born i) ∧
    nonmonomialPartAlong n NU IU bornU = GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (oldResidualPart N old born i) := by
  have hOld := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
  obtain ⟨hcI,_hnzI,hcJ,_hnzJ,hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hIU := actual_normalized_trace_whole_open_pullback hN
    (MonomialPart.isClosedSubmanifold_get hn hOld i) U
  dsimp only
  rw [hIU]
  exact ⟨(pullback_monomialPartAlong
    (fun y : U => ⟨openInv U y,isLocalInverseAt_val U y⟩)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcI hg)).symm,
    (pullback_nonmonomialPartAlong
      (fun y : U => ⟨openInv U y,isLocalInverseAt_val U y⟩) hcI hcD hcJ).symm⟩

end
end Hironaka.HironakaG4RecordedPartsOpen
