import Hironaka.Resolution.HironakaG3DenseEscape
import Hironaka.Resolution.HironakaG11ExceptionalDivisibilityGeometry

set_option autoImplicit false

/-!
# A dense escaping born trace through an avoiding history

For a well-formed marked ideal, the strict transform of a carrier/boundary
intersection is the intersection of the transformed carrier and strict
boundary. If that intersection initially has dense complement of a closed
old member and later centres avoid its complement, the same density persists
at every later point. A listed strict old member then prevents order-one
exceptional-term divisibility along the transformed boundary.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11HistoryDenseEscape

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  BoundaryCount DivisorExponentAlong GermIdealOrder HironakaG11InvBMLower
  HironakaG8SuccExponents HironakaG3DenseEscape MemberInterTowerAlong

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n}

/-- An initial trace escaping a closed old member continues to rule out
exceptional-term divisibility along that trace's boundary through every
later test tower whose centres avoid the complement of the old member. -/
theorem not_isDivNearAlong_exceptionalTerm_of_avoiding_history
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (i : Fin M.E.length)
    (H : Set X) (hH : IsClosed H)
    (hDense : M.N ∩ M.E.get i ⊆ closure ((M.N ∩ M.E.get i) \ H))
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hAvoid : RestrictEmptyTower.CentresAvoid ⟨Hᶜ, hH.isOpen_compl⟩ T)
    {S : List (Set Y)} (hS : ∀ K ∈ S, IsClosed K)
    (hmem : strictAlong T H ∈ S) (e : ℕ) {y : Y}
    (hy : y ∈ (geoTransformAlong M T).N ∩ strictAlong T (M.E.get i)) :
    ¬ IsDivNearAlong n (geoTransformAlong M T).N (exceptionalTermBM (n := n) S e)
      (strictAlong T (M.E.get i)) 1 y := by
  classical
  have hA : IsClosed (M.N ∩ M.E.get i) :=
    hM.isClosedSubmanifold_N.1.inter (hM.isSNCDivisor.1 _ (List.get_mem _ _))
  have htrace : strictAlong T (M.N ∩ M.E.get i) =
      (geoTransformAlong M T).N ∩ strictAlong T (M.E.get i) := by
    simpa [BoundaryCount.memberInter] using
      (strictAlong_inter_memberInter M hM ({i} : Finset (Fin M.E.length)) T hT)
  have hdense := strictAlong_subset_closure_diff_of_centresAvoid
    (M.N ∩ M.E.get i) H hA hH hDense T hAvoid
  rw [htrace] at hdense
  have hcl := hdense hy
  intro hdiv
  obtain ⟨q, hqdiv, ⟨⟨hqN, hqD⟩, hqH⟩⟩ := (mem_closure_iff_nhds.mp hcl) _ hdiv
  have hqCos := hqdiv hqN hqD
  exact hqH (mem_of_mem_cosupport_one_exceptionalTermBM (Y := Y) (S := S) (e := e) hS hqCos _ hmem)

end

end Hironaka.HironakaG11HistoryDenseEscape
