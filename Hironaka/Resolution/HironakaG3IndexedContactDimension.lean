import Hironaka.Resolution.HironakaG3IndexedCanonicalContact
import Hironaka.Resolution.HironakaG3ContactDimensionBound
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedContactDimension
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary
  HironakaG3IndexedCanonicalContact HironakaG3ContactDimensionBound

/-- The original irreducible component's pure dimension is bounded by the
actual canonical indexed containing-contact dimension. -/
theorem indexed_component_dimension_le_contact {n r : ℕ} {X : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hpure : C ⊆ closure (regularLocus (n := n) C r)) :
    r ≤ n - (containingLabels C D hC.nonempty hD.1).card := by
  let S := containingLabels C D hC.nonempty hD.1
  let N := canonicalContact C D hC.nonempty hD.1
  have hGeo := canonicalContact_geometry C D hC hD
  change C ⊆ N ∧ N.Nonempty ∧ IsClosed N ∧
    (∀ x ∈ N, RegularAtDim (n := n) N x (n - S.card)) ∧ S.card ≤ n ∧
    IsClosedSubmanifold n N at hGeo
  obtain ⟨hCN,hNe,hNc,hN,hCard,hSm⟩ := hGeo
  generalize hs : S.card = t at hN hCard ⊢
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hCard
  have hn : n = d + t := by omega
  clear hd hCard
  subst n
  have hN' : ∀ x ∈ N, RegularAtDim (n := d+t) N x d := by simpa using hN
  have hr := target_dimension_le_contact N hNc hN' C hC.nonempty hCN hpure
  simpa using hr
end
end Hironaka.HironakaG3IndexedContactDimension
