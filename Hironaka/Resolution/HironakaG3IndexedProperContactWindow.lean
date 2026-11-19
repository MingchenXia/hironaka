import Hironaka.Resolution.HironakaG3FixedHeadCompactWindow
import Hironaka.Resolution.HironakaG3IndexedCanonicalContact
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedProperContactWindow
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary
  HironakaG3IndexedCanonicalContact HironakaG3OrderedFiniteWindows
  HironakaG3FixedContactHeadClass HironakaG3FixedHeadCompactWindow

/-- Every compact-enclosed ambient window has an actual fixed-contact head
using a finite residual boundary window containing all visible residual labels. -/
theorem indexed_proper_contact_head_over_compact_window {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X : CMfd.{0} (d+t)} {ι : Type*} [LinearOrder ι]
    (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := d+t) C)
    (hD : IsLocallyFiniteSNCDivisor (d+t) D)
    (hS : (containingLabels C D hC.nonempty hD.1).card = t)
    {r : ℕ} (hr : r < d) (hpure : C ⊆ closure (regularLocus (n := d+t) C r))
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    let S := containingLabels C D hC.nonempty hD.1
    let N := canonicalContact C D hC.nonempty hD.1
    ∃ (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
      (R : Finset ι) (Y : CMfd.{0} (d+t)) (A : BlowupTower (CMfd.of (n := d+t) U) Y),
      Disjoint S R ∧
      (∀ i, i ∉ S → (D i ∩ (U : Set X)).Nonempty → i ∈ R) ∧
      fixedContactHead N hNc hN ((R.sort (· ≤ ·)).map D) C r U Y A := by
  let S := containingLabels C D hC.nonempty hD.1
  let N := canonicalContact C D hC.nonempty hD.1
  have hGeo := canonicalContact_geometry C D hC hD
  change C ⊆ N ∧ N.Nonempty ∧ IsClosed N ∧
    (∀ x ∈ N, RegularAtDim (n := d+t) N x (d+t - S.card)) ∧ S.card ≤ d+t ∧
    IsClosedSubmanifold (d+t) N at hGeo
  have hNc : IsClosed N := hGeo.2.2.1
  have hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d := by
    have heq : d+t - S.card = d := by
      change (containingLabels C D hC.nonempty hD.1).card = t at hS
      dsimp [S]
      omega
    simpa only [heq] using hGeo.2.2.2.1
  let T := (hD.1.finite_nonempty_inter_compact hK).toFinset
  let R := T \ S
  have hDis : Disjoint S R := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiR
    exact (Finset.mem_sdiff.mp hiR).2 hiS
  have hVis : ∀ i, i ∉ S → (D i ∩ (U : Set X)).Nonempty → i ∈ R := by
    intro i hiS hiU
    apply Finset.mem_sdiff.mpr
    refine ⟨?_,hiS⟩
    apply (hD.1.finite_nonempty_inter_compact hK).mem_toFinset.mpr
    obtain ⟨x,hxD,hxU⟩ := hiU
    exact ⟨x,hxD,hUK hxU⟩
  have hB := sorted_boundary_snc D hD R
  have hTrans := isTransverse_residual_window C D hC hD R hDis
  have hAvoid : C ⊆ closure (C \ ⋃ H ∈ (R.sort (· ≤ ·)).map D, H) := by
    apply (dense_off_residual_family C D hC hD).trans
    apply closure_mono
    rintro x ⟨hxC,hxOut⟩
    refine ⟨hxC,?_⟩
    intro hxB
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    have hiR : i ∈ R := by simpa using hi
    have hiS : i ∉ S := (Finset.mem_sdiff.mp hiR).2
    exact hxOut (mem_iUnion.mpr ⟨⟨i,hiS⟩,hxH⟩)
  obtain ⟨Y,A,hA⟩ := fixed_head_over_relatively_compact_window hd ht N hNc hN
    ((R.sort (· ≤ ·)).map D) hB hTrans C hC.analytic hGeo.1 hr hpure hAvoid U K hK hUK
  exact ⟨hNc,hN,R,Y,A,hDis,hVis,hA⟩
end
end Hironaka.HironakaG3IndexedProperContactWindow
