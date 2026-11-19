import Hironaka.Resolution.HironakaG3IndexedProperContactWindow
import Hironaka.Resolution.HironakaG3ResidualFixedHeadsOverlap
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedResidualFixedHeadClass
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MaxLocusLocal NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3IndexedContainingBoundary
  HironakaG3IndexedCanonicalContact HironakaG3OrderedFiniteWindows HironakaG3FixedContactHeadClass
  HironakaG3IndexedProperContactWindow HironakaG3ResidualFixedHeadsOverlap HironakaG3EmptyAwareHistory
  HironakaOriginalTerminalOverlapComparison

/-- A fixed-contact head for a finite residual window containing all residual
labels visible in its ambient base. -/
def residualFixedHead {d t : ℕ} {X : CMfd.{0} (d+t)} {ι : Type*} [LinearOrder ι]
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (C : Set X) (r : ℕ) (D : ι → Set X) (S : Finset ι) : LocalTowerClass X :=
  fun U Y A => ∃ R : Finset ι, Disjoint S R ∧
    (∀ i, i ∉ S → (D i ∩ (U : Set X)).Nonempty → i ∈ R) ∧
    fixedContactHead N hNc hN ((R.sort (· ≤ ·)).map D) C r U Y A

/-- The physical empty-aware comparison of actual indexed residual heads. -/
theorem canonical_residualFixedHead_physical_overlap {d t : ℕ} (hd : 0 < d) {X : CMfd.{0} (d+t)}
    {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := d+t) C) (hD : IsLocallyFiniteSNCDivisor (d+t) D)
    {r : ℕ} (hr : r < d) (hpure : C ⊆ closure (regularLocus (n := d+t) C r))
    (hNc : IsClosed (canonicalContact C D hC.nonempty hD.1))
    (hN : ∀ x ∈ canonicalContact C D hC.nonempty hD.1,
      RegularAtDim (n := d+t) (canonicalContact C D hC.nonempty hD.1) x d) :
    ∀ (U₁ U₂ : Opens X) (Y₁ Y₂ : CMfd.{0} (d+t))
      (A₁ : BlowupTower (CMfd.of (n := d+t) U₁) Y₁) (A₂ : BlowupTower (CMfd.of (n := d+t) U₂) Y₂),
      residualFixedHead (canonicalContact C D hC.nonempty hD.1) hNc hN C r D
        (containingLabels C D hC.nonempty hD.1) U₁ Y₁ A₁ →
      residualFixedHead (canonicalContact C D hC.nonempty hD.1) hNc hN C r D
        (containingLabels C D hC.nonempty hD.1) U₂ Y₂ A₂ →
      ∃ β : CMfd.of (n := d+t) (openPreimage A₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯
          CMfd.of (n := d+t) (openPreimage A₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
        EmptyAwareTowerIso (overlapBaseEquiv (n := d+t) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
          (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) A₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) A₂) β := by
  let S := containingLabels C D hC.nonempty hD.1
  let N := canonicalContact C D hC.nonempty hD.1
  have hCN : C ⊆ N := (canonicalContact_geometry C D hC hD).1
  have hAvoidR (R : Finset ι) (hDis : Disjoint S R) :
      C ⊆ closure (C \ ⋃ H ∈ (R.sort (· ≤ ·)).map D, H) := by
    apply (dense_off_residual_family C D hC hD).trans
    apply closure_mono
    rintro x ⟨hxC,hxOut⟩
    refine ⟨hxC,?_⟩
    intro hxB
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    have hiR : i ∈ R := by simpa using hi
    have hiS : i ∉ S := fun hiS => (Finset.disjoint_left.mp hDis) hiS hiR
    exact hxOut (mem_iUnion.mpr ⟨⟨i,hiS⟩,hxH⟩)
  intro U₁ U₂ Y₁ Y₂ A₁ A₂ h₁ h₂
  obtain ⟨R₁,hD₁,hVis₁,hHead₁⟩ := h₁
  obtain ⟨R₂,hD₂,hVis₂,hHead₂⟩ := h₂
  obtain ⟨β,hβ⟩ := fixed_heads_residual_overlap hd N hNc hN C hC.analytic hCN hr hpure D hD.2.1 S R₁ R₂
    hD₁ hD₂ (sorted_boundary_snc D hD R₁) (sorted_boundary_snc D hD R₂)
    (isTransverse_residual_window C D hC hD R₁ hD₁) (isTransverse_residual_window C D hC hD R₂ hD₂)
    (hAvoidR R₁ hD₁) (hAvoidR R₂ hD₂) U₁ U₂ hVis₁ hVis₂ A₁ A₂ hHead₁ hHead₂
  exact ⟨β,hβ⟩

/-- Actual indexed residual heads compare on literal overlaps. -/
theorem canonical_residualFixedHead_comparisons {d t : ℕ} (hd : 0 < d) {X : CMfd.{0} (d+t)}
    {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := d+t) C) (hD : IsLocallyFiniteSNCDivisor (d+t) D)
    {r : ℕ} (hr : r < d) (hpure : C ⊆ closure (regularLocus (n := d+t) C r))
    (hNc : IsClosed (canonicalContact C D hC.nonempty hD.1))
    (hN : ∀ x ∈ canonicalContact C D hC.nonempty hD.1,
      RegularAtDim (n := d+t) (canonicalContact C D hC.nonempty hD.1) x d) :
    HasComparisons (residualFixedHead (canonicalContact C D hC.nonempty hD.1) hNc hN C r D
      (containingLabels C D hC.nonempty hD.1)) := by
  intro U₁ U₂ Y₁ Y₂ A₁ A₂ h₁ h₂
  obtain ⟨β,hβ⟩ := canonical_residualFixedHead_physical_overlap hd C D hC hD hr hpure hNc hN U₁ U₂ Y₁ Y₂ A₁ A₂ h₁ h₂
  refine ⟨β,?_⟩
  intro y
  have hz := congrArg (fun q : nestedOpens U₂ (U₁ ⊓ U₂) => q.val.val) (emptyAware_proj_comm hβ y)
  rw [overlapBaseEquiv_point] at hz
  have htproj := congrArg (fun q : U₂ => q.val)
    (proj_restrict (nestedOpens U₂ (U₁ ⊓ U₂)) A₂ (β y))
  have hsproj := congrArg (fun q : U₁ => q.val)
    (proj_restrict (nestedOpens U₁ (U₁ ⊓ U₂)) A₁ y)
  exact htproj.symm.trans (hz.trans hsproj)

/-- Compact-enclosed windows produce a cover for the indexed residual class. -/
theorem canonical_residualFixedHead_covers {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X : CMfd.{0} (d+t)} {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := d+t) C) (hD : IsLocallyFiniteSNCDivisor (d+t) D)
    (hS : (containingLabels C D hC.nonempty hD.1).card = t)
    {r : ℕ} (hr : r < d) (hpure : C ⊆ closure (regularLocus (n := d+t) C r))
    (hNc : IsClosed (canonicalContact C D hC.nonempty hD.1))
    (hN : ∀ x ∈ canonicalContact C D hC.nonempty hD.1,
      RegularAtDim (n := d+t) (canonicalContact C D hC.nonempty hD.1) x d) :
    Covers (residualFixedHead (canonicalContact C D hC.nonempty hD.1) hNc hN C r D
      (containingLabels C D hC.nonempty hD.1)) := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel (d+t)) X
  intro x
  obtain ⟨K,hK,hxK⟩ := exists_compact_mem_nhds x
  let U : Opens X := ⟨interior K,isOpen_interior⟩
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr hxK
  obtain ⟨hNc',hN',R,Y,A,hDis,hVis,hHead⟩ :=
    indexed_proper_contact_head_over_compact_window hd ht C D hC hD hS hr hpure U K hK interior_subset
  exact ⟨U,hxU,Y,A,R,hDis,hVis,hHead⟩

/-- One proper map is glued from all actual residual-window heads. -/
theorem exists_glued_canonical_residual_heads {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X : CMfd.{0} (d+t)} {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := d+t) C) (hD : IsLocallyFiniteSNCDivisor (d+t) D)
    (hS : (containingLabels C D hC.nonempty hD.1).card = t)
    {r : ℕ} (hr : r < d) (hpure : C ⊆ closure (regularLocus (n := d+t) C r))
    (hNc : IsClosed (canonicalContact C D hC.nonempty hD.1))
    (hN : ∀ x ∈ canonicalContact C D hC.nonempty hD.1,
      RegularAtDim (n := d+t) (canonicalContact C D hC.nonempty hD.1) x d) :
    ∃ (Z : CMfd.{0} (d+t)) (P : Z → X),
      IsGluedFrom (residualFixedHead (canonicalContact C D hC.nonempty hD.1) hNc hN C r D
        (containingLabels C D hC.nonempty hD.1)) Z P :=
  exists_isGluedFrom (canonical_residualFixedHead_covers hd ht C D hC hD hS hr hpure hNc hN)
    (canonical_residualFixedHead_comparisons hd C D hC hD hr hpure hNc hN)
end
end Hironaka.HironakaG3IndexedResidualFixedHeadClass
