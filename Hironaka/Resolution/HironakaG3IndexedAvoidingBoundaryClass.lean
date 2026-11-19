import Hironaka.Resolution.HironakaG3ResidualStoppedOverlapFinite
import Hironaka.Resolution.HironakaG3IndexedCanonicalContact
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedAvoidingBoundaryClass
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MaxLocusLocal NormalCrossings HironakaActualLocallyFiniteBoundary
  HironakaG3RTowerClass HironakaG3RBoundaryEmbedded HironakaG3IndexedContainingBoundary
  HironakaG3IndexedCanonicalContact HironakaG3OrderedFiniteWindows HironakaG3ResidualStoppedOverlapFinite
  HironakaG3EmptyAwareHistory HironakaOriginalTerminalOverlapComparison
  HironakaFromSeqInvariant HironakaRelativelyCompact EmbeddedFromResolution CanonicalCentres RestrictEmptyTower

/-- Actual boundary-relative stopped histories for finite visible indexed windows. -/
def indexedAvoidingBoundaryClass {n : ℕ} {X : CMfd.{0} n} {ι : Type*} [LinearOrder ι]
    (C : Set X) (r : ℕ) (D : ι → Set X) : LocalTowerClass X :=
  fun U Y A => ∃ R : Finset ι,
    (∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ R) ∧
    bdryClass C r ((R.sort (· ≤ ·)).map D) U Y A

/-- Physical empty-aware overlap of actual indexed avoiding histories. -/
theorem indexed_avoiding_boundary_physical_overlap {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : containingLabels C D hC.nonempty hD.1 = ∅)
    {r : ℕ} (hr : r < n) (hpure : C ⊆ closure (regularLocus (n := n) C r)) :
    ∀ (U₁ U₂ : Opens X) (Y₁ Y₂ : CMfd.{0} n)
      (A₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (A₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂),
      indexedAvoidingBoundaryClass C r D U₁ Y₁ A₁ → indexedAvoidingBoundaryClass C r D U₂ Y₂ A₂ →
      ∃ β : CMfd.of (n := n) (openPreimage A₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage A₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
        EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
          (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) A₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) A₂) β := by
  have hAvoidR (R : Finset ι) : C ⊆ closure (C \ ⋃ H ∈ (R.sort (· ≤ ·)).map D, H) := by
    apply (dense_off_residual_family C D hC hD).trans
    apply closure_mono
    rintro x ⟨hxC,hxOut⟩
    refine ⟨hxC,?_⟩
    intro hxB
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    have hiS : i ∉ containingLabels C D hC.nonempty hD.1 := by rw [hS]; simp
    exact hxOut (mem_iUnion.mpr ⟨⟨i,hiS⟩,hxH⟩)
  intro U₁ U₂ Y₁ Y₂ A₁ A₂ h₁ h₂
  obtain ⟨R₁,hVis₁,hHead₁⟩ := h₁
  obtain ⟨R₂,hVis₂,hHead₂⟩ := h₂
  have hn : 0 < n := by omega
  obtain ⟨β,hβ⟩ := residual_stopped_histories_overlap_of_window_avoid hn C hC.analytic hr hpure D hD.2.1
    ∅ R₁ R₂ (by simp) (by simp)
    (sorted_boundary_snc D hD R₁) (sorted_boundary_snc D hD R₂) (hAvoidR R₁) (hAvoidR R₂)
    U₁ U₂ (fun i _ => hVis₁ i) (fun i _ => hVis₂ i) A₁ A₂ hHead₁ hHead₂
  exact ⟨β,hβ⟩

/-- If no original boundary member contains the irreducible target, its
finite visible-window stopped histories compare on actual overlaps. -/
theorem indexed_avoiding_boundary_comparisons {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : containingLabels C D hC.nonempty hD.1 = ∅)
    {r : ℕ} (hr : r < n) (hpure : C ⊆ closure (regularLocus (n := n) C r)) :
    HasComparisons (indexedAvoidingBoundaryClass C r D) := by
  intro U₁ U₂ Y₁ Y₂ A₁ A₂ h₁ h₂
  obtain ⟨β,hβ⟩ := indexed_avoiding_boundary_physical_overlap C D hC hD hS hr hpure U₁ U₂ Y₁ Y₂ A₁ A₂ h₁ h₂
  refine ⟨β,?_⟩
  intro y
  have hz := congrArg (fun q : nestedOpens U₂ (U₁ ⊓ U₂) => q.val.val) (emptyAware_proj_comm hβ y)
  rw [overlapBaseEquiv_point] at hz
  have htproj := congrArg (fun q : U₂ => q.val) (proj_restrict (nestedOpens U₂ (U₁ ⊓ U₂)) A₂ (β y))
  have hsproj := congrArg (fun q : U₁ => q.val) (proj_restrict (nestedOpens U₁ (U₁ ⊓ U₂)) A₁ y)
  exact htproj.symm.trans (hz.trans hsproj)

/-- Compact windows provide actual stopped histories for the indexed class. -/
theorem indexed_avoiding_boundary_member_over_compact_window {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    {r : ℕ} (hr : r < n) (hpure : C ⊆ closure (regularLocus (n := n) C r))
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ (Y : CMfd.{0} n) (A : BlowupTower (CMfd.of (n := n) U) Y), indexedAvoidingBoundaryClass C r D U Y A := by
  let R := (hD.1.finite_nonempty_inter_compact hK).toFinset
  have hVis : ∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ R := by
    intro i ⟨x,hxD,hxU⟩
    apply (hD.1.finite_nonempty_inter_compact hK).mem_toFinset.mpr
    exact ⟨x,hxD,hUK hxU⟩
  let E := (R.sort (· ≤ ·)).map D
  have hE : IsSNCDivisor n E := sorted_boundary_snc D hD R
  have hdom := isInvDomain_bdry hC.analytic hr hpure hE
  obtain ⟨Y,T,hcanon,hres⟩ := HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (canonicalInvariant n) hdom hK U hUK
  have hmem : ∃ (Y' : CMfd.{0} n) (A : BlowupTower (CMfd.of (n := n) U) Y'), bdryClass C r E U Y' A := by
    by_cases ha : CentresAvoid (nestedOpens U (bdryOpen C r E)) T
    · exact ⟨Y,T,hcanon,ha,Or.inr hres⟩
    · obtain ⟨Y',A,-,-,h₁,h₂,c,hc,hcU⟩ := EmbeddedFromResolution.exists_first_centre _ _ (nestedOpens U (bdryOpen C r E)) T hcanon ha
      exact ⟨Y',A,h₁,h₂,Or.inl ⟨c,hc,hcU⟩⟩
  obtain ⟨Y',A,hA⟩ := hmem
  exact ⟨Y',A,R,hVis,hA⟩

/-- The indexed avoiding-boundary class covers and glues. -/
theorem exists_glued_indexed_avoiding_boundary_class {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : containingLabels C D hC.nonempty hD.1 = ∅)
    {r : ℕ} (hr : r < n) (hpure : C ⊆ closure (regularLocus (n := n) C r)) :
    ∃ (Z : CMfd.{0} n) (P : Z → X), IsGluedFrom (indexedAvoidingBoundaryClass C r D) Z P := by
  have hcov : Covers (indexedAvoidingBoundaryClass C r D) := by
    let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
    intro x
    obtain ⟨K,hK,hxK⟩ := exists_compact_mem_nhds x
    let U : Opens X := ⟨interior K,isOpen_interior⟩
    have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr hxK
    obtain ⟨Y,A,hA⟩ := indexed_avoiding_boundary_member_over_compact_window C D hC hD hr hpure U K hK interior_subset
    exact ⟨U,hxU,Y,A,hA⟩
  exact exists_isGluedFrom hcov (indexed_avoiding_boundary_comparisons C D hC hD hS hr hpure)
end
end Hironaka.HironakaG3IndexedAvoidingBoundaryClass
