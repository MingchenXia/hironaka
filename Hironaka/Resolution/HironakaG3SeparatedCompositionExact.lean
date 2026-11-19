import Hironaka.Resolution.HironakaG3SeparatorBoundaryLower
import Hironaka.Resolution.HironakaG3ComposedBoundarySupport
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Resolution.HironakaG3IndexedMixedGlobalSeparator
import Hironaka.Resolution.HironakaG3SeparatorIrreducible
import Hironaka.Resolution.HironakaG3VaryingSeparatedExactEndpoint
import Hironaka.Resolution.HironakaG3SeparatorExhaustionOriginalGood
import Hironaka.Resolution.HironakaG3ComposedSeparatedStrictGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatedCompositionExact
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation HironakaG3RTowerClass
  HironakaG3IndexedMixedGluing HironakaG3IndexedMixedGlobalSeparator HironakaG3ProperDenseIrreducible
  HironakaG3VaryingContactComponentClass HironakaG3VaryingSeparatedExactEndpoint HironakaG3SeparatorExhaustionOriginalGood
  HironakaG3ComposedSeparatedStrictGeometry HironakaG3LocallyFiniteStrictUnion
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas HironakaG3PhysicalClassComparisons RestrictEmptyTower
  HironakaG3SeparatorBoundaryLower HironakaG3SeparatorBoundaryFootprint HironakaG3ComposedBoundarySupport
  HironakaG3MixedBadSubsetSingular HironakaG3IndexedMixedBad

theorem exists_separator_component_composition_with_branch_provenance {n d : ℕ} {X : CMfd.{0} n}
    {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier)) (hDim : ∀ i, (V i).dim < n)
    (hSameDim : ∀ i, (V i).dim = d)
    (hDistinct : ∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z Y : CMfd.{0} n) (P : Z → X) (Q : Y → Z) (ρ₀ ρ : Type) (B₀ : ρ₀ → Set Z) (B : ρ → Set Y),
      ∃ (W : ι → Opens Z) (K : ι → LocalTowerClass Z),
      (∀ i, strictTransform n P (V i).carrier ⊆ W i) ∧
      (∀ i j, i ≠ j → Disjoint (strictTransform n P (V j).carrier) (W i : Set Z)) ∧
      (letI : LinearOrder ρ₀ := WellOrderingRel.isWellOrder.linearOrder
       ∃ hB₀ : IsLocallyFiniteSNCDivisor n B₀,
         ∀ i, ∃ hCi : IsComplexAnalyticallyIrreducible (n := n) (strictTransform n P (V i).carrier),
           ActualComponentResolutionClass (V i).dim (strictTransform n P (V i).carrier)
             B₀ hCi hB₀ (K i)) ∧
      (∀ i, HasPhysicalComparisons (K i)) ∧
      (∀ (i : ι) (U : Opens Z) (A : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) A),
        K i U A T → CentresOver ((Subtype.val : U → Z) ⁻¹' strictTransform n P (V i).carrier) T) ∧
      (∀ (i : ι) (U : Opens Z) (L : Set Z), IsCompact L → (U : Set Z) ⊆ L →
        ∃ (A : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) A), K i U A T) ∧
      IsGluedFrom (indexedMixedClass V D) Z P ∧
      IsGluedFrom (finiteVisibleClass (disjointWindowClass (fun i => strictTransform n P (V i).carrier) W K) B₀) Y Q ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (P ∘ Q) ∧
      IsProperMap (P ∘ Q) ∧ Surjective (P ∘ Q) ∧
      (P ∘ Q) '' strictTransform n (P ∘ Q) (⋃ i, (V i).carrier) = ⋃ i, (V i).carrier ∧
      IsIsomorphismOver n (P ∘ Q) (((⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ∪
        ((⋃ i, (V i).carrier) ∩ ⋃ j, D j))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) ∧
      (∀ z ∈ strictTransform n (P ∘ Q) (⋃ i, (V i).carrier),
        RegularAtDim (n := n) (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) z d) ∧
      IsLocallyFiniteSNCDivisor n B₀ ∧ IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n (P ∘ Q) ∧
      HasNormalCrossingsWithBoundary (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) B := by
  obtain ⟨Z,P,hG,hDis,hProj,hAnalytic,hPure,hSLF,_hWindows,Ex,hCharts,ρ₀,B₀,hB₀,_hNE₀,hUnion⟩ :=
    exists_indexed_mixed_separator_with_global_snc V hLF hDim hDistinct D hD
  let C : ι → Set Z := fun i => strictTransform n P (V i).carrier
  have hIrr : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i) :=
    fun i => indexed_separator_strictTransform_irreducible V hDim hDistinct D hG i
  let : LinearOrder ρ₀ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨W,K,Y,Q,ρ,B,hCW,hWindow,hKind,hPhys,hCentres,_hActive,_hBound,_hGeo,hCompact,hQG,hGood,hProjQ,hSmooth,hRegular,hB,hNE,hSupport,hNC⟩ :=
    exists_varying_separated_exact_with_branch_provenance C (fun i => (V i).dim) B₀ hIrr hSLF hDis hB₀ hDim hPure
  have hGeo := composed_separated_strict_geometry (fun i => (V i).carrier)
    (fun i => (V i).isClosed_carrier) hLF hG.1 hQG.1 hDis hProj hProjQ hSmooth
    (fun i z hz => by simpa [hSameDim i] using hRegular i z hz)
  have hEq : strictTransform n (P ∘ Q) (⋃ i, (V i).carrier) = ⋃ i, strictTransform n Q (C i) := by
    rw [StrictTransformComposition.strictTransform_comp hG.1 hQG.1,
      strictTransform_iUnion_of_locallyFinite (fun i => (V i).carrier) hLF P hG.1.continuous,
      strictTransform_iUnion_of_locallyFinite C hSLF Q hQG.1.continuous]
  have hBLower : P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P ⊆ ⋃ j, B₀ j := by
    rw [hUnion]
    exact separator_global_boundary_lower V D hDim hDistinct hD hG.1 Ex hCharts
  have hBUpper : (⋃ j, B₀ j) ⊆ P ⁻¹' ((⋃ j, D j) ∪ indexedMixedBad V) := by
    rw [hUnion]
    exact separator_global_boundary_footprint V D hDim hDistinct hD Ex hCharts
  have hWClosed : IsClosed (⋃ i, (V i).carrier) := hLF.isClosed_iUnion (fun i => (V i).isClosed_carrier)
  have hBad := indexed_mixed_bad_subset_singular V hLF hDistinct (⋃ i, (V i).carrier) rfl (d := d)
  have hBadExc : (P ∘ Q) ⁻¹' indexedMixedBad V ⊆ exceptionalLocus n (P ∘ Q) :=
    (preimage_mono hBad).trans (HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus
      (hG.1.comp hQG.1) hWClosed hGeo.2.2)
  have hExactSupport := hSupport.trans (composed_boundary_exact_support hG.1 hQG.1
    (⋃ j, D j) (indexedMixedBad V) (⋃ j, B₀ j) hBLower hBUpper hBadExc)
  have hGood' := separator_exhaustion_composed_original_good (d := d) V hLF hDim hDistinct
    (⋃ i, (V i).carrier) rfl D hD hG Ex B₀ hCharts hUnion Q hQG.1 hGood
  exact ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,W,K,hCW,hWindow,⟨hB₀,fun i => ⟨hIrr i,hKind i⟩⟩,hPhys,hCentres,hCompact,hG,hQG,hG.1.comp hQG.1,hG.2.1.comp hQG.2.1,
    hG.2.2.1.comp hQG.2.2.1,hGeo.1,hGood',hGeo.2.1,hGeo.2.2,hB₀,hB,hNE,hExactSupport,by simpa only [hEq] using hNC⟩

theorem exists_separator_component_composition_with_atlases_and_certificates {n d : ℕ} {X : CMfd.{0} n}
    {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier)) (hDim : ∀ i, (V i).dim < n)
    (hSameDim : ∀ i, (V i).dim = d)
    (hDistinct : ∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z Y : CMfd.{0} n) (P : Z → X) (Q : Y → Z) (ρ₀ ρ : Type) (B₀ : ρ₀ → Set Z) (B : ρ → Set Y),
      ∃ (W : ι → Opens Z) (K : ι → LocalTowerClass Z),
      (∀ i, strictTransform n P (V i).carrier ⊆ W i) ∧
      (∀ i j, i ≠ j → Disjoint (strictTransform n P (V j).carrier) (W i : Set Z)) ∧
      (∀ i, HasPhysicalComparisons (K i)) ∧
      (∀ (i : ι) (U : Opens Z) (A : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) A),
        K i U A T → CentresOver ((Subtype.val : U → Z) ⁻¹' strictTransform n P (V i).carrier) T) ∧
      (∀ (i : ι) (U : Opens Z) (L : Set Z), IsCompact L → (U : Set Z) ⊆ L →
        ∃ (A : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) A), K i U A T) ∧
      IsGluedFrom (indexedMixedClass V D) Z P ∧
      IsGluedFrom (finiteVisibleClass (disjointWindowClass (fun i => strictTransform n P (V i).carrier) W K) B₀) Y Q ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (P ∘ Q) ∧
      IsProperMap (P ∘ Q) ∧ Surjective (P ∘ Q) ∧
      (P ∘ Q) '' strictTransform n (P ∘ Q) (⋃ i, (V i).carrier) = ⋃ i, (V i).carrier ∧
      IsIsomorphismOver n (P ∘ Q) (((⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ∪
        ((⋃ i, (V i).carrier) ∩ ⋃ j, D j))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) ∧
      (∀ z ∈ strictTransform n (P ∘ Q) (⋃ i, (V i).carrier),
        RegularAtDim (n := n) (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) z d) ∧
      IsLocallyFiniteSNCDivisor n B₀ ∧ IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n (P ∘ Q) ∧
      HasNormalCrossingsWithBoundary (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) B := by
  obtain ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,W,K,hCW,hWindow,_hKind,hRest⟩ :=
    exists_separator_component_composition_with_branch_provenance V hLF hDim hSameDim hDistinct D hD
  exact ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,W,K,hCW,hWindow,hRest⟩

theorem exists_separator_component_composition_with_atlases {n d : ℕ} {X : CMfd.{0} n}
    {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier)) (hDim : ∀ i, (V i).dim < n)
    (hSameDim : ∀ i, (V i).dim = d)
    (hDistinct : ∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z Y : CMfd.{0} n) (P : Z → X) (Q : Y → Z) (ρ₀ ρ : Type) (B₀ : ρ₀ → Set Z) (B : ρ → Set Y),
      ∃ (W : ι → Opens Z) (K : ι → LocalTowerClass Z),
      IsGluedFrom (indexedMixedClass V D) Z P ∧
      IsGluedFrom (finiteVisibleClass (disjointWindowClass (fun i => strictTransform n P (V i).carrier) W K) B₀) Y Q ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (P ∘ Q) ∧
      IsProperMap (P ∘ Q) ∧ Surjective (P ∘ Q) ∧
      (P ∘ Q) '' strictTransform n (P ∘ Q) (⋃ i, (V i).carrier) = ⋃ i, (V i).carrier ∧
      IsIsomorphismOver n (P ∘ Q) (((⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ∪
        ((⋃ i, (V i).carrier) ∩ ⋃ j, D j))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) ∧
      (∀ z ∈ strictTransform n (P ∘ Q) (⋃ i, (V i).carrier),
        RegularAtDim (n := n) (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) z d) ∧
      IsLocallyFiniteSNCDivisor n B₀ ∧ IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n (P ∘ Q) ∧
      HasNormalCrossingsWithBoundary (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) B := by
  obtain ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,W,K,_hCW,_hWindow,_hPhys,_hCentres,_hCompact,hGP,hGQ,hRest⟩ :=
    exists_separator_component_composition_with_atlases_and_certificates V hLF hDim hSameDim hDistinct D hD
  exact ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,W,K,hGP,hGQ,hRest⟩

theorem exists_separator_component_composition_exact {n d : ℕ} {X : CMfd.{0} n}
    {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier)) (hDim : ∀ i, (V i).dim < n)
    (hSameDim : ∀ i, (V i).dim = d)
    (hDistinct : ∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z Y : CMfd.{0} n) (P : Z → X) (Q : Y → Z) (ρ₀ ρ : Type) (B₀ : ρ₀ → Set Z) (B : ρ → Set Y),
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (P ∘ Q) ∧
      IsProperMap (P ∘ Q) ∧ Surjective (P ∘ Q) ∧
      (P ∘ Q) '' strictTransform n (P ∘ Q) (⋃ i, (V i).carrier) = ⋃ i, (V i).carrier ∧
      IsIsomorphismOver n (P ∘ Q) (((⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ∪
        ((⋃ i, (V i).carrier) ∩ ⋃ j, D j))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) ∧
      (∀ z ∈ strictTransform n (P ∘ Q) (⋃ i, (V i).carrier),
        RegularAtDim (n := n) (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) z d) ∧
      IsLocallyFiniteSNCDivisor n B₀ ∧ IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n (P ∘ Q) ∧
      HasNormalCrossingsWithBoundary (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) B := by
  obtain ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,W,K,_hGP,_hGQ,hRest⟩ :=
    exists_separator_component_composition_with_atlases V hLF hDim hSameDim hDistinct D hD
  exact ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,hRest⟩

end
end Hironaka.HironakaG3SeparatedCompositionExact
