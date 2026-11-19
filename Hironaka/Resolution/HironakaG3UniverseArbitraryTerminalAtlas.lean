import Hironaka.Resolution.HironakaG3UniverseArbitraryGeometricEndpoint
import Hironaka.Resolution.HironakaG3UniverseProvenanceEndpoint
import Hironaka.Resolution.HironakaG3PureTargetGeometricAtlas
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology
universe u w

namespace Hironaka.HironakaG3UniverseArbitraryTerminalAtlas

noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaActualLocallyFiniteBoundary
  HironakaActualIndexedBoundaryContinuation HironakaG3UniverseSmallManifold HironakaG3UniverseShrinkManifold
  HironakaG3UniverseLiftManifold HironakaG3UniversePureBoundaryInput HironakaG3RTowerClass
  HironakaG3PureTargetGeometricAtlas HironakaG3CompositeTerminalHistory HironakaG3IndexedMixedGluing
  HironakaG3VaryingContactComponentClass HironakaG3UniverseArbitraryGeometricEndpoint
  G3UniverseChartProvenance G3UniverseProvenanceEndpoint GlobalComponents

/-- The original indexed pure target has a terminal atlas in its original
universe, whose towers retain the actual branch-certified small histories. -/
theorem exists_arbitrary_universe_pure_terminal_atlas_with_provenance {n d : ℕ}
    (X : CMfd.{u} n) {ι : Type w} (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) (hd : d < n)
    (hPure : W ⊆ closure (regularLocus (n := n) W d))
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    let X₀ := shrinkCMfd X
    let ex := shrinkDiffeomorph X
    let W₀ : Set X₀ := ex.symm ⁻¹' W
    ∃ (κ : Type) (f : κ → ι),
      Injective f ∧ (∀ i, (D i).Nonempty → i ∈ range f) ∧
      let D₀ : κ → Set X₀ := fun j => ex.symm ⁻¹' D (f j)
      IsLocallyFiniteSNCDivisor n D₀ ∧ (∀ j, (D₀ j).Nonempty) ∧
      (⋃ j, D₀ j) = ex.symm ⁻¹' (⋃ i, D i) ∧
      let I := globalComponents (n := n) W₀
      letI : LinearOrder I := WellOrderingRel.isWellOrder.linearOrder
      letI : LinearOrder κ := WellOrderingRel.isWellOrder.linearOrder
      ∃ (V : I → ClosedIrreducibleAnalyticSubvariety n X₀)
        (Z₀ Y₀ : CMfd.{0} n) (P₀ : Z₀ → X₀) (Q₀ : Y₀ → Z₀)
        (ρ₀ ρ : Type) (B₀ : ρ₀ → Set Z₀) (B' : ρ → Set Y₀)
        (U : I → Opens Z₀) (K : I → LocalTowerClass Z₀) (hQ₀ : Continuous Q₀),
        (∀ i, (V i).carrier = (i : Set X₀)) ∧ (∀ i, (V i).dim = d) ∧ (⋃ i, (V i).carrier) = W₀ ∧
        (letI : LinearOrder ρ₀ := WellOrderingRel.isWellOrder.linearOrder
         ∃ hB₀ : IsLocallyFiniteSNCDivisor n B₀,
           ∀ i, ∃ hCi : IsComplexAnalyticallyIrreducible (n := n) (strictTransform n P₀ (V i).carrier),
             ActualComponentResolutionClass (V i).dim (strictTransform n P₀ (V i).carrier)
               B₀ hCi hB₀ (K i)) ∧
        let Class₀ := CompositeHistoryClass (P := P₀) hQ₀ (indexedMixedClass V D₀)
          (componentTailClass (fun i => strictTransform n P₀ (V i).carrier) U K B₀ Q₀)
        let Class := liftedProvenanceClass ex Class₀
        let Y : CMfd.{u} n := liftCMfd.{u} Y₀
        let P : Y → X := ex.symm ∘ (P₀ ∘ Q₀) ∘ (liftDiffeomorph.{u} Y₀).symm
        let D' : ρ → Set Y := fun j => (liftDiffeomorph.{u} Y₀).symm ⁻¹' B' j
        IsGluedFrom Class Y P ∧ HasComparisons Class ∧
        (∀ (A : Opens X) (L : Set X), IsCompact L → (A : Set X) ⊆ L →
          ∃ c : TowerChart Class Y P, c.U = A) ∧
        ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
        P '' strictTransform n P W = W ∧
        IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ ∧
        IsClosedSubmanifold n (strictTransform n P W) ∧
        (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
        P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P ∧
        IsLocallyFiniteSNCDivisor n D' ∧ (∀ j, (D' j).Nonempty) ∧
        (⋃ j, D' j) = P ⁻¹' (⋃ i, D i) ∪ exceptionalLocus n P ∧
        (⋃ j, D' j) = P ⁻¹' ((⋃ i, D i) ∪ W \ regularLocus (n := n) W d) ∧
        HasNormalCrossingsWithBoundary (strictTransform n P W) D' := by
  letI : Small.{0} X := complex_manifold_small X
  let X₀ := shrinkCMfd X
  let ex := shrinkDiffeomorph X
  let W₀ : Set X₀ := ex.symm ⁻¹' W
  have hInput := transported_pure_boundary_input_with_labels X (Shrink.homeomorph X) W hW hPure D hD
  change IsComplexAnalyticSubset (n := n) W₀ ∧
    W₀ ⊆ closure (regularLocus (n := n) W₀ d) ∧
    ∃ (κ : Type) (f : κ → ι),
      Injective f ∧ (∀ i, (D i).Nonempty → i ∈ range f) ∧
      let D₀ : κ → Set X₀ := fun j => ex.symm ⁻¹' D (f j)
      IsLocallyFiniteSNCDivisor n D₀ ∧ (∀ j, (D₀ j).Nonempty) ∧
      (⋃ j, D₀ j) = ex.symm ⁻¹' (⋃ i, D i) at hInput
  obtain ⟨hW₀,hPure₀,κ,f,hf,hRange,hD₀,hD₀ne,hD₀supp⟩ := hInput
  let D₀ : κ → Set X₀ := fun j => ex.symm ⁻¹' D (f j)
  obtain ⟨V,Z₀,Y₀,P₀,Q₀,ρ₀,ρ,B₀,B',U,K,hQ₀,hCarrier,hDim,hUnion,hKind,hAtlas,hCmp,hWindows,
    hHol,hProper,hSurj,hImage,hGood,hSmooth,hReg,hSing,_hB₀,hB',hBne,hSupp,hSupp',hNC⟩ :=
    exists_pure_target_terminal_atlas_with_provenance W₀ hW₀ hd hPure₀ D₀ hD₀
  have hGeometry := conjugate_pure_endpoint_from_small_model (d := d) X W D D₀ hD₀supp (P₀ ∘ Q₀) B'
    ⟨hHol,hProper,hSurj,hImage,hGood,hSmooth,hReg,hSing,hB',hBne,hSupp,hSupp',hNC⟩
  exact ⟨κ,f,hf,hRange,hD₀,hD₀ne,hD₀supp,V,Z₀,Y₀,P₀,Q₀,ρ₀,ρ,B₀,B',U,K,hQ₀,hCarrier,hDim,hUnion,hKind,
    lifted_provenance_atlas ex hAtlas,lifted_provenance_endpoint_comparisons ex hAtlas hCmp,
    lifted_provenance_compact_window ex hWindows,hGeometry⟩

end
end Hironaka.HironakaG3UniverseArbitraryTerminalAtlas
