import Hironaka.Resolution.HironakaG3SeparatedCompositionExact
import Hironaka.Resolution.HironakaG3GoodSmoothBoundarySupport
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatedCompositionFinalSupport
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation
  HironakaG3SeparatedCompositionExact HironakaG3GoodSmoothBoundarySupport

theorem exists_separator_component_final_support {n d : ℕ} {X : CMfd.{0} n}
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
      (P ∘ Q) ⁻¹' ((⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ⊆ exceptionalLocus n (P ∘ Q) ∧
      IsLocallyFiniteSNCDivisor n B₀ ∧ IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n (P ∘ Q) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' ((⋃ j, D j) ∪ (⋃ i, (V i).carrier) \ regularLocus (n := n) (⋃ i, (V i).carrier) d) ∧
      HasNormalCrossingsWithBoundary (strictTransform n (P ∘ Q) (⋃ i, (V i).carrier)) B := by
  obtain ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,hP,hProper,hSurj,hImage,hGood,hSmooth,hRegular,hB₀,hB,hNE,hSupport,hNC⟩ :=
    exists_separator_component_composition_exact V hLF hDim hSameDim hDistinct D hD
  have hWClosed : IsClosed (⋃ i, (V i).carrier) := hLF.isClosed_iUnion (fun i => (V i).isClosed_carrier)
  have hSing := HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus hP hWClosed hRegular
  have hSupport' := hSupport.trans (good_smooth_boundary_support (⋃ i, (V i).carrier) (⋃ j, D j) hWClosed hP hGood hRegular)
  exact ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,hP,hProper,hSurj,hImage,hGood,hSmooth,hRegular,hSing,hB₀,hB,hNE,hSupport,hSupport',hNC⟩
end
end Hironaka.HironakaG3SeparatedCompositionFinalSupport
