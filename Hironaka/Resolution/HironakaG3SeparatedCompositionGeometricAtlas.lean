import Hironaka.Resolution.HironakaG3CompositeTerminalHistory
import Hironaka.Resolution.HironakaG3CompositeGeometricAtlas
import Hironaka.Resolution.HironakaG3SeparatedCompositionExact
import Hironaka.Resolution.HironakaG3GoodSmoothBoundarySupport
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatedCompositionGeometricAtlas
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation HironakaG3RTowerClass
  HironakaG3IndexedMixedGluing HironakaG3SeparatedCompositionExact HironakaG3CompositeGeometricAtlas HironakaG3CompositeTerminalHistory
  HironakaG3PhysicalClassComparisons HironakaG3IndexedSeparatedComponents HironakaG3GoodSmoothBoundarySupport

theorem exists_separator_composition_geometric_atlas {n d : ℕ} {X : CMfd.{0} n}
    {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier)) (hDim : ∀ i, (V i).dim < n)
    (hSameDim : ∀ i, (V i).dim = d)
    (hDistinct : ∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z Y : CMfd.{0} n) (P : Z → X) (Q : Y → Z) (ρ₀ ρ : Type) (B₀ : ρ₀ → Set Z) (B : ρ → Set Y),
      IsGluedFrom (fun _ _ _ => True) Y (P ∘ Q) ∧
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
  obtain ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,W,K,hQ,hAtlas,_hCmp,_hWindowChart,
    hMD,hProper,hSurj,hProj,hIso,hSmooth,hRegular,hSing,hB₀,hB,hNE,hSupport,hSupport',hNC⟩ :=
    exists_separator_composition_terminal_atlas V hLF hDim hSameDim hDistinct D hD
  have hGeometry : IsGluedFrom (fun _ _ _ => True) Y (P ∘ Q) := by
    refine ⟨hAtlas.1,hAtlas.2.1,hAtlas.2.2.1,?_⟩
    intro x
    obtain ⟨c,hx⟩ := hAtlas.2.2.2 x
    exact ⟨⟨c.U,c.Y,c.T,True.intro,c.V,c.V_eq,c.φ,c.proj_φ⟩,hx⟩
  exact ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,hGeometry,hMD,hProper,hSurj,hProj,hIso,hSmooth,hRegular,hSing,hB₀,hB,
    hNE,hSupport,hSupport',hNC⟩

end
end Hironaka.HironakaG3SeparatedCompositionGeometricAtlas
