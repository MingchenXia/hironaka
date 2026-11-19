import Hironaka.Resolution.HironakaG3CompositeTerminalHistory
import Hironaka.Resolution.HironakaG3PureGlobalComponents
import Hironaka.Resolution.HironakaG3SeparatedCompositionGeometricAtlas
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3PureTargetGeometricAtlas
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation GlobalComponents
  HironakaG3PureGlobalComponents HironakaG3SeparatedCompositionGeometricAtlas HironakaG3RTowerClass
  HironakaG3CompositeTerminalHistory HironakaG3VaryingContactComponentClass HironakaG3IndexedMixedGluing

/-- The original pure target and indexed boundary determine a terminal atlas
with the actual contact branch of each selected component class. -/
theorem exists_pure_target_terminal_atlas_with_provenance {n d : ℕ} {X : CMfd.{0} n} {κ : Type}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (hd : d < n)
    (hPure : W ⊆ closure (regularLocus (n := n) W d))
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    let I := globalComponents (n := n) W
    letI : LinearOrder I := WellOrderingRel.isWellOrder.linearOrder
    letI : LinearOrder κ := WellOrderingRel.isWellOrder.linearOrder
    ∃ (V : I → ClosedIrreducibleAnalyticSubvariety n X)
      (Z Y : CMfd.{0} n) (P : Z → X) (Q : Y → Z)
      (ρ₀ ρ : Type) (B₀ : ρ₀ → Set Z) (B : ρ → Set Y)
      (U : I → Opens Z) (K : I → LocalTowerClass Z) (hQ : Continuous Q),
      (∀ i, (V i).carrier = (i : Set X)) ∧ (∀ i, (V i).dim = d) ∧ (⋃ i, (V i).carrier) = W ∧
      (letI : LinearOrder ρ₀ := WellOrderingRel.isWellOrder.linearOrder
       ∃ hB₀ : IsLocallyFiniteSNCDivisor n B₀,
         ∀ i, ∃ hCi : IsComplexAnalyticallyIrreducible (n := n) (strictTransform n P (V i).carrier),
           ActualComponentResolutionClass (V i).dim (strictTransform n P (V i).carrier)
             B₀ hCi hB₀ (K i)) ∧
      let Class := CompositeHistoryClass (P := P) hQ (indexedMixedClass V D)
        (componentTailClass (fun i => strictTransform n P (V i).carrier) U K B₀ Q)
      IsGluedFrom Class Y (P ∘ Q) ∧ HasComparisons Class ∧
      (∀ (A : Opens X) (L : Set X), IsCompact L → (A : Set X) ⊆ L →
        ∃ c : TowerChart Class Y (P ∘ Q), c.U = A) ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (P ∘ Q) ∧
      IsProperMap (P ∘ Q) ∧ Surjective (P ∘ Q) ∧
      (P ∘ Q) '' strictTransform n (P ∘ Q) W = W ∧
      IsIsomorphismOver n (P ∘ Q) (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n (P ∘ Q) W) ∧
      (∀ z ∈ strictTransform n (P ∘ Q) W,
        RegularAtDim (n := n) (strictTransform n (P ∘ Q) W) z d) ∧
      (P ∘ Q) ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n (P ∘ Q) ∧
      IsLocallyFiniteSNCDivisor n B₀ ∧ IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n (P ∘ Q) ∧
      (⋃ a, B a) = (P ∘ Q) ⁻¹' ((⋃ j, D j) ∪ W \ regularLocus (n := n) W d) ∧
      HasNormalCrossingsWithBoundary (strictTransform n (P ∘ Q) W) B := by
  let : LinearOrder κ := WellOrderingRel.isWellOrder.linearOrder
  let : LinearOrder (globalComponents (n := n) W) := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨V,hCarrier,hDim,hLF,hDistinct,hUnion⟩ := exists_pure_global_component_family W hW hd hPure
  have hDimLt : ∀ i, (V i).dim < n := fun i => (hDim i).symm ▸ hd
  obtain ⟨Z,Y,P,Q,ρ₀,ρ,B₀,B,U,K,hQ,hKind,hAtlas,hCmp,hWindow,
    hP,hProper,hSurj,hImage,hGood,hSmooth,hRegular,hSing,hB₀,hB,hNE,hSupport,hSupport',hNC⟩ :=
    exists_separator_composition_terminal_atlas_with_provenance V hLF hDimLt hDim hDistinct D hD
  rw [hUnion] at hImage hGood hSmooth hRegular hSing hSupport' hNC
  exact ⟨V,Z,Y,P,Q,ρ₀,ρ,B₀,B,U,K,hQ,hCarrier,hDim,hUnion,hKind,hAtlas,hCmp,hWindow,
    hP,hProper,hSurj,hImage,hGood,hSmooth,hRegular,hSing,hB₀,hB,hNE,hSupport,hSupport',hNC⟩

theorem exists_pure_target_geometric_atlas {n d : ℕ} {X : CMfd.{0} n} {κ : Type}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (hd : d < n)
    (hPure : W ⊆ closure (regularLocus (n := n) W d))
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Y : CMfd.{0} n) (P : Y → X) (ρ : Type) (B : ρ → Set Y),
      IsGluedFrom (fun _ _ _ => True) Y P ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
      P '' strictTransform n P W = W ∧
      IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n P W) ∧
      (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
      P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P ∧
      IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P ∧
      (⋃ a, B a) = P ⁻¹' ((⋃ j, D j) ∪ W \ regularLocus (n := n) W d) ∧
      HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
  obtain ⟨_V,_Z,Y,P,Q,_ρ₀,ρ,_B₀,B,_U,_K,_hQ,_hCarrier,_hDim,_hUnion,_hKind,hAtlas,_hCmp,_hWindow,
    hP,hProper,hSurj,hImage,hGood,hSmooth,hRegular,hSing,_hB₀,hB,hNE,hSupport,hSupport',hNC⟩ :=
    exists_pure_target_terminal_atlas_with_provenance W hW hd hPure D hD
  have hGeometry : IsGluedFrom (fun _ _ _ => True) Y (P ∘ Q) := by
    refine ⟨hAtlas.1,hAtlas.2.1,hAtlas.2.2.1,?_⟩
    intro x
    obtain ⟨c,hx⟩ := hAtlas.2.2.2 x
    exact ⟨⟨c.U,c.Y,c.T,True.intro,c.V,c.V_eq,c.φ,c.proj_φ⟩,hx⟩
  exact ⟨Y,P ∘ Q,ρ,B,hGeometry,hP,hProper,hSurj,hImage,hGood,hSmooth,hRegular,hSing,hB,hNE,hSupport,hSupport',hNC⟩

end
end Hironaka.HironakaG3PureTargetGeometricAtlas
