import Hironaka.Resolution.HironakaG3UniverseArbitraryTerminalAtlas
import Hironaka.Resolution.HironakaG3IdentityHistoryAtlas
import Hironaka.Resolution.HironakaG3PureIndexedBoundaryTop
import Hironaka.Resolution.HironakaG3UniverseSmallBoundaryReindex

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u w

namespace Hironaka.HironakaG3IndexedBoundaryTargetA

noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaActualLocallyFiniteBoundary
  HironakaActualIndexedBoundaryContinuation HironakaG3RTowerClass GlobalComponents
  HironakaG3UniverseShrinkManifold HironakaG3UniverseLiftManifold G3UniverseChartProvenance
  HironakaG3CompositeTerminalHistory HironakaG3VaryingContactComponentClass
  HironakaG3IndexedMixedGluing HironakaG3IdentityHistoryAtlas HironakaG3PureIndexedBoundaryTop
  HironakaG3UniverseArbitraryTerminalAtlas HironakaG3UniverseSmallBoundaryReindex

/-- The class on the terminal map is the lift of the actual certified two-phase
class in lower dimension, or the literal identity history class in the top case. -/
def TerminalAtlasProvenance {n : ℕ} (X : CMfd.{u} n) (W : Set X) (d : ℕ)
    {ι : Type w} (D : ι → Set X) (Y : CMfd.{u} n) (P : Y → X) (Class : LocalTowerClass X) : Prop :=
  (n ≤ d ∧ Y = X ∧ HEq P (id : X → X) ∧ Class = identityHistoryClass (X := X)) ∨
    (d < n ∧
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
          (ρ₀ : Type) (B₀ : ρ₀ → Set Z₀)
          (U : I → Opens Z₀) (K : I → LocalTowerClass Z₀) (hQ₀ : Continuous Q₀),
          (∀ i, (V i).carrier = (i : Set X₀)) ∧ (∀ i, (V i).dim = d) ∧ (⋃ i, (V i).carrier) = W₀ ∧
          (letI : LinearOrder ρ₀ := WellOrderingRel.isWellOrder.linearOrder
           ∃ hB₀ : IsLocallyFiniteSNCDivisor n B₀,
             ∀ i, ∃ hCi : IsComplexAnalyticallyIrreducible (n := n) (strictTransform n P₀ (V i).carrier),
               ActualComponentResolutionClass (V i).dim (strictTransform n P₀ (V i).carrier)
                 B₀ hCi hB₀ (K i)) ∧
          let Class₀ := CompositeHistoryClass (P := P₀) hQ₀ (indexedMixedClass V D₀)
            (componentTailClass (fun i => strictTransform n P₀ (V i).carrier) U K B₀ Q₀)
          Y = liftCMfd.{u} Y₀ ∧
          HEq P (ex.symm ∘ (P₀ ∘ Q₀) ∘ (liftDiffeomorph.{u} Y₀).symm) ∧
          Class = liftedProvenanceClass ex Class₀)

/-- Target (A) for an original pure analytic target with an indexed SNC
boundary, with the actual chart class and its geometry on the same map. -/
theorem indexed_boundary_targetA {n d : ℕ}
    (X : CMfd.{u} n) (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hPure : W ⊆ closure (regularLocus (n := n) W d)) {ι : Type w}
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Y : CMfd.{u} n) (P : Y → X) (ρ : Type) (B : ρ → Set Y) (Class : LocalTowerClass X),
      TerminalAtlasProvenance X W d D Y P Class ∧
      IsGluedFrom Class Y P ∧ HasComparisons Class ∧
      (∀ (A : Opens X) (L : Set X), IsCompact L → (A : Set X) ⊆ L →
        ∃ c : TowerChart Class Y P, c.U = A) ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
      P '' strictTransform n P W = W ∧
      IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n P W) ∧
      (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
      P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P ∧
      IsLocallyFiniteSNCDivisor n B ∧ (∀ j, (B j).Nonempty) ∧
      (⋃ j, B j) = P ⁻¹' (⋃ i, D i) ∪ exceptionalLocus n P ∧
      (⋃ j, B j) = P ⁻¹' ((⋃ i, D i) ∪ W \ regularLocus (n := n) W d) ∧
      HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
  by_cases hd : d < n
  · obtain ⟨κ,f,hInjective,hRange,hD₀,hD₀ne,hD₀supp,V,Z₀,Y₀,P₀,Q₀,ρ₀,ρ,B₀,B',U,K,hQ₀,
      hCarrier,hDim,hUnion,hKind,hAtlas,hCompare,hWindows,hGeometry⟩ :=
      exists_arbitrary_universe_pure_terminal_atlas_with_provenance X W hW hd hPure D hD
    exact ⟨_,_,ρ,_,_,Or.inr ⟨hd,κ,f,hInjective,hRange,hD₀,hD₀ne,hD₀supp,
        V,Z₀,Y₀,P₀,Q₀,ρ₀,B₀,U,K,hQ₀,hCarrier,hDim,hUnion,hKind,rfl,HEq.rfl,rfl⟩,
      hAtlas,hCompare,hWindows,hGeometry⟩
  · have hd' : n ≤ d := Nat.le_of_not_gt hd
    obtain ⟨κ,f,_hInjective,_hRange,hD',_hD'ne,hUnion⟩ := exists_small_boundary_reindex_with_labels X D hD
    obtain ⟨ρ,B,hImage,hGood,hSmooth,hRegular,hSing,hB,hBne,hSupp,hSupp',hNC⟩ :=
      pure_indexed_boundary_identity W hW hd' hPure (fun j => D (f j)) hD'
    rw [hUnion] at hGood hSupp hSupp'
    exact ⟨X,id,ρ,B,identityHistoryClass,Or.inl ⟨hd',rfl,HEq.rfl,rfl⟩,identity_history_atlas X,
      G3UniversePhysicalClassComparisons.physical_comparisons_to_comparisons
        (identity_history_hasPhysicalComparisons X),fun A _ _ _ => ⟨identity_history_chart A,rfl⟩,
      contMDiff_id,isProperMap_id,surjective_id,hImage,hGood,hSmooth,hRegular,hSing,hB,hBne,hSupp,hSupp',hNC⟩

end
end Hironaka.HironakaG3IndexedBoundaryTargetA
