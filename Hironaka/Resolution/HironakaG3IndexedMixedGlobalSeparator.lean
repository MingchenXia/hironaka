import Hironaka.Resolution.HironakaG3IndexedMixedGlobalSNC
import Hironaka.Resolution.HironakaG3IndexedSeparatedComponents
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedMixedGlobalSeparator
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC
  HironakaG3IndexedMixedGluing HironakaG3IndexedMixedChartBoundary HironakaG3IndexedMixedGlobalSNC
  HironakaG3IndexedSeparatedComponents

/-- A single proper glued separator has disjoint strict transforms of all
original components and the actual locally finite global SNC boundary. -/
theorem exists_indexed_mixed_separator_with_global_snc {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z : CMfd.{0} n) (P : Z → X), IsGluedFrom (indexedMixedClass V D) Z P ∧
      (∀ a b, a ≠ b → Disjoint (strictTransform n P (V a).carrier) (strictTransform n P (V b).carrier)) ∧
      (∀ a, P '' strictTransform n P (V a).carrier = (V a).carrier) ∧
      (∀ a, IsComplexAnalyticSubset (n := n) (strictTransform n P (V a).carrier)) ∧
      (∀ a, strictTransform n P (V a).carrier ⊆
        closure (regularLocus (n := n) (strictTransform n P (V a).carrier) (V a).dim)) ∧
      LocallyFinite (fun a => strictTransform n P (V a).carrier) ∧
      (∀ a, ∃ U : Opens Z, strictTransform n P (V a).carrier ⊆ U ∧
        ∀ b, b ≠ a → Disjoint (strictTransform n P (V b).carrier) (U : Set Z)) ∧
      ∃ Ex : SNCExhaustion Z,
        (∀ k, ∃ (c : TowerChart (indexedMixedClass V D) Z P) (Ef : List (Set c.Y)),
          MixedBoundaryWitness V D c Ef ∧ Ex.W k = c.V ∧ Ex.B k = mixedChartBoundary V D c Ef) ∧
        ∃ (ρ : Type) (B : ρ → Set Z), IsLocallyFiniteSNCDivisor n B ∧
          (∀ i, (B i).Nonempty) ∧ (⋃ i, B i) = ⋃ k, ⋃ H ∈ Ex.B k, H := by
  obtain ⟨Z,P,hG,hdisj,hproj,hanalytic,hpure,hLF,hwindows⟩ :=
    exists_indexed_separator_with_pure_component_windows V hV hDim hDistinct D hD
  exact ⟨Z,P,hG,hdisj,hproj,hanalytic,hpure,hLF,hwindows,
    indexed_mixed_exists_global_boundary V D hV hDim hDistinct hD hG⟩
end
end Hironaka.HironakaG3IndexedMixedGlobalSeparator
