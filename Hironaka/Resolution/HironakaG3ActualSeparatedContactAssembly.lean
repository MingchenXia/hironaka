import Hironaka.Resolution.HironakaG3SeparatorBoundaryDichotomy
import Hironaka.Resolution.HironakaG3IndexedMixedGlobalSeparator
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ActualSeparatedContactAssembly
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC
  HironakaG3IndexedMixedGluing HironakaG3IndexedMixedChartBoundary HironakaG3IndexedMixedGlobalSNC
  HironakaG3IndexedMixedGlobalSeparator HironakaG3SeparatorBoundaryDichotomy
  HironakaG3ProperDenseIrreducible HironakaG3IndexedCanonicalContact
  HironakaG3IndexedContainingBoundary

/-- One actual separator and its actual transformed-boundary exhaustion carry
all original-dimensional irreducible strict components and their full indexed
boundary contact dichotomies. -/
theorem exists_actual_separator_with_component_contacts {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Z : CMfd.{0} n) (P : Z → X) (hG : IsGluedFrom (indexedMixedClass V D) Z P)
      (Ex : SNCExhaustion Z) (ρ : Type) (B : ρ → Set Z) (hB : IsLocallyFiniteSNCDivisor n B),
      (∀ a b, a ≠ b → Disjoint (strictTransform n P (V a).carrier) (strictTransform n P (V b).carrier)) ∧
      (∀ a, P '' strictTransform n P (V a).carrier = (V a).carrier) ∧
      (∀ k, ∃ (c : TowerChart (indexedMixedClass V D) Z P) (Ef : List (Set c.Y)),
        MixedBoundaryWitness V D c Ef ∧ Ex.W k = c.V ∧ Ex.B k = mixedChartBoundary V D c Ef) ∧
      (∀ i, (B i).Nonempty) ∧ (⋃ i, B i) = ⋃ k, ⋃ H ∈ Ex.B k, H ∧
      ∀ a, (∃ W : ClosedIrreducibleAnalyticSubvariety n Z,
          W.carrier = strictTransform n P (V a).carrier ∧ W.dim = (V a).dim) ∧
        ((∃ i, strictTransform n P (V a).carrier ⊆ B i) ∨
          strictTransform n P (V a).carrier ⊆ closure (strictTransform n P (V a).carrier \ ⋃ i, B i)) ∧
        let C := strictTransform n P (V a).carrier
        let hC := indexed_separator_strictTransform_irreducible V hDim hDistinct D hG a
        let S := containingLabels C B hC.nonempty hB.1
        let N := canonicalContact C B hC.nonempty hB.1
        C ⊆ N ∧ N.Nonempty ∧ IsClosed N ∧
          (∀ x ∈ N, RegularAtDim (n := n) N x (n - S.card)) ∧
          S.card ≤ n ∧ IsClosedSubmanifold n N ∧
          C ⊆ closure (C \ ⋃ i : {i // i ∉ S}, B i.val) := by
  obtain ⟨Z,P,hG,hDis,hProj,_hAnalytic,_hPure,_hLF,_hWindows,Ex,hCharts,ρ,B,hB,hNE,hUnion⟩ :=
    exists_indexed_mixed_separator_with_global_snc V hV hDim hDistinct D hD
  refine ⟨Z,P,hG,Ex,ρ,B,hB,hDis,hProj,hCharts,hNE,hUnion,?_⟩
  intro a
  exact ⟨exists_separator_strict_component V hDim hDistinct D hG a,
    separator_component_boundary_dichotomy V hDim hDistinct D hG B hB a,
    separator_component_canonical_contact V hDim hDistinct D hG B hB a⟩
end
end Hironaka.HironakaG3ActualSeparatedContactAssembly
