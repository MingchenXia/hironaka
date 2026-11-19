import Hironaka.Resolution.HironakaG3SeparatorOriginalGoodTransfer
import Hironaka.Resolution.HironakaG3IsomorphismOverComposition
import Hironaka.Resolution.HironakaG3SeparatedAvoidingGood
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatorComposedOriginalGood
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG3IndexedMixedBad HironakaG3IndexedMixedGluing HironakaG3MixedBadSubsetSingular
  HironakaG3SeparatorOriginalGoodTransfer HironakaG3IsomorphismOverComposition HironakaG3SeparatedAvoidingGood

theorem separator_composed_original_good {n d : ℕ} {X Z Y : CMfd.{0} n}
    {ι κ ρ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier)) (hDim : ∀ i, (V i).dim < n)
    (hDistinct : ∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier)
    (W : Set X) (hW : W = ⋃ i, (V i).carrier) (D : κ → Set X) (B : ρ → Set Z)
    {P : Z → X} (hG : IsGluedFrom (indexedMixedClass V D) Z P)
    (hB : (⋃ j, B j) ⊆ P ⁻¹' ((⋃ j, D j) ∪ indexedMixedBad V))
    (Q : Y → Z) (hQm : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ Q)
    (hQ : IsIsomorphismOver n Q
      (⋃ i, (strictTransform n P (V i).carrier \ regularLocus (n := n) (strictTransform n P (V i).carrier) (V i).dim) ∪
        (strictTransform n P (V i).carrier ∩ ⋃ j, B j))ᶜ) :
    IsIsomorphismOver n (P ∘ Q) (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ := by
  let G : Set X := (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ
  have hBad := indexed_mixed_bad_subset_singular V hLF hDistinct W hW (d := d)
  have hGsub : G ⊆ (indexedMixedBad V)ᶜ := fun x hx hb => hx (Or.inl (hBad hb))
  have hPiso := iso_mono hGsub (glued_indexed_isIsomorphismOver V hDim hDistinct D hG)
  have hTransfer := separator_preimage_original_good_subset_component_good V hLF hDim hDistinct W hW D B hG hB (d := d)
  have hQiso := iso_mono hTransfer hQ
  exact isomorphism_over_comp hG.1 hQm G hPiso hQiso
end
end Hironaka.HironakaG3SeparatorComposedOriginalGood
