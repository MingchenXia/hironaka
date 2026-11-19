import Hironaka.Analytic.AnalyticDescendingChain

/-! Compact stabilization for descending analytic chains. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaCompactAnalyticDescendingChain
open AnalyticDescendingChain
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem analytic_descending_chain_stable_on_compact {A : ℕ → Set M}
    (hA : ∀ i,IsComplexAnalyticSubset (n := n) (A i)) (hanti : Antitone A)
    {K : Set M} (hK : IsCompact K) :
    ∃ N,∀ i,N ≤ i → A i ∩ K=A N ∩ K := by
  choose N U hU hpU hstab using AnalyticDescendingChain.exists_local_stable hA hanti
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover U hU (fun p _ => mem_iUnion.mpr ⟨p,hpU p⟩)
  refine ⟨t.sup N,fun i hi => ?_⟩
  ext x
  constructor
  · rintro ⟨hx,hxK⟩
    obtain ⟨p,hpt,hxp⟩ := mem_iUnion₂.mp (ht hxK)
    have hle : N p ≤ t.sup N := Finset.le_sup hpt
    have h1 := hstab p i (hle.trans hi)
    have h2 := hstab p (t.sup N) hle
    have hh : x ∈ A (N p) ∩ U p := h1 ▸ (show x ∈ A i ∩ U p from ⟨hx,hxp⟩)
    exact ⟨(h2.symm ▸ hh : x ∈ A (t.sup N) ∩ U p).1,hxK⟩
  · rintro ⟨hx,hxK⟩
    obtain ⟨p,hpt,hxp⟩ := mem_iUnion₂.mp (ht hxK)
    have hle : N p ≤ t.sup N := Finset.le_sup hpt
    have h1 := hstab p i (hle.trans hi)
    have h2 := hstab p (t.sup N) hle
    have hh : x ∈ A (N p) ∩ U p := h2 ▸ (show x ∈ A (t.sup N) ∩ U p from ⟨hx,hxp⟩)
    exact ⟨(h1.symm ▸ hh : x ∈ A i ∩ U p).1,hxK⟩
end
end Hironaka.HironakaCompactAnalyticDescendingChain
