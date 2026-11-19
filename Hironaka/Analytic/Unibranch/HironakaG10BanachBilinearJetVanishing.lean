import Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorRemainder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! # Bilinear preservation of vanishing finite Banach jets -/
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachBilinearJetVanishing

/-- If every derivative of the first factor below degree `N` vanishes,
  every derivative below `N` of its bilinear product with a smooth factor
  vanishes. This applies to operator composition without a tensor norm. -/
theorem iteratedFDeriv_bilinear_eq_zero_of_left
    {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (B : E →L[ℂ] F →L[ℂ] G) (f : X → E) (g : X → F)
    (hf : ContDiffAt ℂ ⊤ f 0) (hg : ContDiffAt ℂ ⊤ g 0)
    (N n : ℕ) (hn : n < N)
    (hzero : ∀ j < N, iteratedFDeriv ℂ j f 0 = 0) :
    iteratedFDeriv ℂ n (fun x => B (f x) (g x)) 0 = 0 := by
  obtain ⟨U,hU,h0U,hfU⟩ := hf.contDiffOn' (m := (n : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨V,hV,h0V,hgV⟩ := hg.contDiffOn' (m := (n : ℕ∞ω)) (by simp) (by simp)
  have hfU' : ContDiffOn ℂ (n : ℕ∞ω) f U := by simpa using hfU
  have hgV' : ContDiffOn ℂ (n : ℕ∞ω) g V := by simpa using hgV
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have h0W : (0 : X) ∈ W := ⟨h0U,h0V⟩
  have hbound := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfU'.mono (show W ⊆ U from inter_subset_left))
    (hgV'.mono (show W ⊆ V from inter_subset_right)) hW.uniqueDiffOn h0W (n := n) le_rfl
  have hsum : (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
      ‖iteratedFDerivWithin ℂ i f W 0‖ * ‖iteratedFDerivWithin ℂ (n-i) g W 0‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiN : i < N := by have := Finset.mem_range.mp hi; omega
    rw [iteratedFDerivWithin_of_isOpen i hW h0W, hzero i hiN, norm_zero]
    ring
  rw [hsum,mul_zero] at hbound
  rw [iteratedFDerivWithin_of_isOpen n hW h0W] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

end Hironaka.Analytic.Unibranch.HironakaG10BanachBilinearJetVanishing
