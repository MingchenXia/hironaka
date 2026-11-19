import Hironaka.Analytic.ProductComplexManifold
import Hironaka.Analytic.AnalyticSubsetPreimage

/-! # The literal analytic fibre-product carrier of genuine holomorphic maps

This is a geometric prerequisite for a future direct common-resolution
construction. It produces closedness and actual finite local holomorphic
presentations of the WHOLE equalizer carrier. No main irreducible component,
smooth resolution, finite domination, comparison map or reader is supplied
or claimed. Dimensions and original product points are unchanged.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.AnalyticFibreProductCarrier



variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The actual entire diagonal is analytic, without connectedness or a
nonempty-point hypothesis; its regularity comes from genuine product charts. -/
theorem isComplexAnalyticSubset_diagonal :
    IsComplexAnalyticSubset (n := n + n) (diagonal X) := by
  apply AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
  refine ⟨isClosed_diagonal, ?_⟩
  rintro ⟨x, y⟩ (h : x = y)
  subst y
  exact ⟨n, ProductComplexManifold.regularAtDim_diagonal x⟩

variable {m₀ m₁ : ℕ} {Y₀ : Type*} [TopologicalSpace Y₀]
  [ChartedSpace (ComplexModel m₀) Y₀] [IsComplexManifold m₀ Y₀]
  {Y₁ : Type*} [TopologicalSpace Y₁]
  [ChartedSpace (ComplexModel m₁) Y₁] [IsComplexManifold m₁ Y₁]

omit [IsComplexManifold m₀ Y₀] [IsComplexManifold m₁ Y₁] in
/-- The same literal whole fibre-product set is closed by the genuine maps. -/
theorem isClosed_fibreProduct {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : ContMDiff 𝓘(ℂ, ComplexModel m₀) 𝓘(ℂ, ComplexModel n) ∞ c₀)
    (hc₁ : ContMDiff 𝓘(ℂ, ComplexModel m₁) 𝓘(ℂ, ComplexModel n) ∞ c₁) :
    IsClosed {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} :=
  isClosed_eq (hc₀.continuous.comp continuous_fst) (hc₁.continuous.comp continuous_snd)

/-- The entire actual equalizer carrier is the holomorphic inverse image of
the same actual diagonal in the original product atlas. No main component
or proper/birational geometry is an input or an output of this theorem. -/
theorem isComplexAnalyticSubset_fibreProduct {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : ContMDiff 𝓘(ℂ, ComplexModel m₀) 𝓘(ℂ, ComplexModel n) ∞ c₀)
    (hc₁ : ContMDiff 𝓘(ℂ, ComplexModel m₁) 𝓘(ℂ, ComplexModel n) ∞ c₁) :
    IsComplexAnalyticSubset (n := m₀ + m₁) {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} := by
  change IsComplexAnalyticSubset (n := m₀ + m₁) ((Prod.map c₀ c₁) ⁻¹' diagonal X)
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (ProductComplexManifold.contMDiff_prodMap hc₀ hc₁) isComplexAnalyticSubset_diagonal

end Hironaka.AnalyticFibreProductCarrier
