import Hironaka.Analytic.OhsawaTakegoshiRegularReduction
import Hironaka.Analytic.ConvexExhaustion
import Hironaka.Analytic.StrongOpennessFromOhsawaTakegoshi

set_option autoImplicit false

/-!
# Strong openness from the regular Ohsawa--Takegoshi theorem

`ohsawaTakegoshiHyperplane_of_regular` derives the Ohsawa--Takegoshi interface
`OhsawaTakegoshiHyperplane` (arbitrary open convex domains, arbitrary extended-real
plurisubharmonic weights, arbitrary holomorphic data on the slice) from its regular case
`OhsawaTakegoshiHyperplaneRegular` (bounded convex domains, weights smooth and
plurisubharmonic near the closure).

* If the right-hand side is finite, `exists_extension_of_regular_of_exhaustion` applies to a
  bounded convex exhaustion (`exists_bounded_convex_exhaustion`).
* If it is infinite, only a holomorphic extension is required.  The domain is a proper subset
  (its last coordinate is bounded), so a convex exhaustion weight `ψ` makes the data
  weighted-`L²` (`exists_plurisubharmonic_weight_lintegral_lt_top`), and the finite case with
  the weight `ψ` produces the extension.

Composed with `increasingStrongOpenness_of_ohsawaTakegoshi`, strong openness for increasing
sequences follows from the regular case alone.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka

noncomputable section



/-- **The Ohsawa--Takegoshi theorem from its regular case.** -/
theorem ohsawaTakegoshiHyperplane_of_regular (hOTR : OhsawaTakegoshiHyperplaneRegular) :
    OhsawaTakegoshiHyperplane := by
  intro m
  let _ : MeasurableSpace (ComplexModel m) := borel _
  have _ : BorelSpace (ComplexModel m) := ⟨rfl⟩
  let _ : MeasurableSpace (ComplexModel (m + 1)) := borel _
  have _ : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
  intro R hR
  obtain ⟨C, hC, hreg⟩ := hOTR m R hR
  refine ⟨C, hC, fun Ω hΩo hΩc hΩR φ hφ c hc f hf => ?_⟩
  obtain ⟨K, hKo, hKc, hKb, hKcl, hKΩ, hKU⟩ := exists_bounded_convex_exhaustion hΩo hΩc
  let Ωo : TopologicalSpace.Opens (ComplexModel (m + 1)) := ⟨Ω, hΩo⟩
  by_cases hS : (∫⁻ w in hyperplaneEmbedding m ⁻¹' Ω,
      multiplierDensity (fun w => φ (hyperplaneEmbedding m w)) c f w) ≠ ⊤
  · exact exists_extension_of_regular_of_exhaustion hreg (Ω := Ωo) hΩR hKo hKc hKb hKcl hKΩ
      hKU hφ hc hf hS
  · rw [not_not] at hS
    have hne : Ω ≠ univ := by
      intro h
      have h1 := hΩR (EuclideanSpace.single (Fin.last m) (R : ℂ)) (h ▸ mem_univ _)
      simp [abs_of_pos hR] at h1
    obtain ⟨ψ, hψ, hψS⟩ :=
      exists_plurisubharmonic_weight_lintegral_lt_top hΩo hΩc hne hc hf.continuousOn
    obtain ⟨F, hF, hFext, -⟩ := exists_extension_of_regular_of_exhaustion hreg (Ω := Ωo) hΩR
      hKo hKc hKb hKcl hKΩ hKU hψ hc hf hψS.ne
    refine ⟨F, hF, hFext, ?_⟩
    rw [hS, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC).ne']
    exact le_top

/-- **Strong openness for increasing sequences** (Xia, Theorem 1.4.4) in every dimension, from
the regular case of the Ohsawa--Takegoshi theorem. -/
theorem increasingStrongOpenness_of_ohsawaTakegoshiRegular
    (hOTR : OhsawaTakegoshiHyperplaneRegular) (n : ℕ) : IncreasingStrongOpenness n :=
  increasingStrongOpenness_of_ohsawaTakegoshi (ohsawaTakegoshiHyperplane_of_regular hOTR) n

end

end Hironaka
