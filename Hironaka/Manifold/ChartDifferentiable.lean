import Hironaka.Analytic.GlobalAnalyticSingularities
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false

/-!
# The pole set of a potential with analytic singularities is an analytic subset

Source: Demailly, *Complex analytic and differential geometry*, II.5 (the zero
set of a coherent ideal is analytic); Copy-4, `sec:nK`; blueprint
`ana:ideal-sheaves` and `ana:locus-properties`.

If `φ = c·log ∑|gᵢ|² + R` near every point, with `c > 0` rational, `gᵢ`
holomorphic and `R` bounded, then `φ y = -∞` exactly when all the `gᵢ` vanish at
`y` (`scaled_generatorLog_add_eq_bot_iff`).  So `poleSet φ` is locally the common
zero set of finitely many holomorphic functions, which is literally what
`IsComplexAnalyticSubset` asks for.

Two pieces are needed to match the encodings:

* `differentiableOn_comp_chartSymm`: manifold holomorphy
  (`MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)`, the convention of
  `HolomorphicIdealSheaves`) transported into the preferred chart as ordinary
  `DifferentiableOn ℂ` (the convention of `ComplexAnalyticPresentationAt`).  The
  chart inverse is holomorphic because it is the inverse of a chart of a complex
  manifold (`contMDiffOn_chart_symm`), and for maps between model spaces
  `MDifferentiableOn` is `DifferentiableOn`.
* `isComplexAnalyticSubset_poleSet_of_hasAnalyticSingularities`: the resulting
  local presentation.

The consumer is `Hironaka.LocusProperties.isComplexAnalyticSubset_nonKahlerLocus`,
which combines this with the (still open) Boucksom regularization theorem
supplying a Kähler current whose polar set is exactly `E_nK(α)`.
-/

open Set
open scoped Manifold ContDiff

namespace Hironaka

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Manifold holomorphy on `U`, read in the preferred chart at `x`, is ordinary
complex differentiability on the part of the chart target lying over `U`. -/
theorem differentiableOn_comp_chartSymm (x : M) {f : M → ℂ} {U : Set M}
    (hf : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f U) :
    DifferentiableOn ℂ (fun z => f ((complexChartAt (n := n) x).val.symm z))
      ((complexChartAt (n := n) x).val.target ∩
        (complexChartAt (n := n) x).val.symm ⁻¹' U) := by
  rw [← mdifferentiableOn_iff_differentiableOn]
  have hsymm : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (chartAt (ComplexModel n) x).symm (chartAt (ComplexModel n) x).target :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) (x := x)).mdifferentiableOn
      (by simp)
  exact hf.comp (hsymm.mono inter_subset_left) (fun z hz => hz.2)

open GlobalAnalyticSingularities NumericalRestrictedVolumeScaffold

/-- **The pole set of a potential with analytic singularities is a complex
analytic subset.** -/
theorem isComplexAnalyticSubset_poleSet_of_hasAnalyticSingularities
    {φ : M → EReal} (hφ : HasAnalyticSingularities (n := n) φ) :
    IsComplexAnalyticSubset (n := n) (poleSet φ) := by
  obtain ⟨c, 𝔞, hc, -, hloc⟩ := hφ
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  intro x
  obtain ⟨U, hUopen, hxU, N, g, hgdiff, -, R, Cb, -, hrep⟩ := hloc x
  refine ⟨{
    generatorCount := N
    generator := fun i z => g i ((complexChartAt (n := n) x).val.symm z)
    coordinateNeighborhood := (complexChartAt (n := n) x).val.target ∩
      (complexChartAt (n := n) x).val.symm ⁻¹' U
    isOpen_coordinateNeighborhood :=
      (complexChartAt (n := n) x).val.isOpen_inter_preimage_symm hUopen
    center_mem_coordinateNeighborhood := ?_
    coordinateNeighborhood_subset_target := inter_subset_left
    generator_holomorphic := fun i => differentiableOn_comp_chartSymm x (hgdiff i)
    zeroLocus := ?_ }⟩
  · refine ⟨(complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x), ?_⟩
    simp only [mem_preimage,
      (complexChartAt (n := n) x).val.left_inv (mem_complexChartAt_source x)]
    exact hxU
  · intro y hysrc hymem
    have hyy : (complexChartAt (n := n) x).val.symm
        ((complexChartAt (n := n) x).val y) = y :=
      (complexChartAt (n := n) x).val.left_inv hysrc
    have hyU : y ∈ U := by
      have := hymem.2
      rwa [mem_preimage, hyy] at this
    simp only [hyy, mem_poleSet, hrep y hyU]
    exact scaled_generatorLog_add_eq_bot_iff g y hcR (R y)

end

end Hironaka
