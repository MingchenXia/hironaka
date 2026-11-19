import Hironaka.Analytic.HormanderL2EstimateProof
import Hironaka.Analytic.HormanderDensity

set_option autoImplicit false

/-!
# Hörmander's `L²` estimate on convex domains: the theorem

`HormanderL2Estimate n` holds for every `n`: the density statement (Hörmander's Lemma 4.1.3) is
`exists_testForm_tendsto`, and the rest is `hormanderL2Estimate_of_density`.
-/

namespace Hironaka.Hormander

theorem hormanderDensityStatement (n : ℕ) : HormanderDensityStatement n :=
  fun _ hD _ _ hw₃ hψ _ _ hη hηev hηgrad _ _ _ hβ hγ hσ hT hS ↦
    exists_testForm_tendsto hD hw₃ hψ (fun k ↦ (hη k).1) (fun k ↦ (hη k).2.1)
      (fun k ↦ (hη k).2.2.1) (fun k x ↦ (hη k).2.2.2 x) hηev hηgrad hβ hγ hσ hT hS

/-- **Hörmander's `L²` estimate on convex domains**, in the form used for Ohsawa--Takegoshi. -/
theorem hormanderL2Estimate (n : ℕ) : HormanderL2Estimate n :=
  hormanderL2Estimate_of_density (hormanderDensityStatement n)

end Hironaka.Hormander
