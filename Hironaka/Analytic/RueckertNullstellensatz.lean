/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GermPrimeNullstellensatz

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Hironaka.RueckertNullstellensatz

open Hironaka
open AnalyticGermDecomposition

noncomputable section

variable {n : ℕ}

/-- **Rückert's Nullstellensatz, radical form.**  If the germs of `f_1, …, f_s` lie in `I`, every
germ vanishing on `{f_1 = ⋯ = f_s = 0}` near `0` lies in `√I`. -/
theorem vanishingIdeal_le_radical (I : Ideal (HolGerm (ComplexModel n))) {s : ℕ}
    (f : Fin s → ComplexModel n → ℂ)
    (hf : ∀ j, ∃ hfj : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f j) z, HolGerm.mk (f j) hfj ∈ I) :
    vanishingIdeal {z | ∀ j, f j z = 0} ≤ I.radical := by
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J hJ => ?_
  obtain ⟨hIJ, hJp⟩ := hJ
  have : J.IsPrime := hJp
  exact GermPrimeNullstellensatz.vanishingIdeal_le_of_isPrime J f fun j =>
    (hf j).imp fun _ h => hIJ h


end
end Hironaka.RueckertNullstellensatz
