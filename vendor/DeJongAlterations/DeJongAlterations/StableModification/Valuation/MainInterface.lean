import DeJongAlterations.StableModification.Valuation.MainUniformization
import DeJongAlterations.StableModification.Valuation.UnramifiedEtale

/-!
# The interface statement M3 is a theorem

This file proves `UniformizationEtaleStatement` (`InterfaceStatement.lean`), the form of
Theorem 2.1.8 (`valunif`) of M. Temkin, *Stable modification of relative curves*, J. Algebraic
Geom. 19 (2010) (`semi-stable.tex`, l. 2056–2061) consumed by Proposition 4.3.3 (`locunifprop`,
l. 3059–3061): "there exists an element `T ∈ L` such that `L` is unramified over `K(T)`, and so
`O` is étale over `O ∩ K(T)` by Lemma 2.1.1". Plan `PLAN-SM-VAL.md`, node M3; blueprint
`thm:sm-val-interface` in `sm-val-main.tex`.

The standard-unramified generator of `MainUniformization.stdUnramifiedConclusion` gives
`Algebra.IsStandardEtale (O ∩ K(T)) O` by Temkin's Lemmas 2.1.1 and 2.1.6
(`IsStdUnramifiedGenerator.isStandardEtale`), which needs `O ∩ K(T)` to have finite height. This
holds because `K(T)/K` has transcendence degree one and `O ∩ K` has finite height
(`finite_primeSpectrum_of_trdeg_le_one`).

## Main results

* `finite_primeSpectrum_comap_adjoin`: `O ∩ K(T)` has finite height.
* `UniformizationHypotheses.uniformizationConclusion`: the hypotheses imply the conclusion.
* `uniformizationEtaleStatement` (**interface statement M3**).
-/

noncomputable section

open IsLocalRing
open scoped IntermediateField

namespace DeJongAlterations.StableModification.Valuation

open MainUniformization

universe u v

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O : ValuationSubring L}

/-- The trace of `O ∩ K(T)` on `K` is `O ∩ K`. -/
theorem comap_comap_adjoin (T : L) :
    (O.comap (algebraMap K⟮T⟯ L)).comap (algebraMap K K⟮T⟯) = O.comap (algebraMap K L) := by
  ext c
  rfl

/-- **`O ∩ K(T)` has finite height** when `O ∩ K` has, since `trdeg (K(T)/K) ≤ 1`. -/
theorem finite_primeSpectrum_comap_adjoin (h : UniformizationHypotheses K L O) (T : L) :
    Finite (PrimeSpectrum (O.comap (algebraMap K⟮T⟯ L))) := by
  have : Finite (PrimeSpectrum ((O.comap (algebraMap K⟮T⟯ L)).comap (algebraMap K K⟮T⟯))) := by
    rw [comap_comap_adjoin]
    exact h.finite_primeSpectrum
  have htr : Algebra.trdeg K K⟮T⟯ ≤ 1 :=
    (trdeg_le_of_injective (K⟮T⟯).val Subtype.val_injective).trans h.trdeg_eq_one.le
  exact finite_primeSpectrum_of_trdeg_le_one _ htr

/-- **Temkin, Theorem 2.1.8 with Lemma 2.1.1** (`semi-stable.tex` l. 2056–2061 and
l. 3059–3061; blueprint `thm:sm-val-interface`): under the uniformization hypotheses there is
`T ∈ L` transcendental over `K` with `O` standard étale over `O ∩ K(T)`. -/
theorem UniformizationHypotheses.uniformizationConclusion (h : UniformizationHypotheses K L O) :
    UniformizationConclusion K L O := by
  obtain ⟨T, hT, y, hy, -⟩ := stdUnramifiedConclusion h
  have := finite_primeSpectrum_comap_adjoin h T
  exact ⟨T, hT, hy.isStandardEtale⟩

/-- **The interface statement M3 holds** (plan `PLAN-SM-VAL.md` §9.1; Temkin, Theorem 2.1.8 in
the étale form consumed by Proposition 4.3.3). -/
theorem uniformizationEtaleStatement : UniformizationEtaleStatement.{u, v} :=
  fun _ _ _ _ _ _ h ↦ h.uniformizationConclusion

end DeJongAlterations.StableModification.Valuation
