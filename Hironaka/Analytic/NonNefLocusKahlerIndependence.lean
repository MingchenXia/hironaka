import Hironaka.Analytic.KahlerCurrentPerturbation
import Hironaka.Analytic.KahlerDomination

set_option autoImplicit false

/-!
# The non-nef locus does not depend on the Kähler form

Source: Copy-4, `sec:nK` (`transcendental-nakamaye-copy4-20260911`); Boucksom,
*Divisorial Zariski decompositions*, Section 3; blueprint `ana:locus-properties`.

On a compact complex manifold with Kähler forms `ω` and `ω'`,
`E_nn^ω(α) = E_nn^{ω'}(α)`, where `E_nn^ω(α) = ⋃_{ε>0} E_nK(α + ε{ω})`.

Given `ε > 0`, compactness gives `A > 0` with `Aω - ω'` Kähler
(`KahlerDomination.exists_pos_isKahler_add_smul`), so with `δ = ε / A` the form
`K = εω - δω' = (ε/A)(Aω - ω')` is Kähler.  A Kähler current `S = θ + ddᶜu` in
`α + δ{ω'}` then yields the Kähler current `S + K` in `α + ε{ω}` with the SAME
potential `u` (`KahlerCurrent.addKahler`).  Hence every point of
`E_nK(α + ε{ω})` lies in `E_nK(α + δ{ω'})`, and the inclusion
`E_nn^ω(α) ⊆ E_nn^{ω'}(α)` follows; symmetry gives equality.

No local `ddᶜ` potential and no plurisubharmonicity lemma is needed, and
positive dimension is not used.
-/

open Set

namespace Hironaka.NonNefLocusKahlerIndependence

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus
  Hironaka.NumericalRestrictedVolumeScaffold

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A Kähler current stays a Kähler current after adding a Kähler form `K`, with
the same potential: `T + K` lies in `α + {K}` and dominates `ω' + K`. -/
def KahlerCurrent.addKahler {alpha : RealBottChern n M}
    (T : KahlerCurrent alpha) (K : KahlerBackground n M) :
    KahlerCurrent (alpha + RealBottChern.ofRepresentative K.form) where
  representative := T.representative + K.form
  represents := by
    rw [RealBottChern.ofRepresentative_add, T.represents]
  potential := T.potential
  lowerBound := T.lowerBound.add K
  strictlyPsh := by
    have hform : T.representative + K.form - (T.lowerBound.add K).form =
        T.representative - T.lowerBound.form := by
      rw [KahlerBackground.add_form]
      abel
    rw [hform]
    exact T.strictlyPsh

/-- Transport a Kähler current along an equality of classes, keeping the
potential. -/
def KahlerCurrent.ofEq {alpha beta : RealBottChern n M} (h : alpha = beta)
    (T : KahlerCurrent alpha) : KahlerCurrent beta where
  representative := T.representative
  represents := T.represents.trans h
  potential := T.potential
  lowerBound := T.lowerBound
  strictlyPsh := T.strictlyPsh

/-- For every `ε > 0` there is `δ > 0` such that `εω - δω'` is a Kähler form. -/
theorem exists_pos_kahlerBackground_eq_smul_sub_smul [CompactSpace M]
    (omega omega' : KahlerBackground n M) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ K : KahlerBackground n M,
      K.form = epsilon • omega.form - delta • omega'.form := by
  obtain ⟨A, hA, hK⟩ :=
    KahlerDomination.exists_pos_isKahler_add_smul omega (-omega'.form)
  let K₀ : KahlerBackground n M := ⟨-omega'.form + A • omega.form, hK⟩
  have hc : 0 < epsilon / A := div_pos heps hA
  refine ⟨epsilon / A, hc, KahlerBackground.smul hc K₀, ?_⟩
  rw [KahlerBackground.smul_form]
  change (epsilon / A) • (-omega'.form + A • omega.form) = _
  rw [smul_add, smul_neg, smul_smul, div_mul_cancel₀ epsilon hA.ne']
  abel

/-- One inclusion: `E_nn^ω(α) ⊆ E_nn^{ω'}(α)`. -/
theorem nonNefLocus_subset_nonNefLocus [CompactSpace M]
    (omega omega' : KahlerBackground n M) (alpha : RealBottChern n M) :
    nonNefLocus omega alpha ⊆ nonNefLocus omega' alpha := by
  intro x hx
  obtain ⟨epsilon, hxeps⟩ := mem_nonNefLocus.mp hx
  obtain ⟨delta, hdelta, K, hK⟩ :=
    exists_pos_kahlerBackground_eq_smul_sub_smul omega omega' epsilon.2
  refine mem_nonNefLocus.mpr ⟨⟨delta, hdelta⟩, fun S => ?_⟩
  have hclass : alpha + delta • RealBottChern.ofRepresentative omega'.form +
      RealBottChern.ofRepresentative K.form =
        alpha + (epsilon : ℝ) • RealBottChern.ofRepresentative omega.form := by
    rw [hK, sub_eq_add_neg, RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_smul, ← neg_smul,
      RealBottChern.ofRepresentative_smul]
    module
  exact hxeps (KahlerCurrent.ofEq hclass (KahlerCurrent.addKahler S K))

/-- **The non-nef locus does not depend on the Kähler form.** -/
theorem nonNefLocus_kahler_independent [CompactSpace M]
    (omega omega' : KahlerBackground n M) (alpha : RealBottChern n M) :
    nonNefLocus omega alpha = nonNefLocus omega' alpha :=
  (nonNefLocus_subset_nonNefLocus omega omega' alpha).antisymm
    (nonNefLocus_subset_nonNefLocus omega' omega alpha)

end

end Hironaka.NonNefLocusKahlerIndependence
