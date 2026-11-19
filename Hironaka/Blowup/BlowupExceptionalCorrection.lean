import Hironaka.Blowup.BlowupNonKahlerLocus
import Hironaka.Analytic.LelongNumberScaling
import Hironaka.Analytic.LelongNumberAdditivity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Correcting a Kähler current back into a pullback class across the exceptional divisor

Source: CT22, proof of Lemma 4.2 (`transcendental-nakamaye-copy4-20260911`, `sec:prelim`).

Let `π : Z → Y` be the blowup of a compact Kähler manifold along a smooth centre and let
`ω_Z = π^* ω_Y + ε Θ` be the Blanchard Kähler form of `Hironaka.BlowupKahler`, where `Θ` is the
smooth closed form with local potentials `-c log U` for the Blanchard weight `U` of the
exceptional centre.  Since `log (U ∘ π)` is `Θ`-PSH
(`FactorizedWeightPsh.thetaPlurisubharmonic_logWeight`, i.e. `ddᶜ log(U ∘ π) ≥ Θ`), the class
`{Θ}` is carried by the exceptional divisor: the difference between `π^* α + t{ω_Z}` and
`π^* (α + t{ω_Y})` is `tε{Θ}`, and adding `tε log (U ∘ π)` to a potential moves a current from
the first class to the second **without losing positivity**.

* `blanchardCorrection`: the corrected Kähler current, in the pullback class.
* `lelongNumber_blanchardCorrection_le`: the correction costs at most
  `tε · ν(log (U ∘ π), z)` of Lelong number at `z`.  This is the exceptional loss that
  Boucksom's uniform minimal multiplicity has to beat.
-/

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace Hironaka.BlowupExceptionalCorrection

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  BlanchardWeight FactorizedWeightForm FactorizedWeightPsh BlowupExceptionalCentre

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

variable {θ : ClosedRealOneOneForm n Y} {C : Set Y} {g : Z → Y}
  {omegaY : KahlerBackground n Y} {omegaZ : KahlerBackground n Z}
  {D : BlanchardData n (exceptionalCentre n g)}

-- Twice the default budget: the `represents` field rewrites a Bott--Chern class equation and
-- the `strictlyPsh` field an equation between closed `(1,1)`-forms, both by `simp only`/`abel`
-- on the whole `KahlerCurrent` structure literal.
set_option maxHeartbeats 400000 in
/-- **The exceptional correction of a Kähler current.**  Adding `tε log (U ∘ π)` to the
potential moves a Kähler current of `π^* α + t{ω_Z}` into `π^* α + t π^*{ω_Y}` without losing
positivity, at the price of at most `tε · ν(log (U ∘ π), z)` of Lelong number at every point. -/
theorem exists_blanchardCorrection (hg : IsBlowupAlong n C g)
    (F : WeightFactorization n (fun z => D.weight (g z))) {ε : ℝ} (hε : 0 < ε)
    (homega : omegaZ.form =
      ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form + ε • F.closedForm)
    {t : ℝ} (ht : 0 < t)
    (S : KahlerCurrent (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ) +
      t • RealBottChern.ofRepresentative omegaZ.form)) :
    ∃ S' : KahlerCurrent (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ) +
      t • RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form)),
      ∀ z : Z, lelongNumber (n := n) S'.potential z ≤
        lelongNumber (n := n) S.potential z +
          ENNReal.ofReal (t * ε) *
            lelongNumber (n := n) (logWeight (fun z' => D.weight (g z'))) z := by
  have htε : 0 < t * ε := mul_pos ht hε
  have hrepZ : RealBottChern.ofRepresentative omegaZ.form =
      RealBottChern.ofRepresentative
          (ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form) +
        ε • RealBottChern.ofRepresentative F.closedForm := by
    rw [homega, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
  have hrep : RealBottChern.ofRepresentative S.representative =
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ) +
        t • (RealBottChern.ofRepresentative
            (ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form) +
          ε • RealBottChern.ofRepresentative F.closedForm) := by
    rw [← hrepZ]; exact S.represents
  refine ⟨{
    representative := S.representative - (t * ε) • F.closedForm
    represents := by
      simp only [sub_eq_add_neg, RealBottChern.ofRepresentative_add,
        RealBottChern.ofRepresentative_neg, RealBottChern.ofRepresentative_smul, hrep,
        smul_add, smul_smul]
      abel
    potential := fun z => S.potential z +
      ((t * ε : ℝ) : EReal) * logWeight (fun z' => D.weight (g z')) z
    lowerBound := S.lowerBound
    strictlyPsh := by
      refine ⟨?_, ?_⟩
      · have hsum := Hironaka.LocalPotentials.thetaPlurisubharmonic_add S.strictlyPsh.1
          (thetaPlurisubharmonic_logWeight F htε)
        have hform : S.representative - S.lowerBound.form + -((t * ε) • F.closedForm) =
            S.representative - (t * ε) • F.closedForm - S.lowerBound.form := by abel
        rwa [hform] at hsum
      · intro x U hU hxU
        have hnot : ¬ U ⊆ g ⁻¹' C := fun hsub => by
          have hx := interior_maximal hsub hU hxU
          rw [ExceptionalFibres.interior_preimage_eq_empty hg] at hx
          exact hx
        obtain ⟨z₀, hz₀U, hz₀C⟩ := not_subset.mp hnot
        have hU'open : IsOpen (U ∩ (g ⁻¹' C)ᶜ) :=
          hU.inter (hg.1.1.preimage hg.contMDiff.continuous).isOpen_compl
        obtain ⟨y, hyU', hy⟩ := S.strictlyPsh.2 z₀ _ hU'open ⟨hz₀U, hz₀C⟩
        refine ⟨y, hyU'.1, ?_⟩
        have hpos : 0 < D.weight (g y) :=
          D.weight_pos_of_notMem fun h2 => hyU'.2 (exceptionalCentre_subset hg h2)
        change S.potential y +
          ((t * ε : ℝ) : EReal) * logWeight (fun z' => D.weight (g z')) y ≠ ⊥
        rw [logWeight_of_pos (U := fun z' => D.weight (g z')) hpos, ← EReal.coe_mul]
        exact EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot _⟩ }, fun z => ?_⟩
  have hS : ManifoldQuasiPlurisubharmonic (n := n) S.potential :=
    S.strictlyPsh.1.quasiPlurisubharmonic
  have hW : ManifoldQuasiPlurisubharmonic (n := n)
      (fun z' => ((t * ε : ℝ) : EReal) * logWeight (fun z'' => D.weight (g z'')) z') :=
    (thetaPlurisubharmonic_logWeight F htε).quasiPlurisubharmonic
  refine (LelongNumberAdditivity.lelongNumber_add_le hS hW z).trans ?_
  gcongr
  exact LelongNumberScaling.lelongNumber_smul_le (n := n) (M := Z)
    (u := logWeight (fun z' => D.weight (g z'))) (x := z) htε

end

end Hironaka.BlowupExceptionalCorrection
