import Hironaka.Analytic.KahlerCurrentPerturbation
import Hironaka.Analytic.ThetaPshEnvelopes
import Hironaka.Analytic.LelongNumberComparison
import Hironaka.Analytic.PotentialTheory.LocalPotentials

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Proof of Boucksom's minimal multiplicities

Source: S. Boucksom, *Divisorial Zariski decompositions on compact complex
manifolds*, Ann. Sci. ÉNS 37 (2004), Section 3; CT22, Section 2 and the proof of
Lemma 4.2.

This module proves, sorry-free, the statement of
`Hironaka.BoucksomMinimalMultiplicity.exists_uniform_lelongNumber_lowerBound_of_mem_nonNefLocus`
(same hypotheses, same conclusion), so that named interface can be discharged.

## The proof

Write `b = {ω}`.  Membership `y ∈ E_nn(α) = ⋃_{ε>0} E_nK(α + εb)` produces one
`ε > 0` with `y ∈ E_nK(α + εb)`.  Put `s = 2ε/3` and `t₀ = ε/3`, so
`0 < t₀ < s < ε`.

*The uniform constant is the Lelong number of the minimal-singularity
potential.*  If `α + s b` carries no Kähler current at all, then neither does
`α + t b` for `t ≤ t₀ < s` — adding `(s-t)ω` to a Kähler current leaves a Kähler
current with the *same potential*
(`Hironaka.NonKahlerLocus.KahlerCurrent.addSmulKahler`) — so the conclusion is
vacuous and `c = 1` works.

Otherwise fix a Kähler current `T₀` in `α + s b`, let `Θ = θ_{T₀}` be its
representative and let `V = V_Θ = sup {u : u is Θ-PSH, u ≤ 0}` be the envelope of
`Θ`.  By `Hironaka.thetaPshSupremum_isThetaPshPotential` (which needs nothing
but one competitor, supplied by `T₀`) `V` is an actual `Θ`-PSH potential; then
`Θ + (ε-s)ω + ddᶜV ≥ (ε-s)ω` exhibits `V` as the potential of a Kähler current in
`α + εb`.  Hence `c := ν(V, y) > 0` by `y ∈ E_nK(α + εb)`.

*Every Kähler current in every `α + t b`, `0 < t ≤ t₀`, has `ν ≥ c` at `y`.*  Let
`T` be one, with potential `u`.  Discarding its own Kähler lower bound, `u` is
`θ_T`-PSH; adding the Kähler form `(s-t)ω` it is `(θ_T + (s-t)ω)`-PSH, and that
form has *exactly* the Bott–Chern class of `Θ`.  So the two differ by `ddᶜf` with
`f` chart-smooth, and `u - f` is `Θ`-PSH.  Minimality of the envelope
(`Hironaka.thetaPshSupremum_minimalSingularities`, which normalizes internally)
gives one constant `C` with `u - f ≤ V + C` on all of `Y`, whence

  `ν(V, y) ≤ ν(V + C, y) ≤ ν(u - f, y) ≤ ν(u, y)`,

the last two steps being monotonicity of the Lelong number in the potential and
invariance under subtracting a function continuous at `y`.  The constant `C` and
the function `f` depend on `T`, but the *bound* `ν(V, y)` does not: that is the
uniformity Boucksom's theorem asserts.

Everything here is sorry-free.  Nothing in it needs the Hironaka
statements or a regularization theorem.
-/

open Set Filter
open scoped Topology ENNReal NNReal

namespace Hironaka.BoucksomMinimalMultiplicityProof

open Hironaka Hironaka.PositiveClasses Hironaka.NonKahlerLocus
  Hironaka.NumericalRestrictedVolumeScaffold

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-! ### Elementary transport lemmas -/

/-- Splitting the perturbation parameter of a class. -/
theorem add_smul_split (alpha b : RealBottChern n Y) (t c : ℝ) :
    alpha + (t + c) • b = (alpha + t • b) + c • b := by
  rw [add_smul, add_assoc]

/-- Adding `cω` moves a Kähler current into any class *presented* as
`α + c{ω}`, without changing its potential.  The `beta = …` form avoids a
dependent cast at the use sites. -/
theorem exists_kahlerCurrent_potential_eq_of_eq_add_smul
    {alpha beta : RealBottChern n Y} (omega : KahlerBackground n Y) {c : ℝ} (hc : 0 < c)
    (hbeta : beta = alpha + c • RealBottChern.ofRepresentative omega.form)
    (T : KahlerCurrent alpha) :
    ∃ S : KahlerCurrent beta, S.potential = T.potential := by
  subst hbeta
  exact ⟨T.addSmulKahler omega hc, rfl⟩

/-- **The Kähler lower bound may be discarded.**  The potential of a Kähler
current is `θ`-PSH for its own representative `θ`. -/
theorem isThetaPshPotential_representative {alpha : RealBottChern n Y}
    (T : KahlerCurrent alpha) :
    IsThetaPshPotential T.representative.val T.potential := by
  have hsemi : (T.lowerBound.form - 0).val.IsSemipositive := by
    simpa using T.lowerBound.isSemipositive
  have h := Hironaka.LocalPotentials.isThetaPshPotential_add_of_semipositive
    T.strictlyPsh hsemi
  rwa [sub_add_sub_cancel, sub_zero] at h

/-! ### The envelope of a class is the potential of a Kähler current one step up -/

/-- **The minimal-singularity potential is a Kähler-current potential after an
arbitrarily small positive shift.**  If `T₀` is a Kähler current in `α` with
representative `Θ`, then for every `c > 0` the envelope `V_Θ` is the potential of
a Kähler current in `α + c{ω}`: `Θ + cω + ddᶜV_Θ ≥ cω`. -/
theorem exists_kahlerCurrent_potential_eq_thetaPshSupremum [CompactSpace Y] [Nonempty Y]
    {alpha beta : RealBottChern n Y} (omega : KahlerBackground n Y) {c : ℝ} (hc : 0 < c)
    (hbeta : beta = alpha + c • RealBottChern.ofRepresentative omega.form)
    (T₀ : KahlerCurrent alpha) :
    ∃ S : KahlerCurrent beta,
      S.potential = thetaPshSupremum T₀.representative.val := by
  subst hbeta
  have hΘpsh : IsThetaPshPotential T₀.representative.val T₀.potential :=
    isThetaPshPotential_representative T₀
  have hlocal : HasSmoothLocalPotentials T₀.representative.val :=
    hΘpsh.1.hasSmoothLocalPotentials
  have hV : IsThetaPshPotential T₀.representative.val
      (thetaPshSupremum T₀.representative.val) :=
    _root_.Hironaka.thetaPshSupremum_isThetaPshPotential _ T₀.representative.2.1 T₀.representative.2.2
      hlocal ⟨_, hΘpsh⟩
  have hform : (T₀.representative + c • omega.form)
      - (KahlerBackground.smul hc omega).form = T₀.representative := by
    rw [KahlerBackground.smul_form]; abel
  refine ⟨{ representative := T₀.representative + c • omega.form
            represents := by
              rw [RealBottChern.ofRepresentative_add,
                RealBottChern.ofRepresentative_smul, T₀.represents]
            potential := thetaPshSupremum T₀.representative.val
            lowerBound := KahlerBackground.smul hc omega
            strictlyPsh := by rw [hform]; exact hV }, rfl⟩

/-! ### The theorem -/

/-- **Boucksom's minimal multiplicities.**  A point of the non-nef locus admits a
positive lower bound for the Lelong number at that point, uniform over all Kähler
currents in all sufficiently small perturbations of the class. -/
theorem exists_uniform_lelongNumber_lowerBound_of_mem_nonNefLocus [CompactSpace Y]
    (omega : KahlerBackground n Y) (alpha : RealBottChern n Y) {y : Y}
    (hy : y ∈ nonNefLocus omega alpha) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, 0 < t → t ≤ t₀ →
        ∀ T : KahlerCurrent (alpha + t • RealBottChern.ofRepresentative omega.form),
          c ≤ lelongNumber (n := n) T.potential y := by
  classical
  have hYne : Nonempty Y := ⟨y⟩
  obtain ⟨ε, hyε⟩ := mem_nonNefLocus.mp hy
  have he : (0 : ℝ) < (ε : ℝ) := ε.2
  have ht0pos : (0 : ℝ) < (ε : ℝ) / 3 := by positivity
  by_cases hex : Nonempty (KahlerCurrent
      (alpha + (2 * (ε : ℝ) / 3) • RealBottChern.ofRepresentative omega.form))
  · obtain ⟨T₀⟩ := hex
    -- the envelope of `T₀`'s representative
    have hes : (0 : ℝ) < (ε : ℝ) - 2 * (ε : ℝ) / 3 := by linarith
    have hclassS : alpha + (ε : ℝ) • RealBottChern.ofRepresentative omega.form =
        (alpha + (2 * (ε : ℝ) / 3) • RealBottChern.ofRepresentative omega.form)
          + ((ε : ℝ) - 2 * (ε : ℝ) / 3) • RealBottChern.ofRepresentative omega.form := by
      rw [← add_smul_split]
      congr 2
      ring
    obtain ⟨S, hSpot⟩ := exists_kahlerCurrent_potential_eq_thetaPshSupremum
      omega hes hclassS T₀
    have hVpos : 0 < lelongNumber (n := n) (thetaPshSupremum T₀.representative.val) y := by
      rw [← hSpot]; exact hyε S
    refine ⟨lelongNumber (n := n) (thetaPshSupremum T₀.representative.val) y, hVpos,
      (ε : ℝ) / 3, ht0pos, fun t ht htt T => ?_⟩
    have hst : (0 : ℝ) < 2 * (ε : ℝ) / 3 - t := by linarith
    -- `T.potential` is PSH for a form in the Bott-Chern class of `T₀.representative`
    have hu2 : IsThetaPshPotential
        (T.representative + (2 * (ε : ℝ) / 3 - t) • omega.form).val T.potential :=
      Hironaka.LocalPotentials.isThetaPshPotential_add_of_semipositive
        (isThetaPshPotential_representative T)
        (by
          have h := (KahlerBackground.smul hst omega).isSemipositive
          rwa [KahlerBackground.smul_form] at h)
    have hclass2 : RealBottChern.ofRepresentative
        (T.representative + (2 * (ε : ℝ) / 3 - t) • omega.form)
        = RealBottChern.ofRepresentative T₀.representative := by
      rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul,
        T.represents, T₀.represents, ← add_smul_split]
      congr 2
      ring
    obtain ⟨f, hf, hfeq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hclass2
    have hu3 : IsThetaPshPotential T₀.representative.val
        (fun x => T.potential x - (f x : EReal)) :=
      PositiveClasses.thetaPshPotential_sub_smooth hf hfeq hu2
    obtain ⟨C, hC⟩ := _root_.Hironaka.thetaPshSupremum_minimalSingularities T₀.representative.val
      T₀.representative.2.1 T₀.representative.2.2
      (isThetaPshPotential_representative T₀).1.hasSmoothLocalPotentials
      ⟨_, isThetaPshPotential_representative T₀⟩ _ hu3
    -- the three Lelong-number steps
    have h1 : lelongNumber (n := n) (thetaPshSupremum T₀.representative.val) y
        ≤ lelongNumber (n := n)
            (fun x => thetaPshSupremum T₀.representative.val x + (C : EReal)) y := by
      have h := LelongNumberComparison.lelongNumber_le_sub (n := n)
        (u := thetaPshSupremum T₀.representative.val) (h := fun _ => -C) (x := y)
        continuousAt_const
      simpa [sub_eq_add_neg] using h
    have h2 : lelongNumber (n := n)
          (fun x => thetaPshSupremum T₀.representative.val x + (C : EReal)) y
        ≤ lelongNumber (n := n) (fun x => T.potential x - (f x : EReal)) y :=
      KahlerCurrentMax.lelongNumber_le_of_eventually_le
        (Eventually.of_forall fun x => hC x (mem_univ x))
    have h3 : lelongNumber (n := n) (fun x => T.potential x - (f x : EReal)) y
        ≤ lelongNumber (n := n) T.potential y :=
      KahlerCurrentMax.lelongNumber_sub_le
        (KahlerCurrentMax.continuous_of_chartSmooth hf).continuousAt
    exact h1.trans (h2.trans h3)
  · refine ⟨1, one_pos, (ε : ℝ) / 3, ht0pos, fun t ht htt T => ?_⟩
    have hst : (0 : ℝ) < 2 * (ε : ℝ) / 3 - t := by linarith
    obtain ⟨S, -⟩ := exists_kahlerCurrent_potential_eq_of_eq_add_smul
      (alpha := alpha + t • RealBottChern.ofRepresentative omega.form)
      (beta := alpha + (2 * (ε : ℝ) / 3) • RealBottChern.ofRepresentative omega.form)
      omega hst
      (by rw [← add_smul_split]; congr 2; ring) T
    exact absurd ⟨S⟩ hex

end

end Hironaka.BoucksomMinimalMultiplicityProof
