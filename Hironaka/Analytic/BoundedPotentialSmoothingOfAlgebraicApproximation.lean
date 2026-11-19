import Hironaka.Analytic.Demailly1992AlgebraicApproximation
import Hironaka.Analytic.CollarExhaustionDini

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Smoothing a bounded potential is a corollary of Demailly 2.6

`Hironaka.BoundedPotentialSmoothing` filed, in run 0082, a *third* named form of
Demailly 1992 Theorem 1.1: a globally bounded `θ`-PSH function on a compact
Kähler manifold is, up to `ε` in value and `εω` in curvature, a chart-smooth
function.  The human's decision `I-0598` is that Demailly 1992 is ONE named
input.  This module shows the bounded-potential form is not a separate input:
it is a corollary of `Demailly1992AlgebraicApproximation
.demailly1992_exists_algebraicApproximation` (`bou02-volume:2.6`).

## The deduction

Let `a ≤ u ≤ b`.  Apply 2.6 to `u` (it is `θ`-PSH and, being bounded below,
locally nondegenerate).  It returns `ψ_k ↓ u` with analytic singularities in the
`I-0489` convention and `θ + δ_k ω + ddᶜψ_k ≥ 0`, `δ_k → 0`.

* **No poles.**  `ψ_k ≥ u ≥ a > -∞`, so `ψ_k` never takes the value `-∞`; in
  the `I-0489` convention a presentation is smooth off its pole set
  (`SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole`), so
  `h_k := ψ_k.toReal` is chart-smooth.  This is Demailly's remark that for a
  bounded potential the multiplier ideals are trivial, read off the statement
  instead of the construction.
* **Curvature.**  Where `ψ_k` is smooth, `θ + δ_k ω + ddᶜh_k` is semipositive
  pointwise (`isOneOne_and_semipositive_add_smoothDDC_of_smoothOffPoleSet`);
  once `δ_k ≤ ε` add the semipositive `(ε - δ_k) ω`.
* **Lower comparison** `u ≤ h_k + ε`: clause (ii) gives `u ≤ ψ_k`.
* **Upper comparison** `h_k ≤ b + ε`: Dini's argument.  Each `h_k` is
  continuous, the sets `{h_k < b + ε}` increase with `k` (clause (ii)), and they
  cover `M` because `⨅ k, ψ_k x = u x ≤ b < b + ε`; `M` is compact, so one of
  them is all of `M`.  The limit `u` is only upper semicontinuous, which is why
  this is the one-sided form of Dini and not mathlib's.

So the two comparison clauses, which `BoundedPotentialSmoothing`'s docstring
calls "reconstructed rather than quoted", are now **proved** from clause (ii)
of the source theorem; clause (iii) is not used.
-/

open Set Filter
open scoped Topology

namespace Hironaka.BoundedPotentialSmoothingOfAlgebraicApproximation

open Hironaka.PositiveClasses Hironaka.NumericalRestrictedVolumeScaffold
  Hironaka.AdmissibleCurrentFormPositivity Demailly1992AlgebraicApproximation

noncomputable section

/-- **One-sided Dini.**  On a compact space, a pointwise antitone sequence of
continuous real functions that eventually drops below `c` at every point drops
below `c` everywhere from one index on.  No continuity of the limit is needed. -/
theorem exists_forall_lt_of_antitone {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : ℕ → X → ℝ} (hf : ∀ k, Continuous (f k)) (hanti : ∀ x, Antitone fun k => f k x)
    {c : ℝ} (hlt : ∀ x, ∃ k, f k x < c) : ∃ K, ∀ k, K ≤ k → ∀ x, f k x < c := by
  have hmono : Monotone fun k => {x | f k x < c} :=
    fun i j hij x hx => lt_of_le_of_lt (hanti x hij) hx
  obtain ⟨K, hK⟩ := isCompact_univ.elim_directed_cover (fun k => {x | f k x < c})
    (fun k => isOpen_lt (hf k) continuous_const)
    (fun x _ => mem_iUnion.mpr (hlt x)) hmono.directed_le
  exact ⟨K, fun k hk x => hmono hk (hK (mem_univ x))⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A potential bounded below by a real constant is locally nondegenerate. -/
theorem locallyNondegenerate_of_coe_le {u : M → EReal} {a : ℝ}
    (hlow : ∀ x, (a : EReal) ≤ u x) : LocallyNondegenerate u :=
  fun x _ _ hx => ⟨x, hx, ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hlow x)⟩

/-- A function that is smooth off its pole set and has no poles is chart-smooth
after `toReal`. -/
theorem chartSmooth_toReal_of_smoothOffPoleSet {v : M → EReal}
    (hv : SmoothOffPoleSet (n := n) v) (hfin : ∀ x, v x ≠ ⊥) :
    ChartSmooth (n := n) (fun x => (v x).toReal) := by
  intro e z hz
  have hpole : e.val.symm z ∉ poleSet v := by
    rw [mem_poleSet]
    exact hfin _
  obtain ⟨g, hg, hvg⟩ := hv e z hz hpole
  have heq : (fun y => (v (e.val.symm y)).toReal) =ᶠ[𝓝 z] g := by
    filter_upwards [hvg] with y hy
    change (chartFunction v e y).toReal = g y
    rw [hy, EReal.toReal_coe]
  exact (hg.self_of_nhds.congr_of_eventuallyEq heq).contDiffWithinAt

/-- **The curvature clause.**  A pole-free potential that is
`(θ + δω)`-PSH and smooth off its poles has `θ + ddᶜv + εω` semipositive in every
chart, as soon as `δ ≤ ε`. -/
theorem coefficientSemipositive_add_smul_of_le (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {v : M → EReal} {δ ε : ℝ} (hδε : δ ≤ ε)
    (hv : ThetaPlurisubharmonic (theta + δ • omega.form).val v)
    (hs : SmoothOffPoleSet (n := n) v) (hfin : ∀ x, v x ≠ ⊥)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    CoefficientSemipositive
      (theta.val.coeff e z + smoothDDC (fun y => (v (e.val.symm y)).toReal) z
        + ε • omega.form.val.coeff e z) := by
  have hpole : e.val.symm z ∉ poleSet v := by
    rw [mem_poleSet]
    exact hfin _
  have h := (isOneOne_and_semipositive_add_smoothDDC_of_smoothOffPoleSet
    (theta + δ • omega.form) hv hs e hz hpole).2
  rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul] at h
  have hω : CoefficientSemipositive (omega.form.val.coeff e z) :=
    fun w => omega.isSemipositive e z hz w
  have hsum := coefficientSemipositive_add h
    (coefficientSemipositive_smul (sub_nonneg.mpr hδε) hω)
  convert hsum using 1
  module

/-- **`BoundedPotentialSmoothing`'s statement, from Demailly 2.6.**  The
statement is character for character that of
`BoundedPotentialSmoothing.demailly1992_exists_chartSmooth_of_bounded_thetaPsh`. -/
theorem exists_chartSmooth_of_bounded_thetaPsh
    [CompactSpace M] (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : ThetaPlurisubharmonic theta.val u)
    {a b : ℝ} (hlow : ∀ x, (a : EReal) ≤ u x) (hupp : ∀ x, u x ≤ (b : EReal))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ h : M → ℝ, ChartSmooth (n := n) h ∧
      (∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
        CoefficientSemipositive
          (theta.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z
            + eps • omega.form.val.coeff e z)) ∧
      (∀ x, u x ≤ ((h x + eps : ℝ) : EReal)) ∧
      (∀ x, h x ≤ b + eps) := by
  obtain ⟨psiSeq, delta, -, hsmooth, hanti, hinf, -, hdlim, hpsh⟩ :=
    demailly1992_exists_algebraicApproximation omega theta u
      ⟨hu, locallyNondegenerate_of_coe_le hlow⟩
  have hge : ∀ k x, u x ≤ psiSeq k x := fun k x => by
    rw [← hinf x]
    exact iInf_le _ k
  have hbot : ∀ k x, psiSeq k x ≠ ⊥ := fun k x =>
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) ((hlow x).trans (hge k x))
  have htop : ∀ k x, psiSeq k x ≠ ⊤ := fun k x =>
    (hpsh k).quasiPshPotential.1.ne_top x
  have hcoe : ∀ k x, (((psiSeq k x).toReal : ℝ) : EReal) = psiSeq k x :=
    fun k x => EReal.coe_toReal (htop k x) (hbot k x)
  have hsos : ∀ k, SmoothOffPoleSet (n := n) (psiSeq k) := fun k =>
    SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole (hsmooth k)
  have hcont : ∀ k, Continuous fun x => (psiSeq k x).toReal := fun k =>
    continuous_iff_continuousAt.mpr fun x =>
      CollarExhaustionDini.continuousAt_toReal_of_hasManifoldAnalyticSingularitiesSmoothOffPole
        (hsmooth k) (hbot k x)
  have hanti' : ∀ x, Antitone fun k => (psiSeq k x).toReal := fun x _ _ hij =>
    EReal.toReal_le_toReal (hanti x hij) (hbot _ x) (htop _ x)
  have hlt : ∀ x, ∃ k, (psiSeq k x).toReal < b + eps := by
    intro x
    have hux : u x < ((b + eps : ℝ) : EReal) :=
      lt_of_le_of_lt (hupp x) (EReal.coe_lt_coe_iff.mpr (by linarith))
    rw [← hinf x] at hux
    obtain ⟨k, hk⟩ := iInf_lt_iff.mp hux
    refine ⟨k, ?_⟩
    rw [← hcoe k x] at hk
    exact EReal.coe_lt_coe_iff.mp hk
  obtain ⟨K₁, hK₁⟩ := exists_forall_lt_of_antitone (f := fun k x => (psiSeq k x).toReal)
    hcont hanti' hlt
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp (hdlim (Iic_mem_nhds heps))
  refine ⟨fun x => (psiSeq (max K₁ K₂) x).toReal,
    chartSmooth_toReal_of_smoothOffPoleSet (hsos _) (hbot _), ?_, ?_, ?_⟩
  · intro e z hz
    exact coefficientSemipositive_add_smul_of_le omega theta (hK₂ (max K₁ K₂) (le_max_right K₁ K₂))
      (hpsh _).1 (hsos _) (hbot _) e hz
  · intro x
    calc u x ≤ psiSeq (max K₁ K₂) x := hge _ x
      _ = (((psiSeq (max K₁ K₂) x).toReal : ℝ) : EReal) := (hcoe _ x).symm
      _ ≤ (((psiSeq (max K₁ K₂) x).toReal + eps : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by linarith)
  · intro x
    exact (hK₁ (max K₁ K₂) (le_max_left K₁ K₂) x).le

end

end Hironaka.BoundedPotentialSmoothingOfAlgebraicApproximation
