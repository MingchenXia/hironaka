import Hironaka.Analytic.ResidualNefReduction
import Hironaka.Analytic.PshRemovableSingularity
import Hironaka.Analytic.BoundedPotentialSmoothing
import Hironaka.Analytic.MeteredDivisorGlobalIdeal
import Hironaka.Analytic.ManifoldTubePositivity
import Hironaka.Manifold.ChartDifferentiable
import Hironaka.Analytic.AnalyticGluingData
import Hironaka.Analytic.PullbackNonvanishing

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `lem:residual-nef` (Copy-4; Xia, *Hironaka*, Lemma 1.6.1)

> Let `X` be a compact Kähler manifold, let `θ` be a smooth closed real
> `(1,1)`-form on `X`, and let `φ ∈ PSH(X, θ)` have log singularities along an
> effective `ℚ`-divisor `D`.  Then the class `{θ} - {D}` is nef.  If moreover
> `θ + ddᶜφ` is a Kähler current, then `{θ} - {D}` is Kähler.

Source: `transcendental-nakamaye-copy4-20260911`,
`source/main-Nulllocus.tex:328-336`; used at `eq:AW-class` in Step 4 of
`prop:principalization` (`:1903`) and at `:710`.

## What is proved here, and on what it rests

The mathematics splits into three parts, and only the middle one is assumed.

1. **Reduction** (proved, `Hironaka.ResidualNefReduction`): the residual
   `b = φ - ψ_D` is a bounded real function which is `(θ - Θ_D)`-PSH *off*
   `Supp D`, and `Supp D` is a proper analytic subset.
2. **Removable singularity** (named classical input,
   `Hironaka.PshRemovableSingularity`, Demailly CADG I.5.24): `b` therefore has a
   global `(θ - Θ_D)`-PSH representative `b*`, its regularization across
   `Supp D`.  Proved here: `b*` inherits the two-sided bound of `b` — the lower
   bound because a proper analytic subset has empty interior, so every
   neighbourhood of a point of `Supp D` meets its complement.
3. **Smoothing** (named classical input,
   `Hironaka.BoundedPotentialSmoothing`, Demailly 1992 Theorem 1.1 for a bounded
   potential): a bounded `(θ - Θ_D)`-PSH function is, up to `ε ω` in curvature,
   chart-smooth.  That is nefness.

The **Kähler half reduces to the nef half with no further input** (it is not
itself sorry-free — it goes through both named inputs): a Kähler current `θ + ddᶜφ ≥ ω'` gives log singularities along the same
`D` for the form `θ - ω'`, and nefness of `θ - ω' - Θ_D` *taken with respect to
`ω'` itself* at `ε = 1/2` leaves `θ - Θ_D + ddᶜh ≥ ½ ω' > 0`.  No comparison of
two Kähler forms, and no compactness beyond what part 3 already uses, is
needed for that step.

Neither named input is an instantiation of the other, and the removable
singularity statement is not an instance of `lem:residual-nef` at all.  The
smoothing statement *does* contain the `D = 0` case of the nefness half
(`ψ_0 = 0`), which is recorded honestly rather than hidden: what this module
adds to it is parts 1 and 2 and the Kähler half.  That measurement is not
prose — `coefficientSemipositive_of_residualNef` below **proves** the converse
direction, sorry-free, from the nef half taken as a hypothesis, and shows that
the entire residue of the split is the two approximation clauses.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.ResidualNef

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.AnalyticGluingData
  Hironaka.NumericalRestrictedVolumeScaffold
  ThetaPshCodimTwoExtension PshAnalyticSetExtension
  ResidualNefReduction PshRemovableSingularity BoundedPotentialSmoothing
  ManifoldTubePositivity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Local potentials of a difference -/

/-- A difference of two forms with smooth local potentials has smooth local
potentials. -/
theorem hasSmoothLocalPotentials_sub {α β : ClosedRealOneOneForm n M}
    (hα : HasSmoothLocalPotentials α.val) (hβ : HasSmoothLocalPotentials β.val) :
    HasSmoothLocalPotentials (α - β).val := by
  intro e z hz
  obtain ⟨W₁, ρ₁, hzW₁, hpot₁⟩ := hα e z hz
  obtain ⟨W₂, ρ₂, hzW₂, hpot₂⟩ := hβ e z hz
  have hWopen : IsOpen (W₁ ∩ W₂) := hpot₁.1.inter hpot₂.1
  refine ⟨W₁ ∩ W₂, fun y => ρ₁ y - ρ₂ y, ⟨hzW₁, hzW₂⟩, hWopen,
    inter_subset_left.trans hpot₁.2.1,
    (hpot₁.2.2.1.mono inter_subset_left).sub (hpot₂.2.2.1.mono inter_subset_right), ?_⟩
  intro y hy
  rw [smoothDDC_sub hWopen (hpot₁.2.2.1.mono inter_subset_left)
      (hpot₂.2.2.1.mono inter_subset_right) hy,
    hpot₁.2.2.2 hy.1, hpot₂.2.2.2 hy.2, BlowupBigPullback.coeff_sub]

/-- The curvature of a metered divisor has smooth local potentials: the smooth
term of its own local presentation is one. -/
theorem hasSmoothLocalPotentials_curvature (D : MeteredEffectiveQDivisor n M) :
    HasSmoothLocalPotentials D.curvature.val :=
  (MeteredDivisorPositivity.thetaPlurisubharmonic_weight D).hasSmoothLocalPotentials

/-! ### `Supp D` is a proper analytic subset -/

/-- The support of a metered effective `ℚ`-divisor on a compact manifold is a
complex analytic subset: it is the pole set of a weight with analytic
singularities. -/
theorem isComplexAnalyticSubset_support [CompactSpace M]
    (D : MeteredEffectiveQDivisor n M) :
    IsComplexAnalyticSubset (n := n) D.support := by
  obtain ⟨c, 𝔞, hc, -, htype⟩ :=
    MeteredDivisorGlobalIdeal.exists_hasAnalyticSingularitiesOfType D
  exact isComplexAnalyticSubset_poleSet_of_hasAnalyticSingularities
    ⟨c, 𝔞, hc, htype.2.1, htype.2.2⟩

/-! ### The regularized residual keeps the bound -/

/-- Upper bound: upper regularization does not exceed a constant bound. -/
theorem extensionAcross_le_of_forall_le {A : Set M} {v : M → EReal} {c : ℝ}
    (hv : ∀ x, v x ≤ (c : EReal)) (x : M) :
    extensionAcross A v x ≤ (c : EReal) := by
  classical
  refine uscRegularization_le (g := fun _ => (c : EReal))
    (fun _ _ h => Filter.Eventually.of_forall fun _ => h) (fun y => ?_) x
  by_cases hy : y ∈ A
  · simp [hy]
  · simpa [hy] using hv y

/-- Lower bound: if every neighbourhood of `x` meets the complement of `A`,
where `v` is bounded below, the upper regularization keeps that bound. -/
theorem le_extensionAcross_of_interior_eq_empty {A : Set M} {v : M → EReal} {c : ℝ}
    (hA : interior A = ∅) (hv : ∀ x, (c : EReal) ≤ v x) (x : M) :
    (c : EReal) ≤ extensionAcross A v x := by
  classical
  refine le_iInf fun U => le_iInf fun hU => ?_
  obtain ⟨y, hyU, hyA⟩ : ∃ y ∈ U, y ∉ A := by
    by_contra hcon
    have hsub : U ⊆ A := fun y hy => by
      by_contra hyA
      exact hcon ⟨y, hy, hyA⟩
    have hmem : A ∈ 𝓝 x := Filter.mem_of_superset hU hsub
    have hx : x ∈ interior A := mem_interior_iff_mem_nhds.mpr hmem
    rw [hA] at hx
    exact hx
  refine le_iSup_of_le y (le_iSup_of_le hyU ?_)
  simpa [hyA] using hv y

/-! ### `lem:residual-nef`: the nef half -/

/-- **`lem:residual-nef`, first sentence.**  On a compact connected Kähler
manifold, if `φ` is a `θ`-PSH potential with log singularities along the
metered effective `ℚ`-divisor `D`, then `{θ} - {D}` is nef.

Rests on the two named classical inputs
`PshRemovableSingularity.demaillyCadgI524_analyticRemovableThetaPsh` and
`BoundedPotentialSmoothing.demailly1992_exists_chartSmooth_of_bounded_thetaPsh`;
everything else is proved. -/
theorem nefWithRespectTo_sub_curvature [CompactSpace M] [ConnectedSpace M] [Nonempty M]
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    {D : MeteredEffectiveQDivisor n M} {phi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (L : HasLogSingularitiesAlong D phi) :
    NefWithRespectTo omega (theta - D.curvature) := by
  classical
  set A : Set M := D.support with hAdef
  set b : M → EReal := fun x => (L.residual x : EReal) with hbdef
  -- the reduction half
  have hoff : ThetaPshOff (theta - D.curvature).val A b :=
    thetaPshOff_residual hphi.1 L
  have hbound : LocallyBoundedAboveOff A b := L.locallyBoundedAboveOff
  have hanalytic : IsComplexAnalyticSubset (n := n) A := isComplexAnalyticSubset_support D
  have hproper : A ≠ univ := L.support_ne_univ hphi.2
  have hthetaPot : HasSmoothLocalPotentials (theta - D.curvature).val :=
    hasSmoothLocalPotentials_sub hphi.1.hasSmoothLocalPotentials
      (hasSmoothLocalPotentials_curvature D)
  -- the named removable-singularity input
  have hext : ThetaPlurisubharmonic (theta - D.curvature).val (extensionAcross A b) :=
    thetaPlurisubharmonic_extensionAcross_of_analyticRemovable
      (demaillyCadgI524_analyticRemovableThetaPsh _ hthetaPot A b)
      hanalytic hproper hoff hbound
  -- the regularized residual is bounded on both sides
  have hAint : interior A = ∅ :=
    IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ hanalytic hproper
  have hupp : ∀ x, extensionAcross A b x ≤ (L.bound : EReal) :=
    extensionAcross_le_of_forall_le
      (fun y => EReal.coe_le_coe_iff.mpr (L.le_bound y))
  have hlow : ∀ x, ((-L.bound : ℝ) : EReal) ≤ extensionAcross A b x :=
    le_extensionAcross_of_interior_eq_empty hAint
      (fun y => EReal.coe_le_coe_iff.mpr (L.neg_bound_le y))
  -- the named smoothing input
  intro eps heps
  obtain ⟨h, hh, hpos, -, -⟩ :=
    demailly1992_exists_chartSmooth_of_bounded_thetaPsh omega (theta - D.curvature)
      hext hlow hupp heps
  exact ⟨h, hh, hpos⟩

/-! ### Measuring the split -/

/-- **How much smaller than its consumer is the smoothing input?**  Exactly the
two approximation clauses, and no more.

`I-0578` asks that a split be measured by trying to prove the interface *from*
its consumer.  Here that direction really is available for the **curvature**
clause: take `D` to be the zero divisor, whose weight is `0` and whose
curvature is `0`, so that a bounded `θ`-PSH `u` has log singularities along it
with residual `u` itself.  The theorem below carries that out from the nef half
taken as a hypothesis, so it is sorry-free and the measurement is checkable.

What the converse does **not** give is `u ≤ h + ε` and `h ≤ b + ε`: a nefness
statement relates `h` to no function at all.  Those two clauses are therefore
the entire difference between
`BoundedPotentialSmoothing.demailly1992_exists_chartSmooth_of_bounded_thetaPsh`
and the `D = 0` case of `nefWithRespectTo_sub_curvature`, and they are recorded
because they are what Demailly's construction actually delivers — not because
the consumer needs them. -/
theorem coefficientSemipositive_of_residualNef
    (Hnef : ∀ (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
      (D : MeteredEffectiveQDivisor n M) (phi : M → EReal),
      IsThetaPshPotential theta.val phi → HasLogSingularitiesAlong D phi →
      NefWithRespectTo omega (theta - D.curvature))
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : ThetaPlurisubharmonic theta.val u)
    {a b : ℝ} (hlow : ∀ x, (a : EReal) ≤ u x) (hupp : ∀ x, u x ≤ (b : EReal))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ h : M → ℝ, ChartSmooth (n := n) h ∧
      ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
        CoefficientSemipositive
          (theta.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z
            + eps • omega.form.val.coeff e z) := by
  have hne_bot : ∀ x, u x ≠ ⊥ := fun x h => by
    have := hlow x; rw [h] at this; exact (EReal.bot_lt_coe a).not_ge this
  have hne_top : ∀ x, u x ≠ ⊤ := fun x h => by
    have := hupp x; rw [h] at this; exact (EReal.coe_lt_top b).not_ge this
  have hreal : ∀ x, u x = (((u x).toReal : ℝ) : EReal) :=
    fun x => (EReal.coe_toReal (hne_top x) (hne_bot x)).symm
  have hnd : LocallyNondegenerate u := fun x U _ hxU => ⟨x, hxU, hne_bot x⟩
  have L : HasLogSingularitiesAlong (MeteredDivisorOperations.zero n M) u :=
    { residual := fun x => (u x).toReal
      bound := |a| + |b|
      residual_bound := fun x => by
        have h1 : a ≤ (u x).toReal := by
          have := hlow x; rw [hreal x] at this; exact_mod_cast this
        have h2 : (u x).toReal ≤ b := by
          have := hupp x; rw [hreal x] at this; exact_mod_cast this
        have ha := le_abs_self a
        have ha' := neg_abs_le a
        have hb := le_abs_self b
        have hb' := neg_abs_le b
        rw [abs_le]
        constructor <;> linarith
      weight_add := fun x => by
        show u x = (0 : EReal) + (((u x).toReal : ℝ) : EReal)
        rw [zero_add, ← hreal x] }
  have hnef := Hnef omega theta (MeteredDivisorOperations.zero n M) u ⟨hu, hnd⟩ L
  have hcurv : (MeteredDivisorOperations.zero n M).curvature
      = (0 : ClosedRealOneOneForm n M) := rfl
  rw [hcurv, sub_zero] at hnef
  exact hnef eps heps

/-! ### `lem:residual-nef`: the Kähler half -/

/-- **`lem:residual-nef`, second sentence.**  If in addition `θ + ddᶜφ` is a
Kähler current, the class `{θ} - {D}` contains a Kähler form, namely
`θ - Θ_D + ddᶜh` for a chart-smooth `h`.

This half is proved from the nef half alone: writing `ω'` for the Kähler form
the current dominates, `φ` is `(θ - ω')`-PSH with the same log singularities
along `D`, so `θ - ω' - Θ_D` is nef *with respect to `ω'`*; taking `ε = 1/2`
leaves `θ - Θ_D + ddᶜh ≥ ½ ω'`. -/
theorem exists_chartSmooth_isKahler_sub_curvature
    [CompactSpace M] [ConnectedSpace M] [Nonempty M]
    {theta : ClosedRealOneOneForm n M} {D : MeteredEffectiveQDivisor n M}
    {phi : M → EReal} (hphi : IsKahlerCurrentPotential theta phi)
    (L : HasLogSingularitiesAlong D phi) :
    ∃ (h : M → ℝ) (hh : ChartSmooth (n := n) h),
      ((theta - D.curvature) + ddcClosedForm h hh).val.IsKahler := by
  obtain ⟨omega', hpot⟩ := hphi
  obtain ⟨h, hh, hpos⟩ :=
    nefWithRespectTo_sub_curvature omega' (theta := theta - omega'.form)
      (D := D) (phi := phi)
      (by simpa using hpot) L (1 / 2) (by norm_num)
  refine ⟨h, hh, ⟨fun e z hz => ⟨?_, ?_⟩, ((theta - D.curvature) + ddcClosedForm h hh).2.1⟩⟩
  · exact ((theta - D.curvature) + ddcClosedForm h hh).2.2 e z hz
  · intro v hv
    have hkey := hpos e z hz v
    have hstrict := (omega'.isKahler.1 e z hz).2 v hv
    rw [BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub] at hkey
    have hcoeff : ((theta - D.curvature) + ddcClosedForm h hh).val.coeff e z
        = (theta.val.coeff e z - D.curvature.val.coeff e z)
          + smoothDDC (fun y => h (e.val.symm y)) z := by
      rw [ClosedRealOneOneForm.coeff_add, BlowupBigPullback.coeff_sub,
        ddcClosedForm_coeff]
    rw [hcoeff]
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hkey ⊢
    linarith

end

end Hironaka.ResidualNef
