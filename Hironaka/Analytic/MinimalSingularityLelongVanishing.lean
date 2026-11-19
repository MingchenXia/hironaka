import Hironaka.Analytic.BoucksomMinimalMultiplicityProof
import Hironaka.Analytic.KahlerDomination
import Hironaka.Analytic.ThetaPshConvexCombination
import Hironaka.Analytic.GlobalMultilinearExpansion
import Hironaka.Analytic.LelongNumberAdditivity
import Hironaka.Analytic.LelongNumberScaling
import Hironaka.Analytic.KahlerCurrentMax
import Hironaka.Analytic.PotentialTheory.Envelopes

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The minimal-singularity potential has zero Lelong number off the non-nef locus

Source: Copy-4, `sec:nK` (`references/transcendental-nakamaye-copy4-20260911/source/
main-Nulllocus.tex:483-499`): "If `α` is big and `θ ∈ α` is a smooth representative, it is
equivalently given by `E_nn(α) = {x ∈ X : ν(V_θ, x) > 0}`" (citing Xia, *Singularities in global
pluripotential theory*, Definitions 1.7.6--1.7.7; Boucksom 2004, §3), and its use in `sec:setup`
(`main-Nulllocus.tex:1400-1402`): "Since `V ⊄ E_nn(α)`, choose `x_* ∈ V \ E_nn(α)`.  Then
`ν(V_θ, x_*) = 0`."

This module proves the direction Copy-4 uses, for the project's definitions
(`Hironaka.NonKahlerLocus.nonNefLocus = ⋃_{ε>0} E_nK(α + ε{ω})`, `E_nK` = points where every Kähler
current has positive Lelong number, `V_θ = thetaPshSupremum θ`):

* `lelongNumber_thetaPshSupremum_eq_zero` — **for `α = {θ}` big on a compact manifold of positive
  dimension and `x ∉ E_nn(α)`, `ν(V_θ, x) = 0`.**
* `isThetaPshPotential_thetaPshSupremum` — for `α` big, `V_θ` is a `θ`-psh potential.

## The proof (Boucksom's argument, `Bou04` §3)

Fix a Kähler current `T₀ = θ₀ + ddᶜu₀ ≥ ω₀` in `α` (bigness) and `A > 0` with `Aω₀ ≥ ω`
(`KahlerDomination`).  For `ε > 0`, `x ∉ E_nK(α + ε{ω})` gives a Kähler current
`T_ε = θ_ε + ddᶜu_ε` in `α + ε{ω}` with `ν(u_ε, x) = 0`.  With `s = 1/(1 + εA)`,

  `w = s u_ε + (1 - s) u₀`  is  `(s θ_ε + (1-s)(θ₀ - ω₀))`-psh,

and adding the semipositive form `sε(Aω₀ - ω)` (here `sεA = 1 - s`) gives a form in the class
`s(α + ε{ω}) + (1-s)α - sε{ω} = α`.  So `w - f` is `θ`-psh for a smooth `f`, hence
`w - f ≤ V_θ + C` (minimal singularities), and

  `ν(V_θ, x) ≤ ν(w, x) ≤ s ν(u_ε, x) + (1 - s) ν(u₀, x) ≤ εA · ν(u₀, x)`.

`ν(u₀, x) < ∞` (`LelongNumberAdditivity.lelongNumber_ne_top`, positive dimension), and `ε → 0`.

Sorry-free.
-/

open Set Filter
open scoped Topology ENNReal NNReal

namespace Hironaka.MinimalSingularityLelongVanishing

open Hironaka Hironaka.PositiveClasses Hironaka.NonKahlerLocus
  Hironaka.NumericalRestrictedVolumeScaffold BoucksomMinimalMultiplicityProof
  ThetaPshConvexCombination GlobalDiagonalScaling GlobalMultilinearExpansion

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **`V_θ` is a `θ`-psh potential when `{θ}` is big**: the potential of a Kähler current in
`{θ}`, corrected by the `ddᶜ`-potential relating its representative to `θ`, is a competitor. -/
theorem isThetaPshPotential_thetaPshSupremum [CompactSpace Y] [Nonempty Y]
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    IsThetaPshPotential θ.val (thetaPshSupremum θ.val) := by
  obtain ⟨T₀⟩ := hbig
  obtain ⟨f, hf, hfeq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp T₀.represents
  have hu : IsThetaPshPotential θ.val (fun x => T₀.potential x - (f x : EReal)) :=
    PositiveClasses.thetaPshPotential_sub_smooth hf hfeq (isThetaPshPotential_representative T₀)
  exact _root_.Hironaka.PotentialTheory.Envelopes.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2 hu.1.hasSmoothLocalPotentials
    ⟨_, hu⟩

/-- **The key estimate.**  Let `T₀` be a Kähler current in `α = {θ}` with lower bound `ω₀`,
`A > 0` with `Aω₀ - ω` semipositive, and `T` a Kähler current in `α + ε{ω}`.  Then with
`s = 1/(1 + εA)`, `ν(V_θ, x) ≤ s ν(T, x) + (1 - s) ν(T₀, x)`. -/
theorem lelongNumber_thetaPshSupremum_le [CompactSpace Y] (omega : KahlerBackground n Y)
    (θ : ClosedRealOneOneForm n Y) (T₀ : KahlerCurrent (RealBottChern.ofRepresentative θ))
    {A : ℝ} (hA : 0 < A) (hAsemi : (-omega.form + A • T₀.lowerBound.form).val.IsSemipositive)
    {ε : ℝ} (hε : 0 < ε)
    (T : KahlerCurrent (RealBottChern.ofRepresentative θ +
      ε • RealBottChern.ofRepresentative omega.form)) (x : Y) :
    lelongNumber (n := n) (thetaPshSupremum θ.val) x ≤
      ENNReal.ofReal (1 / (1 + ε * A)) * lelongNumber (n := n) T.potential x +
        ENNReal.ofReal (1 - 1 / (1 + ε * A)) * lelongNumber (n := n) T₀.potential x := by
  have : Nonempty Y := ⟨x⟩
  set s : ℝ := 1 / (1 + ε * A) with hsdef
  have hεA : 0 < ε * A := mul_pos hε hA
  have h1 : 0 < 1 + ε * A := by linarith
  have hs : 0 < s := by positivity
  have hs1 : s < 1 := by rw [hsdef, div_lt_one h1]; linarith
  have hr : 0 < 1 - s := by linarith
  have hsεA : s * ε * A = 1 - s := by
    rw [hsdef]; field_simp; ring
  have hu : IsThetaPshPotential T.representative.val T.potential :=
    isThetaPshPotential_representative T
  have h₀ : IsThetaPshPotential (T₀.representative - T₀.lowerBound.form).val T₀.potential :=
    T₀.strictlyPsh
  -- the convex combination
  set w : Y → EReal := convexComb s T.potential T₀.potential with hwdef
  have hwpsh : ThetaPlurisubharmonic
      (s • T.representative + (1 - s) • (T₀.representative - T₀.lowerBound.form)).val w :=
    thetaPlurisubharmonic_add_smul hs hr hu.1 h₀.1
  have hwnd : LocallyNondegenerate w :=
    locallyNondegenerate_of_poles_pluripolar (n := n)
      ((manifoldLocallyPluripolar_union
        (quasiPsh_poles_manifoldLocallyPluripolar hu.quasiPshPotential)
        (quasiPsh_poles_manifoldLocallyPluripolar h₀.quasiPshPotential)).mono
        (poles_convexComb_subset hs hs1 _ _))
  have hw2 : IsThetaPshPotential
      (s • T.representative + (1 - s) • (T₀.representative - T₀.lowerBound.form) +
        (s * ε) • (-omega.form + A • T₀.lowerBound.form)).val w :=
    Hironaka.LocalPotentials.isThetaPshPotential_add_of_semipositive ⟨hwpsh, hwnd⟩
      (KahlerDomination.isSemipositive_smul hAsemi (by positivity))
  -- its form lies in the class of `θ`
  have hclass : RealBottChern.ofRepresentative
      (s • T.representative + (1 - s) • (T₀.representative - T₀.lowerBound.form) +
        (s * ε) • (-omega.form + A • T₀.lowerBound.form)) =
      RealBottChern.ofRepresentative θ := by
    have hsub : T₀.representative - T₀.lowerBound.form =
        T₀.representative + -T₀.lowerBound.form := sub_eq_add_neg _ _
    rw [hsub]
    simp only [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul,
      RealBottChern.ofRepresentative_neg, T.represents, T₀.represents]
    have hlin : ∀ α b c : RealBottChern n Y,
        s • (α + ε • b) + (1 - s) • (α + -c) + (s * ε) • (-b + A • c) =
          (s + (1 - s)) • α + (s * ε - s * ε) • b + (s * ε * A - (1 - s)) • c :=
      fun α b c => by module
    rw [hlin, hsεA, sub_self, sub_self, zero_smul, zero_smul, add_zero, add_zero,
      add_sub_cancel, one_smul]
  obtain ⟨f, hf, hfeq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hclass
  have hw3 : IsThetaPshPotential θ.val (fun y => w y - (f y : EReal)) :=
    PositiveClasses.thetaPshPotential_sub_smooth hf hfeq hw2
  obtain ⟨C, hC⟩ := _root_.Hironaka.PotentialTheory.Envelopes.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
    hw3.1.hasSmoothLocalPotentials ⟨_, hw3⟩ _ hw3
  -- the Lelong-number chain
  have k1 : lelongNumber (n := n) (thetaPshSupremum θ.val) x
      ≤ lelongNumber (n := n) (fun y => thetaPshSupremum θ.val y + (C : EReal)) x := by
    have h := LelongNumberComparison.lelongNumber_le_sub (n := n)
      (u := thetaPshSupremum θ.val) (h := fun _ => -C) (x := x) continuousAt_const
    simpa [sub_eq_add_neg] using h
  have k2 : lelongNumber (n := n) (fun y => thetaPshSupremum θ.val y + (C : EReal)) x
      ≤ lelongNumber (n := n) (fun y => w y - (f y : EReal)) x :=
    KahlerCurrentMax.lelongNumber_le_of_eventually_le
      (Eventually.of_forall fun y => hC y (mem_univ y))
  have k3 : lelongNumber (n := n) (fun y => w y - (f y : EReal)) x
      ≤ lelongNumber (n := n) w x :=
    KahlerCurrentMax.lelongNumber_sub_le
      (KahlerCurrentMax.continuous_of_chartSmooth hf).continuousAt
  have hq₁ : ManifoldQuasiPlurisubharmonic (n := n)
      (fun y => (s : EReal) * T.potential y) :=
    (thetaPlurisubharmonic_smul hs hu.1).quasiPlurisubharmonic
  have hq₂ : ManifoldQuasiPlurisubharmonic (n := n)
      (fun y => ((1 - s : ℝ) : EReal) * T₀.potential y) :=
    (thetaPlurisubharmonic_smul hr h₀.1).quasiPlurisubharmonic
  have k4 : lelongNumber (n := n) w x ≤
      lelongNumber (n := n) (fun y => (s : EReal) * T.potential y) x +
        lelongNumber (n := n) (fun y => ((1 - s : ℝ) : EReal) * T₀.potential y) x :=
    LelongNumberAdditivity.lelongNumber_add_le hq₁ hq₂ x
  have k5 := LelongNumberScaling.lelongNumber_smul_le (n := n) (u := T.potential) (x := x) hs
  have k6 := LelongNumberScaling.lelongNumber_smul_le (n := n) (u := T₀.potential) (x := x) hr
  exact k1.trans (k2.trans (k3.trans (k4.trans (add_le_add k5 k6))))

/-- **`ν(V_θ, x) = 0` off the non-nef locus** (Copy-4 `sec:nK`; Boucksom 2004 §3).  For `{θ}` big on
a compact complex manifold of positive dimension and `x ∉ E_nn({θ})`, the minimal-singularity
potential `V_θ` has zero Lelong number at `x`. -/
theorem lelongNumber_thetaPshSupremum_eq_zero [CompactSpace Y] (hn : 0 < n)
    (omega : KahlerBackground n Y) (θ : ClosedRealOneOneForm n Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {x : Y}
    (hx : x ∉ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    lelongNumber (n := n) (thetaPshSupremum θ.val) x = 0 := by
  obtain ⟨T₀⟩ := hbig
  obtain ⟨A, hA, hAsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul T₀.lowerBound (-omega.form)
  set K : ℝ≥0∞ := lelongNumber (n := n) T₀.potential x with hKdef
  have hK : K ≠ ⊤ := LelongNumberAdditivity.lelongNumber_ne_top hn
    T₀.strictlyPsh.1.quasiPlurisubharmonic T₀.strictlyPsh.2 x
  have hbound : ∀ ε : ℝ, 0 < ε →
      lelongNumber (n := n) (thetaPshSupremum θ.val) x ≤ ENNReal.ofReal (ε * A) * K := by
    intro ε hε
    have hxε : x ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ +
        ε • RealBottChern.ofRepresentative omega.form) := fun h =>
      hx (mem_nonNefLocus.mpr ⟨⟨ε, hε⟩, h⟩)
    rw [mem_nonKahlerLocus] at hxε
    obtain ⟨T, hT⟩ := not_forall.mp hxε
    have hT0 : lelongNumber (n := n) T.potential x = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hT)
    have h := lelongNumber_thetaPshSupremum_le omega θ T₀ hA hAsemi hε T x
    rw [hT0, mul_zero, zero_add] at h
    refine h.trans ?_
    gcongr
    have h1 : 0 < 1 + ε * A := by positivity
    have h2 : 1 - ε * A ≤ 1 / (1 + ε * A) := by
      rw [le_div_iff₀ h1]
      nlinarith [mul_pos hε hA]
    linarith
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (ε * A) * K) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε * A) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => ε * A) (𝓝 (0 : ℝ)) (𝓝 (0 * A)) := tendsto_id.mul_const A
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ε : ℝ => ENNReal.ofReal (ε * A)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hK)
  refine nonpos_iff_eq_zero.mp (ge_of_tendsto hlim ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

end

end Hironaka.MinimalSingularityLelongVanishing
