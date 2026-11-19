import Mathlib.Topology.UniformSpace.Dini
import Hironaka.Analytic.ThetaCapacityQuasiContinuity

set_option autoImplicit false

/-!
# Convergence in capacity of a decreasing sequence of potentials

Xia, Hironaka, Theorem 2.3.3 (`xia-sgpt:page-0063`), the decreasing case; the same
statement is the capacity convergence input of Darvas--Di Nezza--Lu
(`ddnl-mixed-monotonicity:2.4`), recorded in the blueprint as
`mmass:decreasing-capacity`.

If `u_k` decreases pointwise to `w` inside `PSH(X, theta)`, then `u_k -> w` in
`Cap_theta`: for every `delta > 0`,

  `Cap_theta({w + delta < u_k}) -> 0`.

The proof is the classical one and uses exactly two inputs, both already in
the workspace:

* **quasi-continuity** (`Hironaka.ThetaCapacityQuasiContinuity`, Xia's Theorem
  2.3.2): each of `w` and the `u_k` is continuous off an open set of
  arbitrarily small capacity;
* **countable subadditivity** of `Cap_theta`
  (`Hironaka.ThetaCapacity.thetaCapacity_iUnion_le`), which lets the countably
  many exceptional sets be collected into a single open `G` of capacity below
  the tolerance, with a geometric distribution of the tolerance.

Off `G` all the functions are continuous and the convergence is monotone, so
**Dini's theorem** upgrades it to a uniform bound: for `k` large,
`u_k < w + delta` everywhere off `G`, i.e. `{w + delta < u_k}` is contained in
`G`.  Dini is mathlib's `Antitone.tendstoUniformlyOn_of_forall_tendsto`; the
first section only puts it in the one-sided form used below.

**Scope, and a warning.**  As in `Hironaka.ThetaCapacityQuasiContinuity`, the
reference `V` and the potentials are assumed globally bounded, since that is
the range in which this workspace has quasi-continuity.  That restriction is
not innocuous.  Every `theta`-PSH potential `u` has a real upper bound `C`, so
`u - C <= 0` and hence `u - C <= V_theta`; if `V_theta` is unbounded below --
which happens exactly when `nK({theta})` is nonempty -- then *every*
`theta`-PSH potential is unbounded below, and the hypotheses
`IsThetaPshPotential` and `IsBoundedPotential` cannot be met together.  What
is proved below is therefore Xia's Theorem 2.3.3 on the stratum where
`V_theta` is bounded below, and nothing more there; the pre-existing
`Hironaka.ThetaCapacityChart` and `Hironaka.ThetaCapacityQuasiContinuity` carry
the same restriction.

The Dini theorem of the first section is unconditional and does not depend on
any of this.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace Hironaka.ThetaCapacityDecreasingConvergence

open Hironaka.PositiveClasses
open BoundedGlobalProduct
open Hironaka.ThetaCapacity
open Hironaka.ThetaCapacityQuasiContinuity

noncomputable section

/-! ## Dini's theorem, in the one-sided form used below -/

section Dini

variable {X : Type*} [TopologicalSpace X]

/-- **Dini's theorem, one-sided form.**  Let `f k` be continuous on a compact
set `K`, antitone in `k` at every point of `K`, and converging pointwise on
`K` to a function `g` continuous on `K`.  Then for every `delta > 0` the
inequality `f k < g + delta` holds on all of `K` simultaneously, for every
large `k`.  This is mathlib's `Antitone.tendstoUniformlyOn_of_forall_tendsto`
read through the metric characterization of uniform convergence. -/
theorem exists_forall_lt_add_of_antitone_of_continuousOn
    {K : Set X} (hK : IsCompact K) {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ k, ContinuousOn (f k) K) (hg : ContinuousOn g K)
    (hanti : ∀ x ∈ K, Antitone fun k => f k x)
    (hlim : ∀ x ∈ K, Tendsto (fun k => f k x) atTop (𝓝 (g x)))
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ k, N ≤ k → ∀ x ∈ K, f k x < g x + delta := by
  have h := Antitone.tendstoUniformlyOn_of_forall_tendsto hK hf hanti hg hlim
  rw [Metric.tendstoUniformlyOn_iff] at h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h delta hdelta)
  refine ⟨N, fun k hk x hx => ?_⟩
  have hd := hN k hk x hx
  rw [Real.dist_eq] at hd
  have := (abs_lt.mp hd).1
  linarith

end Dini

/-! ## Convergence in capacity -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The geometric distribution of a tolerance used to collect countably many
exceptional sets. -/
theorem tsum_ofReal_geometric_half (eps : ℝ) (heps : 0 < eps) :
    ∑' j : ℕ, ENNReal.ofReal (eps / 2 / 2 / 2 ^ j) = ENNReal.ofReal (eps / 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    (summable_geometric_two' (eps / 2)), tsum_geometric_two']

/-- **The quantitative step.**  For every tolerance `eps > 0` there is an open
set `G` of capacity at most `eps` and an index `N` beyond which
`{w + delta < u_k}` is contained in `G`. -/
theorem exists_isOpen_forall_subset
    {theta : ClosedRealOneOneForm n M} {V : M → EReal}
    {c d : ℝ} (hcd : c ≤ d) (hVbd : ∀ x, (c : EReal) ≤ V x ∧ V x ≤ (d : EReal))
    {u : ℕ → M → EReal} {w : M → EReal}
    (hu : ∀ k, IsThetaPshPotential theta.val (u k))
    (hub : ∀ k, IsBoundedPotential (u k))
    (hw : IsThetaPshPotential theta.val w) (hwb : IsBoundedPotential w)
    (hanti : ∀ x, Antitone fun k => u k x)
    (hlim : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (w x)))
    {delta : ℝ} (hdelta : 0 < delta) {eps : ℝ} (heps : 0 < eps) :
    ∃ G : Set M, IsOpen G ∧ thetaCapacity theta V G ≤ ENNReal.ofReal eps ∧
      ∃ N : ℕ, ∀ k, N ≤ k →
        {x | w x + (delta : EReal) < u k x} ⊆ G := by
  classical
  -- one exceptional set for `w`, one for each `u k`, with geometric tolerances
  obtain ⟨G₀, hG₀open, hG₀cap, hG₀cont⟩ :=
    exists_isOpen_thetaCapacity_lt_continuousOn_compl hw hwb hcd hVbd
      (eps := eps / 2 / 2 / 2 ^ (0 : ℕ)) (by positivity)
  choose Gu hGuopen hGucap hGucont using fun k : ℕ =>
    exists_isOpen_thetaCapacity_lt_continuousOn_compl (hu k) (hub k) hcd hVbd
      (eps := eps / 2 / 2 / 2 ^ (k + 1)) (by positivity)
  set E : ℕ → Set M := fun j => Nat.rec G₀ (fun k _ => Gu k) j with hE_def
  have hE0 : E 0 = G₀ := rfl
  have hEsucc : ∀ k, E (k + 1) = Gu k := fun _ => rfl
  set G : Set M := ⋃ j, E j with hG_def
  have hGopen : IsOpen G := isOpen_iUnion fun j => by
    cases j with
    | zero => exact hG₀open
    | succ k => exact hGuopen k
  have hEcap : ∀ j, thetaCapacity theta V (E j) ≤ ENNReal.ofReal (eps / 2 / 2 / 2 ^ j) := by
    intro j
    cases j with
    | zero => exact hG₀cap.le
    | succ k => exact (hGucap k).le
  have hGcap : thetaCapacity theta V G ≤ ENNReal.ofReal eps := by
    refine le_trans (thetaCapacity_iUnion_le theta V E) ?_
    refine le_trans (ENNReal.tsum_le_tsum hEcap) ?_
    rw [tsum_ofReal_geometric_half eps heps]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- off `G` everything is continuous, and Dini applies
  have hKcompact : IsCompact Gᶜ := (hGopen.isClosed_compl).isCompact
  have hsub0 : Gᶜ ⊆ G₀ᶜ := compl_subset_compl.mpr (le_iSup E 0)
  have hsubk : ∀ k, Gᶜ ⊆ (Gu k)ᶜ := fun k =>
    compl_subset_compl.mpr (le_iSup E (k + 1))
  have hcontw : ContinuousOn (fun y => (w y).toReal) Gᶜ := hG₀cont.mono hsub0
  have hcontu : ∀ k, ContinuousOn (fun y => (u k y).toReal) Gᶜ := fun k =>
    (hGucont k).mono (hsubk k)
  have hantiR : ∀ x ∈ Gᶜ, Antitone fun k => (u k x).toReal := by
    intro x _ j k hjk
    exact EReal.toReal_le_toReal (hanti x hjk) ((hub k).ne_bot x) ((hub j).ne_top x)
  have hlimR : ∀ x ∈ Gᶜ, Tendsto (fun k => (u k x).toReal) atTop (𝓝 ((w x).toReal)) := by
    intro x _
    exact (EReal.tendsto_toReal (hwb.ne_top x) (hwb.ne_bot x)).comp (hlim x)
  obtain ⟨N, hN⟩ := exists_forall_lt_add_of_antitone_of_continuousOn hKcompact
    hcontu hcontw hantiR hlimR hdelta
  refine ⟨G, hGopen, hGcap, N, fun k hk x hx => ?_⟩
  by_contra hxG
  have hxK : x ∈ Gᶜ := hxG
  have hlt : (u k x).toReal < (w x).toReal + delta := hN k hk x hxK
  have hwx : ((w x).toReal : EReal) = w x := EReal.coe_toReal (hwb.ne_top x) (hwb.ne_bot x)
  have hux : ((u k x).toReal : EReal) = u k x :=
    EReal.coe_toReal ((hub k).ne_top x) ((hub k).ne_bot x)
  have hxmem : w x + (delta : EReal) < u k x := hx
  rw [← hwx, ← hux, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hxmem
  linarith

/-- **Xia, Hironaka, Theorem 2.3.3, decreasing case.**  A decreasing sequence of
globally bounded `theta`-PSH potentials converges to its pointwise limit in the
Monge--Ampere capacity relative to a globally bounded reference. -/
theorem tendsto_thetaCapacity_of_antitone
    {theta : ClosedRealOneOneForm n M} {V : M → EReal}
    {c d : ℝ} (hcd : c ≤ d) (hVbd : ∀ x, (c : EReal) ≤ V x ∧ V x ≤ (d : EReal))
    {u : ℕ → M → EReal} {w : M → EReal}
    (hu : ∀ k, IsThetaPshPotential theta.val (u k))
    (hub : ∀ k, IsBoundedPotential (u k))
    (hw : IsThetaPshPotential theta.val w) (hwb : IsBoundedPotential w)
    (hanti : ∀ x, Antitone fun k => u k x)
    (hlim : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (w x)))
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun k => thetaCapacity theta V {x | w x + (delta : EReal) < u k x})
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro eta heta
  rcases eq_or_ne eta ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  · have hreal : 0 < eta.toReal := ENNReal.toReal_pos heta.ne' htop
    obtain ⟨G, _, hGcap, N, hN⟩ :=
      exists_isOpen_forall_subset hcd hVbd hu hub hw hwb hanti hlim hdelta hreal
    filter_upwards [eventually_ge_atTop N] with k hk
    refine le_trans (le_trans (thetaCapacity_mono (hN k hk)) hGcap) ?_
    rw [ENNReal.ofReal_toReal htop]

end

end Hironaka.ThetaCapacityDecreasingConvergence
