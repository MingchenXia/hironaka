/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.DivisorExponent
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.Invariant.MemberInterAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Invariant.BoundaryCount
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.IdealPowers
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.OrderTaylor
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Exponents of an ideal along the trace of a member on a submanifold

For an ideal `𝔞` of holomorphic germs, a set `N` (a submanifold) and a set `H` (in the application a member of `E`)
put `IsDivNearAlong n N 𝔞 H e x` when, near `x`, the points of `N ∩ H` lie in `cosupp(𝔞|_N, e)`; the **exponent along
`N`** `divExpAlong n N 𝔞 H x` is the largest such `e`.

The route is a **local holomorphic retraction** `r` onto `N` (`IsLocalRetraction`, from
`MarkedIdealOperationsAlong.exists_localRetraction`): at the points `z ∈ N` near `x`, the order of `f` along `N` is the
ambient order of `f ∘ r` (`IsLocalRetraction.vanishesToOrderOn_iff`).  This turns the statements along `N` into the
ambient ones of `DivisorExponent`:

* `IsLocalRetraction.eventually_eq_zero_of_forall`: **Krull along `N`** -- a germ of infinite order along `N` vanishes
  on `N` near `x`; hence the exponent is finite (`exists_not_isDivNearAlong`) where `𝔞|_N` does not vanish near `x`
  (`IsNonzeroAlongAt`);
* `isDivNearAlong_of_frequently` (**identity principle along `N ∩ H`**): the ambient identity principle
  `DivisorExponent.mem_idealPow_vanishingIdeal_of_frequently` applied to `s_i ∘ r`, `s_i` generators of `𝔞`, with the
  submanifold `C = N ∩ H`;
* `eventually_divExpAlong_eq`: **local constancy** of `divExpAlong` on `N ∩ H`;
* `IsLocalRetraction.mem_idealPow_vanishingIdeal_comp`: when moreover `r` maps `H` into `H` (adapted coordinates), the
  retracted germ `g ∘ r` lies in `𝓘_H^e` itself;
* for a simple normal crossings divisor `E` transverse to a closed `N` (`n > 0`): `regularAtDim_inter_get` (`N ∩ E_i` is
  regular, by `MemberInterAlong`) and `eventually_divExpAlong_get_eq`.

For `N = univ` the definitions are those of `DivisorExponent`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.DivisorExponentAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder Hironaka.OrderTaylor Hironaka.HadamardBridge Hironaka.IdealOrderArithmetic Hironaka.GermOrderProduct Hironaka.DivisorExponent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Local retractions: order along `N` is ambient order of the retracted germ -/

section Retraction

variable (n) in
/-- **`r` is a holomorphic retraction onto `N` near `x`**: `r x = x`, `r` is holomorphic near `x`, takes values in `N`
near `x`, and is the identity on `N` near `x`. -/
structure IsLocalRetraction (N : Set M) (r : M → M) (x : M) : Prop where
  apply_self : r x = x
  mdifferentiableAt : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) r y
  mem : ∀ᶠ y in 𝓝 x, r y ∈ N
  eq_self : ∀ᶠ y in 𝓝 x, y ∈ N → r y = y

variable {N : Set M} {r : M → M} {x : M}

/-- **Local retractions exist at regular points** (`MarkedIdealOperationsAlong.exists_localRetraction`). -/
theorem exists_isLocalRetraction {k : ℕ} (hN : RegularAtDim (n := n) N x k) :
    ∃ r, IsLocalRetraction n N r x := by
  obtain ⟨r, h1, h2, h3, h4⟩ := MarkedIdealOperationsAlong.exists_localRetraction hN
  exact ⟨r, ⟨h1, h2, h3, h4⟩⟩

theorem IsLocalRetraction.mem_self (h : IsLocalRetraction n N r x) : x ∈ N := by
  have := h.mem.self_of_nhds
  rwa [h.apply_self] at this

theorem IsLocalRetraction.tendsto (h : IsLocalRetraction n N r x) : Tendsto r (𝓝 x) (𝓝 x) := by
  have := h.mdifferentiableAt.self_of_nhds.continuousAt.tendsto
  rwa [h.apply_self] at this

/-- **The retraction data propagate** to the points of `N` near `x`. -/
theorem IsLocalRetraction.eventually (h : IsLocalRetraction n N r x) :
    ∀ᶠ z in 𝓝 x, z ∈ N → IsLocalRetraction n N r z := by
  filter_upwards [h.mdifferentiableAt.eventually_nhds, h.mem.eventually_nhds, h.eq_self.eventually_nhds,
    h.eq_self] with z h1 h2 h3 h4 hzN
  exact ⟨h4 hzN, h1, h2, h3⟩

/-- `r ∘ r = r` near `x`. -/
theorem IsLocalRetraction.eventually_comp_self (h : IsLocalRetraction n N r x) :
    ∀ᶠ y in 𝓝 x, r (r y) = r y := by
  filter_upwards [h.mem, h.tendsto.eventually h.eq_self] with y h1 h2
  exact h2 h1

theorem IsLocalRetraction.holomorphicAt_comp (h : IsLocalRetraction n N r x) {f : M → ℂ}
    (hf : HolomorphicAt n f x) : HolomorphicAt n (f ∘ r) x :=
  holomorphicAt_comp_map h.mdifferentiableAt (by rw [h.apply_self]; exact hf)

/-- A germ agrees on `N` with its retraction. -/
theorem IsLocalRetraction.eventually_eq_comp (h : IsLocalRetraction n N r x) (f : M → ℂ) :
    ∀ᶠ y in 𝓝 x, y ∈ N → f y = (f ∘ r) y := by
  filter_upwards [h.eq_self] with y hy hyN
  simp [hy hyN]

/-- **Order along `N` is the ambient order of the retracted germ**: `f|_N ∈ 𝔪_{N,x}^q` iff `f ∘ r ∈ 𝔪_x^q`. -/
theorem IsLocalRetraction.vanishesToOrderOn_iff (h : IsLocalRetraction n N r x) {f : M → ℂ} {q : ℕ} :
    VanishesToOrderOn n N x q f ↔ (idealPow (pointIdeal n x) q).mem x (f ∘ r) := by
  constructor
  · rintro ⟨g, hg, hfg⟩
    have hg' : (idealPow (pointIdeal n (r x)) q).mem (r x) g := by rw [h.apply_self]; exact hg
    refine mem_idealPow_congr (comp_mem_idealPow_pointIdeal h.mdifferentiableAt q hg') ?_
    filter_upwards [h.mem, h.tendsto.eventually hfg] with y hy1 hy2
    exact (hy2 hy1).symm
  · exact fun hfr => ⟨f ∘ r, hfr, h.eventually_eq_comp f⟩

/-- **Krull along `N`**: a germ lying in every power of `𝔪_{N,x}` vanishes on `N` near `x`. -/
theorem IsLocalRetraction.eventually_eq_zero_of_forall (h : IsLocalRetraction n N r x) {f : M → ℂ}
    (hf : HolomorphicAt n f x) (hall : ∀ q, VanishesToOrderOn n N x q f) : ∀ᶠ y in 𝓝 x, y ∈ N → f y = 0 := by
  have h0 := eventually_eq_zero_of_forall_mem_idealPow (h.holomorphicAt_comp hf)
    fun q => h.vanishesToOrderOn_iff.mp (hall q)
  filter_upwards [h0, h.eventually_eq_comp f] with y hy1 hy2 hyN
  rw [hy2 hyN]
  exact hy1

/-- A germ that does not vanish on `N` near `x` has finite order along `N`. -/
theorem IsLocalRetraction.exists_not_vanishesToOrderOn (h : IsLocalRetraction n N r x) {f : M → ℂ}
    (hf : HolomorphicAt n f x) (hne : ∃ᶠ y in 𝓝 x, y ∈ N ∧ f y ≠ 0) :
    ∃ q, ¬ VanishesToOrderOn n N x q f := by
  by_contra! hall
  exact hne ((h.eventually_eq_zero_of_forall hf hall).mono fun y hy ⟨hyN, hy0⟩ => hy0 (hy hyN))

end Retraction

/-! ### Divisibility along `N` near a point and the exponent -/

section Exponent

variable {N : Set M} {𝔞 : GermIdeal n M} {H : Set M} {r : M → M}

variable (n) in
/-- **`𝔞|_N ⊆ 𝓘_{N ∩ H}^e` near `x`, in cosupport form**: near `x`, the points of `N ∩ H` lie in
`cosupp(𝔞|_N, e)`. -/
def IsDivNearAlong (N : Set M) (𝔞 : GermIdeal n M) (H : Set M) (e : ℕ) (x : M) : Prop :=
  ∀ᶠ z in 𝓝 x, z ∈ N → z ∈ H → z ∈ cosupport n N 𝔞 e

theorem isDivNearAlong_zero (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (x : M) :
    IsDivNearAlong n N 𝔞 H 0 x :=
  Eventually.of_forall fun z hzN _ => by rw [cosupport_zero h𝔞]; exact hzN

theorem IsDivNearAlong.mono {e e' : ℕ} {x : M} (h : IsDivNearAlong n N 𝔞 H e x) (he : e' ≤ e) :
    IsDivNearAlong n N 𝔞 H e' x :=
  Filter.Eventually.mono h fun _ hz hzN hzH => cosupport_anti he (hz hzN hzH)

/-- Divisibility near `x` holds near every point close to `x`. -/
theorem IsDivNearAlong.eventually {e : ℕ} {x : M} (h : IsDivNearAlong n N 𝔞 H e x) :
    ∀ᶠ y in 𝓝 x, IsDivNearAlong n N 𝔞 H e y :=
  Filter.Eventually.eventually_nhds h

/-- Off the closed set `N ∩ H`, every divisibility holds. -/
theorem isDivNearAlong_of_notMem (hc : IsClosed (N ∩ H)) {x : M} (hx : x ∉ N ∩ H) (e : ℕ) :
    IsDivNearAlong n N 𝔞 H e x := by
  filter_upwards [hc.isOpen_compl.mem_nhds hx] with z hz hzN hzH
  exact absurd ⟨hzN, hzH⟩ hz

/-- **Divisibility from restricted generators**: if near `x` the generators of a coherent ideal agree on `N` with germs
of `𝓘_A^e`, where `A ⊇ N ∩ H`, then `IsDivNearAlong 𝔞 N H e x`. -/
theorem isDivNearAlong_of_generators {A : Set M} (hA : ∀ z, z ∈ N → z ∈ H → z ∈ A) {U : Set M} (hUo : IsOpen U)
    {x : M} (hxU : x ∈ U) {K : ℕ} {s : Fin K → M → ℂ}
    (hgen : ∀ y ∈ U, ∀ g, 𝔞.mem y g ↔ IsInSpanAt (n := n) (· ∈ range s) y g) {e : ℕ}
    (hs : ∀ i, ∃ h, (idealPow (vanishingIdeal (n := n) A) e).mem x h ∧ ∀ᶠ y in 𝓝 x, y ∈ N → s i y = h y) :
    IsDivNearAlong n N 𝔞 H e x := by
  choose h hh hsh using hs
  filter_upwards [hUo.mem_nhds hxU, eventually_all.mpr fun i => eventually_mem_idealPow_vanishingIdeal (hh i),
    eventually_all.mpr fun i => (hsh i).eventually_nhds] with z hzU hz hzs hzN hzH
  refine ⟨hzN, fun f hf => IsInSpanAt.vanishesToOrderOn ((hgen z hzU f).mp hf) ?_⟩
  rintro _ ⟨i, rfl⟩
  exact ⟨h i, mem_idealPow_pointIdeal_of_mem_idealPow_vanishingIdeal (hA z hzN hzH) (hz i), hzs i⟩

/-- **Divisibility from the stalk**: if every germ of the coherent ideal `𝔞` at `x` agrees on `N` with a germ of
`𝓘_A^e` (`A ⊇ N ∩ H`), then `IsDivNearAlong 𝔞 N H e x`. -/
theorem isDivNearAlong_of_forall_mem (h𝔞 : 𝔞.IsCoherent) {A : Set M} (hA : ∀ z, z ∈ N → z ∈ H → z ∈ A) {x : M}
    {e : ℕ} (hall : ∀ g, 𝔞.mem x g →
      ∃ h, (idealPow (vanishingIdeal (n := n) A) e).mem x h ∧ ∀ᶠ y in 𝓝 x, y ∈ N → g y = h y) :
    IsDivNearAlong n N 𝔞 H e x := by
  obtain ⟨U, hUo, hxU, K, s, hs, hgen⟩ := h𝔞 x
  refine isDivNearAlong_of_generators hA hUo hxU hgen fun i => hall _ ((hgen x hxU _).mpr ?_)
  exact isInSpanAt_of_eq_mul ⟨i, rfl⟩
    (holomorphicAt_of_mdifferentiableOn_open hUo (hs i) hxU) (holomorphicAt_const 1)
    (Eventually.of_forall fun _ => (one_mul _).symm)

/-- **The retracted germ lies in `𝓘_A^e`**: if `IsDivNearAlong 𝔞 N H e x`, `A` is a submanifold at `x` contained in
`H`, and the retraction `r` maps the points of `A` near `x` into `N ∩ H`, then for `g ∈ 𝔞_x` the germ `g ∘ r` lies in
`(𝓘_A^e)_x`.  (Two cases: `A = N ∩ H`, and `A = H` for a retraction preserving `H`.) -/
theorem IsLocalRetraction.mem_idealPow_vanishingIdeal_comp {x : M} (hr : IsLocalRetraction n N r x)
    (h𝔞 : 𝔞.IsCoherent) {A : Set M} {k : ℕ} (hAreg : RegularAtDim (n := n) A x k)
    (hrA : ∀ᶠ z in 𝓝 x, z ∈ A → r z ∈ H) {e : ℕ} (hd : IsDivNearAlong n N 𝔞 H e x) {g : M → ℂ}
    (hg : 𝔞.mem x g) : (idealPow (vanishingIdeal (n := n) A) e).mem x (g ∘ r) := by
  have hghol : HolomorphicAt n g x := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  refine mem_idealPow_vanishingIdeal_of_eventually hAreg (hr.holomorphicAt_comp hghol) ?_
  -- the facts needed at `r z`, pulled back along `r`
  have hP : ∀ᶠ w in 𝓝 x, (w ∈ N → w ∈ H → w ∈ cosupport n N 𝔞 e) ∧ 𝔞.mem w g ∧
      (w ∈ N → IsLocalRetraction n N r w) := by
    filter_upwards [hd, eventually_mem_of_isCoherent h𝔞 hg, hr.eventually] with w h1 h2 h4
    exact ⟨h1, h2, h4⟩
  filter_upwards [hr.tendsto.eventually hP, hr.mem, hrA, hr.mdifferentiableAt.eventually_nhds,
    hr.eventually_comp_self.eventually_nhds] with z hz hzN hzA hzd hzrr hzA'
  obtain ⟨h1, h2, h4⟩ := hz
  have hrzH : r z ∈ H := hzA hzA'
  -- `g ∘ r ∈ 𝔪_{r z}^e`, then pull back along `r` and use `r ∘ r = r`
  have hw : (idealPow (pointIdeal n (r z)) e).mem (r z) (g ∘ r) :=
    (h4 hzN).vanishesToOrderOn_iff.mp ((h1 hzN hrzH).2 g h2)
  refine mem_idealPow_congr (comp_mem_idealPow_pointIdeal hzd e hw) ?_
  filter_upwards [hzrr] with p hp
  simp [Function.comp, hp]

/-- **Identity principle along `N ∩ H`**: for `𝔞` coherent, `r` a retraction onto `N` at `x` and `N ∩ H` a submanifold
at `x`, if points `y ∈ N ∩ H` with `IsDivNearAlong 𝔞 N H e y` accumulate at `x`, then `IsDivNearAlong 𝔞 N H e x`. -/
theorem isDivNearAlong_of_frequently (h𝔞 : 𝔞.IsCoherent) {x : M} (hr : IsLocalRetraction n N r x) {k : ℕ}
    (hNH : RegularAtDim (n := n) (N ∩ H) x k) {e : ℕ}
    (h : ∃ᶠ y in 𝓝 x, y ∈ N ∧ y ∈ H ∧ IsDivNearAlong n N 𝔞 H e y) : IsDivNearAlong n N 𝔞 H e x := by
  obtain ⟨U, hUo, hxU, K, s, hs, hgen⟩ := h𝔞 x
  have hshol : ∀ i, ∀ z ∈ U, HolomorphicAt n (s i) z := fun i _ hz =>
    holomorphicAt_of_mdifferentiableOn_open hUo (hs i) hz
  have hmem : ∀ i, ∀ z ∈ U, 𝔞.mem z (s i) := fun i z hz => (hgen z hz (s i)).mpr
    (isInSpanAt_of_eq_mul ⟨i, rfl⟩ (hshol i z hz) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm))
  refine isDivNearAlong_of_generators (A := N ∩ H) (fun z hzN hzH => ⟨hzN, hzH⟩) hUo hxU hgen fun i =>
    ⟨s i ∘ r, ?_, hr.eventually_eq_comp (s i)⟩
  refine mem_idealPow_vanishingIdeal_of_frequently hNH (hr.holomorphicAt_comp (hshol i x hxU)) ?_
  have hU' : ∀ᶠ z in 𝓝 x, z ∈ U := hUo.mem_nhds hxU
  have hW : ∀ᶠ z in 𝓝 x, z ∈ U ∧ (z ∈ N → IsLocalRetraction n N r z) := hU'.and hr.eventually
  refine (h.and_eventually hW.eventually_nhds).mono ?_
  rintro y ⟨⟨hyN, hyH, hyd⟩, hyW⟩
  refine ⟨⟨hyN, hyH⟩, ?_⟩
  filter_upwards [hyd, hyW] with z hz ⟨hzU, hzr⟩ ⟨hzN, hzH⟩
  exact (hzr hzN).vanishesToOrderOn_iff.mp ((hz hzN hzH).2 (s i) (hmem i z hzU))

variable (n) in
/-- **The exponent of `𝔞` along `N ∩ H` at `x`**: the largest `e` with `IsDivNearAlong 𝔞 N H e x` (`0` if there is
none, or if every `e` works). -/
noncomputable def divExpAlong (N : Set M) (𝔞 : GermIdeal n M) (H : Set M) (x : M) : ℕ := by
  classical
  exact if h : ∃ e, ¬ IsDivNearAlong n N 𝔞 H (e + 1) x then Nat.find h else 0

/-- `𝔞|_N` does not vanish near `x` on `N`: `𝔞_x` contains a germ which does not vanish identically on `N` near
`x`. -/
def IsNonzeroAlongAt (N : Set M) (𝔞 : GermIdeal n M) (x : M) : Prop :=
  ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, y ∈ N ∧ g y ≠ 0

/-- **The exponent along `N` is finite**: at a point `x ∈ H` where `𝔞|_N` does not vanish near `x` on `N` (and `r` is a
retraction onto `N` at `x`), some `IsDivNearAlong 𝔞 N H e x` fails. -/
theorem exists_not_isDivNearAlong {x : M} (hr : IsLocalRetraction n N r x) (hx : x ∈ H)
    (hne : IsNonzeroAlongAt N 𝔞 x) (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    ∃ e, ¬ IsDivNearAlong n N 𝔞 H (e + 1) x := by
  obtain ⟨g, hg, hgne⟩ := hne
  obtain ⟨q, hq⟩ := hr.exists_not_vanishesToOrderOn (h𝔞 x g hg) hgne
  exact ⟨q, fun hd => hq (((hd.self_of_nhds hr.mem_self hx).2 g hg).mono (Nat.le_succ q))⟩

theorem isDivNearAlong_divExpAlong (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (x : M) :
    IsDivNearAlong n N 𝔞 H (divExpAlong n N 𝔞 H x) x := by
  classical
  unfold divExpAlong
  split_ifs with h
  · rcases hm : Nat.find h with _ | m
    · exact isDivNearAlong_zero h𝔞 x
    · have := Nat.find_min h (show m < Nat.find h by omega)
      push Not at this
      exact this
  · exact isDivNearAlong_zero h𝔞 x

theorem not_isDivNearAlong_divExpAlong_succ {x : M} (hr : IsLocalRetraction n N r x) (hx : x ∈ H)
    (hne : IsNonzeroAlongAt N 𝔞 x) (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    ¬ IsDivNearAlong n N 𝔞 H (divExpAlong n N 𝔞 H x + 1) x := by
  classical
  have h := exists_not_isDivNearAlong hr hx hne h𝔞
  unfold divExpAlong
  rw [dif_pos h]
  exact Nat.find_spec h

/-- **The exponent characterizes divisibility**: `IsDivNearAlong 𝔞 N H e x ↔ e ≤ divExpAlong 𝔞 N H x`. -/
theorem isDivNearAlong_iff_le_divExpAlong {x : M} (hr : IsLocalRetraction n N r x) (hx : x ∈ H)
    (hne : IsNonzeroAlongAt N 𝔞 x) (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {e : ℕ} :
    IsDivNearAlong n N 𝔞 H e x ↔ e ≤ divExpAlong n N 𝔞 H x := by
  refine ⟨fun hd => ?_, fun he => (isDivNearAlong_divExpAlong h𝔞 x).mono he⟩
  by_contra hlt
  exact not_isDivNearAlong_divExpAlong_succ hr hx hne h𝔞 (hd.mono (by omega))

/-- **The exponent along `N` is locally constant on `N ∩ H`** (`hir:exponent-along`): for `𝔞` coherent, `r` a
retraction onto `N` at `x`, `N ∩ H` a submanifold at `x`, and `𝔞|_N` nonvanishing near the points of `N` close to `x`,
`divExpAlong 𝔞 N H y = divExpAlong 𝔞 N H x` for `y ∈ N ∩ H` near `x`. -/
theorem eventually_divExpAlong_eq (h𝔞 : 𝔞.IsCoherent) {x : M} (hr : IsLocalRetraction n N r x) {k : ℕ}
    (hNH : RegularAtDim (n := n) (N ∩ H) x k) (hne : ∀ᶠ y in 𝓝 x, y ∈ N → IsNonzeroAlongAt N 𝔞 y) :
    ∀ᶠ y in 𝓝 x, y ∈ N → y ∈ H → divExpAlong n N 𝔞 H y = divExpAlong n N 𝔞 H x := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  set e := divExpAlong n N 𝔞 H x
  have hxN : x ∈ N := hr.mem_self
  have hxH : x ∈ H := hNH.2.1.2
  have h1 : ∀ᶠ y in 𝓝 x, IsDivNearAlong n N 𝔞 H e y := (isDivNearAlong_divExpAlong hhol x).eventually
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ N → y ∈ H → ¬ IsDivNearAlong n N 𝔞 H (e + 1) y := by
    by_contra hc
    rw [Filter.not_eventually] at hc
    exact not_isDivNearAlong_divExpAlong_succ hr hxH (hne.self_of_nhds hxN) hhol
      (isDivNearAlong_of_frequently h𝔞 hr hNH (hc.mono fun y hy => by push Not at hy; exact hy))
  filter_upwards [h1, h2, hne, hr.eventually] with y hy1 hy2 hyne hyr hyN hyH
  have hle : e ≤ divExpAlong n N 𝔞 H y :=
    (isDivNearAlong_iff_le_divExpAlong (hyr hyN) hyH (hyne hyN) hhol).mp hy1
  have hlt : ¬ e + 1 ≤ divExpAlong n N 𝔞 H y := fun h =>
    hy2 hyN hyH ((isDivNearAlong_iff_le_divExpAlong (hyr hyN) hyH (hyne hyN) hhol).mpr h)
  omega

end Exponent

/-! ### Members of a divisor transverse to `N` -/

section Members

open NormalCrossings BoundaryCount

variable {N : Set M} {E : List (Set M)}

/-- `memberInter E {i}` is the member `E_i`. -/
theorem memberInter_singleton (i : Fin E.length) : memberInter E {i} = E.get i := by
  ext y
  simp [memberInter]

/-- **The trace of a member on `N` is regular** at its points (`E` simple normal crossings and transverse to the
closed set `N`, `0 < n`; `MemberInterAlong.isClosedSubmanifold_inter_memberInter`). -/
theorem regularAtDim_inter_get (hn : 0 < n) (hNc : IsClosed N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (i : Fin E.length) {x : M} (hx : x ∈ N) (hxi : x ∈ E.get i) : ∃ k, RegularAtDim (n := n) (N ∩ E.get i) x k := by
  have h := MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hNc hE hT {i}
  rw [memberInter_singleton] at h
  exact h.2 x ⟨hx, hxi⟩

/-- **The exponents along `N` of the members are locally constant on their traces** (`hir:exponent-along`), for `N` a
closed submanifold, `E` simple normal crossings and transverse to `N`, `𝔞` coherent with `𝔞|_N` nonvanishing near every
point of `N`. -/
theorem eventually_divExpAlong_get_eq (hn : 0 < n) (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (hne : ∀ y ∈ N, IsNonzeroAlongAt N 𝔞 y)
    (i : Fin E.length) {x : M} (hx : x ∈ N) (hxi : x ∈ E.get i) :
    ∀ᶠ y in 𝓝 x, y ∈ N → y ∈ E.get i →
      divExpAlong n N 𝔞 (E.get i) y = divExpAlong n N 𝔞 (E.get i) x := by
  obtain ⟨k, hk⟩ := hN.2 x hx
  obtain ⟨r, hr⟩ := exists_isLocalRetraction hk
  obtain ⟨k', hk'⟩ := regularAtDim_inter_get hn hN.1 hE hT i hx hxi
  exact eventually_divExpAlong_eq h𝔞 hr hk' (Eventually.of_forall hne)

end Members

end

end Hironaka.DivisorExponentAlong
