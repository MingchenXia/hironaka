/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.LocalGiraudTransform
import Hironaka.MarkedIdeal.TangentDirectionAlong
import Hironaka.Blowup.NestedFlattening
import Hironaka.Invariant.MonomialPart
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Wlodarczyk's lemma on tangent directions along a submanifold

Source: Włodarczyk 2005 (`wlodarczyk05-hironaka`), §2.7, Lemma `le:Gi` (Giraud) parts (2) and (3), applied on the
submanifold `N` of a marked ideal (§2.1, the transform along a submanifold).

Let `π` be the blowup along `C`, `N ⊇ C` a closed submanifold, `U` open, `u` holomorphic on `U`
with multiplicity one along `N` at its zeros on `N` (some holomorphic field tangent to `N` has
`ξ(u) ≠ 0` there), `C ∩ U ⊆ V(u)`, `h` a local equation of the exceptional divisor on `U'`, and
`u ∘ π = h · u'` near `z ∈ U' ∩ π⁻¹ U`.  Write `W = N ∩ V(u) ∩ U`, `W'` and `N'` for the strict
transforms.

* `vanishingIdeal_geoStrictTransform_inter_zeroSet_mem_iff` (if `π z ∈ W`): `𝓘_{W'} = 𝓘_{N'} + (u')`
  at `z`;
* `eventually_mem_geoStrictTransform_inter_zeroSet_iff` (`le:Gi` (3) along `N`): near `z`, a point
  of `N'` lies on `W'` iff `u'` vanishes there;
* `exists_fieldDeriv_ne_zero_controlledTransform_along` (`le:Gi` (2) along `N`): at `z ∈ W'` some
  holomorphic field tangent to `N'` has `ξ(u') ≠ 0` -- `u'` has multiplicity one along `N'`;
* `IsTangentDirectionAlong.giraud_hypotheses_along`: a tangent direction along `N`
  (`TangentDirectionAlong.IsTangentDirectionAlong`) and a centre in the cosupport satisfy the hypotheses.
* tools: `exists_fieldDeriv_ne_zero_of_vanishingIdeal_le` (if `A ⊆ B` are regular at `z` of dimensions `a < b` and
  `𝓘_A ⊆ 𝓘_B + (f)` at `z`), `isInSpanAt_pullback_of_mem_vanishingIdeal_geoStrictTransform` (`𝒪(-D) 𝓘_{A'} ⊆ π^*
  𝓘_A` for a set `A` whose trace on an open `V` is a closed submanifold of `V` containing `C ∩ V`: the strict ideal
  theorem `BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul` on the restricted blowup
  `BlowupRestrictOpen.isBlowupAlong_restrict`), `eventually_eq_zero_of_mem_geoStrictTransform`,
  `isInSpanAt_of_mul_isInSpanAt` (cancelling a local equation).

Proof of the ideal identity: `𝓘_W = 𝓘_N + (u)` near `π z`
(`TangentDirectionAlong.exists_vanishingIdeal_inter_zeroSet_mem_iff`); `𝒪(-D) 𝓘_{W'} ⊆ π^* 𝓘_W` (the strict ideal
theorem for `W` on `V = U`); `π^* 𝓘_N = 𝒪(-D) 𝓘_{N'}` (for `N`); `u ∘ π = h u'`. So `h 𝓘_{W'} ⊆ h (𝓘_{N'} + (u'))`,
and `h` cancels (it vanishes identically near no point). Conversely `𝓘_{N'} ⊆ 𝓘_{W'}` as `W' ⊆ N'`, and `u'`
vanishes on `W'` by continuity. Then (3) evaluates generators at a point, and (2) is the tool above with `A = W'`
(regular of dimension `k - 1`) and `B = N'` (dimension `k`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.LocalGiraudTransformAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences DerivativeIdeal DerivativeIdealAlong DerivativeIdealAlongCoherent GiraudAlong BlowupFlatCoordinates BlowupStrictSubmanifold BlowupStrictIdeal BlowupFunctionTransform BlowupExceptionalDivisor BlowupRestrictOpen LocalGiraudTransform AnalyticSubsetOpens RelativePrincipalizationSpan TangentDirectionAlong

noncomputable section

variable {n : ℕ}

/-! ### Elementary facts on spans -/

section Span

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- A combination of germs vanishing at `y` vanishes at `y`. -/
theorem apply_eq_zero_of_isInSpanAt {S : (M → ℂ) → Prop} {y : M} (hS : ∀ s, S s → s y = 0)
    {g : M → ℂ} (hg : IsInSpanAt (n := n) S y g) : g y = 0 := by
  obtain ⟨-, K, s, c, hs, -, hsum⟩ := hg
  rw [hsum.self_of_nhds]
  exact Finset.sum_eq_zero fun i _ => by rw [hS _ (hs i), mul_zero]

/-- **Cancelling a factor that vanishes identically near no point**: if `h g` is a combination of
products `h t` with `t` in a family of holomorphic germs, then `g` is a combination of the `t`. -/
theorem isInSpanAt_of_mul_isInSpanAt [IsComplexManifold n M] {S : (M → ℂ) → Prop} {y : M}
    {h g : M → ℂ} (hh : HolomorphicAt n h y) (hhne : ∃ᶠ p in 𝓝 y, h p ≠ 0)
    (hgh : HolomorphicAt n g y) (hS : ∀ t, S t → HolomorphicAt n t y)
    (hg : IsInSpanAt (n := n) (fun s => ∃ t, S t ∧ s = fun p => h p * t p) y
      (fun p => h p * g p)) :
    IsInSpanAt (n := n) S y g := by
  obtain ⟨-, K, s, c, hs, hc, hsum⟩ := hg
  choose t ht hst using hs
  have hthol : ∀ k, HolomorphicAt n (t k) y := fun k => hS _ (ht k)
  have hF : HolomorphicAt n (fun p => g p - ∑ k, c k p * t k p) y :=
    GiraudAlong.holomorphicAt_sub hgh (HolomorphicAt.sum _ fun k _ => (hc k).mul (hthol k))
  have hzero := MonomialPart.eventually_eq_zero_of_mul_eventually_eq_zero hF hh hhne (by
    filter_upwards [hsum] with p hp
    have hp' : h p * g p = ∑ k, c k p * (h p * t k p) := by
      rw [hp]
      exact Finset.sum_congr rfl fun k _ => by rw [hst k]
    show (g p - ∑ k, c k p * t k p) * h p = 0
    rw [sub_mul, Finset.sum_mul, mul_comm (g p), hp', Finset.sum_congr rfl fun k _ =>
      show c k p * t k p * h p = c k p * (h p * t k p) by ring, sub_self])
  refine ⟨hgh, K, t, c, ht, hc, ?_⟩
  filter_upwards [hzero] with p hp
  exact sub_eq_zero.mp hp

end Span

/-! ### A generator modulo a submanifold has a nonvanishing tangential derivative -/

section Tangent

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A generator of `𝓘_A` modulo `𝓘_B` has a nonvanishing derivative along `B`.**  Let `A ⊆ B` be
regular at `z` of dimensions `a < b`, `f` holomorphic at `z` with `f(z) = 0`, and suppose every germ
of `𝓘_A` at `z` is a combination of germs of `𝓘_B` and of `f`.  Then some holomorphic vector field
tangent to `B` at `z` has `ξ(f)(z) ≠ 0`.  (In nested flat coordinates `A = ℂᵃ × 0`, `B = ℂᵇ × 0`,
the coordinate `ψ_a` lies in `𝓘_A` and `∂ψ_a/∂ψ_a = 1`, while `∂/∂ψ_a` is tangent to `B` and kills
the germs of `𝓘_B` at `z`.) -/
theorem exists_fieldDeriv_ne_zero_of_vanishingIdeal_le {A B : Set M} {z : M} {a b : ℕ}
    (hab : a < b) (hA : RegularAtDim (n := n) A z a) (hB : RegularAtDim (n := n) B z b)
    (hAB : A ⊆ B) {f : M → ℂ} (hf : HolomorphicAt n f z) (hf0 : f z = 0)
    (hgen : ∀ g, (vanishingIdeal (n := n) A).mem z g →
      IsInSpanAt (n := n) (fun s => (vanishingIdeal (n := n) B).mem z s ∨ s = f) z g) :
    ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ), IsTangentField B e ξ z ∧
      fieldDeriv e ξ f z ≠ 0 := by
  classical
  have hbn : b ≤ n := hB.1
  have hzB : z ∈ B := hB.2.1
  obtain ⟨Φ, hΦt, -, hflat⟩ := NestedFlattening.exists_nested_flattening hab.le hA hB hAB
  have hz : z ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hflatA : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Φ.source →
        (y ∈ A ↔ Φ.toFun (chartAt (ComplexModel n) z y) ∈ complexCoordinatePlane n a) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatB : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Φ.source →
        (y ∈ B ↔ Φ.toFun (chartAt (ComplexModel n) z y) ∈ complexCoordinatePlane n b) :=
    fun hy hyΦ => (hflat hy hyΦ).2
  set i : Fin n := ⟨a, by omega⟩ with hi
  set v : ComplexModel n := EuclideanSpace.single i 1 with hv
  have hvB : v ∈ complexCoordinatePlane n b := by
    intro t ht
    have hti : t ≠ i := fun h => by rw [h] at ht; simp [hi] at ht; omega
    simp [hv, hti]
  have hξ : IsTangentField B (complexChartAt (n := n) z) (flatField Φ v) z :=
    isTangentField_flatField hΦt hflatB hvB hz
  refine ⟨complexChartAt (n := n) z, flatField Φ v, hξ, fun h0 => ?_⟩
  -- the flat coordinate `ψ_a` lies in `𝓘_A`
  have hψ : (vanishingIdeal (n := n) A).mem z (flatCoord Φ i) :=
    flatCoord_mem_vanishingIdeal Φ hflatA (i := i) (le_refl a) hz
  obtain ⟨-, K, s, c, hs, hc, hsum⟩ := hgen _ hψ
  have hshol : ∀ k, HolomorphicAt n (s k) z := fun k =>
    (hs k).elim (fun h => h.1) (fun h => h ▸ hf)
  have hD := (fieldDeriv_eventuallyEq_sum_mul (ξ := flatField Φ v)
    (mem_complexChartAt_source z) hc hshol hsum).self_of_nhds
  -- the left side is `1`
  have h1 : fieldDeriv (complexChartAt (n := n) z) (flatField Φ v) (flatCoord Φ i) z = 1 := by
    rw [fieldDeriv_flatField hz (holomorphicAt_flatCoord Φ i hz) v]
    have hloc : (flatCoord Φ i ∘ flatInv Φ) =ᶠ[𝓝 (flatMap Φ z)] fun w => w i := by
      filter_upwards [Φ.isOpen_target.mem_nhds (flatMap_mem_target hz)] with w hw
      show flatCoord Φ i (flatInv Φ w) = w i
      have := flatMap_flatInv hw hΦt
      simp only [flatMap] at this
      simp only [flatCoord, this]
    rw [hloc.fderiv_eq]
    have hproj : HasFDerivAt (fun w : ComplexModel n => w i)
        (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ) (flatMap Φ z) :=
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).hasFDerivAt
    rw [hproj.fderiv]
    simp [hv]
  -- every term on the right vanishes at `z`
  have h2 : ∀ k, fieldDeriv (complexChartAt (n := n) z) (flatField Φ v) (c k) z * s k z +
      c k z * fieldDeriv (complexChartAt (n := n) z) (flatField Φ v) (s k) z = 0 := by
    intro k
    have hs0 : s k z = 0 := (hs k).elim (fun h => h.2.self_of_nhds hzB) (fun h => h ▸ hf0)
    have hds0 : fieldDeriv (complexChartAt (n := n) z) (flatField Φ v) (s k) z = 0 :=
      (hs k).elim (fun h => (hξ.preserves _ h).2.self_of_nhds hzB) (fun h => h ▸ h0)
    rw [hs0, hds0]
    ring
  rw [h1] at hD
  exact one_ne_zero (hD.trans (Finset.sum_eq_zero fun k _ => h2 k))

end Tangent

/-! ### Local equations, and the strict ideal theorem on an open set -/

section Blowup

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **A local equation of the exceptional divisor vanishes nowhere off it.** -/
theorem ne_zero_of_isLocalEquation {hπ : IsBlowupAlong n C π} {U' : Set Y} {h : Y → ℂ}
    (hh : IsLocalEquation hπ U' h) {y : Y} (hy : y ∈ U') (hyC : π y ∉ C) : h y ≠ 0 := by
  have h1 := (hh.generates y hy _).mp (by
    rw [exceptionalDivisor_ideal]
    exact MarkedIdeals.MarkedIdeal.one_mem_pullback_vanishingIdeal (n := n) (π := π) hyC hπ.1.1)
  obtain ⟨-, c, -, hc⟩ := isInSpanAt_eq_iff.mp h1
  intro h0
  have := hc.self_of_nhds
  simp [h0] at this

/-- **A local equation of the exceptional divisor vanishes identically near no point.** -/
theorem frequently_ne_zero_of_isLocalEquation {hπ : IsBlowupAlong n C π} {U' : Set Y} {h : Y → ℂ}
    (hh : IsLocalEquation hπ U' h) {y : Y} (hy : y ∈ U') : ∃ᶠ p in 𝓝 y, h p ≠ 0 := by
  rw [Filter.Frequently]
  intro hall
  obtain ⟨V, hVsub, hVo, hyV⟩ := mem_nhds_iff.mp ((hh.isOpen.eventually_mem hy).and hall)
  obtain ⟨p, hp, hp0⟩ := hh.nonvanishing V hVo (fun p hp => (hVsub hp).1) ⟨y, hyV⟩
  exact (hVsub hp).2 hp0

/-- **The transform of a function vanishes on the strict transform of its zero set**: if `u`
vanishes on `A` and `u ∘ π = h · u'` near `z` (`h` a local equation of the exceptional divisor),
then `u'` vanishes on `A' = closure (π⁻¹ (A \ C))` near `z` (off `π⁻¹ C` because `h ≠ 0` there, then
by continuity). -/
theorem eventually_eq_zero_of_mem_geoStrictTransform {hπ : IsBlowupAlong n C π} {U' : Set Y}
    {h : Y → ℂ} (hh : IsLocalEquation hπ U' h) {u : X → ℂ} {A : Set X}
    (hAu : ∀ x ∈ A, u x = 0) {z : Y} (hz : z ∈ U') {u' : Y → ℂ} (hu' : HolomorphicAt n u' z)
    (heq : (u ∘ π) =ᶠ[𝓝 z] fun y => h y * u' y) :
    ∀ᶠ y in 𝓝 z, y ∈ geoStrictTransform π C A → u' y = 0 := by
  have hev : ∀ᶠ y in 𝓝 z, y ∈ U' ∧ HolomorphicAt n u' y ∧ u (π y) = h y * u' y :=
    (hh.isOpen.eventually_mem hz).and ((HolomorphicAt.eventually_holomorphicAt hu').and heq)
  obtain ⟨O, hOsub, hOo, hzO⟩ := mem_nhds_iff.mp hev
  filter_upwards [hOo.mem_nhds hzO] with y hyO hyA
  by_contra hne
  have hnb : {p | u' p ≠ 0} ∩ O ∈ 𝓝 y :=
    inter_mem ((hOsub hyO).2.1.continuousAt.eventually_ne hne) (hOo.mem_nhds hyO)
  obtain ⟨p, ⟨hp0, hpO⟩, hpA, hpC⟩ := mem_closure_iff_nhds.mp hyA _ hnb
  obtain ⟨hpU, -, hpeq⟩ := hOsub hpO
  rw [hAu _ hpA] at hpeq
  exact mul_ne_zero (ne_zero_of_isLocalEquation hh hpU hpC) hp0 hpeq.symm

/-- **`𝒪(-D) 𝓘_{A'} ⊆ π^* 𝓘_A` for a submanifold of an open set.**  Let `V` be open, `A` a set whose
trace on `V` is a closed submanifold of `V` containing `C ∩ V`, `h` a local equation of the
exceptional divisor on `U'`, `z ∈ U'` with `π z ∈ V`, and `g` a germ of `𝓘_{A'}` at `z`
(`A' = closure (π⁻¹ (A \ C))`).  Then `h g` is a combination of pullbacks of germs of `𝓘_A` at
`π z`.  (The strict ideal theorem `BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul` for the
restriction `π⁻¹ V → V` of the blowup, read back on `Y`.) -/
theorem isInSpanAt_pullback_of_mem_vanishingIdeal_geoStrictTransform (hπ : IsBlowupAlong n C π)
    (V : Opens X) {A : Set X} (hA : IsClosedSubmanifold n ((↑) ⁻¹' A : Set V))
    (hCA : ∀ x ∈ C, x ∈ (V : Set X) → x ∈ A) {U' : Set Y} {h : Y → ℂ}
    (hh : IsLocalEquation hπ U' h) {z : Y} (hz : z ∈ U') (hzV : π z ∈ (V : Set X)) {g : Y → ℂ}
    (hg : (vanishingIdeal (n := n) (geoStrictTransform π C A)).mem z g) :
    IsInSpanAt (n := n) (fun t => ∃ b, (vanishingIdeal (n := n) A).mem (π z) b ∧ t = b ∘ π) z
      (fun y => h y * g y) := by
  have hV : IsOpen (π ⁻¹' (V : Set X)) := V.isOpen.preimage hπ.contMDiff.continuous
  have hr := isBlowupAlong_restrict hπ V hV
  have hCAV : ((↑) ⁻¹' C : Set V) ⊆ (↑) ⁻¹' A := fun x hx => hCA x.1 hx x.2
  have key := pullback_vanishingIdeal_eq_mul hr hA hCAV
  have hhW := isLocalEquation_restrict hh V hV
  have hzW : (⟨z, hzV⟩ : (⟨π ⁻¹' (V : Set X), hV⟩ : Opens Y)) ∈
      ((↑) ⁻¹' U' : Set (⟨π ⁻¹' (V : Set X), hV⟩ : Opens Y)) := hz
  have hhmem : (exceptionalDivisor hr).ideal.mem ⟨z, hzV⟩ (h ∘ Subtype.val) :=
    (hhW.generates _ hzW _).mpr
      (InvertibleIdealQuotient.isInSpanAt_self rfl (hhW.holomorphicAt hzW))
  have hgmem : (vanishingIdeal (n := n) (geoStrictTransform
      (fun p : (⟨π ⁻¹' (V : Set X), hV⟩ : Opens Y) => (⟨π p.1, p.2⟩ : V))
      ((↑) ⁻¹' C) ((↑) ⁻¹' A))).mem ⟨z, hzV⟩ (g ∘ Subtype.val) := by
    rw [geoStrictTransform_preimage_val V hV A, vanishingIdeal_comp_val_iff]
    exact hg
  have hprod := GermIdealTotalTransform.mem_mul_of_mem_mem hhmem hgmem
    (((holomorphicAt_comp_val_iff _).mpr (hh.holomorphicAt hz)).mul
      ((holomorphicAt_comp_val_iff _).mpr hg.1))
  rw [← key] at hprod
  have hmono : IsInSpanAt (n := n) (fun s' => ∃ s, (∃ b, (vanishingIdeal (n := n) A).mem (π z) b ∧
      s = b ∘ π) ∧ s' = s ∘ Subtype.val) (⟨z, hzV⟩ : (⟨π ⁻¹' (V : Set X), hV⟩ : Opens Y))
      (fun y => (h ∘ Subtype.val) y * (g ∘ Subtype.val) y) := by
    refine IsInSpanAt.mono (fun s hs => ?_) (GermIdeal.mem_pullback_iff.mp hprod)
    obtain ⟨a, ha, rfl⟩ := hs
    refine ⟨extendOpens V a ∘ π, ⟨extendOpens V a, ?_, rfl⟩, ?_⟩
    · have ha' : (vanishingIdeal (n := n) ((↑) ⁻¹' A : Set V)).mem ⟨π z, hzV⟩
          (extendOpens V a ∘ Subtype.val) := by
        have hfun : extendOpens V a ∘ Subtype.val = a := funext fun x => extendOpens_val V a x
        rw [hfun]
        exact ha
      exact (vanishingIdeal_comp_val_iff V).mp ha'
    · funext p
      exact (extendOpens_val V a ⟨π p.1, p.2⟩).symm
  have hY := (isInSpanAt_comp_val_iff (⟨π ⁻¹' (V : Set X), hV⟩ : Opens Y)).mp hmono
  refine DerivativeIdeal.isInSpanAt_congr hY ?_
  filter_upwards [hV.mem_nhds hzV] with y hy
  exact extendOpens_val (⟨π ⁻¹' (V : Set X), hV⟩ : Opens Y) _ ⟨y, hy⟩

end Blowup

/-! ### Wlodarczyk's lemma on tangent directions along `N` -/

section Giraud

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **`N ∩ V(u) ∩ U` is a closed submanifold of `U`** when `u` (holomorphic on `U`) has multiplicity one along `N` at
its zeros on `N` (`regularAtDim_inter_zeroSet` at each point). -/
theorem isClosedSubmanifold_preimage_val_inter_zeroSet {N : Set X} (hN : IsClosedSubmanifold n N)
    (U : Opens X) {u : X → ℂ} (hu : ∀ x ∈ (U : Set X), HolomorphicAt n u x)
    (hu1 : ∀ x ∈ (U : Set X), x ∈ N → u x = 0 → ∃ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsTangentField N e ξ x ∧ fieldDeriv e ξ u x ≠ 0) :
    IsClosedSubmanifold n ((↑) ⁻¹' (N ∩ {x | u x = 0} ∩ (U : Set X)) : Set U) := by
  refine ⟨isClosed_preimage_val_inter_zeroSet hN.1 hu, fun x hx => ?_⟩
  obtain ⟨⟨hxN, hx0⟩, hxU⟩ := hx
  obtain ⟨k, hkn, -, Φ, hΦsrc, -, hflat⟩ := hN.2 x.1 hxN
  obtain ⟨e, ξ, hξ, hne⟩ := hu1 x.1 hxU hxN hx0
  exact ⟨k - 1, regularAtDim_preimage_val_iff.mpr
    (regularAtDim_inter_zeroSet hΦsrc hflat hkn U.isOpen hu hxU hxN hx0 hξ hne)⟩

/-- **`𝓘_{W'} = 𝓘_{N'} + (u')` at `z`** (`W = N ∩ V(u) ∩ U`).  Let `N ⊇ C` be a closed
submanifold, `u` holomorphic on the open set `U` with multiplicity one along `N` at its zeros on
`N`, `C ∩ U ⊆ V(u)`, `h` a local equation of the exceptional divisor on `U'`, `z ∈ U'` with
`π z ∈ W`, and `u ∘ π = h u'` near `z`.  Then the germs of `𝓘_{W'}` at `z` are exactly the
combinations of germs of `𝓘_{N'}` and of `u'`. -/
theorem vanishingIdeal_geoStrictTransform_inter_zeroSet_mem_iff (hπ : IsBlowupAlong n C π)
    {N : Set X} (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) {U' : Set Y} {h : Y → ℂ}
    (hh : IsLocalEquation hπ U' h) {U : Set X} (hU : IsOpen U) {u : X → ℂ}
    (hu : ∀ x ∈ U, HolomorphicAt n u x)
    (hu1 : ∀ x ∈ U, x ∈ N → u x = 0 → ∃ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsTangentField N e ξ x ∧ fieldDeriv e ξ u x ≠ 0)
    (hCu : ∀ x ∈ C, x ∈ U → u x = 0) {z : Y} (hz : z ∈ U') (hzU : π z ∈ U) (hzN : π z ∈ N)
    (hz0 : u (π z) = 0) {u' : Y → ℂ} (hu' : HolomorphicAt n u' z)
    (heq : (u ∘ π) =ᶠ[𝓝 z] fun y => h y * u' y) (g : Y → ℂ) :
    (vanishingIdeal (n := n) (geoStrictTransform π C (N ∩ {x | u x = 0} ∩ U))).mem z g ↔
      IsInSpanAt (n := n)
        (fun s => (vanishingIdeal (n := n) (geoStrictTransform π C N)).mem z s ∨ s = u') z g := by
  classical
  have hWN : geoStrictTransform π C (N ∩ {x | u x = 0} ∩ U) ⊆ geoStrictTransform π C N :=
    closure_mono (preimage_mono
      (sdiff_subset_sdiff_left (inter_subset_left.trans inter_subset_left)))
  have hu'W := eventually_eq_zero_of_mem_geoStrictTransform hh (A := N ∩ {x | u x = 0} ∩ U)
    (fun x hx => hx.1.2) hz hu' heq
  constructor
  · intro hg
    -- `h g ∈ π^* 𝓘_W` (the strict ideal theorem for `W` on `U`)
    have h1 := isInSpanAt_pullback_of_mem_vanishingIdeal_geoStrictTransform hπ ⟨U, hU⟩
      (isClosedSubmanifold_preimage_val_inter_zeroSet hN ⟨U, hU⟩ hu hu1)
      (fun x hxC hxU => ⟨⟨hCN hxC, hCu x hxC hxU⟩, hxU⟩) hh hz hzU hg
    -- `𝓘_W ⊆ 𝓘_N + (u)` at `π z`
    obtain ⟨k, hkn, -, Φ, hΦsrc, -, hflat⟩ := hN.2 (π z) hzN
    obtain ⟨e, ξ, hξ, hne⟩ := hu1 (π z) hzU hzN hz0
    obtain ⟨V', -, hzV', -, hgenW⟩ :=
      exists_vanishingIdeal_inter_zeroSet_mem_iff hΦsrc hflat hkn hU hu hzU hzN hz0 hξ hne
    have hWgen : ∀ b, (vanishingIdeal (n := n) (N ∩ {x | u x = 0} ∩ U)).mem (π z) b →
        IsInSpanAt (n := n) (fun s => (vanishingIdeal (n := n) N).mem (π z) s ∨ s = u) (π z) b := by
      intro b hb
      refine ((hgenW (π z) hzV' b).mp hb).mono fun s hs => ?_
      rcases hs with rfl | ⟨i, hi, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl (flatCoord_mem_vanishingIdeal Φ hflat hi (mem_flatDomain_self Φ))
    -- `h g` is a combination of the `h t`, `t ∈ 𝓘_{N'}` or `t = u'`
    have hNstrict := pullback_vanishingIdeal_eq_mul hπ hN hCN
    have hπd : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
      Eventually.of_forall fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
    have h2 : IsInSpanAt (n := n) (fun s => ∃ t, ((vanishingIdeal (n := n)
        (geoStrictTransform π C N)).mem z t ∨ t = u') ∧ s = fun p => h p * t p) z
        (fun y => h y * g y) := by
      refine IsInSpanAt.trans (fun s hs => ?_) h1
      obtain ⟨b, hb, rfl⟩ := hs
      have hbπ := GermIdealPullbackCalculus.isInSpanAt_comp hπ.contMDiff (hWgen b hb)
      refine IsInSpanAt.trans (fun s hs => ?_) hbπ
      obtain ⟨a, ha, rfl⟩ := hs
      rcases ha with ha | rfl
      · -- `a ∘ π ∈ π^* 𝓘_N = 𝒪(-D) 𝓘_{N'}`
        have hpb : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) N)).mem z (a ∘ π) :=
          GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self ⟨a, ha, rfl⟩
            (HadamardBridge.holomorphicAt_comp_map hπd ha.1))
        rw [hNstrict] at hpb
        have hpb' : IsInSpanAt (n := n) (fun s => ∃ p q, (exceptionalDivisor hπ).ideal.mem z p ∧
            (vanishingIdeal (n := n) (geoStrictTransform π C N)).mem z q ∧ s = p * q) z (a ∘ π) :=
          hpb
        refine IsInSpanAt.trans (fun s hs => ?_) hpb'
        obtain ⟨p, q, hp, hq, rfl⟩ := hs
        obtain ⟨hphol, κ, hκ, hpκ⟩ := isInSpanAt_eq_iff.mp ((hh.generates z hz p).mp hp)
        refine isInSpanAt_of_eq_mul ⟨fun y => κ y * q y, Or.inl ⟨hκ.mul hq.1, ?_⟩, rfl⟩
          (hphol.mul hq.1) (holomorphicAt_const 1) ?_
        · filter_upwards [hq.2] with y hy hyN
          simp [hy hyN]
        · filter_upwards [hpκ] with y hy
          simp only [Pi.mul_apply, hy, one_mul]
          ring
      · -- `u ∘ π = h u'`
        exact isInSpanAt_of_eq_mul ⟨u', Or.inr rfl, rfl⟩
          (HadamardBridge.holomorphicAt_comp_map hπd (hu _ hzU)) (holomorphicAt_const 1)
          (by
            filter_upwards [heq] with y hy
            simp only [Function.comp_apply] at hy ⊢
            rw [hy, one_mul])
    -- cancel `h`
    exact isInSpanAt_of_mul_isInSpanAt (hh.holomorphicAt hz)
      (frequently_ne_zero_of_isLocalEquation hh hz) hg.1
      (fun t ht => ht.elim (fun h => h.1) (fun h => h ▸ hu')) h2
  · intro hg
    refine mem_vanishingIdeal_of_isInSpanAt' (fun s hs => ?_) hg
    rcases hs with hs | rfl
    · exact ⟨hs.1, by filter_upwards [hs.2] with y hy hyW using hy (hWN hyW)⟩
    · exact ⟨hu', hu'W⟩

/-- **`le:Gi` (3) along `N`: near `z`, `W' ∩ N' = V(u') ∩ N'`.**  Hypotheses as in
`vanishingIdeal_geoStrictTransform_inter_zeroSet_mem_iff`, without `π z ∈ W`: for `y ∈ N'` near
`z`, `y` lies on the strict transform of `N ∩ V(u) ∩ U` iff `u'(y) = 0`. -/
theorem eventually_mem_geoStrictTransform_inter_zeroSet_iff (hπ : IsBlowupAlong n C π)
    {N : Set X} (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) {U' : Set Y} {h : Y → ℂ}
    (hh : IsLocalEquation hπ U' h) {U : Set X} (hU : IsOpen U) {u : X → ℂ}
    (hu : ∀ x ∈ U, HolomorphicAt n u x)
    (hu1 : ∀ x ∈ U, x ∈ N → u x = 0 → ∃ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsTangentField N e ξ x ∧ fieldDeriv e ξ u x ≠ 0)
    (hCu : ∀ x ∈ C, x ∈ U → u x = 0) {z : Y} (hz : z ∈ U') (hzU : π z ∈ U) {u' : Y → ℂ}
    (hu' : HolomorphicAt n u' z) (heq : (u ∘ π) =ᶠ[𝓝 z] fun y => h y * u' y) :
    ∀ᶠ y in 𝓝 z, y ∈ geoStrictTransform π C N →
      (y ∈ geoStrictTransform π C (N ∩ {x | u x = 0} ∩ U) ↔ u' y = 0) := by
  have hπc : Continuous π := hπ.contMDiff.continuous
  filter_upwards [hh.isOpen.mem_nhds hz, (hU.preimage hπc).mem_nhds hzU,
    HolomorphicAt.eventually_holomorphicAt hu', heq.eventually_nhds,
    eventually_eq_zero_of_mem_geoStrictTransform hh (A := N ∩ {x | u x = 0} ∩ U)
      (fun x hx => hx.1.2) hz hu' heq] with y hyU' hyU hu'y heqy hzero hyN
  refine ⟨hzero, fun hy0 => ?_⟩
  by_cases hyC : π y ∈ C
  · have hyNN : π y ∈ N := hCN hyC
    have hu0 : u (π y) = 0 := hCu _ hyC hyU
    by_contra hyW
    have h1 : (vanishingIdeal (n := n) (geoStrictTransform π C (N ∩ {x | u x = 0} ∩ U))).mem y
        (fun _ => 1) :=
      ⟨holomorphicAt_const 1, by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hyW] with p hp hpW
        exact absurd hpW hp⟩
    have h2 := (vanishingIdeal_geoStrictTransform_inter_zeroSet_mem_iff hπ hN hCN hh hU hu hu1 hCu
      hyU' hyU hyNN hu0 hu'y heqy _).mp h1
    have h3 := apply_eq_zero_of_isInSpanAt (fun s hs => hs.elim (fun h => h.2.self_of_nhds hyN)
      (fun h => h ▸ hy0)) h2
    exact one_ne_zero h3
  · have hyNN : π y ∈ N := geoStrictTransform_subset_preimage hπc hN.1 hyN
    have hu0 : u (π y) = 0 := by
      have := heqy.self_of_nhds
      simp only [Function.comp_apply] at this
      rw [this, hy0, mul_zero]
    exact subset_closure ⟨⟨⟨hyNN, hu0⟩, hyU⟩, hyC⟩

/-- **`le:Gi` (2) along `N`: the transform has multiplicity one along `N'`.**  Hypotheses as in
`eventually_mem_geoStrictTransform_inter_zeroSet_iff`; at a point `z` of the strict transform of
`N ∩ V(u) ∩ U`, some holomorphic field tangent to `N'` has `ξ(u')(z) ≠ 0`. -/
theorem exists_fieldDeriv_ne_zero_controlledTransform_along (hπ : IsBlowupAlong n C π)
    {N : Set X} (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) {U' : Set Y} {h : Y → ℂ}
    (hh : IsLocalEquation hπ U' h) {U : Set X} (hU : IsOpen U) {u : X → ℂ}
    (hu : ∀ x ∈ U, HolomorphicAt n u x)
    (hu1 : ∀ x ∈ U, x ∈ N → u x = 0 → ∃ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsTangentField N e ξ x ∧ fieldDeriv e ξ u x ≠ 0)
    (hCu : ∀ x ∈ C, x ∈ U → u x = 0) {z : Y} (hz : z ∈ U') (hzU : π z ∈ U) {u' : Y → ℂ}
    (hu' : HolomorphicAt n u' z) (heq : (u ∘ π) =ᶠ[𝓝 z] fun y => h y * u' y)
    (hzW : z ∈ geoStrictTransform π C (N ∩ {x | u x = 0} ∩ U)) :
    ∃ (e : ComplexChart n Y) (ξ : Fin n → Y → ℂ),
      IsTangentField (geoStrictTransform π C N) e ξ z ∧ fieldDeriv e ξ u' z ≠ 0 := by
  classical
  have hWN : geoStrictTransform π C (N ∩ {x | u x = 0} ∩ U) ⊆ geoStrictTransform π C N :=
    closure_mono (preimage_mono
      (sdiff_subset_sdiff_left (inter_subset_left.trans inter_subset_left)))
  have hV : IsOpen (π ⁻¹' ((⟨U, hU⟩ : Opens X) : Set X)) := hU.preimage hπ.contMDiff.continuous
  have hr := isBlowupAlong_restrict hπ ⟨U, hU⟩ hV
  have hWV := isClosedSubmanifold_preimage_val_inter_zeroSet hN ⟨U, hU⟩ hu hu1
  have hCWV : ((↑) ⁻¹' C : Set (⟨U, hU⟩ : Opens X)) ⊆
      (↑) ⁻¹' (N ∩ {x | u x = 0} ∩ U) := fun x hx => ⟨⟨hCN hx, hCu x.1 hx x.2⟩, x.2⟩
  have hzWV : (⟨z, hzU⟩ : (⟨π ⁻¹' ((⟨U, hU⟩ : Opens X) : Set X), hV⟩ : Opens Y)) ∈
      geoStrictTransform (fun p : (⟨π ⁻¹' ((⟨U, hU⟩ : Opens X) : Set X), hV⟩ : Opens Y) =>
        (⟨π p.1, p.2⟩ : (⟨U, hU⟩ : Opens X))) ((↑) ⁻¹' C) ((↑) ⁻¹' (N ∩ {x | u x = 0} ∩ U)) := by
    rw [geoStrictTransform_preimage_val ⟨U, hU⟩ hV]
    exact hzW
  -- `π z ∈ W`
  obtain ⟨⟨hzN, hz0⟩, -⟩ : (⟨π z, hzU⟩ : (⟨U, hU⟩ : Opens X)) ∈
      ((↑) ⁻¹' (N ∩ {x | u x = 0} ∩ U) : Set (⟨U, hU⟩ : Opens X)) :=
    geoStrictTransform_subset_preimage hr.contMDiff.continuous hWV.1 hzWV
  -- dimensions: `W` has dimension `k - 1` at `π z`, `N` dimension `k ≥ 1`
  obtain ⟨k, hk'⟩ := hN.2 (π z) hzN
  obtain ⟨hkn, -, Φ, hΦsrc, -, hflat⟩ := id hk'
  obtain ⟨e, ξ, hξ, hne⟩ := hu1 (π z) hzU hzN hz0
  obtain ⟨j, hj, -⟩ :=
    exists_flatPartial_ne_zero hΦsrc hflat (mem_flatDomain_self Φ) hzN (hu _ hzU) hξ hne
  have hWreg : RegularAtDim (n := n) (N ∩ {x | u x = 0} ∩ U) (π z) (k - 1) :=
    regularAtDim_inter_zeroSet hΦsrc hflat hkn hU hu hzU hzN hz0 hξ hne
  -- `W'` has dimension `k - 1` at `z` (on the restriction to `U`)
  have hW'reg : RegularAtDim (n := n) (geoStrictTransform π C (N ∩ {x | u x = 0} ∩ U)) z
      (k - 1) := by
    have hWVreg : RegularAtDim (n := n) ((↑) ⁻¹' (N ∩ {x | u x = 0} ∩ U) :
        Set (⟨U, hU⟩ : Opens X)) ⟨π z, hzU⟩ (k - 1) := regularAtDim_preimage_val_iff.mpr hWreg
    have hreg : RegularAtDim (n := n) (geoStrictTransform
        (fun p : (⟨π ⁻¹' ((⟨U, hU⟩ : Opens X) : Set X), hV⟩ : Opens Y) =>
          (⟨π p.1, p.2⟩ : (⟨U, hU⟩ : Opens X))) ((↑) ⁻¹' C) ((↑) ⁻¹' (N ∩ {x | u x = 0} ∩ U)))
        ⟨z, hzU⟩ (k - 1) := by
      by_cases hzC : π z ∈ C
      · obtain ⟨kC, hkC⟩ := hr.1.2 ⟨π z, hzU⟩ hzC
        exact regularAtDim_geoStrictTransform_of_mem hr (le_of_regularAtDim_subset hkC hWVreg hCWV)
          hkC hWVreg hCWV hzWV
      · exact regularAtDim_geoStrictTransform_of_notMem hr hWV.1 (z := ⟨z, hzU⟩) hzC hWVreg
    rw [geoStrictTransform_preimage_val ⟨U, hU⟩ hV] at hreg
    exact regularAtDim_preimage_val_iff.mp hreg
  -- `N'` has dimension `k` at `z`
  have hN'reg : RegularAtDim (n := n) (geoStrictTransform π C N) z k := by
    by_cases hzC : π z ∈ C
    · obtain ⟨kC, hkC⟩ := hπ.1.2 (π z) hzC
      exact regularAtDim_geoStrictTransform_of_mem hπ (le_of_regularAtDim_subset hkC hk' hCN) hkC
        hk' hCN (hWN hzW)
    · exact regularAtDim_geoStrictTransform_of_notMem hπ hN.1 hzC hk'
  have hu'0 : u' z = 0 := (eventually_eq_zero_of_mem_geoStrictTransform hh
    (A := N ∩ {x | u x = 0} ∩ U) (fun x hx => hx.1.2) hz hu' heq).self_of_nhds hzW
  exact exists_fieldDeriv_ne_zero_of_vanishingIdeal_le (by omega : k - 1 < k) hW'reg hN'reg hWN hu'
    hu'0 fun g hg => (vanishingIdeal_geoStrictTransform_inter_zeroSet_mem_iff hπ hN hCN hh hU hu hu1
      hCu hz hzU hzN hz0 hu' heq g).mp hg

end Giraud

end

end Hironaka.LocalGiraudTransformAlong
