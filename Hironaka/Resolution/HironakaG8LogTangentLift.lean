import Hironaka.Resolution.HironakaG8LogLiftChart
import Hironaka.MarkedIdeal.DerivativeIdealAlongTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The logarithmic lift of a logarithmic field under a blowup (G8 lane, run 0079, round 3; toward leaf G8-3H-C06)

Blueprint: `hironaka-g8-resume-log-tangent-lift.tex`.

Let `π : Y → X` be the blowup along a closed centre `C`, `N` a closed carrier with strict transform
`N' = closure (π⁻¹(N \ C))`, `E` a list of closed boundary members with transformed list
`E' = strict E ++ [π⁻¹C]`, and assume the simultaneous normal crossings of `C`, `N`, `E` at the points of `C ∩ N`
(`BlowupSNCTransform.IsAdaptedAt`).  At every point `z ∈ N'`, for a generator `y` of `π^*𝓘_C` near `z`
(`DerivativeIdealAlongTransform.IsUniformDerivationGenerator`) and every field `ξ` logarithmic for `(N, E)` at `π z`,
`exists_log_tangent_lift` gives a field `D'` at `z`, LOGARITHMIC for `(N', E')`, with

  `y · (ξ f) ∘ π = D'(f ∘ π)` near `z` for every `f` holomorphic at `π z`, and `D'(y) = ρ y`.

This is the logarithmic form of `DerivativeIdealAlongTransform.exists_tangent_lift` (Bierstone--Milman 2008,
Lemma 3.1), the only input of the ordinary inclusion `restrictLe_colonAlong_derivIdealAlong` that changes in the
log setting:

* over the centre, `D' = u · L` with `L` the explicit lift of `ζ_p ξ` in a log-lift chart
  (`HironakaG8LogLiftChart`, built from the actual monomial local inverse) and `y = u ζ_p` (every germ of
  `π^*𝓘_C` is a multiple of the exceptional coordinate, `LogLiftChart.exists_comp_eq_mul_t`);
* off the centre, `D' = y · T` with `T` the transfer of `ξ` through the local inverse of `π`
  (`HironakaG8LogDerivEtale`), the strict transforms agreeing with the preimages there.

Not here (next step): the controlled log inclusion itself (the log analogue of
`restrictLe_colonAlong_derivIdealAlong`, its iterate and the marked form).

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LogTangentLift

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.HolomorphicMaps BlowupTowers
  GermIdealOrder DerivativeIdeal IdealWeightPowers InvertibleIdealQuotient BlowupExceptionalDivisor
  BlowupControlledTransform BlowupDerivativeIdeal DerivativeIdealAlongTransform
open Hironaka.DerivativeIdealAlong Hironaka.DerivativeIdealAlongCoherent
  Hironaka.DerivativeIdealAlongEtale Hironaka.BlowupStrictSubmanifold
  Hironaka.RestrictedIdealExtension Hironaka.RestrictedIdealQuotient
  Hironaka.RestrictedIdealWeight Hironaka.RelativePrincipalizationSpan
  Hironaka.BlowupFlatCoordinates Hironaka.BlowupSNCTransform
  Hironaka.HadamardBridge
  Hironaka.HironakaActualIntrinsicLogDerivativeFrame
  Hironaka.HironakaG8FlatFieldCalculus
  Hironaka.HironakaG8LogDerivEtale
  Hironaka.HironakaG8LogLiftChart

noncomputable section

/-! ### Rescaling a logarithmic field -/

section Smul

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `(a ξ)(f) = a · ξ(f)`. -/
theorem fieldDeriv_smul (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (a f : M → ℂ) :
    fieldDeriv e (fun j p => a p * ξ j p) f = fun p => a p * fieldDeriv e ξ f p := by
  funext p
  simp only [fieldDeriv, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

/-- A holomorphic multiple of a field tangent to `N` is tangent to `N`. -/
theorem isTangentField_smul {N : Set M} {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {x : M}
    (hξ : IsTangentField N e ξ x) {a : M → ℂ} (ha : HolomorphicAt n a x) :
    IsTangentField N e (fun j p => a p * ξ j p) x := by
  refine ⟨hξ.mem_source, fun j => ha.mul (hξ.holomorphicAt j), fun g hg => ?_⟩
  have h := hξ.preserves g hg
  rw [fieldDeriv_smul]
  refine ⟨ha.mul h.1, ?_⟩
  filter_upwards [h.2] with p hp hpN
  rw [hp hpN, mul_zero]

/-- A holomorphic multiple of a logarithmic field is logarithmic. -/
theorem isLogTangentField_smul {N : Set M} {E : List (Set M)} {e : ComplexChart n M} {ξ : Fin n → M → ℂ}
    {x : M} (hξ : IsLogTangentField N E e ξ x) {a : M → ℂ} (ha : HolomorphicAt n a x) :
    IsLogTangentField N E e (fun j p => a p * ξ j p) x :=
  ⟨isTangentField_smul hξ.1 ha, fun H hH => isTangentField_smul (hξ.2 H hH) ha⟩

end Smul

/-! ### The logarithmic lift of a logarithmic field -/

section Lift

variable {n : ℕ} {X Y : CMfd.{0} n} {C : Set X} {π : Y → X}

/-- **Off the centre**: `D' = y · T`, `T` the transfer of `ξ` through the local inverse of `π`. -/
theorem exists_log_tangent_lift_of_notMem (hπ : IsBlowupAlong n C π) {N : Set X} (hN : IsClosed N)
    {E : List (Set X)} (hEc : ∀ H ∈ E, IsClosed H) {z : Y} (hzC : π z ∉ C) {U : Set Y} {y : Y → ℂ}
    (hy : IsUniformDerivationGenerator n π C z U y) {e : ComplexChart n X} {ξ : Fin n → X → ℂ}
    (hξ : IsLogTangentField N E e ξ (π z)) :
    ∃ B : Fin n → Y → ℂ, IsLogTangentField (geoStrictTransform π C N)
        (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) (complexChartAt (n := n) z) B z ∧
      (∀ f : X → ℂ, HolomorphicAt n f (π z) →
        (fun p => y p * fieldDeriv e ξ f (π p)) =ᶠ[𝓝 z] fieldDeriv (complexChartAt (n := n) z) B (f ∘ π)) ∧
      ∃ ρ : Y → ℂ, HolomorphicAt n ρ z ∧
        fieldDeriv (complexChartAt (n := n) z) B y =ᶠ[𝓝 z] fun p => ρ p * y p := by
  obtain ⟨ψ, hψ⟩ := exists_isLocalInverseAt_of_notMem_centre hπ hzC
  set ez := complexChartAt (n := n) z with hez
  have hzs : z ∈ ez.val.source := mem_complexChartAt_source z
  have hx : π z ∈ e.val.source := hξ.1.mem_source
  set T := transferField π ψ e ez ξ with hT
  have hyz : HolomorphicAt n y z := hy.holomorphicAt z hy.mem
  have hTlog := isLogTangentField_transfer hψ hzs hξ
  have hTh : ∀ m, HolomorphicAt n (T m) z := hTlog.1.holomorphicAt
  have hO : ∀ᶠ q in 𝓝 z, π q ∉ C :=
    (hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous).mem_nhds hzC
  have hstrict : ∀ {H : Set X}, IsClosed H →
      ∀ᶠ q in 𝓝 z, q ∈ π ⁻¹' H ↔ q ∈ geoStrictTransform π C H := fun {H} hH => by
    filter_upwards [hO] with q hq
    exact (mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hH hq).symm
  have hTlog' : IsLogTangentField (geoStrictTransform π C N) (E.map (geoStrictTransform π C) ++ [π ⁻¹' C])
      ez T z := by
    refine ⟨isTangentField_congr_set hTlog.1 (hstrict hN), fun H' hH' => ?_⟩
    rcases List.mem_append.mp hH' with h | h
    · obtain ⟨H, hH, rfl⟩ := List.mem_map.mp h
      exact isTangentField_congr_set (hTlog.2 _ (List.mem_map.mpr ⟨H, hH, rfl⟩)) (hstrict (hEc H hH))
    · rw [List.mem_singleton] at h
      subst h
      exact isTangentField_of_eventually_notMem hzs hTh hO
  refine ⟨fun j p => y p * T j p, isLogTangentField_smul hTlog' hyz, fun f hf => ?_,
    fieldDeriv ez T y, holomorphicAt_fieldDeriv hzs hTh hyz, ?_⟩
  · have hfπ : HolomorphicAt n (f ∘ π) z := holomorphicAt_comp_map hψ.mdiff hf
    have h1 := fieldDeriv_transfer hψ hzs hx ξ hfπ
    have hfψ : (f ∘ π) ∘ ψ =ᶠ[𝓝 (π z)] f := by
      filter_upwards [hψ.right_inv] with q hq
      simp only [Function.comp_apply, hq]
    have h2 := hψ.mdiff.self_of_nhds.continuousAt.tendsto.eventually (fieldDeriv_congr (ξ := ξ) hx hfψ)
    filter_upwards [h1, h2] with p hp1 hp2
    rw [fieldDeriv_smul]
    show y p * fieldDeriv e ξ f (π p) = y p * fieldDeriv ez (transferField π ψ e ez ξ) (f ∘ π) p
    rw [hp1, hp2]
  · exact Eventually.of_forall fun p => by rw [fieldDeriv_smul]; exact mul_comm _ _

/-- **Over the centre**: `D' = u · L`, `L` the lift of `ζ_p ξ` in a log-lift chart and `y = u ζ_p`. -/
theorem exists_log_tangent_lift_of_mem (hπ : IsBlowupAlong n C π) {N : Set X} {E : List (Set X)}
    (hEc : ∀ H ∈ E, IsClosed H) {z : Y} (hzC : π z ∈ C) (hzN : z ∈ geoStrictTransform π C N)
    (had : IsAdaptedAt n C N E (π z)) {U : Set Y} {y : Y → ℂ}
    (hy : IsUniformDerivationGenerator n π C z U y) {e : ComplexChart n X} {ξ : Fin n → X → ℂ}
    (hξ : IsLogTangentField N E e ξ (π z)) :
    ∃ B : Fin n → Y → ℂ, IsLogTangentField (geoStrictTransform π C N)
        (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) (complexChartAt (n := n) z) B z ∧
      (∀ f : X → ℂ, HolomorphicAt n f (π z) →
        (fun p => y p * fieldDeriv e ξ f (π p)) =ᶠ[𝓝 z] fieldDeriv (complexChartAt (n := n) z) B (f ∘ π)) ∧
      ∃ ρ : Y → ℂ, HolomorphicAt n ρ z ∧
        fieldDeriv (complexChartAt (n := n) z) B y =ᶠ[𝓝 z] fun p => ρ p * y p := by
  classical
  obtain ⟨K⟩ := exists_logLiftChart hπ hEc hzC hzN had
  set ez := complexChartAt (n := n) z with hez
  have hzs : z ∈ ez.val.source := mem_complexChartAt_source z
  have hx : π z ∈ e.val.source := hξ.1.mem_source
  have hξh := hξ.1.holomorphicAt
  have hyz : HolomorphicAt n y z := hy.holomorphicAt z hy.mem
  have ht : HolomorphicAt n (flatCoord K.Θ K.p) z := holomorphicAt_flatCoord K.Θ K.p K.mem_flatDomain_Θ
  -- `y = u ζ_p`
  have hyJ : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem z y :=
    (hy.generates z hy.mem y).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hyz)
  obtain ⟨-, k, s, c, hs, hc, hsum⟩ := hyJ
  choose a ha has using hs
  choose h hh hah using fun i => K.exists_comp_eq_mul_t (ha i)
  set u : Y → ℂ := fun p => ∑ i, c i p * h i p with hu
  have huh : HolomorphicAt n u z := HolomorphicAt.sum _ fun i _ => (hc i).mul (hh i)
  have hyu : y =ᶠ[𝓝 z] fun p => u p * flatCoord K.Θ K.p p := by
    filter_upwards [hsum, eventually_all.2 hah] with p hp1 hp2
    rw [hp1, hu, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [has i]
    have := hp2 i
    simp only [Function.comp_apply] at this ⊢
    rw [this]
    ring
  set L := K.liftField e ξ with hL
  have hLh : ∀ m, HolomorphicAt n (L m) z := K.holomorphicAt_liftField hx hξh
  refine ⟨fun j p => u p * L j p, isLogTangentField_smul (K.isLogTangentField_liftField hξ) huh,
    fun f hf => ?_, fun p => fieldDeriv ez L u p + u p * K.srcCoeff e ξ K.p (π p),
    (holomorphicAt_fieldDeriv hzs hLh huh).add (huh.mul (K.holomorphicAt_srcCoeff_comp hx hξh K.p)), ?_⟩
  · filter_upwards [K.eventually_fieldDeriv_liftField_comp ξ hx hf, hyu] with p hp1 hp2
    rw [fieldDeriv_smul]
    show y p * fieldDeriv e ξ f (π p) = u p * fieldDeriv (complexChartAt (n := n) z) (K.liftField e ξ) (f ∘ π) p
    rw [hp1, hp2]
    ring
  · have h1 := fieldDeriv_congr (ξ := L) hzs hyu
    have h2 := fieldDeriv_mul_eventuallyEq (ξ := L) hzs huh ht
    filter_upwards [h1, h2, K.eventually_fieldDeriv_liftField_t e ξ, hyu] with p hp1 hp2 hp3 hp4
    rw [fieldDeriv_smul]
    beta_reduce
    rw [hp1, hp2, hp3, hp4]
    ring

/-- **The lifted derivation of a logarithmic field is logarithmic** for the strict carrier and the transformed
boundary `strict E ++ [π⁻¹C]`, at every point of the strict carrier: for a generator `y` of `π^*𝓘_C` near `z`, a
field `D'` with `y · (ξ f) ∘ π = D'(f ∘ π)` for every `f` and `D'(y) ∈ (y)`.  Over the centre the simultaneous
normal crossings of `C`, `N`, `E` at `π z` is used. -/
theorem exists_log_tangent_lift (hπ : IsBlowupAlong n C π) {N : Set X} (hN : IsClosed N) {E : List (Set X)}
    (hEc : ∀ H ∈ E, IsClosed H) (hAd : ∀ x ∈ C, x ∈ N → IsAdaptedAt n C N E x) {z : Y}
    (hzN : z ∈ geoStrictTransform π C N) {U : Set Y} {y : Y → ℂ}
    (hy : IsUniformDerivationGenerator n π C z U y) {e : ComplexChart n X} {ξ : Fin n → X → ℂ}
    (hξ : IsLogTangentField N E e ξ (π z)) :
    ∃ B : Fin n → Y → ℂ, IsLogTangentField (geoStrictTransform π C N)
        (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) (complexChartAt (n := n) z) B z ∧
      (∀ f : X → ℂ, HolomorphicAt n f (π z) →
        (fun p => y p * fieldDeriv e ξ f (π p)) =ᶠ[𝓝 z] fieldDeriv (complexChartAt (n := n) z) B (f ∘ π)) ∧
      ∃ ρ : Y → ℂ, HolomorphicAt n ρ z ∧
        fieldDeriv (complexChartAt (n := n) z) B y =ᶠ[𝓝 z] fun p => ρ p * y p := by
  by_cases hzC : π z ∈ C
  · have hxN : π z ∈ N := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN hzN
    exact exists_log_tangent_lift_of_mem hπ hEc hzC hzN (hAd _ hzC hxN) hy hξ
  · exact exists_log_tangent_lift_of_notMem hπ hN hEc hzC hy hξ

end Lift

end

end Hironaka.HironakaG8LogTangentLift
