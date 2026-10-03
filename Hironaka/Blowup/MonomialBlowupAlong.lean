/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.MonomialBlowup
import Hironaka.Blowup.ExceptionalPushforwardAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Invariant.CompanionReduction
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialPart
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Monomial ideals under the blowup of a centre with normal crossings, along a submanifold

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2b of the proof of `pr:resol` (the transform of a monomial
marked ideal), and the transform of marked ideals along a submanifold, §2.1 (3)--(5); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`) §5.

Let `(M, N, E, 𝔞, d)` be a marked ideal with `N` a closed submanifold, `𝔞` coherent, `C` an
admissible centre, `π` the blowup along `C`, `N' = closure (π⁻¹ (N \ C))` and `z ∈ N'` over `C`.

* `isInSpanOnAt_geoTransform_iff_of_eq`: if `Res_N 𝔞 = Res_N (m)` at `π z` and
  `m ∘ π = c · h^e · q` near `z` (`𝒪(-D) = (h)` at `z`, `c(z) ≠ 0`, `d ≤ e`), then
  `Res_{N'} 𝔞' = Res_{N'} (h^{e-d} q)` at `z` (`Res_W 𝔟 = Res_W 𝔠` at a point: the same germs
  `g` are, on `W` near the point, combinations of germs of `𝔟` resp. `𝔠`).
* helpers: `isInSpanOnAt_comp_of_mem_pullback`, `isInSpanOnAt_pullback_comp` (restricted
  generators and restricted membership pull back from `N` to `N'`).

No transversality of `E` to `N` is used: the statement is about the restrictions of ambient
generators.  Reading `W_j|_{N'}`, `W_{s i}|_{N'}` as coordinates of `N'` (the monomial form of
`E'|_{N'}`) needs coordinates adapted to `N'` as well, which this module does not provide.

Proof: `restrictLe_pullback_geoTransform` (`Res_{N'} π^*𝔞 = Res_{N'} 𝒪(-dD) 𝔞'`), the local generator `h₀` of
`𝒪(-dD)` vanishing identically on no piece of `N'` (`isInvertibleAlong_geoStrictTransform`), `h^d = κ h₀` with `κ(z)
≠ 0` (`MonomialBlowup.exists_unit_of_isInSpanAt`), and cancellation of `h₀` along `N'`
(`RestrictedIdealQuotient.eventuallyEq_within_of_mul_eventuallyEq_within`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MonomialBlowupAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupFlatCoordinates Hironaka.BlowupExceptionalDivisor Hironaka.BlowupStrictSubmanifold Hironaka.BlowupStrictIdeal Hironaka.NormalCrossings Hironaka.MonomialPart Hironaka.GermIdealOrder Hironaka.IdealWeightPowers Hironaka.BlowupControlledTransform Hironaka.InvertibleIdealQuotient Hironaka.RelativePrincipalizationSpan Hironaka.RestrictedIdealQuotient Hironaka.GermIdealTotalTransform Hironaka.MonomialBlowup

noncomputable section

variable {n : ℕ}

section Along

open MarkedIdeals MarkedIdeals.MarkedIdeal

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **A restricted generator pulls back.**  If every germ of `𝔞` at `π z` is a multiple of `m` on
`N` near `π z` (`N` closed), then every germ of `π^*𝔞` at `z` is a multiple of `m ∘ π` on
`N' = closure (π⁻¹ (N \ C))` near `z`. -/
theorem isInSpanOnAt_comp_of_mem_pullback (hπ : IsBlowupAlong n C π) {N : Set X}
    (hNc : IsClosed N) {𝔞 : GermIdeal n X} {z : Y} {m : X → ℂ}
    (hgen : ∀ g, 𝔞.mem (π z) g → IsInSpanOnAt (n := n) N (· = m) (π z) g)
    {G : Y → ℂ} (hG : (GermIdeal.pullback (m := n) π 𝔞).mem z G) :
    IsInSpanOnAt (n := n) (geoStrictTransform π C N) (· = fun y => m (π y)) z G := by
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp hG))
  rintro s ⟨a, ha, rfl⟩
  obtain ⟨K, b, d, hb, hd, hsum⟩ := hgen a ha
  have hfy : ∀ᶠ w in 𝓝 z, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π w :=
    Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt
  refine ⟨K, fun _ y => m (π y), fun i => d i ∘ π, fun _ => rfl,
    fun i => (hd i).comp_contMDiff hfy, ?_⟩
  filter_upwards [hπ.contMDiff.continuous.continuousAt.eventually hsum] with w hw hwN
  have h1 := hw (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc hwN)
  show a (π w) = ∑ i, d i (π w) * m (π w)
  rw [h1]
  exact Finset.sum_congr rfl fun i _ => by rw [hb i]

/-- **Restricted membership pulls back.**  If `m` agrees on `N` near `π z` with a combination of
germs of `𝔞` (coherent), then `m ∘ π` agrees on `N'` near `z` with a combination of germs of
`π^*𝔞`. -/
theorem isInSpanOnAt_pullback_comp (hπ : IsBlowupAlong n C π) {N : Set X} (hNc : IsClosed N)
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {z : Y} {m : X → ℂ}
    (hm : IsInSpanOnAt (n := n) N (𝔞.mem (π z)) (π z) m) :
    IsInSpanOnAt (n := n) (geoStrictTransform π C N)
      ((GermIdeal.pullback (m := n) π 𝔞).mem z) z (fun y => m (π y)) := by
  obtain ⟨K, s, d, hs, hd, hsum⟩ := hm
  have hfy : ∀ᶠ w in 𝓝 z, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π w :=
    Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt
  refine ⟨K, fun i => s i ∘ π, fun i => d i ∘ π, fun i => ?_,
    fun i => (hd i).comp_contMDiff hfy, ?_⟩
  · exact GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self (S := fun t => ∃ a, 𝔞.mem (π z) a ∧ t = a ∘ π) ⟨s i, hs i, rfl⟩
        ((GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 (hs i)).comp_contMDiff hfy))
  · filter_upwards [hπ.contMDiff.continuous.continuousAt.eventually hsum] with w hw hwN
    exact hw (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc hwN)

/-- **The transform along `N'` of an ideal whose restriction to `N` is principal.** Let `(M, N, E, 𝔞, d)` have `N` a
closed submanifold, `𝔞` coherent, `C` an admissible centre, and `z ∈ N'` over `C`. If `Res_N 𝔞 = Res_N (m)` at `π z`
and `m ∘ π = c · h^e · q` near `z`, with `𝒪(-D) = (h)` at `z`, `c(z) ≠ 0` and `d ≤ e`, then `Res_{N'} 𝔞' = Res_{N'}
(h^{e-d} q)` at `z`. Proof: `Res_{N'} π^*𝔞 = Res_{N'} 𝒪(-dD) 𝔞'` (`restrictLe_pullback_geoTransform`), `𝒪(-dD) =
(h₀)` near `z` with `h₀` vanishing identically on no piece of `N'` (`isInvertibleAlong_geoStrictTransform`), `h^d =
κ h₀` with `κ(z) ≠ 0` (`exists_unit_of_isInSpanAt`), so `m ∘ π = h₀ · c κ h^{e-d} q`; then cancel `h₀` along `N'`
(`eventuallyEq_within_of_mul_eventuallyEq_within`). -/
theorem isInSpanOnAt_geoTransform_iff_of_eq (hπ : IsBlowupAlong n C π) {𝔪 : MarkedIdeal n X}
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hC : 𝔪.IsAdmissibleCentre C)
    {z : Y} (hz : z ∈ geoStrictTransform π C 𝔪.N) {m : X → ℂ}
    (hgen : ∀ g, IsInSpanOnAt (n := n) 𝔪.N (𝔪.ideal.mem (π z)) (π z) g ↔
      IsInSpanOnAt (n := n) 𝔪.N (· = m) (π z) g)
    {h c q : Y → ℂ}
    (hD : ∀ g, (exceptionalDivisor hπ).ideal.mem z g ↔ IsInSpanAt (n := n) (· = h) z g)
    (hh : HolomorphicAt n h z) (hc : HolomorphicAt n c z) (hcz : c z ≠ 0)
    (hq : HolomorphicAt n q z) {e : ℕ} (hde : 𝔪.d ≤ e)
    (heq : (fun w => m (π w)) =ᶠ[𝓝 z] fun w => c w * h w ^ e * q w) (g : Y → ℂ) :
    IsInSpanOnAt (n := n) (geoStrictTransform π C 𝔪.N) ((𝔪.geoTransform C π).ideal.mem z) z g ↔
      IsInSpanOnAt (n := n) (geoStrictTransform π C 𝔪.N)
        (· = fun w => h w ^ (e - 𝔪.d) * q w) z g := by
  classical
  have hσc : (𝔪.geoTransform C π).ideal.IsCoherent :=
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h𝔞 hC hπ
  obtain ⟨G1, G2⟩ :=
    MarkedIdealOperationsAlong.MarkedIdeal.restrictLe_pullback_geoTransform hN h𝔞 hC hπ
  -- a generator of `𝒪(-dD)` near `z`, vanishing identically on no piece of `N'`
  obtain ⟨U, hU, hzU, h₀, hh₀d, hnon, hgen₀⟩ :=
    isInvertibleAlong_geoStrictTransform hπ 𝔪.N 𝔪.d z hz
  have hh₀ : HolomorphicAt n h₀ z := holomorphicAt_of_mdifferentiableOn hU hh₀d hzU
  have hh₀mem : (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔪.d).mem
      z h₀ := (hgen₀ z hzU h₀).mpr (isInSpanAt_self rfl hh₀)
  -- `h^d = κ h₀` with `κ(z) ≠ 0`
  have hhd : (idealPow (exceptionalDivisor hπ).ideal 𝔪.d).mem z (fun y => h y ^ 𝔪.d) :=
    pow_mem_idealPow ((hD h).mpr (isInSpanAt_self rfl hh)) hh 𝔪.d
  have h1 : IsInSpanAt (n := n) (· = h₀) z (fun y => h y ^ 𝔪.d) := (hgen₀ z hzU _).mp hhd
  have h2 : IsInSpanAt (n := n) (· = fun y => h y ^ 𝔪.d) z h₀ := by
    obtain ⟨b, hb, hbeq⟩ := exists_eq_mul_pow_of_mem_idealPow (I := (exceptionalDivisor hπ).ideal)
      (u := h) (fun g hg => (hD g).mp hg) hh₀mem
    exact isInSpanAt_eq_iff.mpr ⟨hh₀, b, hb, hbeq⟩
  have hfreq : ∃ᶠ y in 𝓝 z, h₀ y ≠ 0 := by
    rw [Filter.Frequently]
    intro hall
    obtain ⟨V, hVsub, hVo, hzV⟩ := mem_nhds_iff.mp ((hU.eventually_mem hzU).and hall)
    obtain ⟨y, hy, hy0⟩ := hnon V hVo (fun y hy => (hVsub hy).1) ⟨z, hzV, hz⟩
    exact (hVsub hy.1).2 hy0
  obtain ⟨κ, hκ, hκz, hκeq⟩ := exists_unit_of_isInSpanAt h1 h2 hfreq
  -- `m ∘ π = h₀ · c κ h^{e-d} q` near `z`
  have hkey : ∀ᶠ w in 𝓝 z, m (π w) = h₀ w * (c w * κ w * h w ^ (e - 𝔪.d) * q w) := by
    filter_upwards [heq, hκeq] with w hw1 hw2
    have he : h w ^ e = h w ^ 𝔪.d * h w ^ (e - 𝔪.d) := by
      rw [← pow_add, Nat.add_sub_cancel' hde]
    rw [hw1, he, hw2]
    ring
  have hL : HolomorphicAt n (fun y => c y * κ y * h y ^ (e - 𝔪.d) * q y) z :=
    ((hc.mul hκ).mul (CompanionReduction.holomorphicAt_pow_of hh _)).mul hq
  constructor
  · -- every germ `t` of `𝔞'` is a multiple of `h^{e-d} q` on `N'`
    intro hg
    refine IsInSpanOnAt.trans (fun t ht => ?_) hg
    have htz : HolomorphicAt n t z := GermIdeal.IsCoherent.holomorphicAt_mem hσc ht
    have hmul : ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔪.d).mul
        (𝔪.geoTransform C π).ideal).mem z (fun y => h₀ y * t y) :=
      mem_mul_of_mem_mem hh₀mem ht (hh₀.mul htz)
    have h3 : IsInSpanOnAt (n := n) (geoStrictTransform π C 𝔪.N) (· = fun y => m (π y)) z
        (fun y => h₀ y * t y) :=
      IsInSpanOnAt.trans (fun s hs => isInSpanOnAt_comp_of_mem_pullback hπ hN.1
        (fun g hg => (hgen g).mp (IsInSpanAt.restrict (isInSpanAt_self hg
          (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg)))) hs) (G2 z hz _ hmul)
    obtain ⟨K, s, a, hs, ha, hsum⟩ := h3
    have hA : HolomorphicAt n (fun y => ∑ i, a i y) z := HolomorphicAt.sum _ fun i _ => ha i
    have hcancel := eventuallyEq_within_of_mul_eventuallyEq_within hU hnon hzU htz
      (hA.mul hL) (by
        filter_upwards [hsum, hkey] with y hy1 hy2 hyW
        rw [hy1 hyW]
        simp only [hs, hy2]
        rw [← Finset.sum_mul]
        ring)
    refine ⟨1, fun _ y => h y ^ (e - 𝔪.d) * q y, fun _ y => (∑ i, a i y) * (c y * κ y),
      fun _ => rfl, fun _ => hA.mul (hc.mul hκ), ?_⟩
    filter_upwards [hcancel] with y hy hyW
    rw [hy hyW]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    ring
  · -- `h^{e-d} q` is on `N'` a combination of germs of `𝔞'`
    intro hg
    refine IsInSpanOnAt.trans (fun s hs => ?_) hg
    subst hs
    -- germs of `𝒪(-dD) 𝔞'` are `h₀` times germs of `𝔞'`
    have hfac : ∀ s, ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C))
        𝔪.d).mul (𝔪.geoTransform C π).ideal).mem z s →
        ∃ r, (𝔪.geoTransform C π).ideal.mem z r ∧ s =ᶠ[𝓝 z] fun y => h₀ y * r y := by
      intro s hs
      obtain ⟨-, K, u, c', hu, hc', husum⟩ := hs
      choose p q' hp hq' hpq using hu
      choose e' he' hee using fun j => (isInSpanAt_eq_iff.mp ((hgen₀ z hzU (p j)).mp (hp j))).2
      have hq'hol : ∀ j, HolomorphicAt n (q' j) z :=
        fun j => GermIdeal.IsCoherent.holomorphicAt_mem hσc (hq' j)
      refine ⟨fun y => ∑ j, (c' j y * e' j y) * q' j y, ?_, ?_⟩
      · exact mem_of_isInSpanAt_mem hσc
          ⟨HolomorphicAt.sum _ fun j _ => ((hc' j).mul (he' j)).mul (hq'hol j), K, q',
            fun j y => c' j y * e' j y, hq', fun j => (hc' j).mul (he' j),
            Eventually.of_forall fun _ => rfl⟩
      · filter_upwards [husum, eventually_all.mpr hee] with y hy hy'
        rw [hy, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hpq j]
        show c' j y * (p j y * q' j y) = h₀ y * (c' j y * e' j y * q' j y)
        rw [hy' j]
        ring
    -- `m ∘ π` is on `N'` a combination of `h₀ r`, `r ∈ 𝔞'`
    have hmN : IsInSpanOnAt (n := n) 𝔪.N (· = m) (π z) m :=
      ⟨1, fun _ => m, fun _ _ => 1, fun _ => rfl,
        fun _ => holomorphicAt_const (n := n) (x := π z) (1 : ℂ),
        Eventually.of_forall fun y _ => by simp⟩
    have h5 := isInSpanOnAt_pullback_comp hπ hN.1 h𝔞 (C := C) ((hgen m).mpr hmN)
    have h6 : IsInSpanOnAt (n := n) (geoStrictTransform π C 𝔪.N)
        (fun s => ∃ r, (𝔪.geoTransform C π).ideal.mem z r ∧ s =ᶠ[𝓝 z] fun y => h₀ y * r y) z
        (fun y => m (π y)) := by
      refine IsInSpanOnAt.trans (fun s hs => ?_) (IsInSpanOnAt.trans (fun s hs => G1 z hz s hs) h5)
      exact ⟨1, fun _ => s, fun _ _ => 1, fun _ => hfac s hs,
        fun _ => holomorphicAt_const (n := n) (x := z) (1 : ℂ),
        Eventually.of_forall fun y _ => by simp⟩
    obtain ⟨K, s, a, hs, ha, hsum⟩ := h6
    choose r hr hreq using hs
    have hR : HolomorphicAt n (fun y => ∑ i, a i y * r i y) z :=
      HolomorphicAt.sum _ fun i _ => (ha i).mul (GermIdeal.IsCoherent.holomorphicAt_mem hσc (hr i))
    have hcancel := eventuallyEq_within_of_mul_eventuallyEq_within hU hnon hzU hL hR (by
      filter_upwards [hsum, hkey, eventually_all.mpr hreq] with y hy1 hy2 hy3 hyW
      rw [← hy2, hy1 hyW, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hy3 i]; ring)
    have hcκ : HolomorphicAt n (fun y => c y * κ y) z := hc.mul hκ
    have hcκz : c z * κ z ≠ 0 := mul_ne_zero hcz hκz
    refine ⟨K, r, fun i y => (c y * κ y)⁻¹ * a i y, hr,
      fun i => (HolomorphicAt.inv hcκ hcκz).mul (ha i), ?_⟩
    filter_upwards [hcancel, (HolomorphicAt.continuousAt hcκ).eventually_ne hcκz] with y hy hne hyW
    have h7 := hy hyW
    show h y ^ (e - 𝔪.d) * q y = ∑ i, (c y * κ y)⁻¹ * a i y * r i y
    have h8 : ∑ i, (c y * κ y)⁻¹ * a i y * r i y = (c y * κ y)⁻¹ * ∑ i, a i y * r i y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hne' : c y * κ y ≠ 0 := hne
    rw [h8, ← h7, mul_assoc (c y * κ y), ← mul_assoc (c y * κ y)⁻¹, inv_mul_cancel₀ hne',
      one_mul]

end Along

end

end Hironaka.MonomialBlowupAlong
