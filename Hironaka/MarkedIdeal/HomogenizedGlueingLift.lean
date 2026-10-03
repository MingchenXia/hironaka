/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.GlueingTrivialAction
import Hironaka.MarkedIdeal.DerivativeIdealTower
import Hironaka.Coherence.VanishingIdealCoherent
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupBiholomorphismLift
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.HomogenizedIdeal
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Glueing Lemma along multiple test blow-ups: the lifts of the glueing biholomorphism

Source: Włodarczyk 2005, Lemma `le:homo` (4) and its proof, `φ_u = φ` a biholomorphism `U ≅ U'`).

## The base case

* `eventually_mdifferentiableAt_W`, `eventually_trivialAt_coordMap`: **a coordinate change
  `φ(p) = e⁻¹Ψ(W(p) + h(p)eᵢ)` acts trivially modulo every coherent ideal `J ∋ h` at the zeros of `J` near `x`**:
  `g ∘ φ - g = h · T(W, h)` (Taylor's formula with holomorphic remainder along `eᵢ`).

## Glueing data acting trivially

* `extendMap Φ` (a map between open sets extended by the identity), `trivialAt_congr`;

## One step

* `preimage_lift_geoStrictTransform`, `pullback_lift_geoTransform`: under the lift `Φ₁` of `Φ : A ≅ B` along a blowup,
  strict transforms and transforms correspond if they do under `Φ`.

## The lifts along a multiple test blow-up (`le:homo` (4))
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedGlueingLift

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal IdealWeightPowers HomogenizedIdeal HomogenizedGlueing HomogenizedGlueingTower GlueingTrivialAction HolomorphicTaylorTail

noncomputable section

/-! ### The base case: coordinate changes act trivially -/

section Base

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The coordinates `W` of a coordinate change are holomorphic near `x`. -/
theorem eventually_mdifferentiableAt_W {x : M} (d : CoordinateChange (n := n) x) :
    ∀ᶠ p in 𝓝 x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) d.W p := by
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  filter_upwards [e.val.open_source.mem_nhds hxs,
    (e.val.continuousAt hxs).preimage_mem_nhds (d.isOpen.mem_nhds d.mem)] with p hp hpN
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.val p :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property hp
  have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (d.W ∘ e.val.symm) (e.val p) :=
    ((d.differentiableOn _ hpN).differentiableAt (d.isOpen.mem_nhds hpN)).mdifferentiableAt
  refine (h2.comp p h1).congr_of_eventuallyEq ?_
  filter_upwards [e.val.open_source.mem_nhds hp] with q hq
  simp [e.val.left_inv hq]

/-- **A coordinate change acts trivially modulo every coherent ideal containing its `h`, at the zeros of the ideal
near `x`** (Włodarczyk, proof of `le:homo` (4): `φ_u^*(f) - φ_v^*(f) ∈ (h)`). -/
theorem eventually_trivialAt_coordMap {x : M} (d : CoordinateChange (n := n) x) {J : GermIdeal n M}
    (hJ : J.IsCoherent) (hh : J.mem x d.h) :
    ∀ᶠ y in 𝓝 x, y ∈ zeroSet J → TrivialAt d.coordMap J y := by
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hWc : ContinuousAt d.W x := d.continuousAt_W
  filter_upwards [eventually_mem hJ hh, eventually_coordMap_eq_self d,
    (eventually_mdifferentiableAt_coordMap d).eventually_nhds, d.left_inv.eventually_nhds,
    e.val.open_source.mem_nhds hxs, hWc.eventually d.differentiableAt.eventually_nhds,
    DerivativeIdeal.HolomorphicAt.eventually_holomorphicAt d.holomorphicAt,
    (eventually_mdifferentiableAt_W d).eventually_nhds]
    with y hJy hfix hmd hΨW hys hΨd hhh hWdy hyJ
  have hy0 : d.h y = 0 := hyJ _ hJy
  refine ⟨hfix hy0, hmd, fun g hg => ?_⟩
  set F : ComplexModel n → ℂ := fun w => g (e.val.symm (d.Ψ w)) with hFdef
  have hΨy : d.Ψ (d.W y) = e.val y := hΨW.self_of_nhds
  have hFd : ∀ᶠ w in 𝓝 (d.W y), DifferentiableAt ℂ F w := by
    have hge := eventually_differentiableAt_comp_symm e hys hg
    have hΨc : Tendsto d.Ψ (𝓝 (d.W y)) (𝓝 (e.val y)) := by
      rw [← hΨy]; exact hΨd.self_of_nhds.continuousAt
    filter_upwards [hΨd, hΨc.eventually hge] with w h1 h2
    exact h2.comp w h1
  obtain ⟨T, hT, hTeq⟩ := exists_taylor_tail hFd (EuclideanSpace.single d.i (1 : ℂ)) 1
  have hγ : Tendsto (fun p => (d.W p, d.h p)) (𝓝 y) (𝓝 (d.W y, (0 : ℂ))) := by
    rw [← hy0]
    exact hWdy.self_of_nhds.continuousAt.prodMk_nhds hhh.self_of_nhds.continuousAt
  have hTγ : HolomorphicAt n (fun p => T (d.W p, d.h p)) y := by
    filter_upwards [hWdy, hhh, hγ.eventually hT] with p h1 h2 h3
    exact h3.mdifferentiableAt.comp p (h1.prodMk_space h2)
  have heq : (fun p => T (d.W p, d.h p) * d.h p) =ᶠ[𝓝 y] fun p => g (d.coordMap p) - g p := by
    filter_upwards [hγ.eventually hTeq, hΨW, e.val.open_source.mem_nhds hys] with p hp1 hp2 hp3
    simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
      one_mul, List.replicate_zero, iterDeriv_nil, pow_zero, mul_one, pow_one] at hp1
    have hgp : g p = F (d.W p) := by
      simp only [hFdef, hp2]
      exact congrArg g ((complexChartAt (n := n) x).val.left_inv hp3).symm
    have hgφ : g (d.coordMap p) = F (d.W p + d.h p • EuclideanSpace.single d.i 1) := rfl
    rw [hgφ, hgp, hp1]
    ring
  exact HomogenizedIdeal.mem_congr hJ (mul_mem hJ hTγ hJy) heq

end Base

/-! ### Maps between open sets, extended by the identity -/

section Extend

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

open scoped Classical in
/-- A map between open subsets of `Y`, extended by the identity to a map `Y → Y`. -/
def extendMap {A B : Opens Y} (Φ : A → B) : Y → Y := fun y => if h : y ∈ A then (Φ ⟨y, h⟩ : Y) else y

theorem extendMap_of_mem {A B : Opens Y} (Φ : A → B) {y : Y} (h : y ∈ A) : extendMap Φ y = Φ ⟨y, h⟩ := by
  classical
  simp only [extendMap, dif_pos h]

theorem extendMap_val {A B : Opens Y} (Φ : A → B) (y : A) : extendMap Φ y = Φ y :=
  extendMap_of_mem Φ y.2

theorem contMDiffAt_extendMap {A B : Opens Y} {Φ : A → B}
    (hΦ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Φ) (y : A) :
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (extendMap Φ) y := by
  have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun p : A => extendMap Φ p) y := by
    have : (fun p : A => extendMap Φ p) = Subtype.val ∘ Φ := funext fun p => extendMap_val Φ p
    rw [this]
    exact (contMDiff_subtype_val.comp hΦ) y
  exact contMDiffAt_subtype_iff.mp h1

theorem eventually_mdifferentiableAt_extendMap {A B : Opens Y} {Φ : A → B}
    (hΦ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Φ) (y : A) :
    ∀ᶠ p in 𝓝 (y : Y), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (extendMap Φ) p := by
  filter_upwards [A.isOpen.mem_nhds y.2] with p hp
  exact (contMDiffAt_extendMap hΦ ⟨p, hp⟩).mdifferentiableAt (by simp)

/-- Trivial action depends only on the germ of the map. -/
theorem trivialAt_congr {f g : Y → Y} {J : GermIdeal n Y} (hJ : J.IsCoherent) {y : Y} (h : TrivialAt f J y)
    (hfg : f =ᶠ[𝓝 y] g) : TrivialAt g J y := by
  refine ⟨hfg.self_of_nhds.symm.trans h.apply_eq, ?_, fun g' hg' => ?_⟩
  · filter_upwards [h.mdifferentiableAt, hfg.eventually_nhds] with p hp hfgp
    exact hp.congr_of_eventuallyEq (show f =ᶠ[𝓝 p] g from hfgp).symm
  · refine HomogenizedIdeal.mem_congr hJ (h.sub_mem g' hg') ?_
    filter_upwards [hfg] with p hp
    rw [hp]

end Extend

/-! ### One step of the lift: transforms and strict transforms correspond -/

section Step

open BlowupBiholomorphismLift MarkedIdealRestrictOpen MarkedIdealBiholomorphism BlowupStrictSubmanifold BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal BlowupRestrictOpen

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π) {A B : Opens Y}
  (Φ : CMfd.of (n := n) A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) B)
  (hcorr : Φ ⁻¹' ((↑) ⁻¹' C : Set B) = ((↑) ⁻¹' C : Set A))
  (Φ₁ : CMfd.of (n := n) (preOpen hπ A) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
    CMfd.of (n := n) (preOpen hπ B))
  (hΦ₁ : ∀ p : preOpen hπ A, π (Φ₁ p : Z) = (Φ (restrictMap hπ A p) : Y))
include hcorr hΦ₁

theorem restrictMap_comp_lift : restrictMap hπ B ∘ Φ₁ = Φ ∘ restrictMap hπ A :=
  funext fun p => Subtype.ext (hΦ₁ p)

/-- **Strict transforms correspond under the lift.** -/
theorem preimage_lift_geoStrictTransform {Su Sv : Set Y} (hS : Φ ⁻¹' ((↑) ⁻¹' Su : Set B) = ((↑) ⁻¹' Sv : Set A)) :
    Φ₁ ⁻¹' ((↑) ⁻¹' geoStrictTransform π C Su : Set (preOpen hπ B)) =
      ((↑) ⁻¹' geoStrictTransform π C Sv : Set (preOpen hπ A)) := by
  have hBr : ((↑) ⁻¹' geoStrictTransform π C Su : Set (preOpen hπ B)) =
      geoStrictTransform (restrictMap hπ B) ((↑) ⁻¹' C : Set B) ((↑) ⁻¹' Su : Set B) :=
    (geoStrictTransform_restrict B (preOpen hπ B).isOpen Su).symm
  have hAr : ((↑) ⁻¹' geoStrictTransform π C Sv : Set (preOpen hπ A)) =
      geoStrictTransform (restrictMap hπ A) ((↑) ⁻¹' C : Set A) ((↑) ⁻¹' Sv : Set A) :=
    (geoStrictTransform_restrict A (preOpen hπ A).isOpen Sv).symm
  rw [hBr, hAr, ← geoStrictTransform_comp_diffeo Φ₁, restrictMap_comp_lift hπ Φ hcorr Φ₁ hΦ₁]
  unfold geoStrictTransform
  rw [preimage_comp, preimage_sdiff, hS, hcorr]

/-- **Transforms correspond under the lift**: if `Φ^*(𝔪|_B) = 𝔪|_A`, then `Φ₁^*((𝔪')|_{π⁻¹B}) = (𝔪')|_{π⁻¹A}` for the
transform `𝔪'` of `𝔪` along `π` (coherent ideals, `C` a closed submanifold). -/
theorem pullback_lift_geoTransform {m : MarkedIdeal n Y} (hm : m.ideal.IsCoherent)
    (hc : (m.geoTransform C π).ideal.IsCoherent)
    (hpb : MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : B → Y) m) =
      MarkedIdeal.pullback (Subtype.val : A → Y) m) :
    MarkedIdeal.pullback Φ₁ (MarkedIdeal.pullback (Subtype.val : preOpen hπ B → Z) (m.geoTransform C π)) =
      MarkedIdeal.pullback (Subtype.val : preOpen hπ A → Z) (m.geoTransform C π) := by
  have hmB : (MarkedIdeal.pullback (Subtype.val : B → Y) m).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hm
  have hICB : (vanishingIdeal (n := n) ((↑) ⁻¹' C : Set B)).IsCoherent :=
    VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_preimage_val hπ.1 B)
  have hBr : MarkedIdeal.pullback (Subtype.val : preOpen hπ B → Z) (m.geoTransform C π) =
      (MarkedIdeal.pullback (Subtype.val : B → Y) m).geoTransform ((↑) ⁻¹' C : Set B) (restrictMap hπ B) :=
    (geoTransform_pullback_val hm hπ hc B (preOpen hπ B).isOpen).symm
  have hAr : MarkedIdeal.pullback (Subtype.val : preOpen hπ A → Z) (m.geoTransform C π) =
      (MarkedIdeal.pullback (Subtype.val : A → Y) m).geoTransform ((↑) ⁻¹' C : Set A) (restrictMap hπ A) :=
    (geoTransform_pullback_val hm hπ hc A (preOpen hπ A).isOpen).symm
  have hcB : ((MarkedIdeal.pullback (Subtype.val : B → Y) m).geoTransform ((↑) ⁻¹' C : Set B)
      (restrictMap hπ B)).ideal.IsCoherent := by
    rw [← hBr]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hc
  have hnat := MarkedIdeal.geoTransform_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
    Φ.symm_apply_apply (MarkedIdeal.pullback (Subtype.val : B → Y) m) hmB ((↑) ⁻¹' C : Set B)
    (Φ.contMDiff.comp (isBlowupAlong_restrictMap hπ A).contMDiff)
  have hsimp : (Φ.symm ∘ Φ ∘ restrictMap hπ A) = restrictMap hπ A := funext fun p => by simp
  rw [hBr, hAr, ← geoTransform_comp_diffeo Φ₁ _ hmB _ hICB (isBlowupAlong_restrictMap hπ B).contMDiff hcB,
    restrictMap_comp_lift hπ Φ hcorr Φ₁ hΦ₁, ← hnat, hpb, hcorr, hsimp]

end Step

end

end Hironaka.HomogenizedGlueingLift
