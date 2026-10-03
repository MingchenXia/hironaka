/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.LocalGiraudTransformAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.MarkedIdeal.DerivativeIdealAlongTransform
import Hironaka.MarkedIdeal.MaximalContactTower
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Hypersurfaces of maximal contact inside a submanifold along multiple test blow-ups

Source: Włodarczyk 2005, §2.7, Lemma `le:Giraud` (from Lemma `le:Gi`), here along a closed submanifold `N` as in
Bierstone--Milman 2008, §3: if `u` is a tangent direction of `(𝔞|_N, μ)` on `U`, then along every multiple test
blow-up of `(M, N, E, 𝔞, μ)` the cosupports of the transforms lie in the strict transforms of `N ∩ V(u) ∩ U`.

Built on `hir:along-transform` (`DerivativeIdealAlongTransform.restrictLe_geoTransform_derivMarkedAlong`: the
transform of `𝓓_N^{μ-1}(𝔪)` lies, on `N'`, in `𝓓_{N'}^{μ-1}(𝔪')`), along-`N'` local Giraud lemma
(`LocalGiraudTransformAlong`) and tower inclusions along `N` (`HomogenizedIdealAlongTower.inclusions_tower_along`).

* `apply_eq_zero_of_isInSpanOnAt`: a combination on `W` of germs vanishing at `x ∈ W` vanishes at `x`.
* `strictAlong_subset_N`: strict transforms of subsets of `N` along `T` lie in `N_T`.
* `exists_contact_along` (**tangent directions along `N` persist, restricted to `N_T`**): for every multiple test blow-up `T`
  and every `z ∈ N_T` over `U` there are an open `O ∋ z` over `U` and `w` holomorphic on `O` which, at the points of
  `N_T ∩ O`, agrees on `N_T` with germs of `𝓓_{N_T}^{μ-1}(𝔞_T)`, has multiplicity one along `N_T` at its zeros, and
  whose zero set in `N_T ∩ O` is the strict transform of `N ∩ V(u) ∩ U` along `T`.
* `cosupp_subset_strictAlong_along` (**Włodarczyk `le:Giraud` along `N`**): `cosupp(𝔪_T) ∩ T⁻¹(U) ⊆ (N ∩ V(u) ∩ U)_T`;
  `centre_subset_strictAlong_along`: the next centre over `U` lies in that strict transform.

The tangent direction of the transform is only controlled on `N_T` (agreement on `N_T` with germs of the derivative ideal
along `N_T`, multiplicity one at its zeros on `N_T`), which is all that the next step and the cosupport need.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MaximalContactAlongTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers Hironaka.DerivativeIdealAlong Hironaka.TangentDirectionAlong Hironaka.HomogenizedIdealAlong Hironaka.RestrictedIdealWeight Hironaka.BlowupFunctionTransform Hironaka.BlowupStrictSubmanifold Hironaka.BlowupExceptionalDivisor Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.HomogenizedGlueingTower Hironaka.RestrictedIdealExtension Hironaka.RestrictedIdealQuotient Hironaka.InvertibleIdealQuotient Hironaka.GiraudAlong

noncomputable section

variable {n : ℕ}

section Span

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- A combination on `W` of germs vanishing at `x ∈ W` vanishes at `x`. -/
theorem apply_eq_zero_of_isInSpanOnAt {W : Set M} {S : (M → ℂ) → Prop} {x : M} (hxW : x ∈ W)
    (hS : ∀ s, S s → s x = 0) {g : M → ℂ} (hg : IsInSpanOnAt (n := n) W S x g) : g x = 0 := by
  obtain ⟨K, s, a, hs, -, hsum⟩ := hg
  rw [hsum.self_of_nhds hxW]
  exact Finset.sum_eq_zero fun i _ => by rw [hS _ (hs i), mul_zero]

end Span

section Tower

variable {X : CMfd.{u} n}

/-- **Strict transforms of subsets of `N` stay in `N_T`.** -/
theorem strictAlong_subset_N (𝔪 : MarkedIdeal n X) {A : Set X} (hA : A ⊆ 𝔪.N) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → strictAlong T A ⊆ (geoTransformAlong 𝔪 T).N
  | _, .refl => hA
  | _, .step T C π hπ => by
      rw [strictAlong_step, N_geoTransformAlong_step]
      exact closure_mono (preimage_mono (sdiff_subset_sdiff_left (strictAlong_subset_N 𝔪 hA T)))

variable (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
  (hμ : 1 ≤ 𝔪.d) {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d U u)
include hN h𝔞 hμ hu

/-- **Tangent directions along `N` persist along multiple test blow-ups, on `N_T`** (Włodarczyk `le:Gi` along `N`,
iterated): every point `z ∈ N_T` over `U` has an open neighbourhood `O` over `U` with a function `w`, holomorphic on `O`,
which at the points of `N_T ∩ O` agrees on `N_T` with germs of `𝓓_{N_T}^{μ-1}(𝔞_T)`, has multiplicity one along `N_T`
at its zeros there, and whose zero set in `N_T ∩ O` is the strict transform of `N ∩ V(u) ∩ U` along `T`. -/
theorem exists_contact_along :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      ∀ z : Y, z ∈ (geoTransformAlong 𝔪 T).N → T.proj z ∈ U →
      ∃ (O : Set Y) (w : Y → ℂ), z ∈ O ∧ IsOpen O ∧ O ⊆ T.proj ⁻¹' U ∧
        (∀ x ∈ O, HolomorphicAt n w x) ∧
        (∀ x ∈ O, x ∈ (geoTransformAlong 𝔪 T).N → IsInSpanOnAt (n := n) (geoTransformAlong 𝔪 T).N
          ((iterDerivIdealAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (𝔪.d - 1)).mem x) x w) ∧
        (∀ x ∈ O, x ∈ (geoTransformAlong 𝔪 T).N → w x = 0 →
          ∃ (e : ComplexChart n Y) (ξ : Fin n → Y → ℂ),
            IsTangentField (geoTransformAlong 𝔪 T).N e ξ x ∧ fieldDeriv e ξ w x ≠ 0) ∧
        ∀ y ∈ O, y ∈ (geoTransformAlong 𝔪 T).N →
          (w y = 0 ↔ y ∈ strictAlong T (𝔪.N ∩ {x | u x = 0} ∩ U))
  | _, .refl, _, z, _, hz => by
      have hhol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
        RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
      refine ⟨U, u, hz, hu.isOpen, fun _ hy => hy,
        fun x hx => holomorphicAt_of_mem_iterDerivIdealAlong hhol _ x u (hu.mem x hx), fun x hx _ => ?_,
        fun x hx _ h0 => hu.multiplicity_one x hx h0,
        fun y hy hyN => ⟨fun h0 => ⟨⟨hyN, h0⟩, hy⟩, fun h => h.1.2⟩⟩
      exact ⟨1, fun _ => u, fun _ _ => 1, fun _ => hu.mem x hx, fun _ => holomorphicAt_const 1,
        Eventually.of_forall fun y _ => by simp⟩
  | _, .step T C π hπ, hT, z', hz'N, hz' => by
      obtain ⟨hT0, hC⟩ := hT
      obtain ⟨-, -, -, hNT, hcoh, -, -⟩ :=
        HomogenizedIdealAlongTower.inclusions_tower_along 𝔪 hN h𝔞 (Nat.zero_le _) T hT0
      have hd : (geoTransformAlong 𝔪 T).d = 𝔪.d := d_geoTransformAlong 𝔪 T
      have hπc : Continuous π := hπ.contMDiff.continuous
      have hz'NT : π z' ∈ (geoTransformAlong 𝔪 T).N := geoStrictTransform_subset_preimage hπc hNT.1 hz'N
      obtain ⟨O, w, hzO, hOo, hOU, hwhol, hwD, hw1, hwA⟩ := exists_contact_along T hT0 (π z') hz'NT hz'
      have hCN : C ⊆ (geoTransformAlong 𝔪 T).N := hC.subset_N
      have hhol : ∀ x g, (geoTransformAlong 𝔪 T).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
        RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg
      -- `w` vanishes on the centre
      have hCw : ∀ x ∈ C, x ∈ O → w x = 0 := by
        intro x hxC hxO
        have hxc : x ∈ cosupport n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal 𝔪.d := by
          have := hC.2.1 hxC
          rwa [MarkedIdeal.cosupp, hd] at this
        exact apply_eq_zero_of_isInSpanOnAt (hCN hxC)
          (fun s hs => TangentDirectionAlong.apply_eq_zero_of_mem_cosupport hhol hμ hxc hs) (hwD x hxO (hCN hxC))
      -- the controlled transform `w'` of `w`
      obtain ⟨Uh, h, hz'h, hh⟩ := exists_isLocalEquation hπ z'
      have hwI : (idealPow (vanishingIdeal (n := n) C) 1).mem (π z') w := by
        refine BlowupDerivativeIdeal.mem_idealPow_one_of_mem (fun _ _ hg => hg.1) ⟨hwhol _ hzO, ?_⟩
        filter_upwards [hOo.mem_nhds hzO] with y hy hyC
        exact hCw y hyC hy
      obtain ⟨w', hw'z, heq⟩ := exists_eq_pow_mul hh hz'h hwI
      have heq' : (w ∘ π) =ᶠ[𝓝 z'] fun y => h y * w' y := heq.mono fun y hy => by rw [hy]; simp
      have hev : ∀ᶠ y in 𝓝 z', (y ∈ Uh ∧ π y ∈ O) ∧ HolomorphicAt n w' y ∧
          ((w ∘ π) =ᶠ[𝓝 y] fun y => h y * w' y) ∧
          (y ∈ geoStrictTransform π C (geoTransformAlong 𝔪 T).N →
            (y ∈ geoStrictTransform π C ((geoTransformAlong 𝔪 T).N ∩ {x | w x = 0} ∩ O) ↔ w' y = 0)) :=
        ((hh.isOpen.eventually_mem hz'h).and ((hOo.preimage hπc).eventually_mem hzO)).and
          ((DerivativeIdeal.HolomorphicAt.eventually_holomorphicAt hw'z).and (heq'.eventually_nhds.and
            (LocalGiraudTransformAlong.eventually_mem_geoStrictTransform_inter_zeroSet_iff hπ hNT hCN hh hOo
              hwhol hw1 hCw hz'h hzO hw'z heq')))
      obtain ⟨O', hO'sub, hO'o, hz'O'⟩ := mem_nhds_iff.mp hev
      refine ⟨O', w', hz'O', hO'o, fun y hy => hOU (hO'sub hy).1.2, fun y hy => (hO'sub hy).2.1, ?_, ?_, ?_⟩
      · -- `w'` lies, on `N'`, in the derivative ideal along `N'` of the transform (`hir:along-transform`)
        intro x hx hxN
        obtain ⟨⟨hxh, hxO⟩, hw'x, heqx, -⟩ := hO'sub hx
        have hπxN : π x ∈ (geoTransformAlong 𝔪 T).N := geoStrictTransform_subset_preimage hπc hNT.1 hxN
        obtain ⟨K, s, a, hs, ha, hsum⟩ := hwD (π x) hxO hπxN
        have hmem : ((derivMarkedAlong (geoTransformAlong 𝔪 T) (𝔪.d - 1)).geoTransform C π).ideal.mem x w' := by
          show HolomorphicAt n w' x ∧ ∀ p, (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C))
              ((geoTransformAlong 𝔪 T).d - (𝔪.d - 1))).mem x p →
            (restrictOn n (geoStrictTransform π C (geoTransformAlong 𝔪 T).N)
              (GermIdeal.pullback (m := n) π (iterDerivIdealAlong (geoTransformAlong 𝔪 T).N
                (geoTransformAlong 𝔪 T).ideal (𝔪.d - 1)))).mem x (fun y => p y * w' y)
          refine ⟨hw'x, fun p hp => ?_⟩
          rw [show (geoTransformAlong 𝔪 T).d - (𝔪.d - 1) = 1 by rw [hd]; omega] at hp
          have hp1 : (exceptionalDivisor hπ).ideal.mem x p := by
            rw [← BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ]
            exact hp
          obtain ⟨hph, c, hc, hpc⟩ := isInSpanAt_eq_iff.mp ((hh.generates x hxh p).mp hp1)
          have hπat : ∀ᶠ y' in 𝓝 x, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π y' :=
            Eventually.of_forall fun y' => hπ.contMDiff y'
          have hsh : ∀ i, HolomorphicAt n (s i) (π x) := fun i =>
            holomorphicAt_of_mem_iterDerivIdealAlong hhol _ (π x) (s i) (hs i)
          refine ⟨hph.mul hw'x, K, fun i => s i ∘ π, fun i y => c y * a i (π y),
            fun i => BlowupDerivativeIdeal.comp_mem_pullback (c := fun _ => 1) (hs i)
              ((hsh i).comp_contMDiff hπat) (holomorphicAt_const 1) (Eventually.of_forall fun p => by simp),
            fun i => hc.mul ((ha i).comp_contMDiff hπat), ?_⟩
          filter_upwards [hpc, heqx, hπc.continuousAt.eventually hsum] with y h1 h2 h3 hyN
          have h3' := h3 (geoStrictTransform_subset_preimage hπc hNT.1 hyN)
          have h2' : h y * w' y = w (π y) := h2.symm
          rw [h1, mul_assoc, h2', h3', Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Function.comp_apply]
          ring
        exact DerivativeIdealAlongTransform.restrictLe_geoTransform_derivMarkedAlong (geoTransformAlong 𝔪 T) hNT
          hcoh hC hπ (by rw [hd]; omega) x hxN w' hmem
      · -- Multiplicity one along `N'` at the zeros (along-`N'` local Giraud, (ii))
        intro x hx hxN h0
        obtain ⟨⟨hxh, hxO⟩, hw'x, heqx, hiff⟩ := hO'sub hx
        exact LocalGiraudTransformAlong.exists_fieldDeriv_ne_zero_controlledTransform_along hπ hNT hCN hh hOo
          hwhol hw1 hCw hxh hxO hw'x heqx ((hiff hxN).mpr h0)
      · -- The zero set on `N'` ((i), and locality of strict transforms over `O`)
        intro y hy hyN
        obtain ⟨⟨-, hyO⟩, -, -, hiff⟩ := hO'sub hy
        rw [← hiff hyN, strictAlong_step]
        have hAB : ((geoTransformAlong 𝔪 T).N ∩ {x | w x = 0} ∩ O) ∩ O =
            strictAlong T (𝔪.N ∩ {x | u x = 0} ∩ U) ∩ O := by
          ext x
          constructor
          · rintro ⟨⟨⟨hxN, hx0⟩, hxO⟩, -⟩
            exact ⟨(hwA x hxO hxN).mp hx0, hxO⟩
          · rintro ⟨hxA, hxO⟩
            have hxN := strictAlong_subset_N 𝔪 (fun x hx => hx.1.1) T hxA
            exact ⟨⟨⟨hxN, (hwA x hxO hxN).mpr hxA⟩, hxO⟩, hxO⟩
        have hloc := MaximalContactTower.geoStrictTransform_inter_preimage (C := C) hπc hOo hAB
        constructor
        · intro hy'
          have : y ∈ geoStrictTransform π C ((geoTransformAlong 𝔪 T).N ∩ {x | w x = 0} ∩ O) ∩ π ⁻¹' O :=
            ⟨hy', hyO⟩
          rw [hloc] at this
          exact this.1
        · intro hy'
          have : y ∈ geoStrictTransform π C (strictAlong T (𝔪.N ∩ {x | u x = 0} ∩ U)) ∩ π ⁻¹' O := ⟨hy', hyO⟩
          rw [← hloc] at this
          exact this.1

/-- **Włodarczyk, Lemma `le:Giraud`, along a submanifold** (the tower half of `hir:along-calculus` (3)): let
`𝔪 = (M, N, E, 𝔞, μ)` with `N` a closed submanifold, `𝔞` coherent and `μ ≥ 1`, and `u` a tangent direction of
`(𝔞|_N, μ)` along `N` on `U`.  For every multiple test blow-up `T` of `𝔪`, the cosupport of the transform `𝔪_T` over `U`
lies in the strict transform of `N ∩ V(u) ∩ U` along `T`. -/
theorem cosupp_subset_strictAlong_along {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong 𝔪 T).cosupp ∩ T.proj ⁻¹' U ⊆ strictAlong T (𝔪.N ∩ {x | u x = 0} ∩ U) := by
  rintro z ⟨hzc, hzU⟩
  obtain ⟨-, -, -, -, hcoh, -, -⟩ :=
    HomogenizedIdealAlongTower.inclusions_tower_along 𝔪 hN h𝔞 (Nat.zero_le _) T hT
  have hzN : z ∈ (geoTransformAlong 𝔪 T).N := (geoTransformAlong 𝔪 T).cosupp_subset_N hzc
  obtain ⟨O, w, hzO, -, -, -, hwD, -, hwA⟩ := exists_contact_along 𝔪 hN h𝔞 hμ hu T hT z hzN hzU
  have hz : z ∈ cosupport n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal 𝔪.d := by
    have := hzc
    rwa [MarkedIdeal.cosupp, d_geoTransformAlong] at this
  have hhol : ∀ x g, (geoTransformAlong 𝔪 T).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg
  refine (hwA z hzO hzN).mp ?_
  exact apply_eq_zero_of_isInSpanOnAt hzN
    (fun s hs => TangentDirectionAlong.apply_eq_zero_of_mem_cosupport hhol hμ hz hs) (hwD z hzO hzN)

/-- **Admissible centres lie in the strict transform of `N ∩ V(u)` over `U`** (the hypersurface of maximal contact
inside `N` keeps containing the centres). -/
theorem centre_subset_strictAlong_along {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    {C : Set Y} (hC : (geoTransformAlong 𝔪 T).IsAdmissibleCentre C) :
    C ∩ T.proj ⁻¹' U ⊆ strictAlong T (𝔪.N ∩ {x | u x = 0} ∩ U) := fun _ hz =>
  cosupp_subset_strictAlong_along 𝔪 hN h𝔞 hμ hu T hT ⟨hC.2.1 hz.1, hz.2⟩

end Tower

end

end Hironaka.MaximalContactAlongTower
