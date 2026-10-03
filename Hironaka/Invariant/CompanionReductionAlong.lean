/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.CompanionReduction
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.DerivativeIdealAlongTransform
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.TransformOffCentre
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Analytic.GermOrderProduct
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.OrderMultiplicativity
import Hironaka.Invariant.OrderTaylor
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Reduction to maximal order inside a submanifold: the companion ideal along `N`

For `N = M` this is `CompanionReduction`.

Let `N` be a closed submanifold, `𝔟, 𝔠` coherent, `E` a common sequence of members, `o ≥ 1`, and suppose
`ord_x(𝔟|_N) ≤ o` at every point of `cosupp((𝔟𝔠)|_N, d)`.  The **companion ideal along `N`** is
`(N, E, 𝔟, o) + (N, E, 𝔠, d - o)` if `o < d` and `(N, E, 𝔟, o)` if `o ≥ d` (`companionAlong`).  In the application
`𝔟 = 𝓝_N(𝔞)`, `𝔠 = 𝓜_N(𝔞)` (`MonomialPartAlong`), and `(N, E, 𝔞, d)` is restricted-equivalent to `(N, E, 𝔟𝔠, d)`.

## Main results

* orders along `N` through a local retraction (`DivisorExponentAlong.IsLocalRetraction`):
  `mem_cosupport_of_mem_cosupport_mul_along` (if `x ∈ cosupp((𝔟𝔠)|_N, d)` and `ord_x(𝔟|_N) ≤ o ≤ d`, then
  `x ∈ cosupp(𝔠|_N, d - o)`);
* one blowup (any closed `N`, coherent ideal, admissible centre): `mem_cosupp_of_mem_cosupp_geoTransform_along` (the
  cosupport of the transform lies over the cosupport), `notMem_cosupport_succ_geoTransform_along` (the bound
  `ord_{π z} ≤ d` passes to the transform; from `DerivativeIdealAlongTransform.restrictLe_geoTransform_derivMarkedAlong`
  and Giraud along `N`), `geoTransform_ideal_le` (monotonicity of the transform in the ideal and the mark);
* `cosupp_add_eq_inter_cosupp_mul_along` (under the bound, `cosupp((N, 𝔟, o) + (N, 𝔠, d')) = cosupp(𝔟, o) ∩ cosupp(𝔟𝔠, o + d')`),
  `cosupp_subset_of_le`; along towers `bound_along_along` (the bound persists along common multiple test blow-ups),
  `reduction_add_along` (case `o < d`, through `MarkedIdealOperationsAlong`: the transforms of sums and products are
  restricted-equivalent to the sums and products of the transforms) and `reduction_le_along` (case `o ≥ d`);
* `companionAlong` (+ `companionAlong_N`, `companionAlong_E`, `mul_eq_of_le_along`), `companion_reduction_along`:
  along every multiple test blow-up `T` of the companion ideal, `T` is one of `(N, E, 𝔟𝔠, d)` and of `(N, E, 𝔟, o)`,
  the bound `ord(𝔟_T|_{N_T}) ≤ o` persists on `cosupp((𝔟𝔠)_T, d)`, and the companion's cosupport is `cosupp(𝔟_T, o)
  ∩ cosupp((𝔟𝔠)_T, d)`; after a resolution of the companion, `ord(𝔟_T|_{N_T}) < o` on `cosupp((𝔟𝔠)_T, d)`;
* `companion_isMaximalOrderAlong`: the companion ideal is of maximal order along `N`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CompanionReductionAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers Hironaka.DivisorExponentAlong Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealOperationsTransform Hironaka.MarkedIdealOperationsTransform.MarkedIdeal Hironaka.MarkedIdealOperationsAlong.MarkedIdeal Hironaka.RestrictedIdealExtension Hironaka.RestrictedIdealQuotient Hironaka.BlowupStrictSubmanifold Hironaka.OrderTaylor Hironaka.DerivativeIdealAlong

noncomputable section

/-! ### Orders along `N` of products -/

section Germs

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A point of `N` outside `cosupp(𝔞|_N, q)` carries a germ of `𝔞` of order `< q` along `N`. -/
theorem exists_not_vanishesToOrderOn_of_notMem {N : Set M} {𝔞 : GermIdeal n M} {x : M} {q : ℕ} (hxN : x ∈ N)
    (hx : x ∉ cosupport n N 𝔞 q) : ∃ g, 𝔞.mem x g ∧ ¬ VanishesToOrderOn n N x q g := by
  by_contra! hall
  exact hx ⟨hxN, hall⟩

/-- **The cosupport along `N` of a product along a factor of bounded order**: if `x ∈ cosupp((𝔟𝔠)|_N, d)`,
`ord_x(𝔟|_N) ≤ o` (i.e. `x ∉ cosupp(𝔟|_N, o + 1)`) and `o ≤ d`, then `x ∈ cosupp(𝔠|_N, d - o)`; at a regular point of `N`,
through a local retraction, from `GermOrderProduct.mem_idealPow_of_mul_mem`. -/
theorem mem_cosupport_of_mem_cosupport_mul_along {N : Set M} (hN : ∀ x ∈ N, ∃ k, RegularAtDim (n := n) N x k)
    {𝔟 𝔠 : GermIdeal n M} (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x)
    (h𝔠 : ∀ x g, 𝔠.mem x g → HolomorphicAt n g x) {x : M} {o d : ℕ} (hod : o ≤ d)
    (hx : x ∈ cosupport n N (𝔟.mul 𝔠) d) (hxo : x ∉ cosupport n N 𝔟 (o + 1)) :
    x ∈ cosupport n N 𝔠 (d - o) := by
  obtain ⟨k, hk⟩ := hN x hx.1
  obtain ⟨r, hr⟩ := exists_isLocalRetraction hk
  obtain ⟨g, hg, hgo⟩ := exists_not_vanishesToOrderOn_of_notMem hx.1 hxo
  have hgo' : ¬ (idealPow (pointIdeal n x) (o + 1)).mem x (g ∘ r) := fun h =>
    hgo (hr.vanishesToOrderOn_iff.mpr h)
  refine ⟨hx.1, fun f hf => hr.vanishesToOrderOn_iff.mpr ?_⟩
  have hgf : (𝔟.mul 𝔠).mem x (fun p => g p * f p) :=
    IdealOrderArithmetic.mul_mem_mul hg hf ((h𝔟 x g hg).mul (h𝔠 x f hf))
  have hmem := hr.vanishesToOrderOn_iff.mp (hx.2 _ hgf)
  have hmem' : (idealPow (pointIdeal n x) ((d - o) + o)).mem x (fun p => (f ∘ r) p * (g ∘ r) p) := by
    rw [Nat.sub_add_cancel hod]
    exact mem_idealPow_congr hmem (Eventually.of_forall fun p => mul_comm (g (r p)) (f (r p)))
  exact GermOrderProduct.mem_idealPow_of_mul_mem (hr.holomorphicAt_comp (h𝔠 x f hf))
    (hr.holomorphicAt_comp (h𝔟 x g hg)) hgo' hmem'

end Germs

/-! ### One admissible blowup, along `N` -/

section OneBlowup

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **The cosupport of the transform lies over the cosupport** (closed `N`, holomorphic germs, admissible centre):
over the centre since `C ⊆ cosupp`, off it by `TransformOffCentre.mem_cosupp_geoTransform_iff`. -/
theorem mem_cosupp_of_mem_cosupp_geoTransform_along {𝔪 : MarkedIdeal n X} (hN : IsClosed 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hC : 𝔪.IsAdmissibleCentre C)
    (hπ : IsBlowupAlong n C π) {z : Y} (hz : z ∈ (𝔪.geoTransform C π).cosupp) : π z ∈ 𝔪.cosupp := by
  by_cases hzC : π z ∈ C
  · exact hC.2.1 hzC
  · exact (TransformOffCentre.mem_cosupp_geoTransform_iff 𝔪 hN h𝔞 hπ hzC).mp hz

/-- **The order bound along `N` passes to the transform** (`N` a closed submanifold, coherent ideal, admissible
centre): `ord_{π z}(𝔞|_N) ≤ d` gives `ord_z(𝔞'|_{N'}) ≤ d` (Villamayor; Włodarczyk `le:inclusions` with `r = d`, along `N`:
a germ `u ∈ 𝓓_N^d(𝔞)` with `u(π z) ≠ 0` gives `u ∘ π` in the transform of `(X, N, E, 𝓓_N^d 𝔞, 0)`, hence in
`𝓓_{N'}^d(𝔞')` on `N'` (`DerivativeIdealAlongTransform.restrictLe_geoTransform_derivMarkedAlong`); Giraud along `N` on
both sides). -/
theorem notMem_cosupport_succ_geoTransform_along (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hC : 𝔪.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) {z : Y}
    (hz : π z ∉ cosupport n 𝔪.N 𝔪.ideal (𝔪.d + 1)) :
    z ∉ cosupport n (𝔪.geoTransform C π).N (𝔪.geoTransform C π).ideal (𝔪.d + 1) := by
  have h𝔞hol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hN' := isClosedSubmanifold_geoTransform_N hN hC hπ
  have h𝔞'hol : ∀ x g, (𝔪.geoTransform C π).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
  intro hz'
  have hzN : z ∈ (𝔪.geoTransform C π).N := hz'.1
  rw [GiraudAlong.cosupport_succ_eq_inter_zeroLocus_iterDerivIdealAlong h𝔞'hol hN'.2] at hz'
  have hπs := hπ.contMDiff
  have hxN : π z ∈ 𝔪.N := geoStrictTransform_subset_preimage hπs.continuous hN.1 hzN
  rw [GiraudAlong.cosupport_succ_eq_inter_zeroLocus_iterDerivIdealAlong h𝔞hol hN.2] at hz
  have hx : π z ∉ (iterDerivIdealAlong 𝔪.N 𝔪.ideal 𝔪.d).zeroLocus := fun hx => hz ⟨hxN, hx⟩
  simp only [GermIdeal.zeroLocus, Set.mem_ofPred_eq, not_forall] at hx
  obtain ⟨u, hu, hux⟩ := hx
  have huhol : HolomorphicAt n u (π z) := GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔞hol 𝔪.d _ _ hu
  have huπ : HolomorphicAt n (fun p => u (π p)) z :=
    huhol.comp_contMDiff (Eventually.of_forall fun p => hπs p)
  have hmem : ((HomogenizedIdealAlong.derivMarkedAlong 𝔪 𝔪.d).geoTransform C π).ideal.mem z
      (fun p => u (π p)) := by
    refine ⟨huπ, fun h hh => ⟨(holomorphicAt_of_mem_idealPow hh).mul huπ, ?_⟩⟩
    exact RelativePrincipalizationSpan.IsInSpanAt.restrict (isInSpanAt_of_eq_mul
      (BlowupDerivativeIdeal.comp_mem_pullback (𝔟 := iterDerivIdealAlong 𝔪.N 𝔪.ideal 𝔪.d)
        hu huπ (holomorphicAt_const 1) (Eventually.of_forall fun p => by simp))
      ((holomorphicAt_of_mem_idealPow hh).mul huπ) (holomorphicAt_of_mem_idealPow hh)
      (Eventually.of_forall fun p => rfl))
  obtain ⟨K, s, a, hs, -, hsum⟩ :=
    DerivativeIdealAlongTransform.restrictLe_geoTransform_derivMarkedAlong 𝔪 hN h𝔞 hC hπ le_rfl z hzN _ hmem
  have h1 := hsum.self_of_nhds hzN
  simp only at h1
  rw [Finset.sum_eq_zero fun i _ => by rw [hz'.2 _ (hs i), mul_zero]] at h1
  exact hux h1

/-- **Monotonicity of the transform** (no hypothesis on the centre): for marked ideals on the same `N` with
`𝔞 ⊆ 𝔟` and marks `d ≤ o`, the transform of `(N, 𝔞, d)` is contained in that of `(N, 𝔟, o)` (the colon of the restricted
pullback by `(π^*𝓘_C)^d`, resp. `(π^*𝓘_C)^o ⊆ (π^*𝓘_C)^d`). -/
theorem geoTransform_ideal_le {𝔪 𝔫 : MarkedIdeal n X} (hN : 𝔪.N = 𝔫.N) (hle : 𝔪.ideal.Le 𝔫.ideal)
    (hdo : 𝔪.d ≤ 𝔫.d) (π : Y → X) (C : Set X) :
    (𝔪.geoTransform C π).ideal.Le (𝔫.geoTransform C π).ideal := by
  intro z f hf
  refine ⟨hf.1, fun g hg => ?_⟩
  have hLhol : ∀ y ℓ, (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem y ℓ →
      HolomorphicAt n ℓ y := fun _ _ hℓ => hℓ.1
  have hg' := idealPow_le_of_le hLhol hdo z g hg
  obtain ⟨hgf, hspan⟩ := hf.2 g hg'
  refine ⟨hgf, ?_⟩
  show IsInSpanOnAt (n := n) (geoStrictTransform π C 𝔫.N) ((GermIdeal.pullback (m := n) π 𝔫.ideal).mem z) z _
  rw [← hN]
  exact RelativePrincipalizationSpan.IsInSpanOnAt.mono
    (fun s hs => GermIdealPullbackCalculus.pullback_le_pullback hle z s hs) hspan

end OneBlowup

/-! ### Marked ideals on `N`: the cosupport of the companion sum and monotonicity -/

section Marked

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The cosupport of the companion sum along `N`** (a pair on a closed submanifold, marks `≥ 1`): if
`ord_x(𝔫|_N) ≤ 𝔫.d` at every point of the cosupport of the product, then `cosupp(𝔫 + 𝔪') = cosupp 𝔫 ∩ cosupp(𝔫 · 𝔪')`. -/
theorem cosupp_add_eq_inter_cosupp_mul_along {𝔫 𝔪' : MarkedIdeal n M} (h : IsSubmanifoldPair 𝔫 𝔪')
    (ho : 1 ≤ 𝔫.d) (hm : 1 ≤ 𝔪'.d)
    (hbound : ∀ x ∈ (mul 𝔫 𝔪').cosupp, x ∉ cosupport n 𝔫.N 𝔫.ideal (𝔫.d + 1)) :
    (add 𝔫 𝔪').cosupp = 𝔫.cosupp ∩ (mul 𝔫 𝔪').cosupp := by
  rw [cosupp_add_along h ho hm]
  ext x
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, inter_cosupp_subset_cosupp_mul h.N_eq ⟨h₁, h₂⟩⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    have hx : x ∈ cosupport n 𝔫.N (𝔫.ideal.mul 𝔪'.ideal) (𝔫.d + 𝔪'.d) := h₂
    have := mem_cosupport_of_mem_cosupport_mul_along h.isClosedSubmanifold.2 (hol_of_isCoherent h.coh₁)
      (hol_of_isCoherent h.coh₂) (Nat.le_add_right 𝔫.d 𝔪'.d) hx (hbound x h₂)
    rw [Nat.add_sub_cancel_left] at this
    show x ∈ cosupport n 𝔪'.N 𝔪'.ideal 𝔪'.d
    rw [← h.N_eq]
    exact this

/-- **Monotonicity of the cosupport** (same `N`): `𝔞 ⊆ 𝔟` and `d ≤ o` give `cosupp(𝔟, o) ⊆ cosupp(𝔞, d)`. -/
theorem cosupp_subset_of_le {𝔫 𝔪 : MarkedIdeal n M} (hN : 𝔫.N = 𝔪.N) (hle : 𝔪.ideal.Le 𝔫.ideal)
    (hdo : 𝔪.d ≤ 𝔫.d) : 𝔫.cosupp ⊆ 𝔪.cosupp := by
  intro x hx
  refine ⟨hN ▸ hx.1, fun g hg => ?_⟩
  have h1 := hx.2 g (hle x g hg)
  show VanishesToOrderOn n 𝔪.N x 𝔪.d g
  rw [← hN]
  exact h1.mono hdo

end Marked

/-! ### Along multiple test blow-ups -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The bound persists along multiple test blow-ups, along `N`** (closed submanifolds, coherent ideals): if
`ord_x(𝔫|_N) ≤ 𝔫.d` at every point of `cosupp 𝔪` and `T` is a multiple test blow-up of both `𝔫` and `𝔪`, then
`ord_z(𝔫_T|_{N_T}) ≤ 𝔫.d` at every point of `cosupp 𝔪_T` (and the stages keep closed submanifolds and coherent
ideals). -/
theorem bound_along_along (𝔫 𝔪 : MarkedIdeal n X) (hN𝔫 : IsClosedSubmanifold n 𝔫.N)
    (hN𝔪 : IsClosedSubmanifold n 𝔪.N) (h𝔫 : 𝔫.ideal.IsCoherent) (h𝔪 : 𝔪.ideal.IsCoherent)
    (hbound : ∀ x ∈ 𝔪.cosupp, x ∉ cosupport n 𝔫.N 𝔫.ideal (𝔫.d + 1)) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔫 T → IsGeoTestTower 𝔪 T →
      IsClosedSubmanifold n (geoTransformAlong 𝔫 T).N ∧ IsClosedSubmanifold n (geoTransformAlong 𝔪 T).N ∧
      (geoTransformAlong 𝔫 T).ideal.IsCoherent ∧ (geoTransformAlong 𝔪 T).ideal.IsCoherent ∧
      ∀ z ∈ (geoTransformAlong 𝔪 T).cosupp,
        z ∉ cosupport n (geoTransformAlong 𝔫 T).N (geoTransformAlong 𝔫 T).ideal (𝔫.d + 1)
  | _, .refl, _, _ => ⟨hN𝔫, hN𝔪, h𝔫, h𝔪, hbound⟩
  | _, .step T C π hπ, hT𝔫', hT𝔪' => by
      obtain ⟨hT𝔫, hC𝔫⟩ := (isGeoTestTower_step_iff 𝔫 T C π hπ).mp hT𝔫'
      obtain ⟨hT𝔪, hC𝔪⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT𝔪'
      obtain ⟨hN𝔫T, hN𝔪T, hcoh𝔫T, hcoh𝔪T, hbT⟩ :=
        bound_along_along 𝔫 𝔪 hN𝔫 hN𝔪 h𝔫 h𝔪 hbound T hT𝔫 hT𝔪
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [geoTransformAlong_step]; exact isClosedSubmanifold_geoTransform_N hN𝔫T hC𝔫 hπ
      · rw [geoTransformAlong_step]; exact isClosedSubmanifold_geoTransform_N hN𝔪T hC𝔪 hπ
      · rw [geoTransformAlong_step]
        exact HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN𝔫T hcoh𝔫T hC𝔫 hπ
      · rw [geoTransformAlong_step]
        exact HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN𝔪T hcoh𝔪T hC𝔪 hπ
      · intro z hz
        rw [geoTransformAlong_step] at hz
        have hπz := mem_cosupp_of_mem_cosupp_geoTransform_along hN𝔪T.1 (hol_of_isCoherent hcoh𝔪T) hC𝔪 hπ hz
        have hb := hbT (π z) hπz
        rw [← d_geoTransformAlong 𝔫 T] at hb ⊢
        rw [geoTransformAlong_step]
        exact notMem_cosupport_succ_geoTransform_along _ hN𝔫T hcoh𝔫T hC𝔫 hπ hb

/-- **Reduction to maximal order along `N`, case `o < d`** (Włodarczyk Step 2a; BM08 Step II.B): let `𝔫 = (N, E, 𝔟, o)`
and `𝔪' = (N, E, 𝔠, d')` be a pair on a closed submanifold with marks `≥ 1` such that `ord_x(𝔟|_N) ≤ o` on
`cosupp((𝔟𝔠)|_N, o + d')`.  Every multiple test blow-up `T` of `𝔫 + 𝔪'` is one of `𝔫`, of `𝔪'` and of `𝔫 · 𝔪'`; the bound
persists along `T`; and `cosupp (𝔫 + 𝔪')_T = cosupp 𝔫_T ∩ cosupp (𝔫 · 𝔪')_T`. -/
theorem reduction_add_along (𝔫 𝔪' : MarkedIdeal n X) (h : IsSubmanifoldPair 𝔫 𝔪') (ho : 1 ≤ 𝔫.d)
    (hm : 1 ≤ 𝔪'.d) (hbound : ∀ x ∈ (mul 𝔫 𝔪').cosupp, x ∉ cosupport n 𝔫.N 𝔫.ideal (𝔫.d + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (add 𝔫 𝔪') T) :
    IsGeoTestTower 𝔫 T ∧ IsGeoTestTower 𝔪' T ∧ IsGeoTestTower (mul 𝔫 𝔪') T ∧
      (∀ z ∈ (geoTransformAlong (mul 𝔫 𝔪') T).cosupp,
        z ∉ cosupport n (geoTransformAlong 𝔫 T).N (geoTransformAlong 𝔫 T).ideal (𝔫.d + 1)) ∧
      (geoTransformAlong (add 𝔫 𝔪') T).cosupp =
        (geoTransformAlong 𝔫 T).cosupp ∩ (geoTransformAlong (mul 𝔫 𝔪') T).cosupp := by
  obtain ⟨hiff, hEq⟩ := geoTransformAlong_add_along 𝔫 𝔪' h ho hm T
  obtain ⟨hT𝔫, hT𝔪'⟩ := hiff.mp hT
  obtain ⟨heqA, hpairT, -⟩ := hEq hT𝔫 hT𝔪'
  obtain ⟨hTmul, heqM, -, -⟩ := geoTransformAlong_mul_along 𝔫 𝔪' h T hT𝔫 hT𝔪'
  have hNmul : IsClosedSubmanifold n (mul 𝔫 𝔪').N := h.isClosedSubmanifold
  have hcohmul : (mul 𝔫 𝔪').ideal.IsCoherent := isCoherent_mul h.coh₁ h.coh₂
  obtain ⟨-, -, -, -, hboundT⟩ :=
    bound_along_along 𝔫 (mul 𝔫 𝔪') h.isClosedSubmanifold hNmul h.coh₁ hcohmul hbound T hT𝔫 hTmul
  refine ⟨hT𝔫, hT𝔪', hTmul, hboundT, ?_⟩
  have hd₁ : 1 ≤ (geoTransformAlong 𝔫 T).d := by rw [d_geoTransformAlong]; exact ho
  have hd₂ : 1 ≤ (geoTransformAlong 𝔪' T).d := by rw [d_geoTransformAlong]; exact hm
  rw [heqA.cosupp_eq, heqM.cosupp_eq]
  refine cosupp_add_eq_inter_cosupp_mul_along hpairT hd₁ hd₂ ?_
  intro x hx
  rw [← heqM.cosupp_eq] at hx
  rw [d_geoTransformAlong]
  exact hboundT x hx

/-- **Reduction to maximal order along `N`, case `o ≥ d`** (no hypothesis on the ideals): if `𝔫` and `𝔪` have the same
`N` and `E`, `𝔞 ⊆ 𝔟` and `d ≤ o`, every multiple test blow-up of `𝔫 = (N, E, 𝔟, o)` is one of `𝔪 = (N, E, 𝔞, d)`, along
it `N_T` and `E_T` agree, `𝔞_T ⊆ 𝔟_T`, and `cosupp 𝔫_T ⊆ cosupp 𝔪_T`. -/
theorem reduction_le_along (𝔫 𝔪 : MarkedIdeal n X) (hN : 𝔫.N = 𝔪.N) (hE : 𝔫.E = 𝔪.E)
    (hle : 𝔪.ideal.Le 𝔫.ideal) (hdo : 𝔪.d ≤ 𝔫.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔫 T →
      IsGeoTestTower 𝔪 T ∧ (geoTransformAlong 𝔫 T).N = (geoTransformAlong 𝔪 T).N ∧
      (geoTransformAlong 𝔫 T).E = (geoTransformAlong 𝔪 T).E ∧
      (geoTransformAlong 𝔪 T).ideal.Le (geoTransformAlong 𝔫 T).ideal ∧
      (geoTransformAlong 𝔫 T).cosupp ⊆ (geoTransformAlong 𝔪 T).cosupp
  | _, .refl, _ => ⟨trivial, hN, hE, hle, cosupp_subset_of_le hN hle hdo⟩
  | _, .step T C π hπ, hT => by
      obtain ⟨hT𝔫, hC⟩ := (isGeoTestTower_step_iff 𝔫 T C π hπ).mp hT
      obtain ⟨hT𝔪, hNT, hET, hleT, hsubT⟩ := reduction_le_along 𝔫 𝔪 hN hE hle hdo T hT𝔫
      have hC𝔪 : (geoTransformAlong 𝔪 T).IsAdmissibleCentre C :=
        ⟨hC.1, hC.2.1.trans hsubT, by rw [← hET]; exact hC.2.2⟩
      have hdT : (geoTransformAlong 𝔪 T).d ≤ (geoTransformAlong 𝔫 T).d := by
        simp only [d_geoTransformAlong]; exact hdo
      have hleT' := geoTransform_ideal_le hNT.symm hleT hdT π C
      have hNT' : ((geoTransformAlong 𝔫 T).geoTransform C π).N =
          ((geoTransformAlong 𝔪 T).geoTransform C π).N := by
        rw [geoTransform_N, geoTransform_N, hNT]
      refine ⟨(isGeoTestTower_step_iff 𝔪 T C π hπ).mpr ⟨hT𝔪, hC𝔪⟩, ?_, ?_, ?_, ?_⟩
      · rw [geoTransformAlong_step, geoTransformAlong_step]; exact hNT'
      · rw [geoTransformAlong_step, geoTransformAlong_step, geoTransform_E, geoTransform_E, hET]
      · rw [geoTransformAlong_step, geoTransformAlong_step]; exact hleT'
      · rw [geoTransformAlong_step, geoTransformAlong_step]
        exact cosupp_subset_of_le hNT' hleT' (by simp only [geoTransform_d]; exact hdT)

/-! ### The companion ideal along `N` -/

/-- **The companion ideal along `N`** of the factorization `𝔞|_N = (𝔟𝔠)|_N` (Włodarczyk Step 2a, BM08 Step II.B):
`(N, E, 𝔟, o) + (N, E, 𝔠, d - o)` if `o < d`, and `(N, E, 𝔟, o)` if `o ≥ d`.  In the application `𝔟 = 𝓝_N(𝔞)`,
`𝔠 = 𝓜_N(𝔞)` (`MonomialPartAlong`). -/
def companionAlong (N : Set X) (E : List (Set X)) (𝔟 𝔠 : GermIdeal n X) (o d : ℕ) : MarkedIdeal n X :=
  if o < d then add ⟨N, E, 𝔟, o⟩ ⟨N, E, 𝔠, d - o⟩ else ⟨N, E, 𝔟, o⟩

@[simp] theorem companionAlong_N (N : Set X) (E : List (Set X)) (𝔟 𝔠 : GermIdeal n X) (o d : ℕ) :
    (companionAlong N E 𝔟 𝔠 o d).N = N := by
  unfold companionAlong; split_ifs <;> rfl

@[simp] theorem companionAlong_E (N : Set X) (E : List (Set X)) (𝔟 𝔠 : GermIdeal n X) (o d : ℕ) :
    (companionAlong N E 𝔟 𝔠 o d).E = E := by
  unfold companionAlong; split_ifs <;> rfl

/-- `(N, E, 𝔟, o) · (N, E, 𝔠, d - o) = (N, E, 𝔟𝔠, d)` for `o ≤ d`. -/
theorem mul_eq_of_le_along (N : Set X) (E : List (Set X)) (𝔟 𝔠 : GermIdeal n X) {o d : ℕ} (hod : o ≤ d) :
    mul (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) ⟨N, E, 𝔠, d - o⟩ = ⟨N, E, 𝔟.mul 𝔠, d⟩ :=
  ext_of rfl rfl rfl (by show o + (d - o) = d; omega)

/-- **Reduction to maximal order along `N`** (`hir:companion-reduction-along`; Włodarczyk Step 2a, BM08 Step II.B): let
`N` be a closed submanifold, `𝔟, 𝔠` coherent, `o ≥ 1`, and `ord_x(𝔟|_N) ≤ o` at every point of `cosupp((𝔟𝔠)|_N, d)`
(common `E`).  Every multiple test blow-up `T` of the companion ideal is one of `(N, E, 𝔟𝔠, d)` and of `(N, E, 𝔟, o)`;
along it `ord(𝔟_T|_{N_T}) ≤ o` on `cosupp((𝔟𝔠)_T, d)`, and the cosupport of the companion's transform is
`cosupp(𝔟_T, o) ∩ cosupp((𝔟𝔠)_T, d)`. -/
theorem companion_reduction_along {N : Set X} (hN : IsClosedSubmanifold n N) (E : List (Set X))
    {𝔟 𝔠 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent) (h𝔠 : 𝔠.IsCoherent) {o d : ℕ} (ho : 1 ≤ o)
    (hbound : ∀ x ∈ cosupport n N (𝔟.mul 𝔠) d, x ∉ cosupport n N 𝔟 (o + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (companionAlong N E 𝔟 𝔠 o d) T) :
    IsGeoTestTower (⟨N, E, 𝔟.mul 𝔠, d⟩ : MarkedIdeal n X) T ∧
      IsGeoTestTower (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T ∧
      (∀ z ∈ (geoTransformAlong (⟨N, E, 𝔟.mul 𝔠, d⟩ : MarkedIdeal n X) T).cosupp,
        z ∉ cosupport n (geoTransformAlong (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T).N
          (geoTransformAlong (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T).ideal (o + 1)) ∧
      (geoTransformAlong (companionAlong N E 𝔟 𝔠 o d) T).cosupp =
        (geoTransformAlong (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T).cosupp ∩
          (geoTransformAlong (⟨N, E, 𝔟.mul 𝔠, d⟩ : MarkedIdeal n X) T).cosupp := by
  have hcoh : (𝔟.mul 𝔠).IsCoherent := isCoherent_mul h𝔟 h𝔠
  by_cases hod : o < d
  · have hc : companionAlong N E 𝔟 𝔠 o d = add ⟨N, E, 𝔟, o⟩ ⟨N, E, 𝔠, d - o⟩ := if_pos hod
    have hpair : IsSubmanifoldPair (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) ⟨N, E, 𝔠, d - o⟩ :=
      ⟨rfl, rfl, hN, h𝔟, h𝔠⟩
    have hmul := mul_eq_of_le_along N E 𝔟 𝔠 hod.le
    have hb : ∀ x ∈ (mul (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) ⟨N, E, 𝔠, d - o⟩).cosupp,
        x ∉ cosupport n (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X).N (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X).ideal
          ((⟨N, E, 𝔟, o⟩ : MarkedIdeal n X).d + 1) := by
      rw [hmul]; exact hbound
    rw [hc] at hT ⊢
    obtain ⟨h1, -, h3, h4, h5⟩ := reduction_add_along _ _ hpair ho (by show 1 ≤ d - o; omega) hb T hT
    rw [hmul] at h3 h4 h5
    exact ⟨h3, h1, h4, h5⟩
  · have hc : companionAlong N E 𝔟 𝔠 o d = ⟨N, E, 𝔟, o⟩ := if_neg hod
    rw [hc] at hT ⊢
    have hle : (𝔟.mul 𝔠).Le 𝔟 := GermIdealPullbackCalculus.mul_le_left h𝔟
      (fun hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hg)
    have hdo : d ≤ o := le_of_not_gt hod
    obtain ⟨hT𝔪, -, -, -, hsub⟩ :=
      reduction_le_along (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) ⟨N, E, 𝔟.mul 𝔠, d⟩ rfl rfl hle hdo T hT
    obtain ⟨-, -, -, -, hb⟩ :=
      bound_along_along (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) ⟨N, E, 𝔟.mul 𝔠, d⟩ hN hN h𝔟 hcoh hbound T hT hT𝔪
    exact ⟨hT𝔪, hT, hb, (inter_eq_left.mpr hsub).symm⟩

/-! ### The companion ideal along `N` is of maximal order along `N` -/

/-- **The companion ideal is of maximal order along `N`** (`hir:companion-maximal-order-along`; Włodarczyk, Definition of
the companion ideal; BM08 Step II.B): if `ord_x(𝔟|_N) ≤ o` at every point of `cosupp((𝔟𝔠)|_N, d)`, then
`(N, E, 𝔟, o) + (N, E, 𝔠, d - o)` (`o < d`), resp. `(N, E, 𝔟, o)` (`o ≥ d`), has order along `N` at most its mark at every
point.  Orders along `N` are computed through a local retraction (`DivisorExponentAlong.IsLocalRetraction`). -/
theorem companion_isMaximalOrderAlong {N : Set X} (hN : ∀ x ∈ N, ∃ k, RegularAtDim (n := n) N x k)
    (E : List (Set X)) {𝔟 𝔠 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent) (h𝔠 : 𝔠.IsCoherent) {o d : ℕ}
    (hbound : ∀ x ∈ cosupport n N (𝔟.mul 𝔠) d, x ∉ cosupport n N 𝔟 (o + 1)) :
    HomogenizedIdealAlong.IsMaximalOrderAlong N (companionAlong N E 𝔟 𝔠 o d).ideal
      (companionAlong N E 𝔟 𝔠 o d).d := by
  have hhol𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x := hol_of_isCoherent h𝔟
  have hhol𝔠 : ∀ x g, 𝔠.mem x g → HolomorphicAt n g x := hol_of_isCoherent h𝔠
  have hpt : ∀ (x : X) y g, (pointIdeal n x).mem y g → HolomorphicAt n g y := fun _ _ _ hg =>
    holomorphicAt_of_mem_pointIdeal hg
  intro x hx
  have hxN : x ∈ N := hx.1
  by_cases hod : o < d
  · have hc : companionAlong N E 𝔟 𝔠 o d = add ⟨N, E, 𝔟, o⟩ ⟨N, E, 𝔠, d - o⟩ := if_pos hod
    rw [hc] at hx
    change x ∈ cosupport n N (sumIdeal (idealPow 𝔟 (d - o)) (idealPow 𝔠 o)) (o * (d - o) + 1) at hx
    obtain ⟨k, hk⟩ := hN x hxN
    obtain ⟨r, hr⟩ := exists_isLocalRetraction hk
    by_cases hxb : x ∈ cosupport n N 𝔟 (o + 1)
    · -- then `x ∉ cosupp(𝔠|_N, d - o)`: otherwise `x ∈ cosupp((𝔟𝔠)|_N, d)`
      have hxc : x ∉ cosupport n N 𝔠 (d - o) := by
        intro hxc
        have h1 := IdealOrderArithmetic.inter_cosupport_subset_cosupport_mul (o + 1) (d - o) ⟨hxb, hxc⟩
        exact hbound x (cosupport_anti (by omega) h1) hxb
      obtain ⟨f, hf, hfno⟩ := exists_not_vanishesToOrderOn_of_notMem hxN hxc
      have hfr : ¬ (idealPow (pointIdeal n x) ((d - o - 1) + 1)).mem x (f ∘ r) := by
        rw [show d - o - 1 + 1 = d - o by omega]
        exact fun h => hfno (hr.vanishesToOrderOn_iff.mpr h)
      have hmem : (sumIdeal (idealPow 𝔟 (d - o)) (idealPow 𝔠 o)).mem x (fun p => f p ^ o) :=
        IdealOrderArithmetic.le_sumIdeal_right' (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) x _
          (OrderMultiplicativity.pow_mem_idealPow hf (hhol𝔠 x f hf) o)
      have hv := hr.vanishesToOrderOn_iff.mp (hx.2 _ hmem)
      refine CompanionReduction.pow_notMem_idealPow (hr.holomorphicAt_comp (hhol𝔠 x f hf)) hfr o ?_
      refine idealPow_le_of_le (hpt x) ?_ x _ hv
      exact Nat.add_le_add_right (Nat.mul_le_mul_left o (Nat.sub_le _ _)) 1
    · obtain ⟨g, hg, hgno⟩ := exists_not_vanishesToOrderOn_of_notMem hxN hxb
      have hgr : ¬ (idealPow (pointIdeal n x) (o + 1)).mem x (g ∘ r) :=
        fun h => hgno (hr.vanishesToOrderOn_iff.mpr h)
      have hmem : (sumIdeal (idealPow 𝔟 (d - o)) (idealPow 𝔠 o)).mem x (fun p => g p ^ (d - o)) :=
        IdealOrderArithmetic.le_sumIdeal_left' (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) x _
          (OrderMultiplicativity.pow_mem_idealPow hg (hhol𝔟 x g hg) (d - o))
      have hv := hr.vanishesToOrderOn_iff.mp (hx.2 _ hmem)
      have := CompanionReduction.pow_notMem_idealPow (hr.holomorphicAt_comp (hhol𝔟 x g hg)) hgr (d - o)
      rw [show (d - o) * o + 1 = o * (d - o) + 1 by ring] at this
      exact this hv
  · have hc : companionAlong N E 𝔟 𝔠 o d = ⟨N, E, 𝔟, o⟩ := if_neg hod
    rw [hc] at hx
    change x ∈ cosupport n N 𝔟 (o + 1) at hx
    have hle : (𝔟.mul 𝔠).Le 𝔟 := GermIdealPullbackCalculus.mul_le_left h𝔟 (fun hg => hhol𝔠 _ _ hg)
    refine hbound x ⟨hxN, fun g hg => (hx.2 g (hle x g hg)).mono (by omega)⟩ hx

end Tower

end

end Hironaka.CompanionReductionAlong
