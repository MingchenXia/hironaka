/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MonomialInvariantFunctorialAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
import Hironaka.MarkedIdeal.CoefficientRestrictionTower
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedIdeal
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The monomial and nonmonomial parts along a submanifold under local biholomorphisms

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2 of Proposition `pr:resol` and §2.4 (the resolution
procedure commutes with étale morphisms); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Step II.B
(the companion ideal is built from the monomial part `M(𝓘)` and the nonmonomial part `N(𝓘)` of the marked ideal,
both determined by the exponents of the members of `E` through the point).

The general step forms the companion ideal from `𝓜_N(𝔞)` (`MonomialPartAlong.monomialPartAlong`) and
`𝓝_N(𝔞) = (Res_N 𝔞 : 𝓜_N(𝔞))` (`MonomialPartAlong.nonmonomialPartAlong`), and compares nearby points through open
restrictions, biholomorphisms and steps with empty centre.  All three are *local biholomorphisms*: holomorphic maps
`φ : M' → M` with a holomorphic local inverse at every point (`DerivativeIdealAlongEtale.IsLocalInverseAt`; the
inclusion of an open set, `isLocalInverseAt_val`; a blowup along `∅`,
`ContactCanonicalAlong.exists_isLocalInverseAt_of_isBlowupAlong_empty`).

## Main results

* `comp_mem_idealPow_vanishingIdeal_preimage`, `comp_mem_idealPow_vanishingIdeal`: powers of vanishing ideals of
  members transfer along a local inverse;
* `cosupport_pullback_of_local`, `map_nhds_eq_of_local`: cosupports along `N` pull back, and `φ` maps neighbourhoods
  onto neighbourhoods;
* `monomialPartAlong_mem_iff'`, `monomialPartAlong_mem_of_isInSpanAt`: the monomial part by members, and closed under
  holomorphic combinations;
* **`pullback_monomialPartAlong`**: `φ^*𝓜_N(𝔞) = 𝓜_{φ⁻¹N}(φ^*𝔞)` with the members `φ⁻¹E_i`;
* `mem_pullback_iff_of_local`, `mem_restrictOn_pullback_iff_of_local`, **`pullback_colonAlong_of_local`**: the
  quotient along `W` commutes with pullback along a local biholomorphism (coherent ideals and quotient);
* **`pullback_nonmonomialPartAlong`**: `φ^*𝓝_N(𝔞) = 𝓝_{φ⁻¹N}(φ^*𝔞)`;
* **`monomialPartAlong_congr`, `nonmonomialPartAlong_congr`**: both parts only depend on `Res_N 𝔞` (`N` closed);
* **`monomialPartAlong_append_empty`, `nonmonomialPartAlong_append_empty`**: appending an empty member to `E` changes
  neither part.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MonomialPartEtale

open Hironaka.HolomorphicIdealSheaves
open Hironaka.GermIdealOrder Hironaka.DivisorExponentAlong Hironaka.MonomialPartAlong Hironaka.IdealWeightPowers Hironaka.RestrictedIdealExtension Hironaka.RestrictedIdealQuotient Hironaka.InvertibleIdealQuotient Hironaka.DerivativeIdealAlongEtale Hironaka.HadamardBridge Hironaka.RestrictedIdealWeight

noncomputable section

variable {n : ℕ}

/-! ### Transfers along a local inverse -/

section Local

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {φ : M' → M} {ψ : M → M'} {y : M'}

/-- **Powers of the vanishing ideal of a set pull back**: `s ∈ (𝓘_H^e)_{φ y}` gives `s ∘ φ ∈ (𝓘_{φ⁻¹H}^e)_y`. -/
theorem comp_mem_idealPow_vanishingIdeal_preimage (h : IsLocalInverseAt n φ ψ y) {H : Set M} :
    ∀ (e : ℕ) {s : M → ℂ}, (idealPow (vanishingIdeal (n := n) H) e).mem (φ y) s →
      (idealPow (vanishingIdeal (n := n) (φ ⁻¹' H)) e).mem y (s ∘ φ)
  | 0, _, hs => holomorphicAt_comp_map h.mdiff hs
  | e + 1, s, hs => by
      have hs' : IsInSpanAt (n := n) (fun s => ∃ a b, (idealPow (vanishingIdeal (n := n) H) e).mem (φ y) a ∧
          (vanishingIdeal (n := n) H).mem (φ y) b ∧ s = a * b) (φ y) s := hs
      have hc := CoefficientRestrictionTower.isInSpanAt_comp_map h.mdiff hs'
      show IsInSpanAt (n := n) (fun s => ∃ a b, (idealPow (vanishingIdeal (n := n) (φ ⁻¹' H)) e).mem y a ∧
          (vanishingIdeal (n := n) (φ ⁻¹' H)).mem y b ∧ s = a * b) y (s ∘ φ)
      refine IsInSpanAt.mono ?_ hc
      rintro t ⟨s', ⟨a, b, ha, hb, rfl⟩, rfl⟩
      exact ⟨a ∘ φ, b ∘ φ, comp_mem_idealPow_vanishingIdeal_preimage h e ha,
        comp_mem_vanishingIdeal_preimage h hb, rfl⟩

/-- **Powers of the vanishing ideal of a preimage push forward along the local inverse**: `s ∈ (𝓘_{φ⁻¹H}^e)_y` gives
`s ∘ ψ ∈ (𝓘_H^e)_{φ y}`. -/
theorem comp_mem_idealPow_vanishingIdeal (h : IsLocalInverseAt n φ ψ y) {H : Set M} :
    ∀ (e : ℕ) {s : M' → ℂ}, (idealPow (vanishingIdeal (n := n) (φ ⁻¹' H)) e).mem y s →
      (idealPow (vanishingIdeal (n := n) H) e).mem (φ y) (s ∘ ψ)
  | 0, s, hs => by
      have hψy : ψ (φ y) = y := h.left_inv.self_of_nhds
      have hs' : HolomorphicAt n s (ψ (φ y)) := by rw [hψy]; exact hs
      exact holomorphicAt_comp_map h.mdiff_inv hs'
  | e + 1, s, hs => by
      have hψy : ψ (φ y) = y := h.left_inv.self_of_nhds
      have hs' : IsInSpanAt (n := n) (fun s => ∃ a b, (idealPow (vanishingIdeal (n := n) (φ ⁻¹' H)) e).mem y a ∧
          (vanishingIdeal (n := n) (φ ⁻¹' H)).mem y b ∧ s = a * b) (ψ (φ y)) s := by
        rw [hψy]; exact hs
      have hc := CoefficientRestrictionTower.isInSpanAt_comp_map h.mdiff_inv hs'
      show IsInSpanAt (n := n) (fun s => ∃ a b, (idealPow (vanishingIdeal (n := n) H) e).mem (φ y) a ∧
          (vanishingIdeal (n := n) H).mem (φ y) b ∧ s = a * b) (φ y) (s ∘ ψ)
      refine IsInSpanAt.mono ?_ hc
      rintro t ⟨s', ⟨a, b, ha, hb, rfl⟩, rfl⟩
      exact ⟨a ∘ ψ, b ∘ ψ, comp_mem_idealPow_vanishingIdeal h e ha, comp_mem_vanishingIdeal h hb, rfl⟩

/-- **A local biholomorphism maps neighbourhoods onto neighbourhoods**: `map φ (𝓝 y) = 𝓝 (φ y)`. -/
theorem map_nhds_eq_of_local (h : IsLocalInverseAt n φ ψ y) : Filter.map φ (𝓝 y) = 𝓝 (φ y) := by
  refine le_antisymm h.mdiff.self_of_nhds.continuousAt.tendsto fun U hU => ?_
  have h1 : ψ ⁻¹' (φ ⁻¹' U) ∈ 𝓝 (φ y) := h.tendsto hU
  filter_upwards [h1, h.right_inv] with q hq hqr
  rw [mem_preimage, mem_preimage, hqr] at hq
  exact hq

/-- Orders along `N` pull back along a map holomorphic near the point. -/
theorem vanishesToOrderOn_comp {θ : M' → M} {p : M'}
    (hθ : ∀ᶠ w in 𝓝 p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) θ w) {N : Set M} {q : ℕ}
    {g : M → ℂ} (hg : VanishesToOrderOn n N (θ p) q g) : VanishesToOrderOn n (θ ⁻¹' N) p q (g ∘ θ) := by
  obtain ⟨h, hh, hgh⟩ := hg
  exact ⟨h ∘ θ, comp_mem_idealPow_pointIdeal hθ q hh,
    by filter_upwards [hθ.self_of_nhds.continuousAt.eventually hgh] with r hr hrN; exact hr hrN⟩

variable (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
include hloc

/-- **Cosupports along `N` pull back along a local biholomorphism**:
`cosupp((φ^*𝔞)|_{φ⁻¹N}, e) = φ⁻¹ cosupp(𝔞|_N, e)` (ideal of holomorphic germs). -/
theorem cosupport_pullback_of_local {𝔞 : GermIdeal n M} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (N : Set M)
    (e : ℕ) : cosupport n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) e = φ ⁻¹' cosupport n N 𝔞 e := by
  ext x'
  obtain ⟨ψ, hψ⟩ := hloc x'
  have hψx : ψ (φ x') = x' := hψ.left_inv.self_of_nhds
  constructor
  · rintro ⟨hx'N, hord⟩
    refine ⟨hx'N, fun a ha => ?_⟩
    have haφ := comp_mem_pullback hψ.mdiff ha (h𝔞 _ _ ha)
    obtain ⟨h, hh, hev⟩ := hord _ haφ
    have hh' : (idealPow (pointIdeal n (ψ (φ x'))) e).mem (ψ (φ x')) h := by rw [hψx]; exact hh
    refine ⟨h ∘ ψ, comp_mem_idealPow_pointIdeal hψ.mdiff_inv e hh', ?_⟩
    filter_upwards [hψ.tendsto.eventually hev, hψ.right_inv] with q hq hqr hqN
    have := hq (show φ (ψ q) ∈ N by rw [hqr]; exact hqN)
    simpa [hqr] using this
  · rintro ⟨hN, hord⟩
    refine ⟨hN, fun g hg => ?_⟩
    refine IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn
      (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact vanishesToOrderOn_comp hψ.mdiff (hord a ha)

end Local

/-! ### The monomial part -/

section Monomial

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {E : List (Set M)}

/-- **The monomial part by members**: `g ∈ 𝓜_N(𝔞)_y` iff `g` is holomorphic at `y` and, for every member `H ∋ y` of `E`
(`y ∈ N`), `g|_N` lies near `y` in `(𝓘_H^{e_H(y)})|_N`. -/
theorem monomialPartAlong_mem_iff' {y : M} {g : M → ℂ} :
    (monomialPartAlong n N 𝔞 E).mem y g ↔ HolomorphicAt n g y ∧ ∀ H ∈ E, y ∈ N → y ∈ H →
      IsInSpanOnAt (n := n) N ((idealPow (vanishingIdeal (n := n) H) (divExpAlong n N 𝔞 H y)).mem y) y g := by
  constructor
  · rintro ⟨hg, hall⟩
    refine ⟨hg, fun H hH hyN hyH => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    exact hall i hyN hyH
  · rintro ⟨hg, hall⟩
    exact ⟨hg, fun i hyN hyi => hall _ (List.get_mem _ _) hyN hyi⟩

/-- **The monomial part is closed under holomorphic combinations.** -/
theorem monomialPartAlong_mem_of_isInSpanAt {y : M} {g : M → ℂ}
    (hg : IsInSpanAt (n := n) ((monomialPartAlong n N 𝔞 E).mem y) y g) : (monomialPartAlong n N 𝔞 E).mem y g :=
  ⟨hg.1, fun i hyN hyi =>
    RelativePrincipalizationSpan.IsInSpanOnAt.trans (fun _ hs => hs.2 i hyN hyi)
      (RelativePrincipalizationSpan.IsInSpanAt.restrict hg)⟩

/-- **Appending an empty member to `E` does not change the monomial part.** -/
theorem monomialPartAlong_append_empty : monomialPartAlong n N 𝔞 (E ++ [∅]) = monomialPartAlong n N 𝔞 E := by
  refine GermIdeal.ext (funext fun y => funext fun g => propext ?_)
  rw [monomialPartAlong_mem_iff', monomialPartAlong_mem_iff']
  refine and_congr Iff.rfl ⟨fun h H hH => h H (List.mem_append_left _ hH), fun h H hH hyN hyH => ?_⟩
  rcases List.mem_append.mp hH with hH | hH
  · exact h H hH hyN hyH
  · rw [List.mem_singleton.mp hH] at hyH
    exact absurd hyH (notMem_empty y)

/-- **The exponents along `N` only depend on the cosupports along `N`.** -/
theorem divExpAlong_congr {𝔞' : GermIdeal n M} (h : ∀ e, cosupport n N 𝔞 e = cosupport n N 𝔞' e) :
    divExpAlong n N 𝔞 = divExpAlong n N 𝔞' := by
  have hP : IsDivNearAlong n N 𝔞 = IsDivNearAlong n N 𝔞' := by
    funext H e x
    unfold IsDivNearAlong
    rw [h e]
  funext H x
  unfold divExpAlong
  rw [hP]

/-- **The monomial part only depends on `Res_N 𝔞`**: ideals with the same restriction to `N` (`RestrictLe` both
ways) have the same exponents along `N`, hence the same monomial part. -/
theorem monomialPartAlong_congr {𝔞' : GermIdeal n M} (h₁ : RestrictLe N 𝔞 𝔞') (h₂ : RestrictLe N 𝔞' 𝔞) :
    monomialPartAlong n N 𝔞 E = monomialPartAlong n N 𝔞' E := by
  have hexp : divExpAlong n N 𝔞 = divExpAlong n N 𝔞' := divExpAlong_congr fun e =>
    Subset.antisymm (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h₂ e)
      (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h₁ e)
  unfold monomialPartAlong
  rw [hexp]

/-- **The nonmonomial part only depends on `Res_N 𝔞`** (`N` closed). -/
theorem nonmonomialPartAlong_congr (hN : IsClosed N) {𝔞' : GermIdeal n M} (h₁ : RestrictLe N 𝔞 𝔞')
    (h₂ : RestrictLe N 𝔞' 𝔞) : nonmonomialPartAlong n N 𝔞 E = nonmonomialPartAlong n N 𝔞' E := by
  unfold nonmonomialPartAlong colonAlong
  rw [monomialPartAlong_congr h₁ h₂, MarkedIdealOperationsAlong.restrictOn_eq_of_restrictLe hN h₁ h₂]

/-- **Appending an empty member to `E` does not change the nonmonomial part.** -/
theorem nonmonomialPartAlong_append_empty :
    nonmonomialPartAlong n N 𝔞 (E ++ [∅]) = nonmonomialPartAlong n N 𝔞 E := by
  unfold nonmonomialPartAlong
  rw [monomialPartAlong_append_empty]

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {φ : M' → M} (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
include hloc

/-- **The monomial part along `N` pulls back along a local biholomorphism**:
`φ^*𝓜_N(𝔞) = 𝓜_{φ⁻¹N}(φ^*𝔞)`, with the members `φ⁻¹E_i` (ideal of holomorphic germs).  The exponents pull back
(`MonomialInvariantFunctorialAlong.divExpAlong_pullback`), and so do the powers of the member ideals, in both
directions through the local inverse. -/
theorem pullback_monomialPartAlong (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    GermIdeal.pullback (m := n) φ (monomialPartAlong n N 𝔞 E) =
      monomialPartAlong n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) (E.map (φ ⁻¹' ·)) := by
  have hexp : ∀ (x' : M') (H : Set M),
      divExpAlong n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) (φ ⁻¹' H) x' = divExpAlong n N 𝔞 H (φ x') :=
    fun x' H => by
      obtain ⟨ψ, hψ⟩ := hloc x'
      exact MonomialInvariantFunctorialAlong.divExpAlong_pullback
        (fun e => cosupport_pullback_of_local hloc h𝔞 N e) (map_nhds_eq_of_local hψ) H
  refine GermIdeal.ext (funext fun y => funext fun g => propext ?_)
  obtain ⟨ψ, hψ⟩ := hloc y
  have hψy : ψ (φ y) = y := hψ.left_inv.self_of_nhds
  constructor
  · intro hg
    refine monomialPartAlong_mem_of_isInSpanAt
      (IsInSpanAt.mono ?_ (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg))
    rintro s ⟨b, hb, rfl⟩
    rw [monomialPartAlong_mem_iff'] at hb ⊢
    refine ⟨holomorphicAt_comp_map hψ.mdiff hb.1, fun H' hH' hyN hyH' => ?_⟩
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
    obtain ⟨K, s, a, hs, ha, hsum⟩ := hb.2 H hH hyN hyH'
    rw [hexp y H]
    refine ⟨K, fun k => s k ∘ φ, fun k => a k ∘ φ,
      fun k => comp_mem_idealPow_vanishingIdeal_preimage hψ _ (hs k),
      fun k => holomorphicAt_comp_map hψ.mdiff (ha k), ?_⟩
    filter_upwards [hψ.mdiff.self_of_nhds.continuousAt.eventually hsum] with z hz hzN
    exact hz hzN
  · intro hg
    rw [monomialPartAlong_mem_iff'] at hg
    have hmem : (monomialPartAlong n N 𝔞 E).mem (φ y) (g ∘ ψ) := by
      rw [monomialPartAlong_mem_iff']
      have hg1 : HolomorphicAt n g (ψ (φ y)) := by rw [hψy]; exact hg.1
      refine ⟨holomorphicAt_comp_map hψ.mdiff_inv hg1, fun H hH hyN hyH => ?_⟩
      obtain ⟨K, s, a, hs, ha, hsum⟩ :=
        hg.2 (φ ⁻¹' H) (List.mem_map_of_mem hH) (show φ y ∈ N from hyN) (show φ y ∈ H from hyH)
      rw [hexp y H] at hs
      refine ⟨K, fun k => s k ∘ ψ, fun k => a k ∘ ψ,
        fun k => comp_mem_idealPow_vanishingIdeal hψ _ (hs k),
        fun k => holomorphicAt_comp_map hψ.mdiff_inv (by rw [hψy]; exact ha k), ?_⟩
      filter_upwards [hψ.tendsto.eventually hsum, hψ.right_inv] with q hq hqr hqN
      exact hq (show φ (ψ q) ∈ N by rw [hqr]; exact hqN)
    have hhol : HolomorphicAt n ((g ∘ ψ) ∘ φ) y := holomorphicAt_comp_map hψ.mdiff hmem.1
    have hself : IsInSpanAt (n := n) (fun s => ∃ b, (monomialPartAlong n N 𝔞 E).mem (φ y) b ∧ s = b ∘ φ) y
        ((g ∘ ψ) ∘ φ) := isInSpanAt_self ⟨g ∘ ψ, hmem, rfl⟩ hhol
    refine DerivativeIdeal.isInSpanAt_congr hself ?_
    filter_upwards [hψ.left_inv] with p hp
    simp [hp]

end Monomial

/-! ### The quotient along a set and the nonmonomial part -/

section Colon

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {φ : M' → M} {ψ : M → M'} {y : M'}

/-- **Germs of a pulled-back coherent ideal through a local inverse**: `f ∈ (φ^*𝔠)_y` iff `f ∘ ψ ∈ 𝔠_{φ y}`. -/
theorem mem_pullback_iff_of_local {𝔠 : GermIdeal n M} (h𝔠 : 𝔠.IsCoherent) (hψ : IsLocalInverseAt n φ ψ y)
    {f : M' → ℂ} : (GermIdeal.pullback (m := n) φ 𝔠).mem y f ↔ 𝔠.mem (φ y) (f ∘ ψ) := by
  have hψy : ψ (φ y) = y := hψ.left_inv.self_of_nhds
  constructor
  · intro hf
    have hf' : IsInSpanAt (n := n) (fun s => ∃ b, 𝔠.mem (φ y) b ∧ s = b ∘ φ) (ψ (φ y)) f := by
      rw [hψy]; exact hf
    have hc := CoefficientRestrictionTower.isInSpanAt_comp_map hψ.mdiff_inv hf'
    refine HomogenizedIdeal.mem_of_isInSpanAt h𝔠 (IsInSpanAt.mono ?_ hc)
    rintro t ⟨s, ⟨b, hb, rfl⟩, rfl⟩
    refine HomogenizedIdeal.mem_congr h𝔠 hb ?_
    filter_upwards [hψ.right_inv] with q hq
    simp [hq]
  · intro hf
    have h1 := comp_mem_pullback hψ.mdiff hf
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hf)
    refine DerivativeIdeal.isInSpanAt_congr (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp h1) ?_
    filter_upwards [hψ.left_inv] with p hp
    simp [hp]

/-- **Restricted germs of a pulled-back coherent ideal through a local inverse**:
`F ∈ Res_{φ⁻¹W}(φ^*𝔟)_y` iff `F ∘ ψ ∈ Res_W(𝔟)_{φ y}`. -/
theorem mem_restrictOn_pullback_iff_of_local {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent)
    (hψ : IsLocalInverseAt n φ ψ y) {W : Set M} {F : M' → ℂ} :
    (restrictOn n (φ ⁻¹' W) (GermIdeal.pullback (m := n) φ 𝔟)).mem y F ↔ (restrictOn n W 𝔟).mem (φ y) (F ∘ ψ) := by
  have hψy : ψ (φ y) = y := hψ.left_inv.self_of_nhds
  constructor
  · rintro ⟨hF, K, s, a, hs, ha, hsum⟩
    refine ⟨holomorphicAt_comp_map hψ.mdiff_inv (by rw [hψy]; exact hF), K, fun k => s k ∘ ψ, fun k => a k ∘ ψ,
      fun k => (mem_pullback_iff_of_local h𝔟 hψ).mp (hs k),
      fun k => holomorphicAt_comp_map hψ.mdiff_inv (by rw [hψy]; exact ha k), ?_⟩
    have hsum' : ∀ᶠ p in 𝓝 (ψ (φ y)), p ∈ φ ⁻¹' W → F p = ∑ k, a k p * s k p := by rw [hψy]; exact hsum
    filter_upwards [hψ.mdiff_inv.self_of_nhds.continuousAt.eventually hsum', hψ.right_inv] with q hq hqr hqW
    exact hq (show φ (ψ q) ∈ W by rw [hqr]; exact hqW)
  · rintro ⟨hF, K, s, a, hs, ha, hsum⟩
    have hFψφ : (F ∘ ψ) ∘ φ =ᶠ[𝓝 y] F := by
      filter_upwards [hψ.left_inv] with p hp
      simp [hp]
    refine ⟨(holomorphicAt_comp_map hψ.mdiff hF).congr hFψφ, K, fun k => s k ∘ φ, fun k => a k ∘ φ,
      fun k => comp_mem_pullback hψ.mdiff (hs k)
        (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 (hs k)),
      fun k => holomorphicAt_comp_map hψ.mdiff (ha k), ?_⟩
    filter_upwards [hψ.mdiff.self_of_nhds.continuousAt.eventually hsum, hψ.left_inv] with p hp hpl hpW
    have := hp hpW
    simp only [Function.comp_apply, hpl] at this
    simpa using this

/-- Membership in `restrictOn` only depends on the germ. -/
theorem restrictOn_mem_congr {W : Set M} {𝔟 : GermIdeal n M} {x : M} {F G : M → ℂ}
    (hF : (restrictOn n W 𝔟).mem x F) (h : F =ᶠ[𝓝 x] G) : (restrictOn n W 𝔟).mem x G :=
  ⟨hF.1.congr h, RelativePrincipalizationSpan.IsInSpanOnAt.congr_right hF.2
    (by filter_upwards [h] with p hp _; exact hp.symm)⟩

/-- **The quotient along a set commutes with pullback along a local biholomorphism** (coherent ideals and quotient):
`(Res_{φ⁻¹W} φ^*𝔟 : φ^*𝔩) = φ^*(Res_W 𝔟 : 𝔩)`. -/
theorem pullback_colonAlong_of_local (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
    {𝔟 𝔩 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) (h𝔩 : 𝔩.IsCoherent) {W : Set M}
    (hc : (colonAlong n W 𝔟 𝔩).IsCoherent) :
    colonAlong n (φ ⁻¹' W) (GermIdeal.pullback (m := n) φ 𝔟) (GermIdeal.pullback (m := n) φ 𝔩) =
      GermIdeal.pullback (m := n) φ (colonAlong n W 𝔟 𝔩) := by
  refine GermIdeal.ext (funext fun y => funext fun f => propext ?_)
  obtain ⟨ψ, hψ⟩ := hloc y
  have hψy : ψ (φ y) = y := hψ.left_inv.self_of_nhds
  rw [mem_pullback_iff_of_local hc hψ]
  constructor
  · rintro ⟨hf, hcol⟩
    refine ⟨holomorphicAt_comp_map hψ.mdiff_inv (by rw [hψy]; exact hf), fun g' hg' => ?_⟩
    have h1 := hcol (g' ∘ φ) (comp_mem_pullback hψ.mdiff hg'
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔩 hg'))
    have h2 := (mem_restrictOn_pullback_iff_of_local h𝔟 hψ).mp h1
    refine restrictOn_mem_congr h2 ?_
    filter_upwards [hψ.right_inv] with q hq
    simp [hq]
  · rintro ⟨hf, hcol⟩
    have hfψφ : (f ∘ ψ) ∘ φ =ᶠ[𝓝 y] f := by
      filter_upwards [hψ.left_inv] with p hp
      simp [hp]
    refine ⟨(holomorphicAt_comp_map hψ.mdiff hf).congr hfψφ, fun g hg => ?_⟩
    have h1 := hcol (g ∘ ψ) ((mem_pullback_iff_of_local h𝔩 hψ).mp hg)
    exact (mem_restrictOn_pullback_iff_of_local h𝔟 hψ).mpr h1

/-- **The nonmonomial part along `N` pulls back along a local biholomorphism**: `φ^*𝓝_N(𝔞) = 𝓝_{φ⁻¹N}(φ^*𝔞)`, with
the members `φ⁻¹E_i` (`𝔞`, `𝓜_N(𝔞)` and `𝓝_N(𝔞)` coherent). -/
theorem pullback_nonmonomialPartAlong (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y) {N : Set M}
    {𝔞 : GermIdeal n M} {E : List (Set M)} (h𝔞 : 𝔞.IsCoherent) (hM : (monomialPartAlong n N 𝔞 E).IsCoherent)
    (hNN : (nonmonomialPartAlong n N 𝔞 E).IsCoherent) :
    GermIdeal.pullback (m := n) φ (nonmonomialPartAlong n N 𝔞 E) =
      nonmonomialPartAlong n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) (E.map (φ ⁻¹' ·)) := by
  unfold nonmonomialPartAlong at hNN ⊢
  rw [← pullback_monomialPartAlong hloc
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg),
    pullback_colonAlong_of_local hloc h𝔞 hM hNN]

end Colon

end

end Hironaka.MonomialPartEtale
