/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MonomialStepAlong
import Hironaka.Invariant.MonomialInvariantFunctorial
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialCase
import Hironaka.Invariant.MonomialCaseAlong
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The invariant of the monomial case along a submanifold under open restrictions, biholomorphisms and empty blowups

The invariant `γ_N = MonomialCaseAlong.gammaAlong n N 𝔞 E d` at `x` is read off the members of `E` through `x` and the
exponents along `N`, `e^N_{E_i}(x) = DivisorExponentAlong.divExpAlong n N 𝔞 (E_i) x`, which are defined by the
cosupports `cosupp(𝔞|_N, e)` near `x`.

* `isDivNearAlong_pullback_iff`, `divExpAlong_pullback`, `gammaAlong_pullback`: for a map `φ : M' → M` along which the
  cosupports along `N` pull back (`cosupp(φ^*𝔞|_{φ⁻¹N}, e) = φ⁻¹ cosupp(𝔞|_N, e)`) and which maps neighbourhoods of `x'`
  onto neighbourhoods of `φ x'`, the exponents along `φ⁻¹ N` and the invariant of `(φ⁻¹N, φ^*𝔞, φ⁻¹E)` at `x'` are those
  of `(N, 𝔞, E)` at `φ x'`;
* `gammaAlong_pullback_val` (**restriction to an open set**) and `gammaAlong_pullback_diffeomorph` (**biholomorphisms**)
  for marked ideals, `MarkedIdealBiholomorphism.MarkedIdeal.pullback` (which pulls back `N` as well);
* `towerInvAlong_restrict`: along the restriction of a multiple test blow-up to an open set
  (`MarkedIdealRestrictOpen`) and along the transport of a tower by a biholomorphism of the base
  (`MarkedIdealTowerTransport`), the invariants `MonomialStepAlong.towerInvAlong` at the stages correspond.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MonomialInvariantFunctorialAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.DivisorExponentAlong Hironaka.MonomialPartAlong Hironaka.MonomialCase Hironaka.MonomialCaseAlong Hironaka.MonomialStepAlong Hironaka.MonomialInvariant Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealTowerTransport Hironaka.NormalCrossings

noncomputable section

variable {n : ℕ}

/-! ### Exponents along `N` and the invariant along maps that pull back cosupports along `N` -/

section Pullback

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {φ : M' → M} {N : Set M} {𝔞 : GermIdeal n M}
  (hcos : ∀ e, cosupport n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) e = φ ⁻¹' cosupport n N 𝔞 e)
  {x' : M'} (hmap : Filter.map φ (𝓝 x') = 𝓝 (φ x'))
include hcos hmap

/-- **Divisibility along a member, along `N`, pulls back.** -/
theorem isDivNearAlong_pullback_iff (H : Set M) (e : ℕ) :
    IsDivNearAlong n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) (φ ⁻¹' H) e x' ↔
      IsDivNearAlong n N 𝔞 H e (φ x') := by
  show (∀ᶠ z in 𝓝 x', z ∈ φ ⁻¹' N → z ∈ φ ⁻¹' H →
      z ∈ cosupport n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) e) ↔
    ∀ᶠ z in 𝓝 (φ x'), z ∈ N → z ∈ H → z ∈ cosupport n N 𝔞 e
  rw [hcos e, ← hmap, Filter.eventually_map]
  rfl

open Classical in
/-- **The exponent along `N` pulls back**: `e^{φ⁻¹N}_{φ⁻¹H}(φ^*𝔞)(x') = e^N_H(𝔞)(φ x')`. -/
theorem divExpAlong_pullback (H : Set M) :
    divExpAlong n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) (φ ⁻¹' H) x' = divExpAlong n N 𝔞 H (φ x') := by
  have hP : (fun e => IsDivNearAlong n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) (φ ⁻¹' H) e x') =
      fun e => IsDivNearAlong n N 𝔞 H e (φ x') :=
    funext fun e => propext (isDivNearAlong_pullback_iff hcos hmap H e)
  unfold divExpAlong
  show (if h : ∃ e, ¬ (fun e => IsDivNearAlong n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) (φ ⁻¹' H) e x')
      (e + 1) then Nat.find h else 0) =
    (if h : ∃ e, ¬ (fun e => IsDivNearAlong n N 𝔞 H e (φ x')) (e + 1) then Nat.find h else 0)
  rw [hP]

/-- **The exponent data along `N` pull back.** -/
theorem expDataAlong_pullback (E : List (Set M)) (i : ℕ) :
    expDataAlong n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) (E.map (φ ⁻¹' ·)) x' i =
      expDataAlong n N 𝔞 E (φ x') i := by
  unfold expDataAlong
  by_cases hi : i < E.length
  · have hi' : i < (E.map (φ ⁻¹' ·)).length := by simpa using hi
    rw [dif_pos hi', dif_pos hi]
    have hget : (E.map (φ ⁻¹' ·)).get ⟨i, hi'⟩ = φ ⁻¹' E.get ⟨i, hi⟩ := by simp
    rw [hget]
    exact divExpAlong_pullback hcos hmap _
  · have hi' : ¬ i < (E.map (φ ⁻¹' ·)).length := by simpa using hi
    rw [dif_neg hi', dif_neg hi]

/-- **The invariant along `N` pulls back**: `γ_{φ⁻¹N}(φ^*𝔞, φ⁻¹E, d)(x') = γ_N(𝔞, E, d)(φ x')`. -/
theorem gammaAlong_pullback (E : List (Set M)) (d : ℕ) :
    gammaAlong n (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) (E.map (φ ⁻¹' ·)) d x' =
      gammaAlong n N 𝔞 E d (φ x') := by
  unfold gammaAlong
  rw [MonomialInvariantFunctorial.memberIdx_map_preimage]
  congr 1
  funext i
  exact expDataAlong_pullback hcos hmap E i

end Pullback

/-! ### Open restrictions, biholomorphisms, empty centres -/

section Marked

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Restriction to an open set** (`hir:monomial-case` (4) along `N`): the invariant along `N ∩ U` of `𝔪|_U` at `p`
is the invariant along `N` of `𝔪` at `p`. -/
theorem gammaAlong_pullback_val (𝔪 : MarkedIdeal n X) (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x)
    (U : Opens X) (p : U) (d : ℕ) :
    gammaAlong n (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).N
        (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).E d p =
      gammaAlong n 𝔪.N 𝔪.ideal 𝔪.E d p.1 := by
  refine gammaAlong_pullback (φ := (Subtype.val : U → X)) (fun e => ?_) ?_ 𝔪.E d
  · have h := MarkedIdealRestrictOpen.cosupp_pullback_val (⟨𝔪.N, [], 𝔪.ideal, e⟩ : MarkedIdeal n X) h𝔞 U
    exact h
  · exact map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ (U : Set X)) p.2 (U.isOpen.mem_nhds p.2)

/-- **Biholomorphisms** (`hir:monomial-case` (4) along `N`): for a biholomorphism `Φ : X' ≅ X`, the invariant along
`Φ⁻¹ N` of `Φ^*𝔪` at `p` is the invariant along `N` of `𝔪` at `Φ p`. -/
theorem gammaAlong_pullback_diffeomorph {X' : Type u} [TopologicalSpace X'] [ChartedSpace (ComplexModel n) X']
    [IsComplexManifold n X'] (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (𝔪 : MarkedIdeal n X)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (p : X') (d : ℕ) :
    gammaAlong n (MarkedIdeal.pullback Φ 𝔪).N (MarkedIdeal.pullback Φ 𝔪).ideal (MarkedIdeal.pullback Φ 𝔪).E d p =
      gammaAlong n 𝔪.N 𝔪.ideal 𝔪.E d (Φ p) := by
  refine gammaAlong_pullback (φ := Φ) (fun e => ?_) ?_ 𝔪.E d
  · exact MarkedIdeal.cosupp_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply
      (⟨𝔪.N, [], 𝔪.ideal, e⟩ : MarkedIdeal n X) h𝔞
  · exact Φ.toHomeomorph.map_nhds_eq p

end Marked

/-! ### Along restricted and transported towers -/

section Tower

variable {X : CMfd.{u} n}

/-- **The invariant along a restricted tower** (`hir:monomial-case` (4) along `N`, with `hir:open-restriction-tower`):
along the restriction to `U` of a multiple test blow-up `T` of `𝔪`, the invariant along `N_T` of the transform of `𝔪|_U`
at `p` is the invariant along `N_T` of the transform of `𝔪` at `p`. -/
theorem towerInvAlong_restrict (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (p : openPreimage T U) :
    towerInvAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = towerInvAlong 𝔪 T p.1 := by
  obtain ⟨-, hcT⟩ := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  unfold towerInvAlong
  rw [MarkedIdealRestrictOpen.geoTransformAlong_restrict U hN h𝔞 T hT]
  exact gammaAlong_pullback_val (geoTransformAlong 𝔪 T)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) (openPreimage T U) p _

end Tower

end

end Hironaka.MonomialInvariantFunctorialAlong
