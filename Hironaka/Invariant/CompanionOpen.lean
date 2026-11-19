import Hironaka.Invariant.CompanionRebase
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.GiraudAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The companion ideal on an open set where the order of the nonmonomial part is bounded

Hironaka phase H2 (TN3), for TN-CLASSICAL's general step (`hir:general-step`) and the open-set statement missing from
`hir:companion-basic`; claim I-0977 C-0157.  Blueprint `bcalc:companion-open` (chapter `blowup-calculus.tex`).  Sources:
Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2a of Proposition `pr:resol`; Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), Step II.B.

The general step takes, at a point where `o = ord(𝓝_N(𝔞)|_N)` is positive, an open set `W` on which this order is at most
`o` at the points of the cosupport (upper semicontinuity: the points of order `≥ o + 1` form the closed set
`cosupp(𝓝_N(𝔞)|_N, o + 1)`), and the companion ideal `𝓞(𝔪|_W, o)` (`CompanionRebase.companionOf`).
`CompanionReductionAlong` proves the maximal order and the reduction for an abstract factorization `(N, E, 𝔟𝔠, d)` with
the bound on all of `M`; here they are stated for the marked ideal `𝔪` itself, which is restricted-equivalent to the
factorization `(N, E, 𝓝_N(𝔞)𝓜_N(𝔞), d)`, and on an open set with the bound only there.

## Main results

* `restrictEquiv_mul_parts`, `cosupport_mul_parts`: `𝔪 ≃ (N, E, 𝓝_N(𝔞)𝓜_N(𝔞), d)` and the same cosupport;
* `isClosed_cosupport_nonmonomialPartAlong`: the points where `ord(𝓝_N(𝔞)|_N) ≥ o + 1` form a closed set;
* **`isMaximalOrderAlong_companionOf`**, **`companionOf_reduction`**: under `ord(𝓝_N(𝔞)|_N) ≤ o` on `cosupp 𝔪`, the companion
  ideal is of maximal order along `N`, its multiple test blow-ups are multiple test blow-ups of `𝔪` and of `(N, E, 𝓝, o)`,
  the bound persists along them on the cosupport of `𝔪`, and `cosupp 𝓞_T = cosupp(𝓝_T, o) ∩ cosupp 𝔪_T`;
* `bound_pullback_val`, **`isMaximalOrderAlong_companionOf_pullback_val`**, **`companionOf_reduction_pullback_val`**: the same
  for `𝓞(𝔪|_W, o)` when the bound holds on `cosupp 𝔪 ∩ W` only (`hir:companion-basic` on an open set).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CompanionOpen

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong
  Hironaka.CompanionReductionAlong Hironaka.MonomialPartEtale
  Hironaka.CompanionRebase Hironaka.GermIdealOrder
  Hironaka.DivisorExponentAlong Hironaka.BlowupTowers
  Hironaka.DerivativeIdealAlongEtale Hironaka.MarkedIdealRestrictOpen
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.MarkedIdealEquivalence.MarkedIdeal Hironaka.RestrictedIdealWeight

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- **A marked ideal is restricted-equivalent to the factorization by its parts**:
`𝔪 ≃ (N, E, 𝓝_N(𝔞)𝓜_N(𝔞), d)` (`𝔪` well formed and nonzero along `N`, `n > 0`). -/
theorem restrictEquiv_mul_parts (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) :
    RestrictEquiv 𝔪 ⟨𝔪.N, 𝔪.E,
      (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E).mul (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E), 𝔪.d⟩ := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · show RestrictLe 𝔪.N 𝔪.ideal ((nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E).mul (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E))
    rw [RestrictLeCalculus.mul_comm']
    exact restrictLe_mul_along hn h𝔪.isClosedSubmanifold_N h𝔪.isSNCDivisor h𝔪.isTransverse h𝔪.isCoherent hne
  · show RestrictLe 𝔪.N ((nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E).mul (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E)) 𝔪.ideal
    rw [RestrictLeCalculus.mul_comm']
    exact restrictLe_mul_along' h𝔪.isClosedSubmanifold_N h𝔪.isCoherent

/-- **The factorization has the cosupport of `𝔪`**: `cosupp((𝓝_N(𝔞)𝓜_N(𝔞))|_N, d) = cosupp 𝔪`. -/
theorem cosupport_mul_parts (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) :
    cosupport n 𝔪.N ((nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E).mul (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E)) 𝔪.d =
      𝔪.cosupp :=
  (restrictEquiv_mul_parts hn h𝔪 hne).cosupp_eq.symm

/-- **Upper semicontinuity of the order of the nonmonomial part**: the points where `ord(𝓝_N(𝔞)|_N) ≥ q` form a closed
set (`𝔪` well formed and nonzero along `N`, `n > 0`). -/
theorem isClosed_cosupport_nonmonomialPartAlong (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (q : ℕ) :
    IsClosed (cosupport n 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) q) :=
  GiraudAlong.isClosed_cosupport_along
    (isCoherent_nonmonomialPartAlong hn h𝔪.isClosedSubmanifold_N h𝔪.isSNCDivisor h𝔪.isTransverse h𝔪.isCoherent hne)
    h𝔪.isClosedSubmanifold_N q

/-- **The companion ideal is of maximal order along `N`** (`hir:companion-basic`) as soon as `ord(𝓝_N(𝔞)|_N) ≤ o` on
`cosupp 𝔪`. -/
theorem isMaximalOrderAlong_companionOf (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) {o : ℕ}
    (hbound : ∀ x ∈ 𝔪.cosupp, x ∉ cosupport n 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) (o + 1)) :
    HomogenizedIdealAlong.IsMaximalOrderAlong 𝔪.N (companionOf n 𝔪 o).ideal (companionOf n 𝔪 o).d := by
  have hN := h𝔪.isClosedSubmanifold_N
  have hNN := isCoherent_nonmonomialPartAlong hn hN h𝔪.isSNCDivisor h𝔪.isTransverse h𝔪.isCoherent hne
  have hM := isCoherent_monomialPartAlong hn hN h𝔪.isSNCDivisor h𝔪.isTransverse h𝔪.isCoherent hne
  exact companion_isMaximalOrderAlong hN.2 𝔪.E hNN hM fun x hx =>
    hbound x (by rwa [cosupport_mul_parts hn h𝔪 hne] at hx)

/-- **Reduction to maximal order for the marked ideal itself** (`hir:companion-reduction-along` with
`𝔪 ≃ (N, E, 𝓝𝓜, d)`): if `ord(𝓝_N(𝔞)|_N) ≤ o` on `cosupp 𝔪` (`o ≥ 1`), every multiple test blow-up `T` of the companion
ideal is one of `𝔪` and of `(N, E, 𝓝_N(𝔞), o)`; along it `ord(𝓝_T|_{N_T}) ≤ o` on `cosupp 𝔪_T`, and
`cosupp 𝓞_T = cosupp(𝓝_T, o) ∩ cosupp 𝔪_T`. -/
theorem companionOf_reduction (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) {o : ℕ} (ho : 1 ≤ o)
    (hbound : ∀ x ∈ 𝔪.cosupp, x ∉ cosupport n 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) (o + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (companionOf n 𝔪 o) T) :
    IsGeoTestTower 𝔪 T ∧
      IsGeoTestTower (⟨𝔪.N, 𝔪.E, nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E, o⟩ : MarkedIdeal n X) T ∧
      (∀ z ∈ (geoTransformAlong 𝔪 T).cosupp,
        z ∉ cosupport n (geoTransformAlong (⟨𝔪.N, 𝔪.E, nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E, o⟩ : MarkedIdeal n X) T).N
          (geoTransformAlong (⟨𝔪.N, 𝔪.E, nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E, o⟩ : MarkedIdeal n X) T).ideal
          (o + 1)) ∧
      (geoTransformAlong (companionOf n 𝔪 o) T).cosupp =
        (geoTransformAlong (⟨𝔪.N, 𝔪.E, nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E, o⟩ : MarkedIdeal n X) T).cosupp ∩
          (geoTransformAlong 𝔪 T).cosupp := by
  have hN := h𝔪.isClosedSubmanifold_N
  have hNN := isCoherent_nonmonomialPartAlong hn hN h𝔪.isSNCDivisor h𝔪.isTransverse h𝔪.isCoherent hne
  have hM := isCoherent_monomialPartAlong hn hN h𝔪.isSNCDivisor h𝔪.isTransverse h𝔪.isCoherent hne
  obtain ⟨h1, h2, h3, h4⟩ := companion_reduction_along hN 𝔪.E hNN hM ho
    (fun x hx => hbound x (by rwa [cosupport_mul_parts hn h𝔪 hne] at hx)) T hT
  have hW := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv (restrictEquiv_mul_parts hn h𝔪 hne) hN.1
    h𝔪.isCoherent (IdealWeightPowers.isCoherent_mul hNN hM)
  have hT𝔪 : IsGeoTestTower 𝔪 T := ((hW.2 T).1).mpr h1
  have hcos := (hW.2 T).2 hT𝔪
  refine ⟨hT𝔪, h2, fun z hz => h3 z (by rw [← hcos]; exact hz), ?_⟩
  rw [hcos]
  exact h4

/-! ### On an open set where the bound holds -/

/-- **The bound passes to an open set**: if `ord(𝓝_N(𝔞)|_N) ≤ o` at the points of `cosupp 𝔪 ∩ W`, then
`ord(𝓝_{N ∩ W}(𝔞|_W)|_{N ∩ W}) ≤ o` on `cosupp(𝔪|_W)` (`𝔪` well formed and nonzero along `N`, `n > 0`). -/
theorem bound_pullback_val (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (W : Opens X) {o : ℕ}
    (hbound : ∀ x ∈ 𝔪.cosupp, x ∈ W → x ∉ cosupport n 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) (o + 1)) :
    ∀ x ∈ (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).cosupp,
      x ∉ cosupport n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
        (nonmonomialPartAlong n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
          (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E)
        (o + 1) := by
  have hN := h𝔪.isClosedSubmanifold_N
  have h𝔞 := h𝔪.isCoherent
  have hNN := isCoherent_nonmonomialPartAlong hn hN h𝔪.isSNCDivisor h𝔪.isTransverse h𝔞 hne
  have hM := isCoherent_monomialPartAlong hn hN h𝔪.isSNCDivisor h𝔪.isTransverse h𝔞 hne
  have hloc : ∀ y : W, ∃ ψ : X → W, IsLocalInverseAt n (Subtype.val : W → X) ψ y :=
    fun y => ⟨openInv W y, isLocalInverseAt_val W y⟩
  intro x hx hxc
  have hx' : (x : X) ∈ 𝔪.cosupp := by
    rw [cosupp_pullback_val 𝔪 (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg)]
      at hx
    exact hx
  have hpb : nonmonomialPartAlong n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
      (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E =
      GermIdeal.pullback (m := n) (Subtype.val : W → X) (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) :=
    (pullback_nonmonomialPartAlong hloc h𝔞 hM hNN).symm
  rw [hpb] at hxc
  have hxc' : x ∈ cosupport n ((Subtype.val : W → X) ⁻¹' 𝔪.N)
      (GermIdeal.pullback (m := n) (Subtype.val : W → X) (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E)) (o + 1) := hxc
  rw [cosupport_pullback_of_local hloc
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hNN hg)] at hxc'
  exact hbound x hx' x.2 hxc'

open ResolutionInvariantSpec (IsInvDomain)

/-- **The companion ideal on an open set is of maximal order** (`hir:companion-basic` on an open set `W`): for `𝔪` in the
domain and `ord(𝓝_N(𝔞)|_N) ≤ o` on `cosupp 𝔪 ∩ W`, `𝓞(𝔪|_W, o)` is of maximal order along `N ∩ W`. -/
theorem isMaximalOrderAlong_companionOf_pullback_val (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) (W : Opens X) {o : ℕ}
    (hbound : ∀ x ∈ 𝔪.cosupp, x ∈ W → x ∉ cosupport n 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) (o + 1)) :
    HomogenizedIdealAlong.IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
      (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪) o).ideal
      (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪) o).d := by
  have hW := InvDomainTowerAlong.isInvDomain_pullback_val W h
  exact isMaximalOrderAlong_companionOf (X := CMfd.of (n := n) W) hn hW.isWellFormed hW.isNonzeroAlongAt
    (bound_pullback_val hn h.isWellFormed h.isNonzeroAlongAt W hbound)

/-- **Reduction to maximal order on an open set** (`hir:companion-basic` / `hir:general-step` on an open set `W`): for `𝔪`
in the domain, `o ≥ 1` and `ord(𝓝_N(𝔞)|_N) ≤ o` on `cosupp 𝔪 ∩ W`, every multiple test blow-up `T` of `𝓞(𝔪|_W, o)` is one
of `𝔪|_W` and of `(N, E, 𝓝, o)|_W`; along it the bound persists on `cosupp (𝔪|_W)_T`, and
`cosupp 𝓞_T = cosupp(𝓝_T, o) ∩ cosupp (𝔪|_W)_T`. -/
theorem companionOf_reduction_pullback_val (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    (W : Opens X) {o : ℕ} (ho : 1 ≤ o)
    (hbound : ∀ x ∈ 𝔪.cosupp, x ∈ W → x ∉ cosupport n 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) (o + 1))
    {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) W) Y)
    (hT : IsGeoTestTower (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪) o) T) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪) T ∧
      IsGeoTestTower (⟨(MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N, (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E,
        nonmonomialPartAlong n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
          (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E, o⟩ :
            MarkedIdeal n (CMfd.of (n := n) W)) T ∧
      (∀ z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪) T).cosupp,
        z ∉ cosupport n (geoTransformAlong (⟨(MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N,
            (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E,
            nonmonomialPartAlong n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
              (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E, o⟩ :
                MarkedIdeal n (CMfd.of (n := n) W)) T).N
          (geoTransformAlong (⟨(MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N,
            (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E,
            nonmonomialPartAlong n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
              (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E, o⟩ :
                MarkedIdeal n (CMfd.of (n := n) W)) T).ideal (o + 1)) ∧
      (geoTransformAlong (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪) o)
          T).cosupp =
        (geoTransformAlong (⟨(MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N,
            (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E,
            nonmonomialPartAlong n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
              (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E, o⟩ :
                MarkedIdeal n (CMfd.of (n := n) W)) T).cosupp ∩
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪) T).cosupp := by
  have hW := InvDomainTowerAlong.isInvDomain_pullback_val W h
  exact companionOf_reduction (X := CMfd.of (n := n) W) hn hW.isWellFormed hW.isNonzeroAlongAt ho
    (bound_pullback_val hn h.isWellFormed h.isNonzeroAlongAt W hbound) T hT

end

end Hironaka.CompanionOpen
