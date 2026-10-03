/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.Invariant.CompanionReductionAlong
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialPart
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.MarkedIdeal.RestrictedIdealExtension
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The companion ideal lies in the domain of the inductive invariant

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2a of Proposition `pr:resol` (the companion ideal `𝓞(𝓘) =
𝓝(𝓘) + (𝓜(𝓘), μ - o)`, formed from the transform at a later stage); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), Step II.B.

At a point of the cosupport where the order `o` of the nonmonomial part `𝓝_N(𝔞)` is positive, the general step takes
the invariant of the maximal-order step of the companion ideal `𝓞 = companionAlong N E 𝓝_N(𝔞) 𝓜_N(𝔞) o d`
(`CompanionReductionAlong.companionAlong`), formed on an open set and at a later stage of the segment. That
invariant is defined on the marked ideals of `ResolutionInvariantSpec.IsInvDomain k`; this module shows that `𝓞`
lies there whenever the marked ideal does.

## Main results

* `isNonzeroAlongAt_nonmonomialPartAlong`: the nonmonomial part along `N` is nonzero along `N` wherever `𝔞` is (a germ
  `g` of `𝔞` factors as `m · c` on `N` with `c` in the nonmonomial part, and `c` vanishes on `N` only where `g` does);
* `isNonzeroAlongAt_idealPow`, `isNonzeroAlongAt_sumIdeal_left`: powers and sums keep a germ nonzero along `N`;
* **`isInvDomain_companionAlong`**: for `𝔪` in `IsInvDomain k`, `0 < n` and `o ≥ 1`, the companion ideal lies in
  `IsInvDomain k` -- the same `N` and `E`, a coherent ideal, the mark `o` or `o(d - o)`, nonzero along `N`;
* `isInvDomain_companionAlong_geoTransformAlong`, `isInvDomain_companionAlong_pullback_val`,
  `isInvDomain_pullback_val_companionAlong`: the same for the companion ideal of the transform along a multiple test
  blow-up, of the restriction to an open set, and for the restriction of the companion ideal.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.InvDomainCompanion

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.DivisorExponentAlong Hironaka.ResolutionInvariantSpec Hironaka.NormalCrossings Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.MarkedIdealOperationsTransform Hironaka.MarkedIdealOperationsTransform.MarkedIdeal Hironaka.RestrictedIdealExtension Hironaka.GermIdealOrder Hironaka.MarkedIdealBiholomorphism Hironaka.InvDomainTowerAlong Hironaka.BlowupTowers Hironaka.IdealWeightPowers

noncomputable section

variable {n : ℕ}

/-! ### Nonzero along `N` -/

section Nonzero

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M}

/-- **Powers keep a germ nonzero along `N`**: if `𝔟` (of holomorphic germs) is nonzero along `N` at `y`, so is `𝔟^j`
(the `j`-th power of a germ not vanishing identically on `N` near `y` does not either). -/
theorem isNonzeroAlongAt_idealPow {𝔟 : GermIdeal n M} (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) {y : M}
    (h : IsNonzeroAlongAt N 𝔟 y) (j : ℕ) : IsNonzeroAlongAt N (idealPow 𝔟 j) y := by
  obtain ⟨g, hg, hfreq⟩ := h
  exact ⟨fun z => g z ^ j, MonomialPart.pow_mem_idealPow hg (h𝔟 y g hg) j,
    hfreq.mono fun z hz => ⟨hz.1, pow_ne_zero j hz.2⟩⟩

/-- **A sum is nonzero along `N` where its first summand is.** -/
theorem isNonzeroAlongAt_sumIdeal_left {𝔟 𝔠 : GermIdeal n M} (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x)
    {y : M} (h : IsNonzeroAlongAt N 𝔟 y) : IsNonzeroAlongAt N (sumIdeal 𝔟 𝔠) y := by
  obtain ⟨g, hg, hfreq⟩ := h
  exact ⟨g, IdealOrderArithmetic.le_sumIdeal_left' h𝔟 y g hg, hfreq⟩

/-- **The nonmonomial part along `N` is nonzero along `N` wherever `𝔞` is** (`E` simple normal crossings and transverse
to the closed submanifold `N`, `𝔞` coherent and nonzero along `N` at every point of `N`, `0 < n`): a germ `g` of `𝔞` at
`y` not vanishing identically on `N` near `y` is `m · c` on `N` near `y` with `c` a germ of `𝓝_N(𝔞)`
(`MonomialPartAlong.exists_mem_nonmonomialPartAlong_mul`), and `c ≠ 0` wherever `g ≠ 0`. -/
theorem isNonzeroAlongAt_nonmonomialPartAlong (hn : 0 < n) (hN : IsClosedSubmanifold n N) {E : List (Set M)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ y ∈ N, IsNonzeroAlongAt N 𝔞 y) {y : M} (hyN : y ∈ N) :
    IsNonzeroAlongAt N (nonmonomialPartAlong n N 𝔞 E) y := by
  obtain ⟨g, hg, hfreq⟩ := hne y hyN
  obtain ⟨m, c, -, -, -, hc, hgmc⟩ := exists_mem_nonmonomialPartAlong_mul hn hN hE hT h𝔞 hne hyN hg
  refine ⟨c, hc, (hfreq.and_eventually hgmc).mono fun z hz => ⟨hz.1.1, fun hc0 => hz.1.2 ?_⟩⟩
  rw [hz.2 hz.1.1, hc0, mul_zero]

end Nonzero

/-! ### The companion ideal -/

section Companion

variable {X : CMfd.{u} n}

/-- **The companion ideal lies in the domain of the inductive invariant** (`hir:general-step`): for
`𝔪 = (M, N, E, 𝔞, d)` in `IsInvDomain k`, `0 < n` and `o ≥ 1`, the companion ideal
`𝓞 = (N, E, 𝓝_N(𝔞), o) + (N, E, 𝓜_N(𝔞), d - o)` (`o < d`), resp. `(N, E, 𝓝_N(𝔞), o)` (`o ≥ d`), lies in
`IsInvDomain k`: the same `N` and `E`, a coherent ideal
(`MonomialPartAlong.isCoherent_nonmonomialPartAlong`, `isCoherent_monomialPartAlong`), the mark `o(d - o) ≥ 1`
resp. `o ≥ 1`, and nonzero along `N` at every point of `N` (the nonmonomial part is, and so are its powers and the
sums containing them). -/
theorem isInvDomain_companionAlong (hn : 0 < n) {𝔪 : MarkedIdeal n X} {k : ℕ} (h : IsInvDomain k 𝔪) {o : ℕ}
    (ho : 1 ≤ o) :
    IsInvDomain k (companionAlong 𝔪.N 𝔪.E (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E)
      (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) o 𝔪.d) := by
  have hN := h.isWellFormed.isClosedSubmanifold_N
  have hE := h.isWellFormed.isSNCDivisor
  have hT := h.isWellFormed.isTransverse
  have h𝔞 := h.isWellFormed.isCoherent
  have hne := h.isNonzeroAlongAt
  have hcN := isCoherent_nonmonomialPartAlong hn hN hE hT h𝔞 hne
  have hcM := isCoherent_monomialPartAlong hn hN hE hT h𝔞 hne
  have hholN : ∀ x g, (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E).mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcN hg
  have hnzN : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) y :=
    fun y hy => isNonzeroAlongAt_nonmonomialPartAlong hn hN hE hT h𝔞 hne hy
  unfold companionAlong
  split_ifs with hod
  · refine ⟨⟨hN, ?_, hE, hT⟩, h.dimLE, ?_, fun y hy => ?_⟩
    · exact isCoherent_sumIdeal (GermIdealPullbackCalculus.isCoherent_idealPow hcN _)
        (GermIdealPullbackCalculus.isCoherent_idealPow hcM _)
    · show 1 ≤ o * (𝔪.d - o)
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · have hcP := GermIdealPullbackCalculus.isCoherent_idealPow hcN (𝔪.d - o)
      exact isNonzeroAlongAt_sumIdeal_left
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcP hg)
        (isNonzeroAlongAt_idealPow hholN (hnzN y hy) _)
  · exact ⟨⟨hN, hcN, hE, hT⟩, h.dimLE, ho, hnzN⟩

/-- **The companion ideal of the restriction to an open set lies in the domain** (the general step forms `𝓞` on an
open `W`, from `𝔪|_W`). -/
theorem isInvDomain_companionAlong_pullback_val (hn : 0 < n) {𝔪 : MarkedIdeal n X} {k : ℕ} (h : IsInvDomain k 𝔪)
    (W : Opens X) {o : ℕ} (ho : 1 ≤ o) :
    IsInvDomain k (companionAlong (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
      (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E
      (nonmonomialPartAlong n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
        (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E)
      (monomialPartAlong n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
        (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E)
      o (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).d) :=
  isInvDomain_companionAlong (X := CMfd.of (n := n) W) hn (isInvDomain_pullback_val W h) ho

/-- **The restriction of the companion ideal to an open set lies in the domain.** -/
theorem isInvDomain_pullback_val_companionAlong (hn : 0 < n) {𝔪 : MarkedIdeal n X} {k : ℕ} (h : IsInvDomain k 𝔪)
    (W : Opens X) {o : ℕ} (ho : 1 ≤ o) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → X) (companionAlong 𝔪.N 𝔪.E
      (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) o 𝔪.d)) :=
  isInvDomain_pullback_val W (isInvDomain_companionAlong hn h ho)

end Companion

/-! ### At a later stage -/

section Tower

variable {X : CMfd.{u} n}

/-- **The companion ideal formed at a later stage lies in the domain**: for `𝔪` in `IsInvDomain k` and every multiple
test blow-up `T`, the companion ideal of the transform `𝔪_T` lies in `IsInvDomain k` (`isInvDomain_geoTransformAlong`
and `isInvDomain_companionAlong`). -/
theorem isInvDomain_companionAlong_geoTransformAlong (hn : 0 < n) {𝔪 : MarkedIdeal n X} {k : ℕ}
    (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) {o : ℕ} (ho : 1 ≤ o) :
    IsInvDomain k (companionAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).E
      (nonmonomialPartAlong n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E)
      (monomialPartAlong n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E)
      o (geoTransformAlong 𝔪 T).d) :=
  isInvDomain_companionAlong hn (isInvDomain_geoTransformAlong h T hT) ho

end Tower

end

end Hironaka.InvDomainCompanion
