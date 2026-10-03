/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.CompanionOpen
import Hironaka.Invariant.NonmonomialTransformAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.CompanionReductionAlong
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Invariant.InvDomainRebase
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.MonomialPartEtale
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The order of the nonmonomial part: a local, finite, upper semicontinuous invariant

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2a of Proposition `pr:resol`; Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), Step II.B.

At a point `x` of the cosupport of a marked ideal `𝔪 = (X, N, E, 𝔞, d)` the general step reads off the order
`o = ord_x(𝓝_N(𝔞)|_N)` of the nonmonomial part (`MonomialPartAlong.nonmonomialPartAlong`), and along a tower it uses the
order of the nonmonomial part `𝓝_{N_T}(𝔞_T)` *of the transform* (taken with the whole divisor `E_T`).  This module makes
that order a function and proves the facts about it which do not depend on the invariant of the general step:

* `ordGe 𝔪 q = cosupp(𝓝_N(𝔞)|_N, q)` (the points of order `≥ q`), `nmOrd 𝔪 y` the order (`sInf`), with
  `mem_ordGe_iff` (**the order is finite at the points of `N`**, Krull along `N`, `exists_notMem_ordGe`), `isClosed_ordGe`
  and **`eventually_nmOrd_le`** (upper semicontinuity), `nmOrd_congr` (the order is determined by the sets `ordGe`);
* **locality**: the sets `ordGe` pull back along local biholomorphisms (`mem_ordGe_pullback_iff_of_local`), in particular
  under restriction to open sets and under biholomorphisms; across a blowup along the empty set
  (`mem_ordGe_geoTransform_empty_iff`) and along towers with only empty centres;
  **`mem_ordGe_geoTransformAlong_of_centresAvoid`**: along a multiple test blow-up whose centres miss an open `W`, at the
  points over `W` the order is that of the image; **`mem_ordGe_geoTransform_of_notMem`**: off the centre of a test
  blowup; **`mem_ordGe_geoTransformAlong_isTowerIso`**: along isomorphisms of towers (`hir:tower-isomorphism`);
* **`notMem_ordGe_geoTransform_of_mem`** (the order does not go up over a centre of constant order `q ≥ 1`): if the
  centre `C` of a test blowup lies in `{ord = q}`, every cosupport point over `C` has order `≤ q` (the companion ideal on
  `{ord ≤ q}`, `CompanionOpen`, and `NonmonomialTransformAlong`);
* **`companionOf_tower_facts`**: along a multiple test blow-up of the companion ideal `𝓞(𝔪, o)` (`o ≥ 1`, order `≤ o` on
  the cosupport), the tower is one of `𝔪`, the order stays `≤ o` on the cosupport, and the cosupport of `𝓞_T` lies in
  `{ord ≥ o} ∩ cosupp 𝔪_T`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.NonmonomialOrderLocal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.MonomialPartEtale Hironaka.CompanionRebase Hironaka.GermIdealOrder Hironaka.DivisorExponentAlong Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.DerivativeIdealAlongEtale Hironaka.MarkedIdealRestrictOpen Hironaka.RestrictEmptyTower Hironaka.BlowupTowerIsomorphism Hironaka.InvDomainRebase Hironaka.ContactCanonicalAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)

noncomputable section

variable {n : ℕ}

/-! ### The order of the nonmonomial part -/

section Order

variable {M : CMfd.{u} n}

/-- **The nonmonomial part** `𝓝_N(𝔞)` of a marked ideal `(M, N, E, 𝔞, d)` along its submanifold, with its divisor. -/
abbrev nmPart (𝔪 : MarkedIdeal n M) : GermIdeal n M :=
  nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E

/-- **The points of order at least `q`** of the nonmonomial part along `N`: `cosupp(𝓝_N(𝔞)|_N, q)`. -/
abbrev ordGe (𝔪 : MarkedIdeal n M) (q : ℕ) : Set M :=
  cosupport n 𝔪.N (nmPart 𝔪) q

/-- **The order of the nonmonomial part** at `y`: the least `q` with `y ∉ ordGe 𝔪 (q + 1)` (`0` off `N`; finite at the
points of `N`, `exists_notMem_ordGe`). -/
def nmOrd (𝔪 : MarkedIdeal n M) (y : M) : ℕ :=
  sInf {q : ℕ | y ∉ ordGe 𝔪 (q + 1)}

theorem ordGe_anti (𝔪 : MarkedIdeal n M) {q q' : ℕ} (h : q ≤ q') : ordGe 𝔪 q' ⊆ ordGe 𝔪 q :=
  cosupport_anti h

theorem ordGe_subset_N (𝔪 : MarkedIdeal n M) (q : ℕ) : ordGe 𝔪 q ⊆ 𝔪.N :=
  cosupport_subset q

/-- **The order is determined by the sets `ordGe`**: points with the same membership in all of them (possibly for two
marked ideals) have the same order. -/
theorem nmOrd_congr {M' : CMfd.{u} n} {𝔪 : MarkedIdeal n M} {𝔪' : MarkedIdeal n M'} {y : M} {y' : M'}
    (h : ∀ q, y ∈ ordGe 𝔪 q ↔ y' ∈ ordGe 𝔪' q) : nmOrd 𝔪 y = nmOrd 𝔪' y' := by
  unfold nmOrd
  congr 1
  ext q
  exact not_congr (h (q + 1))

/-- A point of order `< q + 1` has `nmOrd ≤ q`. -/
theorem nmOrd_le_of_notMem {𝔪 : MarkedIdeal n M} {y : M} {q : ℕ} (h : y ∉ ordGe 𝔪 (q + 1)) : nmOrd 𝔪 y ≤ q :=
  Nat.sInf_le h

/-- `q + 1 ≤ nmOrd` gives order `≥ q + 1`. -/
theorem mem_ordGe_of_succ_le {𝔪 : MarkedIdeal n M} {y : M} {q : ℕ} (h : q + 1 ≤ nmOrd 𝔪 y) :
    y ∈ ordGe 𝔪 (q + 1) := by
  by_contra hq
  have := nmOrd_le_of_notMem hq
  omega

/-- Where the order is finite, order `≥ q + 1` gives `q + 1 ≤ nmOrd`. -/
theorem succ_le_nmOrd_of_mem {𝔪 : MarkedIdeal n M} {y : M} (hfin : ∃ q, y ∉ ordGe 𝔪 (q + 1)) {q : ℕ}
    (h : y ∈ ordGe 𝔪 (q + 1)) : q + 1 ≤ nmOrd 𝔪 y := by
  have hmem : nmOrd 𝔪 y ∈ {q : ℕ | y ∉ ordGe 𝔪 (q + 1)} := Nat.sInf_mem hfin
  by_contra hlt
  exact hmem (ordGe_anti 𝔪 (by omega) h)

/-- **The order is finite at the points of `N`** (`n > 0`, `𝔪` well formed and nonzero along `N`): `𝔞 ⊆ 𝓝_N(𝔞)`, and a
germ of `𝔞` not vanishing on `N` near `y` has finite order along `N` (Krull along `N`, through a local retraction). -/
theorem exists_notMem_ordGe {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) {y : M} (hy : y ∈ 𝔪.N) :
    ∃ q, y ∉ ordGe 𝔪 (q + 1) := by
  obtain ⟨g, hg, hfreq⟩ := hne y hy
  obtain ⟨k, hk⟩ := h𝔪.isClosedSubmanifold_N.2 y hy
  obtain ⟨r, hr⟩ := exists_isLocalRetraction hk
  have hghol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔪.isCoherent y g hg
  obtain ⟨q, hq⟩ := hr.exists_not_vanishesToOrderOn hghol hfreq
  refine ⟨q, fun hmem => hq ?_⟩
  have hg' : (nmPart 𝔪).mem y g :=
    NonmonomialTransformAlong.le_nonmonomialPartAlong_self h𝔪.isCoherent y g hg
  exact (ordGe_anti 𝔪 (Nat.le_succ q) hmem).2 g hg'

/-- **The order at a point of `N`**: `y ∈ ordGe 𝔪 q ↔ q ≤ nmOrd 𝔪 y` (`𝔪` well formed and nonzero along `N`). -/
theorem mem_ordGe_iff {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) {y : M} (hy : y ∈ 𝔪.N) (q : ℕ) :
    y ∈ ordGe 𝔪 q ↔ q ≤ nmOrd 𝔪 y := by
  cases q with
  | zero =>
    refine ⟨fun _ => Nat.zero_le _, fun _ => ?_⟩
    show y ∈ cosupport n 𝔪.N (nmPart 𝔪) 0
    rw [cosupport_zero (𝔞 := nmPart 𝔪) (fun _ _ hg => hg.1)]
    exact hy
  | succ q =>
    exact ⟨succ_le_nmOrd_of_mem (exists_notMem_ordGe h𝔪 hne hy), mem_ordGe_of_succ_le⟩

/-- **The points of order at least `q` form a closed set** (`n > 0`). -/
theorem isClosed_ordGe (hn : 0 < n) {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (q : ℕ) : IsClosed (ordGe 𝔪 q) :=
  CompanionOpen.isClosed_cosupport_nonmonomialPartAlong hn h𝔪 hne q

/-- **Upper semicontinuity of the order** (`n > 0`): near a point of `N` the order is at most its order there. -/
theorem eventually_nmOrd_le (hn : 0 < n) {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) {y : M} (hy : y ∈ 𝔪.N) :
    ∀ᶠ y' in 𝓝 y, nmOrd 𝔪 y' ≤ nmOrd 𝔪 y := by
  have hy' : y ∉ ordGe 𝔪 (nmOrd 𝔪 y + 1) := fun h => by
    have := (mem_ordGe_iff h𝔪 hne hy _).mp h
    omega
  filter_upwards [(isClosed_ordGe hn h𝔪 hne (nmOrd 𝔪 y + 1)).isOpen_compl.mem_nhds hy'] with y' hy''
  exact nmOrd_le_of_notMem hy''

end Order

/-! ### Locality: local biholomorphisms, open sets, biholomorphisms -/

section Local

variable {M M' : CMfd.{u} n}

/-- **The order pulls back along a local biholomorphism** (`n > 0`, `𝔪` well formed and nonzero along `N`):
`ord_z 𝓝(φ^*𝔪) = ord_{φ z} 𝓝(𝔪)`, as `φ^*𝓝_N(𝔞) = 𝓝_{φ⁻¹N}(φ^*𝔞)` (`MonomialPartEtale`). -/
theorem mem_ordGe_pullback_iff_of_local (hn : 0 < n) {φ : M' → M}
    (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y) {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (q : ℕ) (z : M') :
    z ∈ ordGe (MarkedIdeal.pullback φ 𝔪) q ↔ φ z ∈ ordGe 𝔪 q := by
  have hN := h𝔪.isClosedSubmanifold_N
  have h𝔞 := h𝔪.isCoherent
  have hM := isCoherent_monomialPartAlong hn hN h𝔪.isSNCDivisor h𝔪.isTransverse h𝔞 hne
  have hNN := isCoherent_nonmonomialPartAlong hn hN h𝔪.isSNCDivisor h𝔪.isTransverse h𝔞 hne
  have hpb : nmPart (MarkedIdeal.pullback φ 𝔪) = GermIdeal.pullback (m := n) φ (nmPart 𝔪) :=
    (pullback_nonmonomialPartAlong hloc h𝔞 hM hNN).symm
  show z ∈ cosupport n (φ ⁻¹' 𝔪.N) (nmPart (MarkedIdeal.pullback φ 𝔪)) q ↔ _
  rw [hpb, cosupport_pullback_of_local hloc
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hNN hg)]
  rfl

/-- **Restriction to an open set** does not change the order. -/
theorem mem_ordGe_pullback_val_iff (hn : 0 < n) {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (U : Opens M) (q : ℕ) (z : U) :
    z ∈ ordGe (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪) q ↔ (z : M) ∈ ordGe 𝔪 q :=
  mem_ordGe_pullback_iff_of_local (M' := CMfd.of (n := n) U) hn
    (fun y => ⟨openInv U y, isLocalInverseAt_val U y⟩) h𝔪 hne q z

theorem nmOrd_pullback_val (hn : 0 < n) {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (U : Opens M) (z : U) :
    nmOrd (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪) z = nmOrd 𝔪 z :=
  nmOrd_congr fun q => mem_ordGe_pullback_val_iff hn h𝔪 hne U q z

/-- **Biholomorphisms** preserve the order. -/
theorem mem_ordGe_pullback_diffeo_iff (hn : 0 < n) (Φ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M)
    {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed) (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (q : ℕ)
    (z : M') : z ∈ ordGe (MarkedIdeal.pullback Φ 𝔪) q ↔ Φ z ∈ ordGe 𝔪 q :=
  mem_ordGe_pullback_iff_of_local hn (fun y => ⟨Φ.symm, isLocalInverseAt_diffeo Φ y⟩) h𝔪 hne q z

end Local

/-! ### Steps and towers -/

section Towers

/-- **Across a blowup along the empty set** the order is that of the image (`n > 0`, `𝔪` well formed and nonzero along
`N`): the transform is restricted-equivalent on `π⁻¹N` to `π^*𝔞` with an appended empty member, so its nonmonomial part
is `π^*𝓝_N(𝔞)` (`MonomialPartEtale`). -/
theorem mem_ordGe_geoTransform_empty_iff (hn : 0 < n) {Y Z : CMfd.{u} n} {π : Z → Y} (𝔪 : MarkedIdeal n Y)
    (h𝔪 : 𝔪.IsWellFormed) (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (hπ : IsBlowupAlong n (∅ : Set Y) π)
    (q : ℕ) (z : Z) : z ∈ ordGe (𝔪.geoTransform ∅ π) q ↔ π z ∈ ordGe 𝔪 q := by
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hloc := exists_isLocalInverseAt_of_isBlowupAlong_empty hπ
  have hN := h𝔪.isClosedSubmanifold_N
  have hE := h𝔪.isSNCDivisor
  have h𝔞 := h𝔪.isCoherent
  have hM := isCoherent_monomialPartAlong hn hN hE h𝔪.isTransverse h𝔞 hne
  have hNN := isCoherent_nonmonomialPartAlong hn hN hE h𝔪.isTransverse h𝔞 hne
  have hN' : (𝔪.geoTransform ∅ π).N = π ⁻¹' 𝔪.N := geoStrictTransform_empty hπc hN.1
  have hN'c : IsClosed (𝔪.geoTransform ∅ π).N := by rw [hN']; exact hN.1.preimage hπc
  have hE' : (𝔪.geoTransform ∅ π).E = 𝔪.E.map (π ⁻¹' ·) ++ [∅] := by
    rw [geoTransform_E, preimage_empty]
    congr 1
    exact List.map_congr_left fun H hH => geoStrictTransform_empty hπc (hE.1 H hH)
  have hle1 := restrictLe_geoTransform_empty_le_pullback hπ 𝔪
  have hle2 := restrictLe_pullback_le_geoTransform (π := π) ∅ 𝔪
  have hkey : nmPart (𝔪.geoTransform ∅ π) = GermIdeal.pullback (m := n) π (nmPart 𝔪) := by
    show nonmonomialPartAlong n (𝔪.geoTransform ∅ π).N (𝔪.geoTransform ∅ π).ideal (𝔪.geoTransform ∅ π).E = _
    rw [nonmonomialPartAlong_congr hN'c hle1 hle2, pullback_nonmonomialPartAlong hloc h𝔞 hM hNN, hN', hE',
      nonmonomialPartAlong_append_empty]
  show z ∈ cosupport n (𝔪.geoTransform ∅ π).N (nmPart (𝔪.geoTransform ∅ π)) q ↔ _
  rw [hkey, hN', cosupport_pullback_of_local hloc
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hNN hg)]
  rfl

variable {X : CMfd.{u} n}

/-- **Along a tower with only empty centres** the order is that of the image (`𝔪` in the domain, `n > 0`). -/
theorem mem_ordGe_geoTransformAlong_of_isEmptyTower (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) (q : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T → ∀ z : Y,
      z ∈ ordGe (geoTransformAlong 𝔪 T) q ↔ T.proj z ∈ ordGe 𝔪 q
  | _, .refl, _, _ => Iff.rfl
  | _, .step T C π hπ, hT, z => by
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := hT
      subst hC
      have hdomT := isInvDomain_geoTransformAlong_of_isEmptyTower h T hT
      rw [geoTransformAlong_step,
        mem_ordGe_geoTransform_empty_iff hn _ hdomT.isWellFormed hdomT.isNonzeroAlongAt hπ]
      exact mem_ordGe_geoTransformAlong_of_isEmptyTower hn h q T hT (π z)

/-- **Along a multiple test blow-up whose centres miss an open set `W`**, at the points over `W` the order of the
nonmonomial part of the transform is that of the image (`𝔪` in the domain, `n > 0`): over `W` the tower restricts to one
with only empty centres (`RestrictEmptyTower`), and the order is local. -/
theorem mem_ordGe_geoTransformAlong_of_centresAvoid (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (W : Opens X)
    (hW : CentresAvoid W T) (q : ℕ) {z : Y} (hz : T.proj z ∈ W) :
    z ∈ ordGe (geoTransformAlong 𝔪 T) q ↔ T.proj z ∈ ordGe 𝔪 q := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  let p : openPreimage T W := ⟨z, hz⟩
  have he : IsEmptyTower (restrict W T) := (isEmptyTower_restrict_iff W T).mpr hW
  have hW' := InvDomainTowerAlong.isInvDomain_pullback_val W h
  refine (mem_ordGe_pullback_val_iff hn hdomT.isWellFormed hdomT.isNonzeroAlongAt (openPreimage T W) q p).symm.trans
    ?_
  rw [← geoTransformAlong_restrict W h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T hT]
  refine (mem_ordGe_geoTransformAlong_of_isEmptyTower (X := CMfd.of (n := n) W) hn hW' q (restrict W T) he p).trans
    ?_
  refine (mem_ordGe_pullback_val_iff hn h.isWellFormed h.isNonzeroAlongAt W q _).trans ?_
  rw [proj_restrict W T p]

/-- **Off the centre of a test blowup** the order is that of the image. -/
theorem mem_ordGe_geoTransform_of_notMem (hn : 0 < n) {Y Z : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Y}
    (h : IsInvDomain k 𝔫) {C : Set Y} (hC : 𝔫.IsAdmissibleCentre C) {π : Z → Y} (hπ : IsBlowupAlong n C π)
    (q : ℕ) {z : Z} (hz : π z ∉ C) : z ∈ ordGe (𝔫.geoTransform C π) q ↔ π z ∈ ordGe 𝔫 q := by
  have hT : IsGeoTestTower 𝔫 (.step .refl C π hπ) := (isGeoTestTower_step_iff 𝔫 _ C π hπ).mpr ⟨trivial, hC⟩
  have hW : CentresAvoid ⟨Cᶜ, hC.1.1.isOpen_compl⟩ (.step (.refl : BlowupTower Y Y) C π hπ) :=
    (centresAvoid_step_iff _ _ C π hπ).mpr ⟨trivial, disjoint_compl_right⟩
  exact mem_ordGe_geoTransformAlong_of_centresAvoid hn h (.step .refl C π hπ) hT ⟨Cᶜ, hC.1.1.isOpen_compl⟩ hW q
    (z := z) hz

theorem nmOrd_geoTransform_of_notMem (hn : 0 < n) {Y Z : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Y}
    (h : IsInvDomain k 𝔫) {C : Set Y} (hC : 𝔫.IsAdmissibleCentre C) {π : Z → Y} (hπ : IsBlowupAlong n C π)
    {z : Z} (hz : π z ∉ C) : nmOrd (𝔫.geoTransform C π) z = nmOrd 𝔫 (π z) :=
  nmOrd_congr fun q => mem_ordGe_geoTransform_of_notMem hn h hC hπ q hz

/-- **Along isomorphisms of towers** (`hir:tower-isomorphism`): for `χ : T' → T` over a biholomorphism `Φ` and `T` a
multiple test blow-up of `𝔪` (in the domain, `n > 0`), the order for `Φ^*𝔪` along `T'` at `p` is that for `𝔪` along `T`
at `χ p`. -/
theorem mem_ordGe_geoTransformAlong_isTowerIso (hn : 0 < n) {X' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ T' T χ)
    (hT : IsGeoTestTower 𝔪 T) (q : ℕ) (p : Y') :
    p ∈ ordGe (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T') q ↔ χ p ∈ ordGe (geoTransformAlong 𝔪 T) q := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  rw [IsTowerIso.geoTransformAlong_eq Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent hiso hT]
  exact mem_ordGe_pullback_diffeo_iff hn χ hdomT.isWellFormed hdomT.isNonzeroAlongAt q p

theorem nmOrd_geoTransformAlong_isTowerIso (hn : 0 < n) {X' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ T' T χ)
    (hT : IsGeoTestTower 𝔪 T) (p : Y') :
    nmOrd (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T') p = nmOrd (geoTransformAlong 𝔪 T) (χ p) :=
  nmOrd_congr fun q => mem_ordGe_geoTransformAlong_isTowerIso hn Φ h hiso hT q p

end Towers

/-! ### Along the companion tower, and over a centre of constant order -/

section Companion

/-- **Along a multiple test blow-up of the companion ideal** (`𝔫` in the domain, `n > 0`, `o ≥ 1`, order `≤ o` on
`cosupp 𝔫`): the tower is a multiple test blow-up of `𝔫`, the order of the nonmonomial part of the transform stays `≤ o`
on its cosupport, and the cosupport of the transform of `𝓞(𝔫, o)` lies in `{ord ≥ o} ∩ cosupp 𝔫_T`
(`NonmonomialTransformAlong`, `CompanionOpen`). -/
theorem companionOf_tower_facts (hn : 0 < n) {Z : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Z} (h : IsInvDomain k 𝔫)
    {o : ℕ} (ho : 1 ≤ o) (hbound : ∀ x ∈ 𝔫.cosupp, x ∉ ordGe 𝔫 (o + 1)) {Y : CMfd.{u} n} (T : BlowupTower Z Y)
    (hT : IsGeoTestTower (companionOf n 𝔫 o) T) :
    IsGeoTestTower 𝔫 T ∧ (∀ z ∈ (geoTransformAlong 𝔫 T).cosupp, z ∉ ordGe (geoTransformAlong 𝔫 T) (o + 1)) ∧
      (geoTransformAlong (companionOf n 𝔫 o) T).cosupp ⊆
        ordGe (geoTransformAlong 𝔫 T) o ∩ (geoTransformAlong 𝔫 T).cosupp := by
  obtain ⟨hT𝔫, -, hNeq, -, -, hR, -, hb⟩ :=
    NonmonomialTransformAlong.nonmonomialPart_geoTransformAlong_along hn 𝔫 h.isWellFormed h.isNonzeroAlongAt ho
      hbound T hT
  obtain ⟨-, -, -, hcos⟩ := CompanionOpen.companionOf_reduction hn h.isWellFormed h.isNonzeroAlongAt ho hbound T hT
  refine ⟨hT𝔫, hb, ?_⟩
  rw [hcos]
  rintro z ⟨hz1, hz2⟩
  refine ⟨?_, hz2⟩
  have hz1' : z ∈ cosupport n (geoTransformAlong 𝔫 T).N
      (geoTransformAlong (⟨𝔫.N, 𝔫.E, nonmonomialPartAlong n 𝔫.N 𝔫.ideal 𝔫.E, o⟩ : MarkedIdeal n Z) T).ideal o := by
    have h1 := hz1
    simp only [MarkedIdeal.cosupp, d_geoTransformAlong] at h1
    rw [hNeq] at h1
    exact h1
  exact MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hR o hz1'

/-- **The order does not go up over a centre of constant order** (`𝔫` in the domain, `n > 0`): if the centre `C` of a
test blowup lies in `{ord ≥ q}` and misses `{ord ≥ q + 1}` (`q ≥ 1`), every point of the cosupport of the transform over
`C` has order `≤ q`.  On the open set `W = {ord ≤ q}` the blowup is a test blowup of the companion ideal `𝓞(𝔫|_W, q)`
(its cosupport is `{ord ≥ q} ∩ cosupp`), along which the order stays `≤ q` (`companionOf_tower_facts`). -/
theorem notMem_ordGe_geoTransform_of_mem (hn : 0 < n) {Y Z : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Y}
    (h : IsInvDomain k 𝔫) {C : Set Y} (hC : 𝔫.IsAdmissibleCentre C) {π : Z → Y} (hπ : IsBlowupAlong n C π)
    {q : ℕ} (hq : 1 ≤ q) (hCq : C ⊆ ordGe 𝔫 q) (hCq' : Disjoint C (ordGe 𝔫 (q + 1))) {z : Z}
    (hz : z ∈ (𝔫.geoTransform C π).cosupp) (hzC : π z ∈ C) : z ∉ ordGe (𝔫.geoTransform C π) (q + 1) := by
  set W : Opens Y :=
    ⟨(ordGe 𝔫 (q + 1))ᶜ, (isClosed_ordGe hn h.isWellFormed h.isNonzeroAlongAt (q + 1)).isOpen_compl⟩ with hWdef
  have hCW : C ⊆ (W : Set Y) := fun x hx => Set.disjoint_left.mp hCq' hx
  have hT : IsGeoTestTower 𝔫 (.step .refl C π hπ) := (isGeoTestTower_step_iff 𝔫 _ C π hπ).mpr ⟨trivial, hC⟩
  have hW := InvDomainTowerAlong.isInvDomain_pullback_val W h
  have hbound : ∀ x ∈ (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).cosupp,
      x ∉ ordGe (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫) (q + 1) :=
    fun x _ hx => x.2 ((mem_ordGe_pullback_val_iff hn h.isWellFormed h.isNonzeroAlongAt W (q + 1) x).mp hx)
  have hres := isGeoTestTower_restrict W h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent _ hT
  obtain ⟨-, hadm⟩ := (isGeoTestTower_step_iff _ _ _ _ _).mp hres
  -- the trace of `C` is an admissible centre of the companion ideal on `W`
  have hadmO : (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫) q).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' C) := by
    refine ⟨hadm.1, ?_, ?_⟩
    · obtain ⟨-, -, -, hcos⟩ := CompanionOpen.companionOf_reduction (X := CMfd.of (n := n) W) hn hW.isWellFormed
        hW.isNonzeroAlongAt hq hbound .refl trivial
      intro x hx
      have hx' : x ∈ (geoTransformAlong (companionOf n (M := CMfd.of (n := n) W)
          (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫) q) .refl).cosupp := by
        rw [hcos]
        refine ⟨?_, hadm.2.1 hx⟩
        exact (mem_ordGe_pullback_val_iff hn h.isWellFormed h.isNonzeroAlongAt W q x).mpr (hCq hx)
      exact hx'
    · rw [companionAlong_E]
      exact hadm.2.2
  -- so the restricted blowup is a test blowup of the companion ideal on `W`
  have hTW : IsGeoTestTower (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫) q)
      (restrict W (.step .refl C π hπ)) :=
    (isGeoTestTower_step_iff _ _ _ _ _).mpr ⟨trivial, hadmO⟩
  obtain ⟨-, hb, -⟩ := companionOf_tower_facts (Z := CMfd.of (n := n) W) hn hW hq hbound _ hTW
  rw [geoTransformAlong_restrict W h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent _ hT] at hb
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h _ hT
  let z' : openPreimage (.step (.refl : BlowupTower Y Y) C π hπ) W := ⟨z, hCW hzC⟩
  have hz' : z' ∈ (MarkedIdeal.pullback (Subtype.val : openPreimage (.step .refl C π hπ) W → Z)
      (geoTransformAlong 𝔫 (.step .refl C π hπ))).cosupp := by
    rw [cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hdomT.isWellFormed.isCoherent hg)]
    exact hz
  intro hzq
  exact hb z' hz' ((mem_ordGe_pullback_val_iff hn hdomT.isWellFormed hdomT.isNonzeroAlongAt _ (q + 1) z').mpr hzq)

/-- **The order does not go up over a centre of constant order**, as a bound on `nmOrd`. -/
theorem nmOrd_geoTransform_le_of_mem (hn : 0 < n) {Y Z : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Y}
    (h : IsInvDomain k 𝔫) {C : Set Y} (hC : 𝔫.IsAdmissibleCentre C) {π : Z → Y} (hπ : IsBlowupAlong n C π)
    {q : ℕ} (hq : 1 ≤ q) (hCq : C ⊆ ordGe 𝔫 q) (hCq' : Disjoint C (ordGe 𝔫 (q + 1))) {z : Z}
    (hz : z ∈ (𝔫.geoTransform C π).cosupp) (hzC : π z ∈ C) : nmOrd (𝔫.geoTransform C π) z ≤ q :=
  nmOrd_le_of_notMem (notMem_ordGe_geoTransform_of_mem hn h hC hπ hq hCq hCq' hz hzC)

end Companion

end

end Hironaka.NonmonomialOrderLocal
