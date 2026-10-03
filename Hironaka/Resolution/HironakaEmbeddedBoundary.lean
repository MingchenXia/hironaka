/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Resolution.HironakaPrincipalizationBoundary
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Coherence.CartanIrreducible
import Hironaka.Invariant.CodimOneAdmissibleAlong
import Hironaka.Resolution.EmbeddedFromResolution
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Hironaka.Resolution.HironakaFromSeqInvariant
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Resolution.HironakaPrincipalization
import Hironaka.Resolution.HironakaRelativelyCompact
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Blowup.SimultaneousNormalCrossings
import Hironaka.Invariant.SmoothCentreHomogeneity
import Hironaka.Invariant.SmoothCentreInvariant
import Hironaka.Invariant.SmoothCentreLocus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution relative to a simple normal crossings boundary (Hironaka)

Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), Theorem 1.6 and (1.9) (embedded
desingularization by admissible blowups, the centres having normal crossings with the accumulated divisor; in 1.6
(1) a centre may lie in `X_j ∩ E_j` once the strict transform `X_j` is smooth); Kollár 2007 (`kollar07-resolution`),
"Principalization, III" (an initial simple normal crossings divisor `E`); Włodarczyk 2005 (`wlodarczyk05-hironaka`).

**Statement.**  Let `X` be a complex manifold, `E₀` a divisor on `X` with simple normal crossings, and `W ⊆ X` an analytic set of
pure dimension `d < n` (possibly reducible), no member of `E₀` containing a nonempty relatively open subset of `W`
(`W ⊆ closure (W \ |E₀|)`), with `W` compact (or `X` compact).  Put `F = W_sing ∪ (W ∩ |E₀|)`, where
`W_sing = W \ regularLocus W d`.  There are an admissible blowup sequence `f : X' → X` of `(X, E₀)` with centres over `F` and
accumulated divisor `E` (its first `|E₀|` members are the strict transforms of the members of `E₀`) such that

* `E` has simple normal crossings;
* `Exc f ⊆ ⋃ (the members of E created by the blowups) ⊆ f⁻¹ F`, and `f⁻¹(W_sing) ⊆ Exc f`;
* `f` is an isomorphism over `X \ F`;
* the strict transform of `W` is a closed submanifold of `X'`, of dimension `d` at each of its points, with only normal crossings
  with `E`.

**What is not claimed.**  `f` may blow up smooth points of `W` lying on `|E₀|` (as Bierstone--Milman's Theorem 1.6 (1) may blow
up points of `X_j ∩ E_j` once `X_j` is smooth): the stronger form in which `f` is an isomorphism over every point where `W` is
smooth and has normal crossings with `E₀` would need the canonical invariant of `(X, X, E₀, 𝓘_W, 1)` to be constant along
`W_reg` across the strata of `E₀`, which is not proved.  With `E₀ = []` the theorem is
`HironakaEmbeddedReducible.exists_embeddedResolution_pure_of_isCompact`, whose conclusions are then sharper (`F = W_sing`).

**Route.**  `(X, X, E₀, 𝓘_W, 1)` lies in the domain (Cartan's coherence of `𝓘_W`; `E₀` is transverse to `X`).  Its canonical
resolution (compact cosupport) is cut before the first centre meeting the preimage of the open set `O = X \ (W_sing ∪ |E₀|)`,
on which `W` is smooth of dimension `d` and dense.  The one new point is the homogeneity of the invariant over `O`: the
restriction of `E₀` to `O` is a list of EMPTY members, and the homogeneity step of `EmbeddedFromResolution` (the biholomorphisms
of `SmoothCentreHomogeneity.exists_smoothCentre_iso`) holds verbatim for a marked ideal whose divisor has only empty members,
since a biholomorphism pulls such a list back to itself (`pullback_pullback_val_mk_of_forall_eq_empty`).  So the invariant is
constant on the cosupport over `O` while the centres miss `O`, the first centre meeting `O` contains there exactly the preimage
of `W`, and the identity-principle step `HironakaEmbeddedResolutionLocal.strictTransform_of_centresAvoid` (no marked ideal
involved) makes the strict transform smooth.  The support of the exceptional divisor is the union of the new members
(`HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop`).

## Main results

* `pullback_val_mk_vanishingIdeal`, `cosupp_mk_vanishingIdeal`, `pullback_pullback_val_mk_of_forall_eq_empty`;
* `inv_refl_eq_of_regularAtDim_of_forall_eq_empty`, `inv_eq_of_isEmptyTower_of_pureDim_of_forall_eq_empty`,
  `inv_eq_over_open_of_isEmptyTower_of_pureDim_of_disjoint` (homogeneity with a divisor of empty members);
* `mem_cosupp_iff_of_centresAvoid`, `mem_maxLocus_iff_of_centresAvoid_of_pureDim`, `exists_tower_embedded_of_isCanonical`
  (the first-centre argument for `(X, X, E, 𝓘_W, 1)` over an open set missing the members of `E`);
* `centresOver_of_inter_subset`, `support_exceptionalDivisor_subset_of_centresOver`, `isInvDomain_boundary`,
  `subset_closure_inter_compl`;
* `exists_embeddedResolution_boundary_of_isCanonical` (the assembly);
* **`exists_embeddedResolution_boundary_of_isCompact`** (`W` compact, `X` any complex manifold),
  **`exists_embeddedResolution_boundary`** (`X` compact) and **`exists_embeddedResolution_boundary_of_subset_isCompact`** (any
  `W`, over every open set contained in a compact set, relative to the restriction of `E₀`);
* `subset_closure_diff_biUnion_of_forall_disjoint`: the density hypothesis holds when no member of `E₀` meets `W` (e.g.
  `E₀ = []`), and then `F = W_sing`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaEmbeddedBoundary

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings Hironaka.RestrictEmptyTower Hironaka.DivisorExponentAlong Hironaka.BlowupTowerTransforms Hironaka.HironakaAdmissibleSequence Hironaka.MarkedIdealBiholomorphism
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.EmbeddedFromResolution (EmbeddingFields exists_first_centre)

noncomputable section

variable {n : ℕ}

/-! ### Marked ideals of a subset with a given divisor -/

section MarkedIdeal

/-- **The cosupport of `(M, M, E, 𝓘_Z, 1)` is `Z`** (`Z` closed; the cosupport does not see the divisor). -/
theorem cosupp_mk_vanishingIdeal {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {Z : Set M} (hZ : IsClosed Z) (E : List (Set M)) :
    (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n M).cosupp = Z :=
  SmoothCentreLocus.cosupp_vanishingIdeal hZ (subset_univ Z)

/-- **`(X, X, E, 𝓘_V, 1)` restricted to an open set** is `(U, U, E|_U, 𝓘_{V ∩ U}, 1)`
(`SmoothCentreInvariant.pullback_val_smoothCentreMarked` with a divisor). -/
theorem pullback_val_mk_vanishingIdeal {X : CMfd.{u} n} (U : Opens X) (E : List (Set X)) (V : Set X) :
    MarkedIdeal.pullback (Subtype.val : U → X) (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) =
      (⟨univ, E.map ((Subtype.val : U → X) ⁻¹' ·), vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' V), 1⟩ :
        MarkedIdeal n (CMfd.of (n := n) U)) := by
  show (⟨(Subtype.val : U → X) ⁻¹' univ, E.map ((Subtype.val : U → X) ⁻¹' ·),
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) V), 1⟩ :
      MarkedIdeal n (CMfd.of (n := n) U)) = _
  rw [preimage_univ, SmoothCentreHomogeneity.pullback_val_vanishingIdeal U V]

/-- **The homogeneity biholomorphisms respect a divisor of empty members**: if `Φ : U₁ ≅ U₂` pulls
`(M, M, ∅, 𝓘_Z, d)|_{U₂}` back to `(M, M, ∅, 𝓘_Z, d)|_{U₁}`, it pulls `(M, M, E, 𝓘_Z, d)|_{U₂}` back to
`(M, M, E, 𝓘_Z, d)|_{U₁}` for every list `E` of empty sets. -/
theorem pullback_pullback_val_mk_of_forall_eq_empty {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {Z : Set M} {E : List (Set M)} (hE : ∀ H ∈ E, H = ∅)
    {d : ℕ} {U₁ U₂ : Opens M}
    (Φ : CMfd.of (n := n) U₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U₂)
    (hpb : MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U₂ → M)
          (⟨univ, [], vanishingIdeal (n := n) Z, d⟩ : MarkedIdeal n M)) =
        MarkedIdeal.pullback (Subtype.val : U₁ → M) (⟨univ, [], vanishingIdeal (n := n) Z, d⟩ : MarkedIdeal n M)) :
    MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U₂ → M)
          (⟨univ, E, vanishingIdeal (n := n) Z, d⟩ : MarkedIdeal n M)) =
        MarkedIdeal.pullback (Subtype.val : U₁ → M) (⟨univ, E, vanishingIdeal (n := n) Z, d⟩ : MarkedIdeal n M) := by
  have hN := congrArg MarkedIdeal.N hpb
  have hI := congrArg MarkedIdeal.ideal hpb
  have hE' : (E.map ((Subtype.val : U₂ → M) ⁻¹' ·)).map ((Φ : CMfd.of (n := n) U₁ → CMfd.of (n := n) U₂) ⁻¹' ·) =
      E.map ((Subtype.val : U₁ → M) ⁻¹' ·) := by
    rw [List.map_map]
    refine List.map_congr_left fun H hH => ?_
    simp [hE H hH]
  show (⟨_, _, _, d⟩ : MarkedIdeal n (CMfd.of (n := n) U₁)) = ⟨_, _, _, d⟩
  rw [MarkedIdeal.mk.injEq]
  exact ⟨hN, hE', hI, rfl⟩

end MarkedIdeal

/-! ### Homogeneity with a divisor of empty members -/

section Homogeneity

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Two points of a smooth centre of the same local dimension have the same value along the empty tower, for a divisor of
empty members** (`EmbeddingFields.inv_refl_eq_of_regularAtDim` with `E` a list of empty sets in place of `[]`). -/
theorem inv_refl_eq_of_regularAtDim_of_forall_eq_empty (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {Z : Set X}
    {E : List (Set X)} (hE : ∀ H ∈ E, H = ∅) (hZ : IsClosedSubmanifold n Z)
    (hdom : IsInvDomain k (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X))
    {x x' : X} {j : ℕ} (hxj : RegularAtDim (n := n) Z x j) (hx'j : RegularAtDim (n := n) Z x' j) :
    inv (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x' =
      inv (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x := by
  obtain ⟨U₁, U₂, Φ, hxU, hx'U, hΦx, -, hpb⟩ := SmoothCentreHomogeneity.exists_smoothCentre_iso hxj hx'j 1
  have hpb' := pullback_pullback_val_mk_of_forall_eq_empty hE Φ hpb
  set 𝔪 : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ with h𝔪
  have hcos : 𝔪.cosupp = Z := cosupp_mk_vanishingIdeal hZ.1 E
  have hx : x ∈ Z := hxj.2.1
  have hx' : x' ∈ Z := hx'j.2.1
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hdom.isWellFormed.isCoherent
  have h1 := hF.restrictOpen 𝔪 hdom U₁ BlowupTower.refl trivial ⟨x, hxU⟩
    (by show x ∈ 𝔪.cosupp; rw [hcos]; exact hx)
  have h2 := hF.restrictOpen 𝔪 hdom U₂ BlowupTower.refl trivial ⟨x', hx'U⟩
    (by show x' ∈ 𝔪.cosupp; rw [hcos]; exact hx')
  have hdom₂ := InvDomainTowerAlong.isInvDomain_pullback_val U₂ hdom
  have hc₂ : Φ ⟨x, hxU⟩ ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪)
      (BlowupTower.refl : BlowupTower (CMfd.of (n := n) U₂) (CMfd.of (n := n) U₂))).cosupp := by
    show Φ ⟨x, hxU⟩ ∈ (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪).cosupp
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val 𝔪 hhol U₂, hcos]
    show ((Φ ⟨x, hxU⟩ : U₂) : X) ∈ Z
    rw [hΦx]
    exact hx'
  have h3 := hF.towerIso Φ (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪) hdom₂ BlowupTower.refl BlowupTower.refl
    Φ BlowupTowerIsomorphism.IsTowerIso.refl trivial ⟨x, hxU⟩ hc₂
  rw [hpb'] at h3
  have hΦx' : Φ ⟨x, hxU⟩ = ⟨x', hx'U⟩ := Subtype.ext hΦx
  rw [hΦx'] at h3
  exact h2.symm.trans (h3.symm.trans h1)

/-- **Along a segment with only empty centres the value is constant on the cosupport of a smooth centre of pure dimension,
for a divisor of empty members** (`EmbeddingFields.inv_eq_of_isEmptyTower_of_pureDim` with such a divisor). -/
theorem inv_eq_of_isEmptyTower_of_pureDim_of_forall_eq_empty (hF : EmbeddingFields n k inv) {X : CMfd.{u} n}
    {Z : Set X} {E : List (Set X)} (hE : ∀ H ∈ E, H = ∅) (hZ : IsClosedSubmanifold n Z) {j : ℕ}
    (hpure : ∀ x ∈ Z, RegularAtDim (n := n) Z x j)
    (hdom : IsInvDomain k (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsEmptyTower T) {y y' : Y}
    (hy : y ∈ (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hy' : y' ∈ (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp) :
    inv (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T y' =
      inv (⟨univ, E, vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T y := by
  have hcos := cosupp_mk_vanishingIdeal (n := n) hZ.1 E
  obtain ⟨hm, he⟩ := hF.inv_eq_inv_refl_of_isEmptyTower _ hdom T hT y hy
  obtain ⟨hm', he'⟩ := hF.inv_eq_inv_refl_of_isEmptyTower _ hdom T hT y' hy'
  rw [hcos] at hm hm'
  rw [he, he']
  exact inv_refl_eq_of_regularAtDim_of_forall_eq_empty hF hE hZ hdom (hpure _ hm) (hpure _ hm')

/-- **Over an open set missing the members of `E`, on which the segment has only empty centres, the value on
`(X, X, E, 𝓘_V, 1)` is constant on the cosupport**, when `V ∩ U` is a closed submanifold of `U` of pure dimension
(`EmbeddingFields.inv_eq_over_open_of_isEmptyTower_of_pureDim` with a divisor: over `U` it has only empty members). -/
theorem inv_eq_over_open_of_isEmptyTower_of_pureDim_of_disjoint (hF : EmbeddingFields n k inv) {X : CMfd.{u} n}
    {V : Set X} {E : List (Set X)} (hdom : IsInvDomain k (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (U : Opens X) (hEU : ∀ H ∈ E, Disjoint H (U : Set X))
    (hZ : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' V)) {j : ℕ}
    (hpure : ∀ x ∈ (Subtype.val : U → X) ⁻¹' V, RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' V) x j)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)
      (inv (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) T)
    (hT : IsEmptyTower (restrict U T)) {p p' : openPreimage T U}
    (hp : (p : Y) ∈ (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hp' : (p' : Y) ∈ (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp) :
    inv (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T p' =
      inv (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T p := by
  have h1 := hF.restrictOpen _ hdom U T hcan p hp
  have h2 := hF.restrictOpen _ hdom U T hcan p' hp'
  have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have hTt := hF.isGeoTestTower_of_isCanonical hdom T hcan
  have hc := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent U T hTt
  have hq : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]; exact hp
  have hq' : p' ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]; exact hp'
  rw [pullback_val_mk_vanishingIdeal U E V] at h1 h2 hdomU hq hq'
  rw [← h1, ← h2]
  have hEU' : ∀ H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·), H = ∅ := by
    intro H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact (preimage_val_eq_empty_iff U H₀).mpr (hEU H₀ hH₀)
  exact inv_eq_of_isEmptyTower_of_pureDim_of_forall_eq_empty hF hEU' hZ hpure hdomU (restrict U T) hT hq hq'

end Homogeneity

/-! ### The first-centre argument with a divisor -/

section FirstCentre

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The cosupport over an open set the centres miss is the preimage of `V`** (`EmbeddedFromResolution.
mem_cosupp_iff_of_centresAvoid` for `(X, X, E, 𝓘_V, 1)`, any divisor `E`). -/
theorem mem_cosupp_iff_of_centresAvoid {X : CMfd.{u} n} {V : Set X} {E : List (Set X)} (hV : IsClosed V)
    (hdom : IsInvDomain k (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (U : Opens X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hTt : IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T) (hT : CentresAvoid U T)
    {y : Y} (hy : T.proj y ∈ U) :
    y ∈ (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp ↔ T.proj y ∈ V := by
  have hc := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent U T hTt
  have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have he : IsEmptyTower (restrict U T) := (isEmptyTower_restrict_iff U T).mpr hT
  set p : openPreimage T U := ⟨y, hy⟩ with hp
  have h1 : y ∈ (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp ↔
      p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
        (⟨univ, E, vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]
    rfl
  rw [h1, SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower _
    hdomU.isWellFormed.isClosedSubmanifold_N hdomU.isWellFormed.isCoherent (restrict U T) he p,
    pullback_val_mk_vanishingIdeal U E V, cosupp_mk_vanishingIdeal (hV.preimage continuous_subtype_val)]
  show (((restrict U T).proj p : U) : X) ∈ V ↔ _
  rw [proj_restrict]

/-- **The maximum locus over an open set missing the members of `E` on which `W` is smooth of pure dimension**
(`HironakaEmbeddedResolutionLocal.mem_maxLocus_iff_of_centresAvoid_of_pureDim` for `(X, X, E, 𝓘_W, 1)`): for a canonical
segment whose centres miss the preimages of `O`, once the maximum locus meets the preimage of `O` it contains, over `O`,
exactly the preimage of `W`. -/
theorem mem_maxLocus_iff_of_centresAvoid_of_pureDim (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {W : Set X}
    {E : List (Set X)} (hW : IsClosed W) (O : Opens X) (hEO : ∀ H ∈ E, Disjoint H (O : Set X)) {d : ℕ}
    (hpure : ∀ x : O, (x : X) ∈ W → RegularAtDim (n := n) W x d)
    (hdom : IsInvDomain k (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
      (inv (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) T)
    (hT : CentresAvoid O T) {c : Y}
    (hc : c ∈ maxLocus (inv (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
      (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hcO : T.proj c ∈ O) {y : Y} (hy : T.proj y ∈ O) :
    y ∈ maxLocus (inv (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).cosupp ↔
      T.proj y ∈ W := by
  have hTt := hF.isGeoTestTower_of_isCanonical hdom T hcan
  have hcos := mem_cosupp_iff_of_centresAvoid hW hdom O T hTt hT hy
  refine ⟨fun h => hcos.mp h.1, fun h => ?_⟩
  have hys := hcos.mpr h
  have hpure' : ∀ x ∈ (Subtype.val : O → X) ⁻¹' W,
      RegularAtDim (n := n) ((Subtype.val : O → X) ⁻¹' W) x d := fun x hx =>
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hpure x hx)
  have hZ : IsClosedSubmanifold n ((Subtype.val : O → X) ⁻¹' W) :=
    ⟨hW.preimage continuous_subtype_val, fun x hx => ⟨d, hpure' x hx⟩⟩
  have heq := inv_eq_over_open_of_isEmptyTower_of_pureDim_of_disjoint hF hdom O hEO hZ hpure' T hcan
    ((isEmptyTower_restrict_iff O T).mpr hT) (p := ⟨c, hcO⟩) (p' := ⟨y, hy⟩) hc.1 hys
  refine ⟨hys, fun y' hy' => ?_⟩
  rw [show inv (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T y =
      inv (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T c from heq]
  exact hc.2 y' hy'

/-- **Embedded resolution from a canonical resolution of `(X, X, E, 𝓘_W, 1)`** (any complex manifold `X`, a value function
with the properties `EmbeddingFields`; `HironakaAdmissibleSequence.exists_tower_embedded_of_isCanonical` with a divisor): let
`W` be analytic, `O ⊆ X` an open set missing the members of `E`, `W` regular of dimension `d` at each point of `W ∩ O` and
`W ⊆ closure (W ∩ O)`.  From a canonical segment of `(X, X, E, 𝓘_W, 1)` with empty final cosupport, the part before the first
centre meeting the preimage of `O` is a multiple test blow-up whose centres miss the preimages of `O` and whose strict
transform of `W` is a closed submanifold, regular of dimension `d` at each of its points, with only normal crossings with the
transformed divisor. -/
theorem exists_tower_embedded_of_isCanonical (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {W : Set X}
    {E : List (Set X)} (hWa : IsComplexAnalyticSubset (n := n) W) (O : Opens X) (hEO : ∀ H ∈ E, Disjoint H (O : Set X))
    {d : ℕ} (hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d) (hdense : W ⊆ closure (W ∩ O))
    (hdom : IsInvDomain k (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hcan₀ : IsCanonical (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
      (inv (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) T₀)
    (hres₀ : IsGeoResolution (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T₀) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T ∧ CentresAvoid O T ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      (∀ x ∈ strictTransform n T.proj W, RegularAtDim (n := n) (strictTransform n T.proj W) x d) ∧
      HasNormalCrossings n (strictTransform n T.proj W)
        (geoTransformAlong (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E := by
  have hTt₀ := hres₀.1
  by_cases hA : CentresAvoid O T₀
  · -- every centre misses `O`: then `W` is empty
    have hWO : ∀ x ∈ W, x ∉ O := fun x hxW hxO => by
      obtain ⟨y, rfl⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective T₀.isBlowupSequence x
      have hy := (mem_cosupp_iff_of_centresAvoid hWa.isClosed hdom O T₀ hTt₀ hA hxO).mpr hxW
      rw [hres₀.2] at hy
      exact hy
    have hW0 : W = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have h := hdense hx
      rw [show W ∩ (O : Set X) = ∅ from eq_empty_iff_forall_notMem.mpr fun y hy => hWO y hy.1 hy.2,
        closure_empty] at h
      exact h
    have hS0 : strictTransform n T₀.proj W = ∅ := by
      rw [hW0]
      simp [strictTransform]
    refine ⟨Y₀, T₀, hTt₀, hA, ?_, ?_, ?_⟩
    · rw [hS0]
      exact ⟨isClosed_empty, fun x hx => absurd hx (notMem_empty x)⟩
    · rw [hS0]
      exact fun x hx => absurd hx (notMem_empty x)
    · rw [hS0]
      exact fun x hx => absurd hx (notMem_empty x)
  · -- the first centre meeting `O`
    obtain ⟨Y', T', -, -, h1, h2, c, hc, hcU⟩ := exists_first_centre _ _ O T₀ hcan₀ hA
    have hTt' := hF.isGeoTestTower_of_isCanonical hdom T' h1
    have hadm := hF.isAdmissibleCentre_maxLocus hdom T' h1 hTt'
    have hCV := fun y (hy : T'.proj y ∈ O) =>
      mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hWa.isClosed O hEO (d := d)
        (fun x hx => hreg x hx x.2) hdom T' h1 h2 hc hcU hy
    obtain ⟨hSC, hev, hreg'⟩ :=
      HironakaEmbeddedResolutionLocal.strictTransform_of_centresAvoid hWa O hreg hdense T' h2 hadm.1 hCV
    refine ⟨Y', T', hTt', h2, ⟨isClosed_closure, fun x hx => ⟨d, hreg' x hx⟩⟩, hreg', ?_⟩
    exact CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun x hx =>
      ⟨_, hSC hx, hev x hx, hadm.2.2⟩

end FirstCentre

/-! ### Embedded resolution relative to a boundary -/

section Boundary

/-- Centres over `F` and over `G` lie over any `H ⊇ F ∩ G`. -/
theorem centresOver_of_inter_subset {X : CMfd.{u} n} {F G H : Set X} (hFG : F ∩ G ⊆ H) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver F T → CentresOver G T → CentresOver H T
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hF, hG => by
      obtain ⟨hFT, hFC⟩ : CentresOver F T ∧ C ⊆ T.proj ⁻¹' F := hF
      obtain ⟨hGT, hGC⟩ : CentresOver G T ∧ C ⊆ T.proj ⁻¹' G := hG
      exact ⟨centresOver_of_inter_subset hFG T hFT hGT, fun c hc => hFG ⟨hFC hc, hGC hc⟩⟩

/-- **If the centres of `T` lie over `F`, so does the support of the exceptional divisor of `T`**: after a blowup `π` along
`C` the support is `π⁻¹(supp E_T) ∪ π⁻¹ C`. -/
theorem support_exceptionalDivisor_subset_of_centresOver {X : CMfd.{u} n} (F : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver F T →
      (BlowupTowerTransforms.exceptionalDivisor T).support ⊆ T.proj ⁻¹' F
  | _, .refl, _ => by
      intro x hx
      exact absurd (hx (fun _ => (1 : ℂ)) (holomorphicAt_const 1)) one_ne_zero
  | _, .step T C π hπ, h => by
      obtain ⟨hT, hC⟩ : CentresOver F T ∧ C ⊆ T.proj ⁻¹' F := h
      have ih := support_exceptionalDivisor_subset_of_centresOver F T hT
      show (GermIdealTotalTransform.EffectiveDivisor.add
          (BlowupExceptionalDivisor.totalTransform hπ (BlowupTowerTransforms.exceptionalDivisor T))
          (BlowupExceptionalDivisor.exceptionalDivisor hπ)).support ⊆ _
      rw [HironakaPrincipalization.support_add, BlowupExceptionalDivisor.support_totalTransform,
        BlowupExceptionalDivisor.support_exceptionalDivisor]
      rintro z (hz | hz)
      · exact ih hz
      · exact hC hz

/-- **`(X, X, E₀, 𝓘_W, 1)` lies in the domain** for an analytic `W` with empty interior and a divisor `E₀` with simple normal
crossings (Cartan's coherence of `𝓘_W`; `E₀` is transverse to `X`). -/
theorem isInvDomain_boundary {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W = ∅)
    {E₀ : List (Set M)} (hE₀ : IsSNCDivisor n E₀) :
    IsInvDomain n (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n M) where
  isWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hWa, hE₀,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE₀⟩
  dimLE := fun x _ => ⟨n, le_rfl, AnalyticIrreducibleComponents.regularAtDim_univ x⟩
  one_le_d := le_rfl
  isNonzeroAlongAt := fun x _ =>
    HironakaEmbeddedReducible.isNonzeroAlongAt_vanishingIdeal_of_interior_eq_empty hWa hint x

/-- **The regular points of `W` off a closed set `F` are dense in `W`** when the regular points of dimension `d` are dense and
no nonempty relatively open subset of `W` lies in `F`. -/
theorem subset_closure_inter_compl {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] {W : Set M}
    {d : ℕ} (hpure : W ⊆ closure (regularLocus (n := n) W d)) {F : Set M} (hF : IsClosed F)
    (hWF : W ⊆ closure (W \ F)) :
    W ⊆ closure (W ∩ (W \ regularLocus (n := n) W d ∪ F)ᶜ) := by
  intro x hx
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨y, hyU, hyW, hyF⟩ := mem_closure_iff.mp (hWF hx) U hU hxU
  obtain ⟨z, ⟨hzU, hzF⟩, hzr⟩ :=
    mem_closure_iff.mp (hpure hyW) (U ∩ Fᶜ) (hU.inter hF.isOpen_compl) ⟨hyU, hyF⟩
  exact ⟨z, hzU, regularLocus_subset _ _ hzr, fun h => h.elim (fun h' => h'.2 hzr) hzF⟩

/-- The union of the members of a divisor with closed members is closed. -/
theorem isClosed_biUnion_of_forall_isClosed {M : Type*} [TopologicalSpace M] {E : List (Set M)}
    (hE : ∀ H ∈ E, IsClosed H) : IsClosed (⋃ H ∈ E, H) := by
  have : (⋃ H ∈ E, H) = ⋃ H ∈ {H | H ∈ E}, H := rfl
  rw [this]
  exact (List.finite_toSet E).isClosed_biUnion fun H hH => hE H hH

/-- **Embedded resolution relative to a boundary, from a canonical resolution** (the assembly): let `X` be any complex
manifold, `E₀` a divisor on `X` with simple normal crossings and `W ⊆ X` an analytic set of pure dimension `d < n` with
`W ⊆ closure (W \ |E₀|)`.  From a canonical resolution of `(X, X, E₀, 𝓘_W, 1)` (by the canonical invariant) one gets an
admissible blowup sequence `f : X' → X` of `(X, E₀)` with centres over `F = W_sing ∪ (W ∩ |E₀|)` and divisor `E` such that `E`
has simple normal crossings, `Exc f ⊆ ⋃ (new members) ⊆ f⁻¹ F`, `f⁻¹(W_sing) ⊆ Exc f`, `f` is an isomorphism over `X \ F`,
and the strict transform of `W` is a closed submanifold, regular of dimension `d` at each of its points, with only normal
crossings with `E`. -/
theorem exists_embeddedResolution_boundary_of_isCanonical {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower (CMfd.of (n := n) X) Y₀)
    (hcan₀ : IsCanonical (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X))
      ((CanonicalCentres.canonicalInvariant.{u} n).inv
        (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X))) T₀)
    (hres₀ : IsGeoResolution (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X)) T₀) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E := by
  set 𝔪 : MarkedIdeal n (CMfd.of (n := n) X) := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ with h𝔪
  have hdom : IsInvDomain n 𝔪 := isInvDomain_boundary (M := CMfd.of (n := n) X) hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  have hcl : IsClosed (W \ regularLocus (n := n) W d ∪ ⋃ H ∈ E₀, H) :=
    (HironakaEmbeddedReducible.isClosed_diff_regularLocus hWa.isClosed d).union
      (isClosed_biUnion_of_forall_isClosed hE₀.1)
  let O : Opens (CMfd.of (n := n) X) := ⟨(W \ regularLocus (n := n) W d ∪ ⋃ H ∈ E₀, H)ᶜ, hcl.isOpen_compl⟩
  have hEO : ∀ H ∈ E₀, Disjoint H (O : Set X) := fun H hH =>
    disjoint_left.mpr fun x hxH hxO => hxO (Or.inr (mem_biUnion hH hxH))
  have hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d := fun x hxW hxO => by
    by_contra h
    exact hxO (Or.inl ⟨hxW, h⟩)
  have hdense : W ⊆ closure (W ∩ O) :=
    subset_closure_inter_compl hpure (isClosed_biUnion_of_forall_isClosed hE₀.1) hE₀W
  obtain ⟨Y, T, hTt, hT, hSsub, hregS, hnc⟩ := exists_tower_embedded_of_isCanonical
    (HironakaFromSeqInvariant.embeddingFields_of_seq (CanonicalCentres.canonicalInvariant.{u} n))
    hWa O hEO hreg hdense hdom T₀ hcan₀ hres₀
  set F : Set X := W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H with hFdef
  have hcos : 𝔪.cosupp = W := cosupp_mk_vanishingIdeal hWa.isClosed E₀
  have hover : CentresOver F T := by
    refine centresOver_of_inter_subset (F := 𝔪.cosupp) (G := ((O : Set X)ᶜ)) ?_ T
      (centresOver_cosupp 𝔪 hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent T hTt)
      (centresOver_compl_of_centresAvoid O T hT)
    rintro x ⟨hxW, hxO⟩
    rw [hcos] at hxW
    have hxO' : x ∈ W \ regularLocus (n := n) W d ∪ ⋃ H ∈ E₀, H := not_not.mp hxO
    rcases hxO' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hxW, h⟩
  have hsuppF := support_exceptionalDivisor_subset_of_centresOver F T hover
  have hsupp := HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop 𝔪 hE₀.1 T
  have hexc := HironakaPrincipalization.exceptionalLocus_subset_support T
  have hadm := isAdmissibleBlowupSequence_proj 𝔪 F T hTt hover
  have hsnc := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom T hTt).isWellFormed.isSNCDivisor
  have hsub := HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus T.contMDiff_proj
    hWa.isClosed hregS
  have hExcF : T.proj '' exceptionalLocus n T.proj ⊆ F := by
    rintro x ⟨z, hz, rfl⟩
    exact hsuppF (hexc hz)
  refine ⟨Y, inferInstance, inferInstance, inferInstance, T.proj, _, hadm, hsnc, ?_, ?_, hsub,
    HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence hExcF,
    ⟨isClosed_closure, fun x hx => ⟨d, hregS x hx⟩⟩, hregS, hnc⟩
  · rw [← hsupp]
    exact hexc
  · rw [← hsupp]
    exact hsuppF

/-- **Embedded resolution relative to a simple normal crossings boundary** (Hironaka;
`hir:embedded-resolution-boundary`, embedded half): let `X` be any complex manifold, `E₀` a divisor on `X` with
simple normal crossings, and `W ⊆ X` a compact analytic set of pure dimension `d < n` (possibly reducible) such that
no member of `E₀` contains a nonempty relatively open subset of `W`. Put `F = W_sing ∪ (W ∩ |E₀|)`. There are an
admissible blowup sequence `f: X' → X` of `(X, E₀)` with centres over `F` and its accumulated divisor `E` (the
strict transforms of the members of `E₀`, then the new members) such that `E` has simple normal crossings, `Exc f ⊆
⋃ (new members) ⊆ f⁻¹ F`, `f⁻¹(W_sing) ⊆ Exc f`, `f` is an isomorphism over `X \ F`, and the strict transform of `W`
is a closed submanifold of `X'`, of dimension `d` at each of its points, with only normal crossings with `E`. -/
theorem exists_embeddedResolution_boundary_of_isCompact {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E := by
  have hdom : IsInvDomain n (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X)) :=
    isInvDomain_boundary (M := CMfd.of (n := n) X) hWa (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  have hcos : (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X)).cosupp = W :=
    cosupp_mk_vanishingIdeal hWa.isClosed E₀
  obtain ⟨Y₀, T₀, hcan₀, hres₀⟩ := exists_isGeoResolution_isCanonical_of_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) hdom (by rw [hcos]; exact hK)
  exact exists_embeddedResolution_boundary_of_isCanonical hWa hd hpure hE₀ hE₀W T₀ hcan₀ hres₀

/-- **Embedded resolution relative to a simple normal crossings boundary in a compact manifold** (`X` compact; embedded
half). -/
theorem exists_embeddedResolution_boundary {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ}
    (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  exists_embeddedResolution_boundary_of_isCompact hWa hWa.isClosed.isCompact hd hpure hE₀ hE₀W

/-- **The density hypothesis holds when no member of `E₀` meets `W`** (for instance `E₀ = []`); then
`W ∩ |E₀| = ∅` and the set `F` of the theorems above is `W_sing`. -/
theorem subset_closure_diff_biUnion_of_forall_disjoint {M : Type*} [TopologicalSpace M] {W : Set M}
    {E₀ : List (Set M)} (h : ∀ H ∈ E₀, Disjoint H W) : W ⊆ closure (W \ ⋃ H ∈ E₀, H) := by
  intro x hx
  refine subset_closure ⟨hx, ?_⟩
  simp only [mem_iUnion, not_exists]
  intro H hH hxH
  exact disjoint_left.mp (h H hH) hxH hx

/-- The preimage of the union of the members of a list is the union of the preimages. -/
theorem preimage_biUnion_list {α β : Type*} (f : α → β) (E : List (Set β)) :
    f ⁻¹' (⋃ H ∈ E, H) = ⋃ H ∈ E.map (f ⁻¹' ·), H := by
  ext x
  simp only [mem_preimage, mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨H, hH, hx⟩
    exact ⟨f ⁻¹' H, ⟨H, hH, rfl⟩, hx⟩
  · rintro ⟨_, ⟨H, hH, rfl⟩, hx⟩
    exact ⟨H, hH, hx⟩

/-- **Embedded resolution relative to a simple normal crossings boundary over a relatively compact open set** (embedded
half): let `X` be any complex manifold, `E₀` a divisor on `X` with simple normal crossings, `W ⊆ X` an analytic set
of pure dimension `d < n` (no compactness) with `W ⊆ closure (W \ |E₀|)`, and `X₀ ⊆ X` an open set contained in a
compact set. The conclusions of `exists_embeddedResolution_boundary_of_isCompact` hold for `W ∩ X₀` in `X₀`,
relative to the restriction of `E₀`, with centres over `F ∩ X₀`. -/
theorem exists_embeddedResolution_boundary_of_subset_isCompact {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (X₀ : Opens X) {K : Set X} (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ (E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·))
        ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) X₀' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆
        f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) ∧
      f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d)) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) x d) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E := by
  have hdom : IsInvDomain n (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X)) :=
    isInvDomain_boundary (M := CMfd.of (n := n) X) hWa (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  obtain ⟨Y₀, T₀, hcan₀, hres₀⟩ := HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) hdom (X := CMfd.of (n := n) X) hK X₀ hX₀
  have hdom₀ := InvDomainTowerAlong.isInvDomain_pullback_val X₀ hdom
  rw [pullback_val_mk_vanishingIdeal (X := CMfd.of (n := n) X) X₀ E₀ W] at hcan₀ hres₀ hdom₀
  set W₀ : Set X₀ := (Subtype.val : X₀ → X) ⁻¹' W with hW₀def
  set E₀' : List (Set X₀) := E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·) with hE₀'def
  have hWa₀ : IsComplexAnalyticSubset (n := n) W₀ :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWa
  have hopen := X₀.isOpen.isOpenMap_subtype_val
  have hpure₀ : W₀ ⊆ closure (regularLocus (n := n) W₀ d) := by
    intro x hx
    have h1 : (x : X) ∈ closure (regularLocus (n := n) W d) := hpure hx
    have h3 : x ∈ closure ((Subtype.val : X₀ → X) ⁻¹' regularLocus (n := n) W d) :=
      (Set.ext_iff.mp (hopen.preimage_closure_eq_closure_preimage continuous_subtype_val _) x).mp h1
    refine closure_mono (fun y hy => ?_) h3
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hy
  have hE₀'snc : IsSNCDivisor n E₀' := hdom₀.isWellFormed.isSNCDivisor
  have hU : (Subtype.val : X₀ → X) ⁻¹' (⋃ H ∈ E₀, H) = ⋃ H ∈ E₀', H := preimage_biUnion_list _ E₀
  have hE₀W₀ : W₀ ⊆ closure (W₀ \ ⋃ H ∈ E₀', H) := by
    intro x hx
    have h1 : (x : X) ∈ closure (W \ ⋃ H ∈ E₀, H) := hE₀W hx
    have h3 : x ∈ closure ((Subtype.val : X₀ → X) ⁻¹' (W \ ⋃ H ∈ E₀, H)) :=
      (Set.ext_iff.mp (hopen.preimage_closure_eq_closure_preimage continuous_subtype_val _) x).mp h1
    rwa [preimage_sdiff, hU] at h3
  have hF : (Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) =
      W₀ \ regularLocus (n := n) W₀ d ∪ W₀ ∩ ⋃ H ∈ E₀', H := by
    rw [preimage_union, preimage_inter, hU, HironakaEmbeddedReducible.preimage_val_diff_regularLocus X₀ W d]
  have hS : (Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d) = W₀ \ regularLocus (n := n) W₀ d :=
    HironakaEmbeddedReducible.preimage_val_diff_regularLocus X₀ W d
  have hlen : E₀'.length = E₀.length := List.length_map _
  rw [hF, hS, ← hlen]
  exact exists_embeddedResolution_boundary_of_isCanonical (X := X₀) hWa₀ hd hpure₀ hE₀'snc hE₀W₀ T₀ hcan₀ hres₀

end Boundary

end

end Hironaka.HironakaEmbeddedBoundary
