import Hironaka.Invariant.SmoothCentreHomogeneity
import Hironaka.Invariant.SmoothCentreLocus
import Hironaka.Invariant.ResolutionInvariantExt

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A resolution invariant is constant along a smooth centre

The first claim of `hir:smooth-centre` (`blueprint/src/hironaka.tex`, Hironaka phase H4, TN-CLASSICAL's node), landed by
TN23 as a by-product of the homogeneity of a smooth centre (`SmoothCentreHomogeneity`), on TN-CLASSICAL's invitation
(I-0981 C-0098; claim C-0100): for a resolution invariant `R` (`ResolutionInvariantExt.ResolutionInvariant`) and the marked
ideal `(X, X, ∅, 𝓘_Z, 1)` of a closed submanifold `Z` in the domain, the value of `R` along the empty tower is locally
constant on `Z`, hence constant on `Z` when `Z` is preconnected.  Blueprint `mc:smooth-centre-invariant`
(`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005 (arXiv `hiron.tex`), functoriality of the canonical
resolution for étale morphisms (`pr:resol` (4)).

Proof: near two close points `x, x'` of `Z` a translation along `Z` is a biholomorphism `Φ : U₁ ≅ U₂` with `Φ x = x'` and
`Φ^*(𝔪|_{U₂}) = 𝔪|_{U₁}` (`SmoothCentreHomogeneity.exists_smoothCentre_homogeneity`); property (5) (`restrictOpen`) at `x`
and `x'` and property (6) (`towerIso`) for the empty towers over `Φ` compare the values.  The cosupport is `Z` and the
restrictions stay in the domain (TN3's `SmoothCentreLocus.cosupp_vanishingIdeal`, `InvDomainTowerAlong.isInvDomain_pullback_val`).

## Main results

* `inv_refl_locallyConstant`: `R.inv (X, X, ∅, 𝓘_Z, 1) refl` is locally constant on `Z`;
* `inv_refl_eq_of_isPreconnected`: it is constant on a preconnected `Z`;
* the second claim of `hir:smooth-centre` (claim I-0981 C-0137): `mem_cosupp_geoTransformAlong_of_isEmptyTower` (along a tower
  with only empty centres the cosupport is the preimage of the cosupport), `inv_eq_inv_refl_of_isEmptyTower` (along such a
  segment `R` is `R` of the empty tower composed with the projection, by property (4)),
  `inv_eq_of_isEmptyTower_of_isPreconnected` (for a preconnected `Z` it is constant on the cosupport) and
  `maxLocus_eq_cosupp_of_isEmptyTower` (so the maximum locus after such a segment is the whole cosupport).
* without connectedness, for a smooth centre of pure dimension (the homogeneous local model,
  `SmoothCentreHomogeneity.exists_smoothCentre_iso`; claim I-0981 C-0141): `inv_refl_eq_of_regularAtDim`,
  `inv_refl_eq_of_pureDim`, `inv_eq_of_isEmptyTower_of_pureDim`, `maxLocus_eq_cosupp_of_isEmptyTower_of_pureDim`.
* the smooth part of a subvariety (the middle step of `hir:embedded-from-resolution`; claim I-0981 C-0143):
  `pullback_val_smoothCentreMarked`, `inv_eq_over_open_of_isEmptyTower` (+ `_of_pureDim`): over an open `U` on which `V` is a
  closed preconnected (or pure-dimensional) submanifold and the canonical segment has only empty centres, the invariant of
  `(X, X, ∅, 𝓘_V, 1)` is constant on the cosupport; `mem_maxLocus_over_open_of_isEmptyTower`: a maximum-locus point over `U`
  forces the whole cosupport over `U` into the maximum locus.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.SmoothCentreInvariant

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowerTransforms
  BlowupTowerIsomorphism SmoothCentreHomogeneity
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **A resolution invariant is locally constant along a smooth centre**: for a closed submanifold `Z` of `X` with
`(X, X, ∅, 𝓘_Z, 1)` in the domain of `R`, every `x ∈ Z` has an open neighbourhood `W` such that the value of `R` along the
empty tower at every `x' ∈ Z ∩ W` is its value at `x`. -/
theorem inv_refl_locallyConstant (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) {X : CMfd.{u} n}
    {Z : Set X} (hZ : IsClosedSubmanifold n Z)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X)) {x : X} (hx : x ∈ Z) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∀ x' ∈ Z ∩ W,
      R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x' =
        R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x := by
  set 𝔪 : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ with h𝔪
  have hcos : 𝔪.cosupp = Z := SmoothCentreLocus.cosupp_vanishingIdeal hZ.1 (subset_univ Z)
  obtain ⟨j, hj⟩ := hZ.2 x hx
  obtain ⟨W, hWo, hxW, hW⟩ := exists_smoothCentre_homogeneity hj 1
  refine ⟨W, hWo, hxW, fun x' hx' => ?_⟩
  obtain ⟨U₁, U₂, Φ, hxU, hx'U, hΦx, -, hpb⟩ := hW x' hx'
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hdom.isWellFormed.isCoherent
  -- property (5) at `x` and at `x'`
  have h1 := R.restrictOpen 𝔪 hdom U₁ BlowupTower.refl trivial ⟨x, hxU⟩ (by show x ∈ 𝔪.cosupp; rw [hcos]; exact hx)
  have h2 := R.restrictOpen 𝔪 hdom U₂ BlowupTower.refl trivial ⟨x', hx'U⟩
    (by show x' ∈ 𝔪.cosupp; rw [hcos]; exact hx'.1)
  -- property (6) for the empty towers over `Φ`
  have hdom₂ := InvDomainTowerAlong.isInvDomain_pullback_val U₂ hdom
  have hc₂ : Φ ⟨x, hxU⟩ ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪)
      (BlowupTower.refl : BlowupTower (CMfd.of (n := n) U₂) (CMfd.of (n := n) U₂))).cosupp := by
    show Φ ⟨x, hxU⟩ ∈ (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪).cosupp
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val 𝔪 hhol U₂, hcos]
    show ((Φ ⟨x, hxU⟩ : U₂) : X) ∈ Z
    rw [hΦx]
    exact hx'.1
  have h3 := R.towerIso Φ (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪) hdom₂ BlowupTower.refl BlowupTower.refl Φ
    IsTowerIso.refl trivial ⟨x, hxU⟩ hc₂
  rw [hpb] at h3
  have hΦx' : Φ ⟨x, hxU⟩ = ⟨x', hx'U⟩ := Subtype.ext hΦx
  rw [hΦx'] at h3
  exact h2.symm.trans (h3.symm.trans h1)

/-- **A resolution invariant is constant along a preconnected smooth centre** (the first claim of `hir:smooth-centre`): for
a closed preconnected submanifold `Z` of `X` with `(X, X, ∅, 𝓘_Z, 1)` in the domain of `R`, the value of `R` along the
empty tower is the same at all points of `Z` (`= cosupp (X, X, ∅, 𝓘_Z, 1)`). -/
theorem inv_refl_eq_of_isPreconnected (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) {X : CMfd.{u} n}
    {Z : Set X} (hZ : IsClosedSubmanifold n Z) (hconn : IsPreconnected Z)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X)) {x x' : X} (hx : x ∈ Z)
    (hx' : x' ∈ Z) :
    R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x' =
      R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x := by
  set g : Z → Λ := fun z =>
    R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) z with hg
  have hloc : IsLocallyConstant g := by
    refine (IsLocallyConstant.iff_eventually_eq g).mpr fun z => ?_
    obtain ⟨W, hWo, hzW, hW⟩ := inv_refl_locallyConstant R hZ hdom z.2
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds (hWo.mem_nhds hzW)] with z' hz'
    exact hW z' ⟨z'.2, hz'⟩
  have := isPreconnected_iff_preconnectedSpace.mp hconn
  exact hloc.apply_eq_of_preconnectedSpace ⟨x', hx'⟩ ⟨x, hx⟩

/-! ### Segments with only empty centres (the second claim of `hir:smooth-centre`) -/

open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower isCanonical_of_isEmptyTower)

/-- **Along a tower with only empty centres the cosupport is the preimage of the cosupport** (`𝔪` with a closed submanifold
`N` and a coherent ideal; one step at a time, `TransformOffCentre.mem_cosupp_geoTransform_iff`). -/
theorem mem_cosupp_geoTransformAlong_of_isEmptyTower {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T → ∀ y : Y,
      y ∈ (geoTransformAlong 𝔪 T).cosupp ↔ T.proj y ∈ 𝔪.cosupp
  | _, .refl, _, _ => Iff.rfl
  | _, .step T C π hπ, hT, y => by
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := hT
      subst hC
      obtain ⟨hNT, hcT⟩ := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T
        (isGeoTestTower_of_isEmptyTower 𝔪 T hT)
      rw [geoTransformAlong_step, TransformOffCentre.mem_cosupp_geoTransform_iff _ hNT.1
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcT) hπ (notMem_empty _),
        mem_cosupp_geoTransformAlong_of_isEmptyTower 𝔪 hN h𝔞 T hT (π y)]
      rfl

/-- **Along a segment with only empty centres the invariant is that of the empty tower** (property (4) of
`ResolutionInvariantExt.ResolutionInvariant`, one step at a time; such a segment is canonical): for `𝔪` in the domain of `R`
and `T` with only empty centres, at every point `y` of `cosupp 𝔪_T` the image `T.proj y` lies in `cosupp 𝔪` and
`R.inv 𝔪 T y = R.inv 𝔪 refl (T.proj y)`. -/
theorem inv_eq_inv_refl_of_isEmptyTower (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (h : IsInvDomain k 𝔪) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T → ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp,
      T.proj y ∈ 𝔪.cosupp ∧ R.inv 𝔪 T y = R.inv 𝔪 (BlowupTower.refl : BlowupTower X X) (T.proj y)
  | _, .refl, _, y, hy => ⟨hy, rfl⟩
  | _, .step T C π hπ, hT, y, hy => by
      have hT' := hT
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := hT
      have hiff := mem_cosupp_geoTransformAlong_of_isEmptyTower 𝔪 h.isWellFormed.isClosedSubmanifold_N
        h.isWellFormed.isCoherent (.step T C π hπ) hT' y
      have hπy : π y ∈ (geoTransformAlong 𝔪 T).cosupp :=
        (mem_cosupp_geoTransformAlong_of_isEmptyTower 𝔪 h.isWellFormed.isClosedSubmanifold_N
          h.isWellFormed.isCoherent T hT (π y)).mpr (hiff.mp hy)
      have hstep := R.emptyStep 𝔪 h T C π hπ hC (isCanonical_of_isEmptyTower 𝔪 (R.inv 𝔪) T hT) y hy
      obtain ⟨hmem, heq⟩ := inv_eq_inv_refl_of_isEmptyTower R 𝔪 h T hT (π y) hπy
      exact ⟨hmem, hstep.trans heq⟩

/-- **The second claim of `hir:smooth-centre`**: for a closed preconnected submanifold `Z` of `X` with
`𝔪 = (X, X, ∅, 𝓘_Z, 1)` in the domain of `R`, along a segment `T` with only empty centres the value of `R` is the same at all
points of `cosupp 𝔪_T` (the preimage of `Z`). -/
theorem inv_eq_of_isEmptyTower_of_isPreconnected (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {Z : Set X} (hZ : IsClosedSubmanifold n Z) (hconn : IsPreconnected Z)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsEmptyTower T) {y y' : Y}
    (hy : y ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hy' : y' ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp) :
    R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T y' =
      R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T y := by
  have hcos : (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X).cosupp = Z :=
    SmoothCentreLocus.cosupp_vanishingIdeal hZ.1 (subset_univ Z)
  obtain ⟨hm, he⟩ := inv_eq_inv_refl_of_isEmptyTower R _ hdom T hT y hy
  obtain ⟨hm', he'⟩ := inv_eq_inv_refl_of_isEmptyTower R _ hdom T hT y' hy'
  rw [hcos] at hm hm'
  rw [he, he']
  exact inv_refl_eq_of_isPreconnected R hZ hconn hdom hm hm'

/-- **After a segment with only empty centres the maximum locus is the whole cosupport** (`hir:smooth-centre`, last
sentence): for `Z` closed, preconnected, with `(X, X, ∅, 𝓘_Z, 1)` in the domain of `R`, and `T` with only empty centres. -/
theorem maxLocus_eq_cosupp_of_isEmptyTower (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {Z : Set X} (hZ : IsClosedSubmanifold n Z) (hconn : IsPreconnected Z)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsEmptyTower T) :
    ResolutionDriver.maxLocus (R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp =
      (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp := by
  ext y
  refine ⟨fun hy => hy.1, fun hy => ⟨hy, fun y' hy' => ?_⟩⟩
  exact (inv_eq_of_isEmptyTower_of_isPreconnected R hZ hconn hdom T hT hy hy').le

/-! ### Smooth centres of pure dimension (the homogeneous local model; connectedness not needed) -/

/-- **A resolution invariant takes the same value at two points of a smooth centre of the same local dimension**: for a
closed submanifold `Z` with `(X, X, ∅, 𝓘_Z, 1)` in the domain of `R`, if `Z` is regular of dimension `k` at `x` and at `x'`, the
values of `R` along the empty tower at `x` and `x'` agree (properties (5) and (6) through the biholomorphism of
`SmoothCentreHomogeneity.exists_smoothCentre_iso`). -/
theorem inv_refl_eq_of_regularAtDim (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) {X : CMfd.{u} n}
    {Z : Set X} (hZ : IsClosedSubmanifold n Z)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X)) {x x' : X} {j : ℕ}
    (hxj : RegularAtDim (n := n) Z x j) (hx'j : RegularAtDim (n := n) Z x' j) :
    R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x' =
      R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x := by
  set 𝔪 : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ with h𝔪
  have hcos : 𝔪.cosupp = Z := SmoothCentreLocus.cosupp_vanishingIdeal hZ.1 (subset_univ Z)
  have hx : x ∈ Z := hxj.2.1
  have hx' : x' ∈ Z := hx'j.2.1
  obtain ⟨U₁, U₂, Φ, hxU, hx'U, hΦx, -, hpb⟩ := exists_smoothCentre_iso hxj hx'j 1
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hdom.isWellFormed.isCoherent
  -- property (5) at `x` and at `x'`
  have h1 := R.restrictOpen 𝔪 hdom U₁ BlowupTower.refl trivial ⟨x, hxU⟩ (by show x ∈ 𝔪.cosupp; rw [hcos]; exact hx)
  have h2 := R.restrictOpen 𝔪 hdom U₂ BlowupTower.refl trivial ⟨x', hx'U⟩
    (by show x' ∈ 𝔪.cosupp; rw [hcos]; exact hx')
  -- property (6) for the empty towers over `Φ`
  have hdom₂ := InvDomainTowerAlong.isInvDomain_pullback_val U₂ hdom
  have hc₂ : Φ ⟨x, hxU⟩ ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪)
      (BlowupTower.refl : BlowupTower (CMfd.of (n := n) U₂) (CMfd.of (n := n) U₂))).cosupp := by
    show Φ ⟨x, hxU⟩ ∈ (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪).cosupp
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val 𝔪 hhol U₂, hcos]
    show ((Φ ⟨x, hxU⟩ : U₂) : X) ∈ Z
    rw [hΦx]
    exact hx'
  have h3 := R.towerIso Φ (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪) hdom₂ BlowupTower.refl BlowupTower.refl Φ
    IsTowerIso.refl trivial ⟨x, hxU⟩ hc₂
  rw [hpb] at h3
  have hΦx' : Φ ⟨x, hxU⟩ = ⟨x', hx'U⟩ := Subtype.ext hΦx
  rw [hΦx'] at h3
  exact h2.symm.trans (h3.symm.trans h1)

/-- **A resolution invariant is constant along a smooth centre of pure dimension** (connected or not): if `Z` is regular of
dimension `j` at each of its points and `(X, X, ∅, 𝓘_Z, 1)` lies in the domain of `R`, the value of `R` along the empty tower
is the same at all points of `Z`. -/
theorem inv_refl_eq_of_pureDim (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) {X : CMfd.{u} n}
    {Z : Set X} (hZ : IsClosedSubmanifold n Z) {j : ℕ} (hpure : ∀ x ∈ Z, RegularAtDim (n := n) Z x j)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X)) {x x' : X} (hx : x ∈ Z)
    (hx' : x' ∈ Z) :
    R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x' =
      R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x :=
  inv_refl_eq_of_regularAtDim R hZ hdom (hpure x hx) (hpure x' hx')

/-- **Along a segment with only empty centres, the value is constant on the cosupport of a smooth centre of pure dimension**
(the second claim of `hir:smooth-centre` without connectedness). -/
theorem inv_eq_of_isEmptyTower_of_pureDim (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {Z : Set X} (hZ : IsClosedSubmanifold n Z) {j : ℕ} (hpure : ∀ x ∈ Z, RegularAtDim (n := n) Z x j)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsEmptyTower T) {y y' : Y}
    (hy : y ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hy' : y' ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp) :
    R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T y' =
      R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T y := by
  have hcos : (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X).cosupp = Z :=
    SmoothCentreLocus.cosupp_vanishingIdeal hZ.1 (subset_univ Z)
  obtain ⟨hm, he⟩ := inv_eq_inv_refl_of_isEmptyTower R _ hdom T hT y hy
  obtain ⟨hm', he'⟩ := inv_eq_inv_refl_of_isEmptyTower R _ hdom T hT y' hy'
  rw [hcos] at hm hm'
  rw [he, he']
  exact inv_refl_eq_of_pureDim R hZ hpure hdom hm hm'

/-- **After a segment with only empty centres the maximum locus is the whole cosupport**, for a smooth centre of pure
dimension (connected or not). -/
theorem maxLocus_eq_cosupp_of_isEmptyTower_of_pureDim (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {Z : Set X} (hZ : IsClosedSubmanifold n Z) {j : ℕ} (hpure : ∀ x ∈ Z, RegularAtDim (n := n) Z x j)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsEmptyTower T) :
    ResolutionDriver.maxLocus (R.inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp =
      (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp := by
  ext y
  refine ⟨fun hy => hy.1, fun hy => ⟨hy, fun y' hy' => ?_⟩⟩
  exact (inv_eq_of_isEmptyTower_of_pureDim R hZ hpure hdom T hT hy hy').le

/-! ### The smooth part of a subvariety (the middle step of `hir:embedded-from-resolution`) -/

/-- **The marked ideal of `V` restricted to an open set** is the marked ideal of the trace:
`(X, X, ∅, 𝓘_V, 1)|_U = (U, U, ∅, 𝓘_{V ∩ U}, 1)`. -/
theorem pullback_val_smoothCentreMarked {X : CMfd.{u} n} (U : Opens X) (V : Set X) :
    MarkedIdeal.pullback (Subtype.val : U → X) (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) =
      (⟨univ, [], vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' V), 1⟩ : MarkedIdeal n (CMfd.of (n := n) U)) := by
  show (⟨(Subtype.val : U → X) ⁻¹' univ, [], GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) V),
      1⟩ : MarkedIdeal n (CMfd.of (n := n) U)) = _
  rw [preimage_univ, SmoothCentreHomogeneity.pullback_val_vanishingIdeal U V]

/-- **Over an open set on which the segment has only empty centres, the invariant of `(X, X, ∅, 𝓘_V, 1)` is constant on the
cosupport**, when `V ∩ U` is a closed preconnected submanifold of `U` (the middle step of `hir:embedded-from-resolution`, with
`U = X ∖ V_sing`): for `T` a canonical segment whose restriction to `U` has only empty centres (e.g. its centres miss the
preimages of `U`, `RestrictEmptyTower.isEmptyTower_restrict_iff`), the values at any two points of the cosupport over `U` agree
(property (5) and `inv_eq_of_isEmptyTower_of_isPreconnected` for the restriction). -/
theorem inv_eq_over_open_of_isEmptyTower (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {V : Set X} (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (U : Opens X) (hZ : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' V))
    (hconn : IsPreconnected ((Subtype.val : U → X) ⁻¹' V)) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)
      (R.inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) T)
    (hT : IsEmptyTower (restrict U T)) {p p' : openPreimage T U}
    (hp : (p : Y) ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hp' : (p' : Y) ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp) :
    R.inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T p' =
      R.inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T p := by
  have h1 := R.restrictOpen _ hdom U T hcan p hp
  have h2 := R.restrictOpen _ hdom U T hcan p' hp'
  have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have hTt := ResolutionInvariantExt.isGeoTestTower_of_isCanonical R hdom T hcan
  have hc := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent U T hTt
  have hq : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]; exact hp
  have hq' : p' ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]; exact hp'
  rw [pullback_val_smoothCentreMarked U V] at h1 h2 hdomU hq hq'
  rw [← h1, ← h2]
  exact inv_eq_of_isEmptyTower_of_isPreconnected R hZ hconn hdomU (restrict U T) hT hq hq'

/-- The same over an open set on which `V` is a closed submanifold of pure dimension (connected or not). -/
theorem inv_eq_over_open_of_isEmptyTower_of_pureDim (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {V : Set X} (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (U : Opens X) (hZ : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' V)) {j : ℕ}
    (hpure : ∀ x ∈ (Subtype.val : U → X) ⁻¹' V, RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' V) x j)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)
      (R.inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) T)
    (hT : IsEmptyTower (restrict U T)) {p p' : openPreimage T U}
    (hp : (p : Y) ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hp' : (p' : Y) ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp) :
    R.inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T p' =
      R.inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T p := by
  have h1 := R.restrictOpen _ hdom U T hcan p hp
  have h2 := R.restrictOpen _ hdom U T hcan p' hp'
  have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have hTt := ResolutionInvariantExt.isGeoTestTower_of_isCanonical R hdom T hcan
  have hc := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent U T hTt
  have hq : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]; exact hp
  have hq' : p' ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]; exact hp'
  rw [pullback_val_smoothCentreMarked U V] at h1 h2 hdomU hq hq'
  rw [← h1, ← h2]
  exact inv_eq_of_isEmptyTower_of_pureDim R hZ hpure hdomU (restrict U T) hT hq hq'

/-- **The first centre meeting the smooth part contains all of it** (`hir:embedded-from-resolution`): in the situation of
`inv_eq_over_open_of_isEmptyTower`, if a point `c` over `U` lies in the maximum locus of the invariant on the cosupport, then every
point of the cosupport over `U` does. -/
theorem mem_maxLocus_over_open_of_isEmptyTower (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {V : Set X} (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (U : Opens X) (hZ : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' V))
    (hconn : IsPreconnected ((Subtype.val : U → X) ⁻¹' V)) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)
      (R.inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) T)
    (hT : IsEmptyTower (restrict U T)) {c : Y}
    (hc : c ∈ ResolutionDriver.maxLocus (R.inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T)
      (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hcU : T.proj c ∈ U) {y : Y}
    (hy : y ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hyU : T.proj y ∈ U) :
    y ∈ ResolutionDriver.maxLocus (R.inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T)
      (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp := by
  have heq := inv_eq_over_open_of_isEmptyTower R hdom U hZ hconn T hcan hT (p := ⟨c, hcU⟩) (p' := ⟨y, hyU⟩) hc.1 hy
  refine ⟨hy, fun y' hy' => ?_⟩
  have h := hc.2 y' hy'
  rw [show R.inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T y =
      R.inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T c from heq]
  exact h

end

end Hironaka.SmoothCentreInvariant
