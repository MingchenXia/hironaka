/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.SmoothCentreInvariant
import Hironaka.Resolution.StrictTransformSubvarietySequence
import Hironaka.Analytic.RegularLocusComponent
import Hironaka.Analytic.RegularPointDimension
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.Analytic.RegularPatchNeighborhood
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.ExceptionalLocus
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.SingularLocus
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.SmoothCentreHomogeneity
import Hironaka.Invariant.SmoothCentreLocus
import Hironaka.Resolution.StrictTransformSubvariety
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution from the canonical resolution: the identity-principle step and the stopping

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), the embedded desingularization from the canonical resolution of
`(X, X, ∅, 𝓘_V, 1)`; Bierstone--Milman 2008 (`bierstone-milman08-functoriality`).

Let `V` be a closed irreducible analytic subvariety of a compact complex manifold `X`, `U = X ∖ V_sing`
(`regularOpen V`) and `𝔪_V = (X, X, ∅, 𝓘_V, 1)`. Along a canonical segment `T` of a value function with properties
(1), (4), (5), (6) of a resolution invariant whose centres miss the preimages of `U`, the first centre `C` meeting
the preimage of `U` contains the whole cosupport over `U`, which is the preimage of `V_reg`
(`EmbeddingFields.inv_eq_over_open_of_isEmptyTower_of_pureDim`). The **identity principle** then shows that the
strict transform of `V` at that stage is the connected component of `C` through any point over `U`: a smooth closed
connected submanifold of dimension `dim V`; and the exceptional image of the segment lies in `V_sing`. Stopping
before the blowup of `C` gives the embedded resolution. Such a first centre exists along every canonical segment
with empty final cosupport, because `V_reg ≠ ∅` stays in the cosupport as long as the centres miss `U`.

## Main results

* over an open set the centres miss (`RestrictEmptyTower.CentresAvoid`): `notMem_exceptionalLocus_of_centresAvoid`,
  `strictTransform_subset_preimage`, `mem_strictTransform_iff_of_centresAvoid` (over `U` the strict transform of a
  closed set is its preimage);
* `regularOpen`, `isClosed_singularLocus`, `regularAtDim_of_mem_regularOpen`: `U = X ∖ V_sing` and `V ∩ U = V_reg`;
* `EmbeddingFields n k inv`: the four properties used -- (1), (4), (5), (6) of a resolution invariant, in the shape
  of the fields of `ResolutionInvariantExt.ResolutionInvariant` -- for any value function `inv`; everything below is
  generic in `inv`, and `EmbeddingFields.isGeoTestTower_of_isCanonical`,
  `.inv_eq_over_open_of_isEmptyTower_of_pureDim`, ... restate the smooth-centre lemmas of `SmoothCentreInvariant`
  (proved there for `ResolutionInvariantExt.ResolutionInvariant`) for it;
* `mem_cosupp_iff_of_centresAvoid`: over `U` the cosupport of `𝔪_V` along `T` is the preimage of `V`, and so is the
  maximum locus once it meets the preimage of `U`;
* **`exists_first_centre`** (the stopping, any value function): a canonical segment whose centres do not all miss
  `U` has a canonical prefix whose centres miss `U` and whose maximum locus meets the preimage of `U`

* the domain hypothesis away from Cartan's theorem: `interior_eq_empty_of_dim_lt` (a subvariety of dimension `< n`
  has empty interior), `isNonzeroAlongAt_vanishingIdeal_of_dim_lt` (its ideal is nonzero at every point),
  **`isInvDomain_vanishingIdeal_of_dim_lt`** (`(X, X, ∅, 𝓘_V, 1)` lies in the domain in dimension `≤ k ≥ n` once
  `𝓘_V` is coherent); the case `dim V = n`: `isClosedConnectedSubmanifold_of_dim_eq` (`V` is a connected component
  of `X`)

Not here: a resolution invariant itself and the coherence of `𝓘_V` for a singular `V` (Cartan's theorem); both are
hypotheses of the last theorem.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.EmbeddedFromResolution

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowerTransforms RestrictEmptyTower RegularLocusComponent
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)

noncomputable section

variable {n : ℕ}

/-! ### Towers whose centres miss an open set -/

section Avoid

variable {X : CMfd.{u} n}

/-- **No exceptional point over an open set the centres miss**: if every centre of `T` misses the preimage of `U`, the
composite `T.proj` has bijective differential at every point over `U` (`Exc(f ∘ π) = Exc π ∪ π⁻¹ Exc f`, and the
exceptional locus of a blowup lies over its centre). -/
theorem notMem_exceptionalLocus_of_centresAvoid (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresAvoid U T → ∀ y : Y, T.proj y ∈ U →
      y ∉ exceptionalLocus n T.proj
  | _, .refl, _, y, _ => by
      show y ∉ exceptionalLocus n (id : X → X)
      rw [exceptionalLocus_id]
      exact notMem_empty y
  | _, .step T C π hπ, h, y, hy => by
      obtain ⟨hT, hC⟩ : CentresAvoid U T ∧ Disjoint C (T.proj ⁻¹' (U : Set X)) := h
      show y ∉ exceptionalLocus n (T.proj ∘ π)
      rw [exceptionalLocus_comp (T.contMDiff_proj.mdifferentiable (by simp))
        (hπ.contMDiff.mdifferentiable (by simp))]
      rintro (h1 | h2)
      · exact Set.disjoint_left.mp hC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h1) hy
      · exact notMem_exceptionalLocus_of_centresAvoid U T hT (π y) hy h2

/-- The strict transform of a closed set lies in its preimage. -/
theorem strictTransform_subset_preimage {A : Set X} (hA : IsClosed A) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    strictTransform n T.proj A ⊆ T.proj ⁻¹' A :=
  closure_minimal sdiff_subset (hA.preimage T.contMDiff_proj.continuous)

/-- **Over an open set the centres miss, the strict transform of a closed set is its preimage.** -/
theorem mem_strictTransform_iff_of_centresAvoid (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (h : CentresAvoid U T) {A : Set X} (hA : IsClosed A) {y : Y} (hy : T.proj y ∈ U) :
    y ∈ strictTransform n T.proj A ↔ T.proj y ∈ A :=
  ⟨fun h' => strictTransform_subset_preimage hA T h',
    fun h' => subset_closure ⟨h', notMem_exceptionalLocus_of_centresAvoid U T h y hy⟩⟩

end Avoid

/-! ### The complement of the singular locus -/

section Regular

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The singular locus is closed** (regularity of a fixed dimension is relatively open). -/
theorem isClosed_singularLocus (V : ClosedIrreducibleAnalyticSubvariety n M) : IsClosed (singularLocus V) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  by_cases hyV : y ∈ V.carrier
  · have hreg : RegularAtDim (n := n) V.carrier y V.dim := by
      by_contra h
      exact hy ⟨hyV, h⟩
    filter_upwards [RegularPatchNeighborhood.eventually_regularAtDim hreg] with z hz hzS
    exact hzS.2 (hz hzS.1)
  · filter_upwards [V.isClosed_carrier.isOpen_compl.mem_nhds hyV] with z hz hzS
    exact hz hzS.1

/-- **`U = X ∖ V_sing`**, the open set over which `V` is the closed submanifold `V_reg`. -/
def regularOpen (V : ClosedIrreducibleAnalyticSubvariety n M) : Opens M :=
  ⟨(singularLocus V)ᶜ, (isClosed_singularLocus V).isOpen_compl⟩

/-- **`V ∩ U = V_reg`**: a point of `V` off the singular locus is a regular point of dimension `dim V`. -/
theorem regularAtDim_of_mem_regularOpen {V : ClosedIrreducibleAnalyticSubvariety n M} {x : M} (hxV : x ∈ V.carrier)
    (hxU : x ∈ regularOpen V) : RegularAtDim (n := n) V.carrier x V.dim := by
  by_contra h
  exact hxU ⟨hxV, h⟩

/-- A regular point of dimension `dim V` lies in `U`. -/
theorem mem_regularOpen_of_regularAtDim {V : ClosedIrreducibleAnalyticSubvariety n M} {x : M}
    (hx : RegularAtDim (n := n) V.carrier x V.dim) : x ∈ regularOpen V :=
  fun h => h.2 hx

end Regular

/-! ### The four properties used: (1), (4), (5), (6) -/

section Fields

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

variable (n k) in
/-- **The properties of a resolution invariant that the embedded-resolution argument uses** -- (1) admissibility of the
level sets of the maximum, (4) empty steps, (5) restriction to open sets and (6) isomorphisms of towers -- for a
value function `inv`, in the exact shape of the fields of `ResolutionInvariantExt.ResolutionInvariant`. -/
structure EmbeddingFields (inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    Prop where
  /-- (1) Admissibility of the level sets of the maximum, on open sets. -/
  admissible : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
    ∀ (W : Opens Y) (l : Λ), (∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∈ W → inv 𝔪 T y ≤ l) →
      (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong 𝔪 T)).IsAdmissibleCentre
        ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ inv 𝔪 T y = l})
  /-- (4) Empty steps, after a canonical segment. -/
  emptyStep : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π), C = ∅ →
      IsCanonical 𝔪 (inv 𝔪) T → ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
        inv 𝔪 (.step T C π hπ) z = inv 𝔪 T (π z)
  /-- (5) Restriction to open sets, along canonical segments. -/
  restrictOpen : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ (U : Opens X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
    ∀ p : openPreimage T U, (p : Y) ∈ (geoTransformAlong 𝔪 T).cosupp →
      inv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = inv 𝔪 T p
  /-- (6) Isomorphisms of towers over biholomorphisms, along canonical segments. -/
  towerIso : ∀ {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y')
    (T : BlowupTower X Y) (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y),
      BlowupTowerIsomorphism.IsTowerIso Φ T' T χ → IsCanonical 𝔪 (inv 𝔪) T →
        ∀ p : Y', χ p ∈ (geoTransformAlong 𝔪 T).cosupp → inv (MarkedIdeal.pullback Φ 𝔪) T' p = inv 𝔪 T (χ p)

namespace EmbeddingFields

variable {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The maximum locus is an admissible centre** along a canonical segment which is a multiple test blow-up (property (1)
on the whole last stage; `ResolutionInvariantExt.isAdmissibleCentre_maxLocus` for `inv` with the four properties). -/
theorem isAdmissibleCentre_maxLocus (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔪 (inv 𝔪) T)
    (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong 𝔪 T).IsAdmissibleCentre
      (ResolutionDriver.maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := by
  by_cases hne : (ResolutionDriver.maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hadm := hF.admissible 𝔪 h T hcan ⊤ (inv 𝔪 T y₀) (fun y hy _ => hy₀.2 y hy)
    rw [← ResolutionInvariantDriver.maxLocus_eq_level hy₀] at hadm
    have hcoh := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT).isCoherent
    exact ResolutionInvariantDriver.isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg) hadm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Canonical segments are multiple test blow-ups** (`ResolutionInvariantExt.isGeoTestTower_of_isCanonical` for `inv`). -/
theorem isGeoTestTower_of_isCanonical (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T → IsGeoTestTower 𝔪 T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (inv 𝔪) T ∧
          (C = ∅ ∨ C = ResolutionDriver.maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      have hTt := isGeoTestTower_of_isCanonical hF h T hT
      refine (isGeoTestTower_step_iff 𝔪 T C π hπ).mpr ⟨hTt, ?_⟩
      rcases hC with rfl | rfl
      · exact MarkedIdeal.isAdmissibleCentre_empty _
      · exact isAdmissibleCentre_maxLocus hF h T hT hTt

/-- **Along a segment with only empty centres the value is that of the empty tower** (property (4), one step at a
time). -/
theorem inv_eq_inv_refl_of_isEmptyTower (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)
    (h : IsInvDomain k 𝔪) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T → ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp,
      T.proj y ∈ 𝔪.cosupp ∧ inv 𝔪 T y = inv 𝔪 (BlowupTower.refl : BlowupTower X X) (T.proj y)
  | _, .refl, _, y, hy => ⟨hy, rfl⟩
  | _, .step T C π hπ, hT, y, hy => by
      have hT' := hT
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := hT
      have hiff := SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower 𝔪
        h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent (.step T C π hπ) hT' y
      have hπy : π y ∈ (geoTransformAlong 𝔪 T).cosupp :=
        (SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower 𝔪 h.isWellFormed.isClosedSubmanifold_N
          h.isWellFormed.isCoherent T hT (π y)).mpr (hiff.mp hy)
      have hstep := hF.emptyStep 𝔪 h T C π hπ hC (ResolutionInvariantExt.isCanonical_of_isEmptyTower 𝔪 (inv 𝔪) T hT)
        y hy
      obtain ⟨hmem, heq⟩ := inv_eq_inv_refl_of_isEmptyTower hF 𝔪 h T hT (π y) hπy
      exact ⟨hmem, hstep.trans heq⟩

/-- **Two points of a smooth centre of the same local dimension have the same value along the empty tower** (properties
(5) and (6) through the biholomorphism of `SmoothCentreHomogeneity.exists_smoothCentre_iso`). -/
theorem inv_refl_eq_of_regularAtDim (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {Z : Set X}
    (hZ : IsClosedSubmanifold n Z) (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X))
    {x x' : X} {j : ℕ} (hxj : RegularAtDim (n := n) Z x j) (hx'j : RegularAtDim (n := n) Z x' j) :
    inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x' =
      inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x := by
  set 𝔪 : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ with h𝔪
  have hcos : 𝔪.cosupp = Z := SmoothCentreLocus.cosupp_vanishingIdeal hZ.1 (subset_univ Z)
  have hx : x ∈ Z := hxj.2.1
  have hx' : x' ∈ Z := hx'j.2.1
  obtain ⟨U₁, U₂, Φ, hxU, hx'U, hΦx, -, hpb⟩ := SmoothCentreHomogeneity.exists_smoothCentre_iso hxj hx'j 1
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
  rw [hpb] at h3
  have hΦx' : Φ ⟨x, hxU⟩ = ⟨x', hx'U⟩ := Subtype.ext hΦx
  rw [hΦx'] at h3
  exact h2.symm.trans (h3.symm.trans h1)

/-- **Along a segment with only empty centres the value is constant on the cosupport of a smooth centre of pure
dimension**. -/
theorem inv_eq_of_isEmptyTower_of_pureDim (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {Z : Set X}
    (hZ : IsClosedSubmanifold n Z) {j : ℕ} (hpure : ∀ x ∈ Z, RegularAtDim (n := n) Z x j)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsEmptyTower T) {y y' : Y}
    (hy : y ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hy' : y' ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp) :
    inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T y' =
      inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T y := by
  have hcos : (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X).cosupp = Z :=
    SmoothCentreLocus.cosupp_vanishingIdeal hZ.1 (subset_univ Z)
  obtain ⟨hm, he⟩ := inv_eq_inv_refl_of_isEmptyTower hF _ hdom T hT y hy
  obtain ⟨hm', he'⟩ := inv_eq_inv_refl_of_isEmptyTower hF _ hdom T hT y' hy'
  rw [hcos] at hm hm'
  rw [he, he']
  exact inv_refl_eq_of_regularAtDim hF hZ hdom (hpure _ hm) (hpure _ hm')

/-- **Over an open set on which the segment has only empty centres, the value on `(X, X, ∅, 𝓘_V, 1)` is constant on the
cosupport**, when `V ∩ U` is a closed submanifold of `U` of pure dimension (the middle step of
`hir:embedded-from-resolution`). -/
theorem inv_eq_over_open_of_isEmptyTower_of_pureDim (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {V : Set X}
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (U : Opens X) (hZ : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' V)) {j : ℕ}
    (hpure : ∀ x ∈ (Subtype.val : U → X) ⁻¹' V, RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' V) x j)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)
      (inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) T)
    (hT : IsEmptyTower (restrict U T)) {p p' : openPreimage T U}
    (hp : (p : Y) ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hp' : (p' : Y) ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp) :
    inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T p' =
      inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T p := by
  have h1 := hF.restrictOpen _ hdom U T hcan p hp
  have h2 := hF.restrictOpen _ hdom U T hcan p' hp'
  have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have hTt := isGeoTestTower_of_isCanonical hF hdom T hcan
  have hc := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent U T hTt
  have hq : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]; exact hp
  have hq' : p' ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]; exact hp'
  rw [SmoothCentreInvariant.pullback_val_smoothCentreMarked U V] at h1 h2 hdomU hq hq'
  rw [← h1, ← h2]
  exact inv_eq_of_isEmptyTower_of_pureDim hF hZ hpure hdomU (restrict U T) hT hq hq'

end EmbeddingFields

end Fields

/-! ### The first centre meeting the smooth part -/

section Invariant

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] {X : CMfd.{u} n}
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Over an open set the centres miss, the cosupport of `(X, X, ∅, 𝓘_V, 1)` is the preimage of `V`** (`V` closed, the
marked ideal in the domain, `T` a multiple test blow-up): restrict to `U`
(`ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict`), where the tower has only empty centres
(`RestrictEmptyTower.isEmptyTower_restrict_iff`) and the cosupport is the preimage of `V ∩ U`
(`SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower`). -/
theorem mem_cosupp_iff_of_centresAvoid {V : Set X} (hV : IsClosed V)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (U : Opens X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hTt : IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T) (hT : CentresAvoid U T)
    {y : Y} (hy : T.proj y ∈ U) :
    y ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp ↔ T.proj y ∈ V := by
  have hc := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent U T hTt
  have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have he : IsEmptyTower (restrict U T) := (isEmptyTower_restrict_iff U T).mpr hT
  set p : openPreimage T U := ⟨y, hy⟩ with hp
  have h1 : y ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp ↔
      p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
        (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]
    rfl
  rw [h1, SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower _
    hdomU.isWellFormed.isClosedSubmanifold_N hdomU.isWellFormed.isCoherent (restrict U T) he p,
    SmoothCentreInvariant.pullback_val_smoothCentreMarked U V,
    SmoothCentreLocus.cosupp_vanishingIdeal (hV.preimage continuous_subtype_val) (subset_univ _)]
  show (((restrict U T).proj p : U) : X) ∈ V ↔ _
  rw [proj_restrict]

end Invariant

/-! ### The stopping -/

section Stopping

variable {Λ : Type v} [LinearOrder Λ] {X : CMfd.{u} n}

/-- **The first centre meeting an open set** (any value function): along a canonical segment `T` whose centres do not all
miss the preimages of `U`, some prefix `T'` (`T = T' S`) is canonical, its centres miss the preimages of `U`, and its
maximum locus -- the next centre of `T`, which is nonempty -- meets the preimage of `U`. -/
theorem exists_first_centre (𝔪 : MarkedIdeal n X) (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 inv T → ¬ CentresAvoid U T →
      ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y') (S : BlowupTower Y' Y), T'.append S = T ∧
        IsCanonical 𝔪 inv T' ∧ CentresAvoid U T' ∧
        ∃ c ∈ ResolutionDriver.maxLocus (inv T') (geoTransformAlong 𝔪 T').cosupp, T'.proj c ∈ U
  | _, .refl, _, h => absurd trivial h
  | _, .step T C π hπ, hcan, h => by
      obtain ⟨hcT, hC⟩ : IsCanonical 𝔪 inv T ∧
          (C = ∅ ∨ C = ResolutionDriver.maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      by_cases hT : CentresAvoid U T
      · have hd : ¬ Disjoint C (T.proj ⁻¹' (U : Set X)) := fun hd => h ⟨hT, hd⟩
        obtain ⟨c, hcC, hcU⟩ := Set.not_disjoint_iff.mp hd
        rcases hC with hC | hC
        · rw [hC] at hcC
          exact absurd hcC (notMem_empty c)
        · exact ⟨_, T, .step .refl C π hπ, rfl, hcT, hT, c, by rw [← hC]; exact hcC, hcU⟩
      · obtain ⟨Y', T', S, hTS, h1, h2, h3⟩ := exists_first_centre 𝔪 inv U T hcT hT
        subst hTS
        exact ⟨Y', T', .step S C π hπ, rfl, h1, h2, h3⟩

end Stopping

/-! ### The domain hypothesis away from Cartan's theorem, and the case `dim V = n` -/

section Domain

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A set containing a neighbourhood of `x` is regular of dimension `n` at `x`. -/
theorem regularAtDim_of_mem_nhds {S : Set M} {x : M} (hS : S ∈ 𝓝 x) : RegularAtDim (n := n) S x n := by
  obtain ⟨O, hOS, hOo, hxO⟩ := mem_nhds_iff.mp hS
  refine RegularPointDimension.regularAtDim_of_inter_eq hOo hxO ?_
    (AnalyticIrreducibleComponents.regularAtDim_univ x)
  rw [univ_inter, inter_eq_right.mpr hOS]

/-- A set regular of dimension `n` at `x` is a neighbourhood of `x`. -/
theorem mem_nhds_of_regularAtDim_self {S : Set M} {x : M} (hx : RegularAtDim (n := n) S x n) : S ∈ 𝓝 x := by
  obtain ⟨_, _, Φ, _, _, hflat⟩ := hx
  have hO : IsOpen ((complexChartAt (n := n) x).val.source ∩ (complexChartAt (n := n) x).val ⁻¹' Φ.source) :=
    (complexChartAt (n := n) x).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) x).val.open_source Φ.isOpen_source
  refine mem_of_superset (hO.mem_nhds ⟨mem_complexChartAt_source x, Φ.center_mem_source⟩) fun y hy => ?_
  refine (hflat hy.1 hy.2).mpr ?_
  intro i hi
  exact absurd i.2 (not_lt.mpr hi)

/-- **A subvariety of dimension `< n` has empty interior** (the identity theorem along a component and irreducibility): an
interior point is a regular point of dimension `n`, so `V` is the closure of the component of its regular locus through it
(`StrictTransformSubvariety.eq_closure_component`), whose points are all regular of dimension `n`; a regular point of
dimension `dim V` lies in that closure, hence in that component, and the two dimensions agree
(`RegularPointDimension.eq_of_regularAtDim`). -/
theorem interior_eq_empty_of_dim_lt (V : ClosedIrreducibleAnalyticSubvariety n M) (h : V.dim < n) :
    interior V.carrier = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hxn : RegularAtDim (n := n) V.carrier x n := regularAtDim_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨c, -, hc⟩ := V.exists_regular_point
  have hVeq := StrictTransformSubvariety.eq_closure_component V.irreducible_carrier hxn
  obtain ⟨W, hW, hcW, hWc⟩ := exists_open_inter_subset_component hc (mem_component_self hc)
  have hcl : c ∈ closure (component (n := n) V.carrier x) := hVeq ▸ hc.2.1
  obtain ⟨z, hzW, hzx⟩ := mem_closure_iff.mp hcl W hW hcW
  have hzc : z ∈ component (n := n) V.carrier c := hWc ⟨component_subset V.carrier x hzx, hzW⟩
  have h1 : component (n := n) V.carrier x = component (n := n) V.carrier c :=
    (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzc).symm
  have hcx : c ∈ component (n := n) V.carrier x := by
    rw [h1]
    exact mem_component_self hc
  have := RegularPointDimension.eq_of_regularAtDim hc (regularAtDim_of_mem_component hxn hcx)
  omega

/-- **The ideal of a subvariety of dimension `< n` is nonzero at every point** (`IsNonzeroAlongAt univ`): off `V` the
constant `1` lies in it; at a point of `V`, some local equation of `V` (in a presentation of the analytic set) does not vanish
identically near the point, since otherwise `V` would contain a neighbourhood of it (`interior_eq_empty_of_dim_lt`). -/
theorem isNonzeroAlongAt_vanishingIdeal_of_dim_lt (V : ClosedIrreducibleAnalyticSubvariety n M) (h : V.dim < n)
    (x : M) : DivisorExponentAlong.IsNonzeroAlongAt (univ : Set M) (vanishingIdeal (n := n) V.carrier) x := by
  by_cases hxV : x ∈ V.carrier
  · obtain ⟨P⟩ := V.analytic x
    set e := complexChartAt (n := n) x with he
    have hsrc : e.val.source ∈ 𝓝 x := e.val.open_source.mem_nhds (mem_complexChartAt_source x)
    have hnb : e.val ⁻¹' P.coordinateNeighborhood ∈ 𝓝 x :=
      (e.val.continuousAt (mem_complexChartAt_source x)).preimage_mem_nhds
        (P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood)
    by_cases hall : ∀ i, ∀ᶠ y in 𝓝 x, P.generator i (e.val y) = 0
    · exfalso
      have hVn : V.carrier ∈ 𝓝 x := by
        filter_upwards [eventually_all.mpr hall, hsrc, hnb] with y h1 h2 h3
        exact (P.zeroLocus h2 h3).mpr h1
      have hint : x ∈ interior V.carrier := mem_interior_iff_mem_nhds.mpr hVn
      rw [interior_eq_empty_of_dim_lt V h] at hint
      exact hint
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      refine ⟨fun y => P.generator i (e.val y), ⟨?_, ?_⟩, hi.mono fun y hy => ⟨mem_univ y, hy⟩⟩
      · refine DerivativeIdeal.holomorphicAt_comp_chart e (mem_complexChartAt_source x) ?_
        filter_upwards [P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood] with z hz
        exact (P.generator_holomorphic i z hz).differentiableAt (P.isOpen_coordinateNeighborhood.mem_nhds hz)
      · filter_upwards [hsrc, hnb] with y h2 h3 hyV
        exact (P.zeroLocus h2 h3).mp hyV i
  · refine ⟨fun _ => (1 : ℂ), ⟨holomorphicAt_const 1, ?_⟩,
      Frequently.of_forall fun y => ⟨mem_univ y, one_ne_zero⟩⟩
    filter_upwards [V.isClosed_carrier.isOpen_compl.mem_nhds hxV] with y hy hyV
    exact absurd hyV hy

/-- **`(X, X, ∅, 𝓘_V, 1)` lies in the domain of the invariants in dimension `≤ k`** for `n ≤ k`, a subvariety of dimension
`< n`, and a coherent ideal `𝓘_V` (Cartan's theorem, a hypothesis here). -/
theorem isInvDomain_vanishingIdeal_of_dim_lt {k : ℕ} (hnk : n ≤ k) (V : ClosedIrreducibleAnalyticSubvariety n M)
    (h : V.dim < n) (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) :
    IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n M) where
  isWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, hcoh, NormalCrossings.isSNCDivisor_nil,
    NormalCrossings.isTransverse_nil_of_isClosedSubmanifold HomogenizedGlueingTower.isClosedSubmanifold_univ⟩
  dimLE := fun x _ => ⟨n, hnk, AnalyticIrreducibleComponents.regularAtDim_univ x⟩
  one_le_d := le_rfl
  isNonzeroAlongAt := fun x _ => isNonzeroAlongAt_vanishingIdeal_of_dim_lt V h x

/-- **A subvariety of dimension `n` is a connected component of `M`**, hence a closed connected submanifold of dimension
`n`: at a regular point `c` of dimension `n` it is a neighbourhood of `c`, so it contains the connected component `K` of `c`
(identity theorem along the component `K` of the regular locus of `M`); `K` is open and closed, so `K` and `V ∖ K` are
analytic, and irreducibility gives `V = K`. -/
theorem isClosedConnectedSubmanifold_of_dim_eq (V : ClosedIrreducibleAnalyticSubvariety n M) (h : V.dim = n) :
    IsClosedConnectedSubmanifold n V.carrier n := by
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel n) M
  obtain ⟨c, -, hc⟩ := V.exists_regular_point
  rw [h] at hc
  obtain ⟨O, hOV, hOo, hcO⟩ := mem_nhds_iff.mp (mem_nhds_of_regularAtDim_self hc)
  have hKo : IsOpen (connectedComponent c) := isOpen_connectedComponent
  have hKc : IsClosed (connectedComponent c) := isClosed_connectedComponent
  have hRu : regularPoints (n := n) (univ : Set M) = univ :=
    eq_univ_of_forall fun y => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ y⟩
  have hcomp : component (n := n) (univ : Set M) c = connectedComponent c := by
    show connectedComponentIn (regularPoints (n := n) (univ : Set M)) c = _
    rw [hRu, connectedComponentIn_univ]
  have hKV : connectedComponent c ⊆ V.carrier := by
    rw [← hcomp]
    exact component_subset_of_isOpen V.analytic hOo
      ⟨c, hcO, mem_component_self (AnalyticIrreducibleComponents.regularAtDim_univ c)⟩ fun y hy => hOV hy.1
  have hKan : IsComplexAnalyticSubset (n := n) (connectedComponent c) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_locally_eq isComplexAnalyticSubset_univ hKc
      fun y hy => ⟨connectedComponent c, hKo, hy, by rw [univ_inter, inter_self]⟩
  have hDan : IsComplexAnalyticSubset (n := n) (V.carrier \ connectedComponent c) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_locally_eq V.analytic (V.isClosed_carrier.sdiff hKo)
      fun y hy => ⟨(connectedComponent c)ᶜ, hKc.isOpen_compl, hy.2, by
        ext z
        simp only [mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
        tauto⟩
  rcases V.irreducible_carrier.eq_left_or_eq_right hKan hDan hKV sdiff_subset (union_sdiff_cancel hKV).symm with
    hVK | hVD
  · refine ⟨V.isClosed_carrier, hVK ▸ isConnected_connectedComponent, fun x hx => ?_⟩
    have hxK : x ∈ connectedComponent c := hVK ▸ hx
    refine RegularPointDimension.regularAtDim_of_inter_eq hKo hxK ?_
      (AnalyticIrreducibleComponents.regularAtDim_univ x)
    rw [univ_inter, hVK, inter_self]
  · exfalso
    have hcV : c ∈ V.carrier := hKV mem_connectedComponent
    rw [hVD] at hcV
    exact hcV.2 mem_connectedComponent

end Domain

end

end Hironaka.EmbeddedFromResolution
