/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.SmoothCentreHomogeneity
import Hironaka.Invariant.SmoothCentreLocus
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.MarkedIdeal.TransformOffCentre
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A resolution invariant is constant along a smooth centre

Source: Włodarczyk 2005 (arXiv `hiron.tex`), functoriality of the canonical resolution for étale morphisms
(`pr:resol` (4)).

Proof: near two close points `x, x'` of `Z` a translation along `Z` is a biholomorphism `Φ: U₁ ≅ U₂` with `Φ x = x'`
and `Φ^*(𝔪|_{U₂}) = 𝔪|_{U₁}`; property (5) (`restrictOpen`) at `x` and `x'` and property (6) (`towerIso`) for the
empty towers over `Φ` compare the values. The cosupport is `Z` and the restrictions stay in the domain
(`SmoothCentreLocus.cosupp_vanishingIdeal`, `InvDomainTowerAlong.isInvDomain_pullback_val`).

## Main results

* without connectedness, for a smooth centre of pure dimension (the homogeneous local model,
  `SmoothCentreHomogeneity.exists_smoothCentre_iso`): `inv_refl_eq_of_regularAtDim`,
  `inv_eq_of_isEmptyTower_of_pureDim`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.SmoothCentreInvariant

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowerTransforms BlowupTowerIsomorphism SmoothCentreHomogeneity
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ]

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

/-! ### The smooth part of a subvariety (the middle step of `hir:embedded-from-resolution`) -/

/-- **The marked ideal of `V` restricted to an open set** is the marked ideal of the trace:
`(X, X, ∅, 𝓘_V, 1)|_U = (U, U, ∅, 𝓘_{V ∩ U}, 1)`. -/
theorem pullback_val_smoothCentreMarked {X : CMfd.{u} n} (U : Opens X) (V : Set X) :
    MarkedIdeal.pullback (Subtype.val : U → X) (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) =
      (⟨univ, [], vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' V), 1⟩ : MarkedIdeal n (CMfd.of (n := n) U)) := by
  show (⟨(Subtype.val : U → X) ⁻¹' univ, [], GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) V),
      1⟩ : MarkedIdeal n (CMfd.of (n := n) U)) = _
  rw [preimage_univ, SmoothCentreHomogeneity.pullback_val_vanishingIdeal U V]

end

end Hironaka.SmoothCentreInvariant
