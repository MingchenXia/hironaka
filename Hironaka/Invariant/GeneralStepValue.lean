/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.GeneralEmptyPrefix
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.GeneralAdmissible
import Hironaka.Invariant.GeneralCanonicalTail
import Hironaka.Invariant.GeneralRepresentative
import Hironaka.Invariant.GeneralRestrictOpen
import Hironaka.Invariant.GeneralTowerIso
import Hironaka.Invariant.GeneralUSC
import Hironaka.Invariant.GeneralValue
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxOrderValue
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The general value has the properties (1)--(7), (4') of a resolution invariant

**Main theorem** (`isInvValue_genInv`): for every value function `M` for the marked ideals of maximal order in
dimension `≤ k` (`MaxOrderValue.IsMaxOrderValue n k M`; in the induction, the masked Step 1 value built from the
invariant in dimension `≤ k - 1`) and `0 < n`, the general value `GeneralValue.genInv M` satisfies `IsInvValue n k`:
properties (1) admissibility (`GeneralAdmissible`), (2) upper semicontinuity (`GeneralUSC`), (3) decrease and (4)
empty steps (`GeneralCanonicalTail.genInv_drop`), (4') empty prefixes (`GeneralEmptyPrefix`), (5) open sets
(`GeneralRestrictOpen`), (6) isomorphisms of towers (`GeneralTowerIso`) and (7) representatives
(`GeneralRepresentative`), at every point of the cosupport along every canonical segment, for every marked ideal of
the domain `IsInvDomain k`. At points where the nonmonomial part has order `0` the properties are
(`NonmonomialOrderMonomialCanonical`, `GeneralValueOrderZero`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralStepValue

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MaxOrderValue Hironaka.GeneralValue Hironaka.ResolutionInvariantSeq
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The general value has properties (1)--(7) and (4') of a resolution invariant** (`hir:general-step-value`): for a value
function `M` for the marked ideals of maximal order in dimension `≤ k` and `0 < n`, `genInv M` satisfies
`ResolutionInvariantSeq.IsInvValue n k` -- the fields of `ResolutionInvariantExt.ResolutionInvariant` without (8). -/
theorem isInvValue_genInv (hM : IsMaxOrderValue n k M) (hn : 0 < n) :
    IsInvValue n k (genInv M) where
  admissible := by
    intro X 𝔪 h Y T hcan W l hle
    exact GeneralAdmissible.genInv_admissible hM hn h T
      (GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h T hcan) hcan W l hle
  usc := by
    intro X 𝔪 h Y T hcan
    exact GeneralUSC.genInv_usc hM hn h T (GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h T hcan) hcan
  decrease := by
    intro X 𝔪 h Y Z T C π hπ hcan _ hC z hz
    have hcan' : IsCanonical 𝔪 (genInv M 𝔪) (.step T C π hπ) := ⟨hcan, Or.inr hC⟩
    exact (GeneralCanonicalTail.genInv_drop hM hn h T C π hπ
      (GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h _ hcan') hcan' z hz).2
  emptyStep := by
    intro X 𝔪 h Y Z T C π hπ hC hcan z hz
    have hcan' : IsCanonical 𝔪 (genInv M 𝔪) (.step T C π hπ) := ⟨hcan, Or.inl hC⟩
    refine (GeneralCanonicalTail.genInv_drop hM hn h T C π hπ
      (GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h _ hcan') hcan' z hz).2.2 ?_
    rw [hC]
    exact notMem_empty _
  emptyPrefix := by
    intro X 𝔪 h Y₀ Y T₀ T₁ h₀ hcan z hz
    exact GeneralEmptyPrefix.emptyPrefix_field hM hn 𝔪 h T₀ T₁ h₀ hcan z hz
  restrictOpen := by
    intro X 𝔪 h U Y T hcan p hp
    exact GeneralRestrictOpen.restrictOpen_field hM hn 𝔪 h U T hcan p hp
  towerIso := by
    intro X X' Φ 𝔪 h Y' Y T' T χ hiso hcan p hp
    exact GeneralTowerIso.towerIso_field hM hn Φ 𝔪 h T' T χ hiso hcan p hp
  representative := by
    intro X 𝔪 𝔫 h𝔪 h𝔫 hEq Y T hcan y hy
    exact GeneralRepresentative.representative_field 𝔪 𝔫 h𝔪 h𝔫 hEq T hcan y hy

end

end Hironaka.GeneralStepValue
