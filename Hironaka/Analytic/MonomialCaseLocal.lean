/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MonomialStepAlong
import Hironaka.Invariant.MonomialInvariantFunctorialAlong
import Hironaka.Invariant.NonmonomialOrderZero
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.MarkedIdeal.TransformOffCentre
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Resolution of monomial marked ideals: compact cosupport, level sets on open sets

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), the monomial case of Proposition `pr:resol`; Bierstone--Milman
2008 (`bierstone-milman08-functoriality`); Bierstone--Milman 2003
(`bierstone-milman03-desingularization-algorithms`), Theorem 1.14.

`hir:monomial-case` states, for a well-formed monomial marked ideal `(M, N, E, 𝔞, d)` with `d ≥ 1` and its invariant `γ`:
(1) `γ` is upper semicontinuous on the cosupport, and on every open set on which `γ ≤ λ` the locus `{γ = λ}` is
`N ∩ ⋂_{H ∈ λ₃} H`, an admissible centre; (2) the drop after blowing up the maximum locus; (3) if the cosupport is compact,
the iterated blowup of the maximum locus reaches an empty cosupport; (4) invariance.  Items (2) and (4) and the compact-base
form of (3) were proved (`MonomialStepAlong`, `MonomialInvariantFunctorialAlong`).  New here:

* (1) **on an open set**: if `γ ≤ v` on the part of the cosupport over an open `W`, the points of the cosupport over
  `W` with `γ = v` form an admissible centre of `𝔪|_W`, and near each of its points the locus is `N ∩ ⋂_{i ∈ top(v)}
  E_i` (`MonomialCaseAlong.eventually_gammaAlong_eq_iff_mem_memberInter`).

The second half of (1), read globally on the open set, is false when members are disconnected (the exponent of a member is
only locally constant): for `M = N = ℂ²`, `H₁ = {z₁ = 0} ⊔ {z₁ = 1}`, `H₂ = {z₂ = 0}`, `𝔞 = (z₁² (z₁ - 1) z₂²)`, `d = 3`,
`γ ≤ γ(0, 0)` everywhere, but `(1, 0) ∈ H₁ ∩ H₂` has `γ₂(1, 0) = 3 < 4 = γ₂(0, 0)`.  The corrected statement is local, as
the proof of `hir:monomial-case` (1) is.

## Main results

* `isCompact_cosupp_geoTransformAlong`: along a multiple test blow-up the cosupport stays compact;
* `exists_isGeoResolution_of_wellFounded_invariant_of_isCompact`: the well-founded driver with compact cosupports;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.MonomialCaseLocal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.MonomialPartEtale Hironaka.GermIdealOrder Hironaka.DivisorExponentAlong Hironaka.BlowupTowers Hironaka.DerivativeIdealAlongEtale Hironaka.MonomialInvariant Hironaka.MonomialCaseAlong Hironaka.MonomialStepAlong Hironaka.MarkedIdealRestrictOpen Hironaka.RestrictedIdealWeight
open Hironaka.ResolutionDriver (maxLocus IsCanonicalSegment)
open Hironaka.ResolutionInvariantOrder (IsInvUSCOn)

noncomputable section

variable {n : ℕ}

/-! ### Compact cosupports along towers -/

section Compact

variable {X : CMfd.{u} n}

/-- **Along a multiple test blow-up the cosupport stays compact** (closed submanifold `N`, coherent ideal): it is closed and
lies over the original cosupport, whose preimage under the proper projection is compact. -/
theorem isCompact_cosupp_geoTransformAlong {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hK : IsCompact 𝔪.cosupp) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) : IsCompact (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  exact ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
    (GiraudAlong.isClosed_cosupport_along hcT hNT _)
    (TransformOffCentre.cosupp_geoTransformAlong_subset 𝔪 hN h𝔞 T hT)

variable {Λ : Type v} [LinearOrder Λ]

/-- **The canonical resolution exists, by a well-founded drop, for compact cosupports**: with values in a well-founded
order, if along canonical segments the cosupports are compact, the invariant is upper semicontinuous, its maximum
locus is an admissible centre with empty interior, and after blowing up the maximum locus the invariant at every
point of the new cosupport is below the old maximum, then some canonical segment is a resolution. -/
theorem exists_isGeoResolution_of_wellFounded_invariant_of_isCompact [WellFoundedLT Λ] (𝔪 : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    (hcpt : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      IsCompact (geoTransformAlong 𝔪 T).cosupp)
    (husc : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      IsInvUSCOn (inv T) (geoTransformAlong 𝔪 T).cosupp)
    (hadm : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).cosupp.Nonempty →
      (geoTransformAlong 𝔪 T).IsAdmissibleCentre (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) ∧
        interior (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) = ∅)
    (hdec : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      ∀ x₀ ∈ maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp,
      ∀ {Z : CMfd.{u} n} (π : Z → Y)
        (hπ : IsBlowupAlong n (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π),
      ∀ z ∈ (geoTransformAlong 𝔪
          (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ)).cosupp,
        inv (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ) z < inv T x₀) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T ∧ IsGeoResolution 𝔪 T := by
  have hmaxne : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).cosupp.Nonempty → (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp).Nonempty := by
    intro Y T hPT hT hne
    obtain ⟨x, hx, hmax⟩ := (husc T hPT hT).exists_isMaxOn (hcpt T hPT hT) hne
    exact ⟨x, hx, hmax⟩
  -- strong induction on a bound `l` for the values on the cosupport
  suffices h : ∀ l : Λ, ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T →
      IsGeoTestTower 𝔪 T → (∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, inv T y ≤ l) →
      ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y'), IsCanonicalSegment 𝔪 inv T' ∧ IsGeoResolution 𝔪 T' by
    by_cases hne : (geoTransformAlong 𝔪 (BlowupTower.refl : BlowupTower X X)).cosupp.Nonempty
    · obtain ⟨x₀, -, hmax⟩ := hmaxne (BlowupTower.refl : BlowupTower X X) trivial trivial hne
      exact h _ BlowupTower.refl trivial trivial fun y hy => hmax y hy
    · exact ⟨X, BlowupTower.refl, trivial, trivial, not_nonempty_iff_eq_empty.mp hne⟩
  intro l
  induction l using WellFoundedLT.induction with
  | _ l ih =>
  intro Y T hPT hT hl
  by_cases hne : (geoTransformAlong 𝔪 T).cosupp.Nonempty
  · obtain ⟨hC, hint⟩ := hadm T hPT hT hne
    obtain ⟨x₀, hx₀⟩ := hmaxne T hPT hT hne
    obtain ⟨Z, π, hπ⟩ := ResolutionDriver.exists_blowup _ hC.1 hint
    have hPT' : IsCanonicalSegment 𝔪 inv
        (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ) := ⟨hPT, ⟨x₀, hx₀⟩, rfl⟩
    have hT' : IsGeoTestTower 𝔪 (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ) :=
      (isGeoTestTower_step_iff 𝔪 T _ π hπ).mpr ⟨hT, hC⟩
    by_cases hne' : (geoTransformAlong 𝔪
        (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ)).cosupp.Nonempty
    · obtain ⟨z₀, hz₀, hzmax⟩ := hmaxne _ hPT' hT' hne'
      have hlt := (hdec T hPT hT x₀ hx₀ π hπ z₀ hz₀).trans_le (hl x₀ hx₀.1)
      exact ih _ hlt _ hPT' hT' hzmax
    · exact ⟨_, _, hPT', hT', not_nonempty_iff_eq_empty.mp hne'⟩
  · exact ⟨Y, T, hPT, hT, not_nonempty_iff_eq_empty.mp hne⟩

end Compact

end

end Hironaka.MonomialCaseLocal
