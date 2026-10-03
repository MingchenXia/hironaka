/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneCompare
import Hironaka.Invariant.InvDomainRebase
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestrictionDrop
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestrictionFull
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.Invariant.DropMembers
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainMemberRestriction
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneValue
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Admissible centres of Step 1ab's restricted marked ideal are admissible centres of `J̄`

Source: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Lemma `le:S` and Step 1a of Proposition `pr:resol`.

Step 1ab computes the value at a point `y` of level `s ≥ 1` from the lower-dimensional invariant of the restricted marked
ideal `𝒮 = memberRestrict 𝔫 S` (`InvDomainMemberRestriction`: the coefficient ideal of `𝔫 = J̄_{T₀}` along `N` restricted to
`N ∩ H_S`, the members of `S` deleted from `E`), on a mask `W`.  Admissibility of the maximum locus (property (1)) is
inherited from the inductive invariant once an admissible centre of the transform of `𝒮` is an admissible centre of the
transform of `𝔫`: this is Włodarczyk's `le:S` for one centre.

* `isAdmissibleCentre_lowerMarked_succ_of`: form -- along a multiple test blow-up `T₀ T₁` of `J̄`, for `y₀` in its
  own Step 1ab mask `W` and `T₁|_W` a multiple test blow-up of `StepOneValue.lowerMarked 𝔍 (s + 1) T₀ y₀`, an
  admissible centre of the transform of the lower marked ideal along `T₁|_W` is an admissible centre of `J̄_{T₀T₁}`
  restricted to `T₁⁻¹W`, and conversely for centres on the strict transforms of the original members through `y₀`
  (the Step 1ab twin of `(a1)` for Step 1bb).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MemberRestrictAdmissible

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.InvDomainMemberRestriction Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong Hironaka.CoefficientIdealRestriction Hironaka.NormalCrossings Hironaka.BoundaryCount
open Hironaka.HomogenizedGlueingTower (strictAlong strictAlong_restrict)

noncomputable section

variable {n : ℕ}

/-! ### Local forms: on an open set of the last stage

The resolution invariant gives a level set as an admissible centre only of the restriction to an open set `W''` of
the last stage on which the value is bounded, so the transfer is stated there. -/

section Local

/-- **Transfer of an admissible centre on an open set**: for marked ideals `𝔄`, `𝔅` on one manifold with `𝔄` coherent and
`𝔅` well formed, such that the cosupport of `𝔄` lies in that of `𝔅`, the members of `𝔄` are members of `𝔅`, and the members
of `𝔅` missing from `𝔄` contain `cosupp 𝔄`: every admissible centre of `𝔄|_{W''}` is an admissible centre of `𝔅|_{W''}`, for
every open `W''`. -/
theorem isAdmissibleCentre_pullback_val_of_relations {P : CMfd.{u} n} {𝔄 𝔅 : MarkedIdeal n P}
    (h𝔄 : 𝔄.ideal.IsCoherent) (h𝔅 : 𝔅.IsWellFormed) (hsub : ∀ H ∈ 𝔄.E, H ∈ 𝔅.E)
    (hA : ∀ H ∈ 𝔅.E, H ∉ 𝔄.E → 𝔄.cosupp ⊆ H) (hcos : 𝔄.cosupp ⊆ 𝔅.cosupp) (W'' : Opens P) {C : Set W''}
    (h : (MarkedIdeal.pullback (Subtype.val : W'' → P) 𝔄).IsAdmissibleCentre C) :
    (MarkedIdeal.pullback (Subtype.val : W'' → P) 𝔅).IsAdmissibleCentre C := by
  have hC𝔄 : ∀ x ∈ C, (x : P) ∈ 𝔄.cosupp := fun x hx => by
    have hx' := h.2.1 hx
    rwa [cosupp_pullback_val 𝔄 (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      h𝔄 hg) W''] at hx'
  refine ⟨h.1, fun x hx => ?_, ?_⟩
  · rw [cosupp_pullback_val 𝔅 (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      h𝔅.isCoherent hg) W'']
    exact hcos (hC𝔄 x hx)
  · have hSNC := (IsWellFormed.pullback_val h𝔅 W'').isSNCDivisor
    refine (NormalCrossingsComparison.hasNormalCrossings_iff_of_forall_mem hSNC ?_ ?_).mp h.2.2
    · intro H hH
      obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      exact List.mem_map_of_mem (hsub H₀ hH₀)
    · intro H hH hH'
      obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      have hH₀' : H₀ ∉ 𝔄.E := fun h' => hH' (List.mem_map_of_mem h')
      intro x hx
      exact hA H₀ hH₀ hH₀' (hC𝔄 x hx)

variable {X : CMfd.{u} n}

/-- **The divisors and cosupports along a test tower of the restricted marked ideal**: along a multiple test blow-up `T` of
`memberRestrict 𝔪 S` (`𝔪` well formed, `d ≥ 1`, `n > 0`), the members of its transform are members of `𝔪_T`, the members of
`𝔪_T` missing from it contain its cosupport, and its cosupport lies in `cosupp 𝔪_T`. -/
theorem memberRestrict_tower_relations (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed) (hd : 1 ≤ 𝔪.d)
    (S : Finset (Fin 𝔪.E.length)) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (memberRestrict 𝔪 S) T) :
    (∀ H ∈ (geoTransformAlong (memberRestrict 𝔪 S) T).E, H ∈ (geoTransformAlong 𝔪 T).E) ∧
      (∀ H ∈ (geoTransformAlong 𝔪 T).E, H ∉ (geoTransformAlong (memberRestrict 𝔪 S) T).E →
        (geoTransformAlong (memberRestrict 𝔪 S) T).cosupp ⊆ H) ∧
      (geoTransformAlong (memberRestrict 𝔪 S) T).cosupp ⊆ (geoTransformAlong 𝔪 T).cosupp := by
  classical
  have hwfS := isWellFormed_memberRestrict hn h𝔪 S
  have hS : IsClosedSubmanifold n (𝔪.N ∩ memberInter 𝔪.E S) := hwfS.isClosedSubmanifold_N
  have hsub : ∀ H ∈ (memberRestrict 𝔪 S).E, H ∈ 𝔪.E := by
    intro H hH
    rw [memberRestrict_E] at hH
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hH
    exact List.get_mem _ _
  have hA : ∀ H ∈ 𝔪.E, H ∉ (memberRestrict 𝔪 S).E → 𝔪.N ∩ memberInter 𝔪.E S ⊆ H := by
    intro H hH hHS x hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    by_cases hi : i ∈ S
    · exact hx.2 i hi
    · exfalso
      apply hHS
      rw [memberRestrict_E]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true hi⟩)
  have hiff := CoefficientIdealAlongRestrictionDrop.coeffAlong_restrict_withE_iff 𝔪 h𝔪 hd hS inter_subset_left hsub hA T
  obtain ⟨h𝔪T, hTS⟩ := hiff.1.mp hT
  have hcosR := hiff.2 hT
  have hEeq : (geoTransformAlong (withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ memberInter 𝔪.E S)) T).E =
      (geoTransformAlong 𝔪 T).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ memberInter 𝔪.E S)) (𝔫 := 𝔪) rfl T
  have hSNC : ∀ {Y' : CMfd.{u} n} (T' : BlowupTower X Y'),
      IsGeoTestTower (withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ memberInter 𝔪.E S)) T' →
      IsSNCDivisor n (geoTransformAlong (withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ memberInter 𝔪.E S)) T').E := by
    intro Y' T' hT'
    have h𝔪T' := ((CoefficientIdealAlongRestrictionFull.coeffAlong_restrict_tower_iff 𝔪 h𝔪.isClosedSubmanifold_N
      h𝔪.isCoherent hd hS inter_subset_left T').1.mp hT').1
    rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ memberInter 𝔪.E S)) (𝔫 := 𝔪) rfl T']
    exact (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔪 T' h𝔪T').isSNCDivisor
  obtain ⟨-, hsubT, hAT⟩ := DropMembers.isGeoTestTower_withE_iff_of_centresIn_of_snc
    (withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ memberInter 𝔪.E S)) hSNC hsub hA T hTS
  have hcosS : (geoTransformAlong (memberRestrict 𝔪 S) T).cosupp ⊆
      (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T (𝔪.N ∩ memberInter 𝔪.E S) := by
    intro x hx
    rw [← hcosR]
    exact hx
  refine ⟨fun H hH => hEeq ▸ hsubT H hH, fun H hH hH' => ?_, fun x hx => (hcosS hx).1⟩
  rw [← hEeq] at hH
  exact fun x hx => hAT H hH hH' (hcosS hx).2

/-- **(m1-loc)**: an admissible centre of the transform of `memberRestrict 𝔪 S`, restricted to an open set `W''` of the last
stage, is an admissible centre of `𝔪_T` restricted to `W''` (`𝔪` well formed, `d ≥ 1`, `n > 0`, `T` a multiple test blow-up
of `memberRestrict 𝔪 S`). -/
theorem isAdmissibleCentre_pullback_val_of_memberRestrict (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hd : 1 ≤ 𝔪.d) (S : Finset (Fin 𝔪.E.length)) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (memberRestrict 𝔪 S) T) (W'' : Opens Y) {C : Set W''}
    (h : (MarkedIdeal.pullback (Subtype.val : W'' → Y) (geoTransformAlong (memberRestrict 𝔪 S) T)).IsAdmissibleCentre C) :
    (MarkedIdeal.pullback (Subtype.val : W'' → Y) (geoTransformAlong 𝔪 T)).IsAdmissibleCentre C := by
  classical
  have hwfS := isWellFormed_memberRestrict hn h𝔪 S
  have hS : IsClosedSubmanifold n (𝔪.N ∩ memberInter 𝔪.E S) := hwfS.isClosedSubmanifold_N
  have hsub : ∀ H ∈ (memberRestrict 𝔪 S).E, H ∈ 𝔪.E := by
    intro H hH
    rw [memberRestrict_E] at hH
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hH
    exact List.get_mem _ _
  have hA : ∀ H ∈ 𝔪.E, H ∉ (memberRestrict 𝔪 S).E → 𝔪.N ∩ memberInter 𝔪.E S ⊆ H := by
    intro H hH hHS x hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    by_cases hi : i ∈ S
    · exact hx.2 i hi
    · exfalso
      apply hHS
      rw [memberRestrict_E]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true hi⟩)
  have h𝔪T := ((CoefficientIdealAlongRestrictionDrop.coeffAlong_restrict_withE_iff 𝔪 h𝔪 hd hS inter_subset_left
    hsub hA T).1.mp hT).1
  obtain ⟨hsubT, hAT, hcosT⟩ := memberRestrict_tower_relations hn h𝔪 hd S T hT
  have hwfT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔪 T h𝔪T
  have hwfST := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfS T hT
  exact isAdmissibleCentre_pullback_val_of_relations hwfST.isCoherent hwfT hsubT hAT hcosT W'' h

theorem isAdmissibleCentre_pullback_val_of_lowerMarked_succ {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)
    (h𝔍 : 𝔍.IsWellFormed) (hn : 0 < n) {s : ℕ} {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y)
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀} (hy₀ : y₀ ∈ lowerMask 𝔍 (s + 1) T₀ y₀)
    (hTW : IsGeoTestTower (lowerMarked 𝔍 (s + 1) T₀ y₀) (restrict (lowerMask 𝔍 (s + 1) T₀ y₀) T₁))
    (W'' : Opens (openPreimage T₁ (lowerMask 𝔍 (s + 1) T₀ y₀))) {C : Set W''}
    (h : (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ (lowerMask 𝔍 (s + 1) T₀ y₀))
      (geoTransformAlong (lowerMarked 𝔍 (s + 1) T₀ y₀) (restrict (lowerMask 𝔍 (s + 1) T₀ y₀) T₁))).IsAdmissibleCentre C) :
    (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ (lowerMask 𝔍 (s + 1) T₀ y₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ (lowerMask 𝔍 (s + 1) T₀ y₀) → Y)
        (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)))).IsAdmissibleCentre C := by
  classical
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwf : (geoTransformAlong (barMarked 𝔍) T₀).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hd𝔫 : 1 ≤ (geoTransformAlong (barMarked 𝔍) T₀).d := by
    rw [d_geoTransformAlong]; exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hE₀𝔫 : ∀ H ∈ origMembers 𝔍 T₀, H ∈ (geoTransformAlong (barMarked 𝔍) T₀).E :=
    fun H hH => List.mem_of_mem_take hH
  have h1' : lowerMarked 𝔍 (s + 1) T₀ y₀ = memberRestrict
      (MarkedIdeal.pullback (Subtype.val : lowerMask 𝔍 (s + 1) T₀ y₀ → Y₀) (geoTransformAlong (barMarked 𝔍) T₀))
      (membersThrough (MarkedIdeal.pullback (Subtype.val : lowerMask 𝔍 (s + 1) T₀ y₀ → Y₀)
          (geoTransformAlong (barMarked 𝔍) T₀)).E
        ((origMembers 𝔍 T₀).map ((Subtype.val : lowerMask 𝔍 (s + 1) T₀ y₀ → Y₀) ⁻¹' ·)) ⟨y₀, hy₀⟩) :=
    InvDomainRebase.pullback_val_memberRestrict_membersThrough hwf hd𝔫 hE₀𝔫 (lowerMask 𝔍 (s + 1) T₀ y₀) ⟨y₀, hy₀⟩
  have hwfW := IsWellFormed.pullback_val hwf (lowerMask 𝔍 (s + 1) T₀ y₀)
  have hTW' := h1' ▸ hTW
  have h' := h1' ▸ h
  have hres := isAdmissibleCentre_pullback_val_of_memberRestrict (X := CMfd.of (n := n) (lowerMask 𝔍 (s + 1) T₀ y₀))
    (Y := CMfd.of (n := n) (openPreimage T₁ (lowerMask 𝔍 (s + 1) T₀ y₀))) hn hwfW hd𝔫 _ _ hTW' W'' h'
  rw [geoTransformAlong_restrict _ hwf.isClosedSubmanifold_N hwf.isCoherent T₁ hT₁, ← geoTransformAlong_append] at hres
  exact hres

end Local

end

end Hironaka.MemberRestrictAdmissible
