/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Invariant.MemberRestrictAdmissible
import Hironaka.Invariant.StepOneCompare
import Hironaka.Invariant.InvDomainRebase
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestrictionDrop

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Admissible centres of Step 1ab's restricted marked ideal are admissible centres of `J̄`

Hironaka phase H2 (TN3), for TN-CLASSICAL's property (1) (admissibility) of the Step 1 value function at the non-special
values `(s, λ)`, `s ≥ 1` (`hir:maximal-order-step`); asked I-0977 C-0171, claimed C-0173.  Blueprint
`bcalc:member-restrict-admissible` (chapter `blowup-calculus.tex`).  Source: Włodarczyk 2005 (`wlodarczyk05-hironaka`),
Lemma `le:S` and Step 1a of Proposition `pr:resol`.

Step 1ab computes the value at a point `y` of level `s ≥ 1` from the lower-dimensional invariant of the restricted marked
ideal `𝒮 = memberRestrict 𝔫 S` (`InvDomainMemberRestriction`: the coefficient ideal of `𝔫 = J̄_{T₀}` along `N` restricted to
`N ∩ H_S`, the members of `S` deleted from `E`), on a mask `W`.  Admissibility of the maximum locus (property (1)) is
inherited from the inductive invariant once an admissible centre of the transform of `𝒮` is an admissible centre of the
transform of `𝔫`: this is Włodarczyk's `le:S` for one centre.

* **`isAdmissibleCentre_memberRestrict_iff`**: along a multiple test blow-up `T` of `memberRestrict 𝔪 S` (`𝔪` well formed,
  `d ≥ 1`, `n > 0`), `C` is an admissible centre of its transform iff it is one of `𝔪_T` lying in the strict transform of
  `N ∩ H_S` -- the cosupports by `CoefficientIdealAlongRestrictionFull.cosupp_coeffAlong_withN_tower`, the divisor by
  `NormalCrossingsComparison.isAdmissibleCentre_withE_iff` (the deleted members contain the strict transform of `N ∩ H_S`,
  `DropMembers.isGeoTestTower_withE_iff_of_centresIn_of_snc`);
* **`isAdmissibleCentre_of_lowerMarked_succ`**, `isAdmissibleCentre_lowerMarked_succ_of`: TN-CLASSICAL's form -- along a
  multiple test blow-up `T₀ T₁` of `J̄`, for `y₀` in its own Step 1ab mask `W` and `T₁|_W` a multiple test blow-up of
  `StepOneValue.lowerMarked 𝔍 (s + 1) T₀ y₀`, an admissible centre of the transform of the lower marked ideal along `T₁|_W`
  is an admissible centre of `J̄_{T₀T₁}` restricted to `T₁⁻¹W`, and conversely for centres on the strict transforms of the
  original members through `y₀` (the Step 1ab twin of TN23's `(a1)` for Step 1bb).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MemberRestrictAdmissible

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValue Hironaka.StepOneLowerDomain
  Hironaka.InvDomainMemberRestriction Hironaka.MarkedIdealBiholomorphism
  Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong
  Hironaka.CoefficientIdealRestriction Hironaka.NormalCrossings
  Hironaka.BoundaryCount
open Hironaka.HomogenizedGlueingTower (strictAlong strictAlong_restrict)

noncomputable section

variable {n : ℕ}

/-! ### One admissible centre of the restricted marked ideal -/

section Generic

variable {X : CMfd.{u} n}

/-- **Admissible centres of Step 1ab's restricted marked ideal** (Włodarczyk `le:S` for one centre): along a multiple test
blow-up `T` of `memberRestrict 𝔪 S` (`𝔪` well formed, `d ≥ 1`, `n > 0`), `C` is an admissible centre of the transform of
`memberRestrict 𝔪 S` iff it is an admissible centre of `𝔪_T` contained in the strict transform of `N ∩ H_S`. -/
theorem isAdmissibleCentre_memberRestrict_iff (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed) (hd : 1 ≤ 𝔪.d)
    (S : Finset (Fin 𝔪.E.length)) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (memberRestrict 𝔪 S) T) (C : Set Y) :
    (geoTransformAlong (memberRestrict 𝔪 S) T).IsAdmissibleCentre C ↔
      (geoTransformAlong 𝔪 T).IsAdmissibleCentre C ∧ C ⊆ strictAlong T (𝔪.N ∩ memberInter 𝔪.E S) := by
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
  have hiff := CoefficientIdealAlongRestrictionDrop.coeffAlong_restrict_withE_iff 𝔪 h𝔪 hd
    hS inter_subset_left hsub hA T
  obtain ⟨h𝔪T, hTS⟩ := hiff.1.mp hT
  have hcosR := hiff.2 hT
  have hwfT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔪 T h𝔪T
  have hEeq : (geoTransformAlong (withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ memberInter 𝔪.E S)) T).E =
      (geoTransformAlong 𝔪 T).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ memberInter 𝔪.E S)) (𝔫 := 𝔪) rfl T
  have hcosW := CoefficientIdealAlongRestrictionFull.cosupp_coeffAlong_withN_tower 𝔪 h𝔪.isClosedSubmanifold_N
    h𝔪.isCoherent hd hS inter_subset_left T h𝔪T hTS
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
  have hEsnc : IsSNCDivisor n
      (geoTransformAlong (withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ memberInter 𝔪.E S)) T).E := hEeq ▸ hwfT.isSNCDivisor
  have hstep := DropMembers.isAdmissibleCentre_geoTransformAlong_withE_iff
    (withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ memberInter 𝔪.E S)) (memberRestrict 𝔪 S).E T C
  constructor
  · intro h
    have hCS : C ⊆ strictAlong T (𝔪.N ∩ memberInter 𝔪.E S) := fun x hx => by
      have h' : x ∈ (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T (𝔪.N ∩ memberInter 𝔪.E S) := by
        rw [← hcosR]
        exact h.2.1 hx
      exact h'.2
    have h1 := hstep.mp h
    have h2 := (NormalCrossingsComparison.isAdmissibleCentre_withE_iff _ hEsnc hsubT
      (fun H hH hH' => hCS.trans (hAT H hH hH'))).mp h1
    refine ⟨⟨h2.1, fun x hx => ?_, hEeq ▸ h2.2.2⟩, hCS⟩
    have := h2.2.1 hx
    rw [hcosW] at this
    exact this.1
  · rintro ⟨h, hCS⟩
    refine hstep.mpr ((NormalCrossingsComparison.isAdmissibleCentre_withE_iff _ hEsnc hsubT
      (fun H hH hH' => hCS.trans (hAT H hH hH'))).mpr ⟨h.1, fun x hx => ?_, hEeq.symm ▸ h.2.2⟩)
    rw [hcosW]
    exact ⟨h.2.1 hx, hCS hx⟩

/-- **Admissible centres of the restricted marked ideal, cosupport form**: under the hypotheses of
`isAdmissibleCentre_memberRestrict_iff`, `C` is admissible for the transform of `memberRestrict 𝔪 S` iff it is admissible for
`𝔪_T` and lies in the cosupport of the transform of `memberRestrict 𝔪 S`. -/
theorem isAdmissibleCentre_memberRestrict_iff' (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hd : 1 ≤ 𝔪.d) (S : Finset (Fin 𝔪.E.length)) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (memberRestrict 𝔪 S) T) (C : Set Y) :
    (geoTransformAlong (memberRestrict 𝔪 S) T).IsAdmissibleCentre C ↔
      (geoTransformAlong 𝔪 T).IsAdmissibleCentre C ∧ C ⊆ (geoTransformAlong (memberRestrict 𝔪 S) T).cosupp := by
  classical
  rw [isAdmissibleCentre_memberRestrict_iff hn h𝔪 hd S T hT C]
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
  have hcosR := (CoefficientIdealAlongRestrictionDrop.coeffAlong_restrict_withE_iff 𝔪 h𝔪 hd
    hS inter_subset_left hsub hA T).2 hT
  constructor
  · rintro ⟨h, hCS⟩
    refine ⟨h, fun x hx => ?_⟩
    have h' : x ∈ (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T (𝔪.N ∩ memberInter 𝔪.E S) := ⟨h.2.1 hx, hCS hx⟩
    rw [← hcosR] at h'
    exact h'
  · rintro ⟨h, hCS⟩
    refine ⟨h, fun x hx => ?_⟩
    have h' : x ∈ (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T (𝔪.N ∩ memberInter 𝔪.E S) := by
      rw [← hcosR]
      exact hCS hx
    exact h'.2

end Generic

/-! ### Step 1ab's lower marked ideal on its mask -/

section Masked

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **Admissible centres of Step 1ab's lower marked ideal** (TN-CLASSICAL's form; the Step 1ab twin of TN23's `(a1)` for
Step 1bb): along a multiple test blow-up `T₀ T₁` of `J̄` (`𝔍` well formed, `0 < n`), for `y₀` in its own mask
`W = lowerMask 𝔍 (s + 1) T₀ y₀` and `T₁|_W` a multiple test blow-up of `lowerMarked 𝔍 (s + 1) T₀ y₀`, a set `C` of the open
preimage of `W` is an admissible centre of the transform of the lower marked ideal along `T₁|_W` iff it is an admissible
centre of `J̄_{T₀T₁}` restricted to `T₁⁻¹W` lying on the strict transforms of the original members through `y₀`. -/
theorem isAdmissibleCentre_lowerMarked_succ_iff (h𝔍 : 𝔍.IsWellFormed) (hn : 0 < n) {s : ℕ}
    {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y)
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀} (hy₀ : y₀ ∈ lowerMask 𝔍 (s + 1) T₀ y₀)
    (hTW : IsGeoTestTower (lowerMarked 𝔍 (s + 1) T₀ y₀) (restrict (lowerMask 𝔍 (s + 1) T₀ y₀) T₁))
    (C : Set (openPreimage T₁ (lowerMask 𝔍 (s + 1) T₀ y₀))) :
    (geoTransformAlong (lowerMarked 𝔍 (s + 1) T₀ y₀) (restrict (lowerMask 𝔍 (s + 1) T₀ y₀) T₁)).IsAdmissibleCentre C ↔
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ (lowerMask 𝔍 (s + 1) T₀ y₀) → Y)
        (geoTransformAlong (barMarked 𝔍) (T₀.append T₁))).IsAdmissibleCentre C ∧
        ∀ q ∈ C, ∀ H ∈ origMembers 𝔍 T₀, y₀ ∈ H → (q : Y) ∈ strictAlong T₁ H := by
  classical
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwf : (geoTransformAlong (barMarked 𝔍) T₀).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hd𝔫 : 1 ≤ (geoTransformAlong (barMarked 𝔍) T₀).d := by
    rw [d_geoTransformAlong]; exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hE₀𝔫 : ∀ H ∈ origMembers 𝔍 T₀, H ∈ (geoTransformAlong (barMarked 𝔍) T₀).E :=
    fun H hH => List.mem_of_mem_take hH
  have h1 := InvDomainRebase.pullback_val_memberRestrict_membersThrough hwf hd𝔫 hE₀𝔫
    (lowerMask 𝔍 (s + 1) T₀ y₀) ⟨y₀, hy₀⟩
  have h1' : lowerMarked 𝔍 (s + 1) T₀ y₀ = memberRestrict
      (MarkedIdeal.pullback (Subtype.val : lowerMask 𝔍 (s + 1) T₀ y₀ → Y₀) (geoTransformAlong (barMarked 𝔍) T₀))
      (membersThrough (MarkedIdeal.pullback (Subtype.val : lowerMask 𝔍 (s + 1) T₀ y₀ → Y₀)
          (geoTransformAlong (barMarked 𝔍) T₀)).E
        ((origMembers 𝔍 T₀).map ((Subtype.val : lowerMask 𝔍 (s + 1) T₀ y₀ → Y₀) ⁻¹' ·)) ⟨y₀, hy₀⟩) := h1
  have hwfW := IsWellFormed.pullback_val hwf (lowerMask 𝔍 (s + 1) T₀ y₀)
  have hTW' := h1' ▸ hTW
  have hiff := isAdmissibleCentre_memberRestrict_iff' (X := CMfd.of (n := n) (lowerMask 𝔍 (s + 1) T₀ y₀)) hn hwfW
    hd𝔫 _ _ hTW' C
  rw [← h1', geoTransformAlong_restrict _ hwf.isClosedSubmanifold_N hwf.isCoherent T₁ hT₁,
    ← geoTransformAlong_append] at hiff
  rw [hiff]
  refine and_congr_right fun hadm => ⟨fun hC q hq => ?_, fun hC q hq => ?_⟩
  · exact ((StepOneCompare.mem_cosupp_lowerMarked_succ_iff 𝔍 h𝔍 hn T₀ T₁ hT hy₀ hTW q).mp (hC hq)).2
  · have hJT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ (T₀.append T₁) hT
    have hq' := hadm.2.1 hq
    rw [cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hJT.isCoherent hg)] at hq'
    exact (StepOneCompare.mem_cosupp_lowerMarked_succ_iff 𝔍 h𝔍 hn T₀ T₁ hT hy₀ hTW q).mpr ⟨hq', hC q hq⟩


end Masked
end

end Hironaka.MemberRestrictAdmissible
