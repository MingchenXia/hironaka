/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ContactLowerValue
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.Invariant.ContactMarkedCanonical
import Hironaka.Invariant.ContactRepresentative
import Hironaka.Invariant.ContactStageKept
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainMemberRestriction
import Hironaka.Invariant.InvDomainRebase
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneNearby
import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.StepOneValueMasked
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1ab's lower values under biholomorphisms, restriction to open sets and representatives

The Step 1ab twins of `ContactLowerValue` (level `0`). Source: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 1a of
Proposition `pr:resol` and the commutativity of the resolution with étale morphisms.

At a point of level `s + 1` the lower value is the value of the inductive invariant `R` for Step 1ab's restricted marked ideal
`𝔐 = memberRestrict J̄_{T₀} (members through the image)` (`InvDomainMemberRestriction.memberRestrict`), restricted to the mask
`maskA`, along the restricted tail.  This module shows:

* `mem_of_preimage_mem_map_diffeo`, **`pullback_diffeo_memberRestrict_membersThrough`**: Step 1ab's restricted marked ideal
  commutes with pullback along a biholomorphism (the twin of `InvDomainRebase.pullback_val_memberRestrict_membersThrough`);
* **`lowerValueL_succ_eq`** (the anchor): the lower value at level `s + 1` is the value of `R` for `𝔐` restricted to ANY open
  set around the image on which the restricted tail is a canonical segment (two open sets,
  `StepOneNearby.inv_eq_of_two_opens`);
* **`lowerValueL_succ_isTowerIso`** (property (6) at levels `s + 1`): with lower data on both sides, the lower values at
  corresponding points of isomorphic towers agree;
* `inv_pullback_isTowerIso` (property (6) of `R`, packaged: domain, canonical segment, cosupport and values
  transported along an isomorphism of towers), **`lowerValueL_succ_restrict`** (property (5) at levels `s + 1`,
  `(t5)` shape): restriction to an open set of the base;
* `restrictEquiv_memberRestrict_membersThrough`, **`lowerValueL_succ_representative`** (property (7) at levels `s +
  1`, `(t7)` shape): restricted-equivalent representatives have restricted-equivalent restricted marked ideals and
  the same lower values.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.MemberRestrictTowerIso

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedIdealAlong MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupTowerIsomorphism ResolutionInvariantExt StepOneTangentChange InvDomainMemberRestriction InvDomainRebase StepOneValue StepOneLowerDomain StepOneValueMasked StepOneNearby BoundaryCount
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Step 1ab's restricted marked ideal along a biholomorphism -/

section Diffeo

variable {M M' : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- A set whose preimage under a biholomorphism is the preimage of a member of `E₀` is that member. -/
theorem mem_of_preimage_mem_map_diffeo (χ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M)
    {E₀ : List (Set M)} {H : Set M} (h : χ ⁻¹' H ∈ E₀.map (χ ⁻¹' ·)) : H ∈ E₀ := by
  obtain ⟨H₀, hH₀, hpre⟩ := List.mem_map.mp h
  have hH : H₀ = H := by
    ext x
    have := congrArg (fun s : Set M' => χ.symm x ∈ s) hpre
    simpa using this
  rw [← hH]
  exact hH₀

/-- **Step 1ab's restricted marked ideal commutes with biholomorphisms**: for `𝔪` well formed with `d ≥ 1`, a list `E₀` of
sets and a point `p`, the pullback along `χ` of the restricted marked ideal at `χ p` is the restricted marked ideal of `χ^*𝔪`
at `p`, with the preimages of the members of `E₀`. -/
theorem pullback_diffeo_memberRestrict_membersThrough (χ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M)
    {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed) (hd : 1 ≤ 𝔪.d) (E₀ : List (Set M)) (p : M') :
    MarkedIdeal.pullback χ (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ (χ p))) =
      memberRestrict (MarkedIdeal.pullback χ 𝔪)
        (membersThrough (MarkedIdeal.pullback χ 𝔪).E (E₀.map (χ ⁻¹' ·)) p) := by
  have hcoeff := HomogenizedIdealAlong.pullback_coeffMarkedAlong_of_inverse χ.contMDiff χ.symm.contMDiff
    χ.apply_symm_apply χ.symm_apply_apply 𝔪 h𝔪.isCoherent h𝔪.isClosedSubmanifold_N hd
  have hI := congrArg MarkedIdeal.ideal hcoeff
  have hD := congrArg MarkedIdeal.d hcoeff
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ hI hD
  · show χ ⁻¹' (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ (χ p))).N = _
    rw [memberRestrict_membersThrough_N, memberRestrict_membersThrough_N]
    ext q
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
    refine and_congr_right fun _ => ⟨fun hw H' hH' hH'₀ hpH' => ?_, fun hw H hH hH₀ hpH => ?_⟩
    · obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      exact hw H hH (mem_of_preimage_mem_map_diffeo χ hH'₀) hpH'
    · exact hw _ (List.mem_map_of_mem hH) (List.mem_map_of_mem hH₀) hpH
  · show (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ (χ p))).E.map (χ ⁻¹' ·) = _
    rw [memberRestrict_membersThrough_E, memberRestrict_membersThrough_E]
    exact (filter_map_members (f := (χ ⁻¹' ·)) (y := χ p) (y' := p) (fun H _ => Iff.rfl)
      fun H _ _ h => mem_of_preimage_mem_map_diffeo χ h).symm

end Diffeo

/-! ### The anchor: the lower value at level `s + 1` on any open set -/

section Anchor

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The lower value at level `s + 1` on any open set** (the anchor): let `𝔍` be well formed (`n > 0`), `T₀ T₁` a multiple
test blow-up of `J̄`, and `p` with lower data at level `s + 1` at the split `T₀ T₁`.  For every open `W` of the stage of `T₀`
containing the image of `p` on which Step 1ab's restricted marked ideal `𝔐` (at the members through that image) lies in the
domain of `R`, with `T₁|_W` a canonical segment of it, the lower value of `p` is the value of `R` for `𝔐|_W` along `T₁|_W`. -/
theorem lowerValueL_succ_eq (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (hn : 0 < n) {s : ℕ} {Y₀ Z : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Z)
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {p : Z}
    (hD : LowerDataL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀ T₁ p) (W : Opens Y₀) (hpW : T₁.proj p ∈ W)
    (hdomW : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → Y₀)
      (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
        (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj p)))))
    (hcanW : IsCanonical (MarkedIdeal.pullback (Subtype.val : W → Y₀)
        (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
          (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj p))))
      (R.inv (MarkedIdeal.pullback (Subtype.val : W → Y₀)
        (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
          (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj p)))))
      (restrict W T₁)) :
    lowerValueL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀ T₁ p =
      ((R.inv (MarkedIdeal.pullback (Subtype.val : W → Y₀)
        (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
          (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj p)))) (restrict W T₁)
          ⟨p, hpW⟩ : Λ) : WithTop Λ) := by
  obtain ⟨h, hdom₀, hcan₀, hcos₀⟩ := hD
  rw [lowerValueL_eq_of_mem R 𝔍 _ h]
  congr 1
  have hT₀ := ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1
  have hwf : (geoTransformAlong (barMarked 𝔍) T₀).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong (isWellFormed_barMarked 𝔍 h𝔍) T₀ hT₀
  have hwfS := isWellFormed_memberRestrict hn hwf
    (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj p))
  exact (inv_eq_of_two_opens R hwfS.isClosedSubmanifold_N hwfS.isCoherent T₁ hdom₀ hcan₀ hdomW hcanW h hpW hcos₀).1

end Anchor

/-! ### Property (6): isomorphisms of towers -/

section TowerIso

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {k : ℕ} {Λ : Type v}
  [LinearOrder Λ]

/-- **Property (6) of the masked Step 1 value function at the levels `s + 1`, lower values**: let `𝔍` be well formed with
`d ≥ 1` (`n > 0`), `T₀' ≅ T₀` an isomorphism of towers over `Φ : X' ≅ X` with last-stage map `χ₀`, `T₁' ≅ T₁` one over `χ₀`
with last-stage map `χ` (the split of an isomorphism `T₀' T₁' ≅ T₀ T₁`, `BlowupTowerSplitIso.IsTowerIso.exists_split`), and
`T₀ T₁` a multiple test blow-up of `J̄`.  If `p'` has lower data at level `s + 1` for `Φ^*𝔍` at the split `T₀' T₁'` and `χ p'`
has lower data at level `s + 1` for `𝔍` at the split `T₀ T₁`, the two lower values agree.  (Step 1ab's restricted marked ideal
is transported along `χ₀` (`pullback_diffeo_memberRestrict_membersThrough`), its values along the restricted tails by property
(6) of `R`, and the anchor `lowerValueL_succ_eq` for `Φ^*𝔍` on the preimage of the mask of `χ p'`.) -/
theorem lowerValueL_succ_isTowerIso (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X)
    (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n) {s : ℕ} {Y₀' Y₀ Z' Z : CMfd.{u} n}
    {T₀' : BlowupTower X' Y₀'} {T₀ : BlowupTower X Y₀}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀} (hiso : IsTowerIso Φ T₀' T₀ χ₀)
    {T₁' : BlowupTower Y₀' Z'} {T₁ : BlowupTower Y₀ Z} {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z}
    (hχ : IsTowerIso χ₀ T₁' T₁ χ) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {p' : Z'}
    (hD' : LowerDataL R (MarkedIdeal.pullback Φ 𝔍) (lowerMarkedM (MarkedIdeal.pullback Φ 𝔍)) (s + 1) T₀' T₁' p')
    (hD : LowerDataL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀ T₁ (χ p')) :
    lowerValueL R (MarkedIdeal.pullback Φ 𝔍) (lowerMarkedM (MarkedIdeal.pullback Φ 𝔍)) (s + 1) T₀' T₁' p' =
      lowerValueL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀ T₁ (χ p') := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍' : (MarkedIdeal.pullback Φ 𝔍).IsWellFormed := MarkedIdealTowerTransport.IsWellFormed.pullback h𝔍
  have hbar : barMarked (MarkedIdeal.pullback Φ 𝔍) = MarkedIdeal.pullback Φ (barMarked 𝔍) :=
    ContactStageKept.barMarked_pullback Φ h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd
  have hT₀ : IsGeoTestTower (barMarked 𝔍) T₀ := ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1
  have hiso' : IsTowerIso Φ (T₀'.append T₁') (T₀.append T₁) χ := hiso.append hχ
  have hT' : IsGeoTestTower (barMarked (MarkedIdeal.pullback Φ 𝔍)) (T₀'.append T₁') := by
    rw [hbar]
    exact (IsTowerIso.isGeoTestTower_iff Φ hJ.isClosedSubmanifold_N hJ.isCoherent hiso').mpr hT
  -- the stage `T₀` on both sides
  have h𝔫' : geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) T₀' =
      MarkedIdeal.pullback χ₀ (geoTransformAlong (barMarked 𝔍) T₀) := by
    rw [hbar]
    exact IsTowerIso.geoTransformAlong_eq Φ hJ.isClosedSubmanifold_N hJ.isCoherent hiso hT₀
  have hOrig := ContactLowerValue.origMembers_isTowerIso Φ 𝔍 h𝔍 hd hiso hT₀
  have hwf : (geoTransformAlong (barMarked 𝔍) T₀).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hd𝔫 : 1 ≤ (geoTransformAlong (barMarked 𝔍) T₀).d := by
    rw [d_geoTransformAlong]; exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hy : χ₀ (T₁'.proj p') = T₁.proj (χ p') := hχ.proj_comm p'
  -- Step 1ab's restricted marked ideal of `Φ^*𝔍` at the image of `p'` is the transport of that of `𝔍` at the image of `χ p'`
  have hM : memberRestrict (geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) T₀')
      (membersThrough (geoTransformAlong (barMarked (MarkedIdeal.pullback Φ 𝔍)) T₀').E
        (origMembers (MarkedIdeal.pullback Φ 𝔍) T₀') (T₁'.proj p')) =
      MarkedIdeal.pullback χ₀ (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
        (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj (χ p')))) := by
    rw [h𝔫', hOrig, ← hy]
    exact (pullback_diffeo_memberRestrict_membersThrough χ₀ hwf hd𝔫 _ _).symm
  have hwfS := isWellFormed_memberRestrict hn hwf
    (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj (χ p')))
  -- the data on the side of `𝔍`, on the mask `A` of `χ p'`
  obtain ⟨h, hdom, hcan, hcos⟩ := hD
  set A : Opens Y₀ := lowerMask 𝔍 (s + 1) T₀ (T₁.proj (χ p')) with hAdef
  set W' : Opens Y₀' := ⟨χ₀ ⁻¹' (A : Set Y₀), A.isOpen.preimage χ₀.continuous⟩ with hW'def
  have hW' : ∀ q, q ∈ W' ↔ χ₀ q ∈ A := fun _ => Iff.rfl
  have hξ := isTowerIso_restrictOpens hW' hχ (isTowerIso_mem_openPreimage_iff hχ hW')
  have hpb : MarkedIdeal.pullback (Subtype.val : W' → Y₀')
      (MarkedIdeal.pullback χ₀ (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
        (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj (χ p'))))) =
      MarkedIdeal.pullback (diffeoOpens χ₀ W' A hW') (MarkedIdeal.pullback (Subtype.val : A → Y₀)
        (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
          (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj (χ p'))))) :=
    ContactMarkedCanonical.pullback_pullback_of_comp_eq hwfS.isCoherent χ₀.contMDiff contMDiff_subtype_val
      (diffeoOpens χ₀ W' A hW').contMDiff contMDiff_subtype_val fun _ => rfl
  have hdomA : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : A → Y₀)
      (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
        (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj (χ p'))))) := hdom
  have hcanA : IsCanonical (MarkedIdeal.pullback (Subtype.val : A → Y₀)
        (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
          (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj (χ p')))))
      (R.inv (MarkedIdeal.pullback (Subtype.val : A → Y₀)
        (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
          (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj (χ p'))))))
      (restrict A T₁) := hcan
  -- domain and canonical segment on the preimage `W'` of the mask, for `Φ^*𝔍`
  have hdomW' := InvDomainTowerAlong.isInvDomain_pullback (diffeoOpens χ₀ W' A hW') hdomA
  have hcanW' := isCanonical_of_isTowerIso R hdomA (diffeoOpens χ₀ W' A hW') hξ hcanA
  rw [← hpb, ← hM] at hdomW' hcanW'
  have hpW' : T₁'.proj p' ∈ W' := by
    show χ₀ (T₁'.proj p') ∈ A
    rw [hy]
    exact h
  have key := lowerValueL_succ_eq R (MarkedIdeal.pullback Φ 𝔍) h𝔍' hn T₀' T₁' hT' hD' W' hpW' hdomW' hcanW'
  rw [key, lowerValueL_eq_of_mem R 𝔍 _ h]
  congr 1
  have hpq : diffeoOpens χ (openPreimage T₁' W') (openPreimage T₁ A) (isTowerIso_mem_openPreimage_iff hχ hW')
      ⟨p', hpW'⟩ = ⟨χ p', h⟩ := Subtype.ext rfl
  have hval := R.towerIso _ _ hdomA _ _ _ hξ hcanA ⟨p', hpW'⟩ (by rw [hpq]; exact hcos)
  rw [hpq] at hval
  rw [hM, hpb]
  exact hval

end TowerIso

/-! ### Transport along an isomorphism of towers -/

section Transport

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Values along an isomorphism of towers** (property (6) of `R`, packaged): for `𝔄` in the domain with `S` a canonical
segment, `ψ : B' ≅ B` and `S' ≅ S` over `ψ` with last-stage map `ξ`, the transport `ψ^*𝔄` lies in the domain, `S'` is a canonical
segment of it, and at a point `p` with `ξ p` in the cosupport along `S`, `p` lies in the cosupport along `S'` and the values
agree. -/
theorem inv_pullback_isTowerIso (R : ResolutionInvariant.{u, v} n k Λ) {B B' : CMfd.{u} n} {𝔄 : MarkedIdeal n B}
    (hdom : IsInvDomain k 𝔄) (ψ : B' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B) {Y' Y : CMfd.{u} n}
    {S' : BlowupTower B' Y'} {S : BlowupTower B Y} {ξ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hiso : IsTowerIso ψ S' S ξ) (hcan : IsCanonical 𝔄 (R.inv 𝔄) S) :
    IsInvDomain k (MarkedIdeal.pullback ψ 𝔄) ∧ IsCanonical (MarkedIdeal.pullback ψ 𝔄) (R.inv (MarkedIdeal.pullback ψ 𝔄)) S' ∧
      ∀ p : Y', ξ p ∈ (geoTransformAlong 𝔄 S).cosupp →
        p ∈ (geoTransformAlong (MarkedIdeal.pullback ψ 𝔄) S').cosupp ∧
          R.inv (MarkedIdeal.pullback ψ 𝔄) S' p = R.inv 𝔄 S (ξ p) := by
  refine ⟨InvDomainTowerAlong.isInvDomain_pullback ψ hdom, isCanonical_of_isTowerIso R hdom ψ hiso hcan,
    fun p hp => ⟨?_, R.towerIso ψ 𝔄 hdom S' S ξ hiso hcan p hp⟩⟩
  have hTt := isGeoTestTower_of_isCanonical R hdom S hcan
  rw [IsTowerIso.cosupp_geoTransformAlong ψ hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent hiso hTt]
  exact hp

end Transport

/-! ### Property (5): restriction to an open set of the base -/

section Restrict

variable {X : CMfd.{u} n} (U : Opens X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Property (5) of the masked Step 1 value function at the levels `s + 1`, lower values** (`(t5)` shape): let `𝔍` be
well formed with `d ≥ 1` (`n > 0`), `T₀ T₁` a multiple test blow-up of `J̄`, `U` open in the base, and `T₀' ≅ T₀|_U`
over the identity of `U` with last-stage map `χ₀`, `T₁' ≅ T₁|_{T₀⁻¹U}` over `χ₀` with last-stage map `χ` (the split
of `T|_U`, `BlowupTowerSplitIso.exists_isTowerIso_split_restrict`). If `p'` has lower data at level `s + 1` for
`𝔍|_U` at the split `T₀' T₁'` and `χ p'` has lower data at level `s + 1` for `𝔍` at the split `T₀ T₁`, the two lower
values agree. -/
theorem lowerValueL_succ_restrict (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) (hn : 0 < n) {s : ℕ} {Y₀ Z Y₀' Z' : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Z}
    {T₀' : BlowupTower (CMfd.of (n := n) U) Y₀'}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₀ U)}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) T₀' (restrict U T₀) χ₀)
    {T₁' : BlowupTower Y₀' Z'}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ U))}
    (hχ : IsTowerIso χ₀ T₁' (restrict (openPreimage T₀ U) T₁) χ) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁))
    {p' : Z'}
    (hD' : LowerDataL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
      (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (s + 1) T₀' T₁' p')
    (hD : LowerDataL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀ T₁ ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)) :
    lowerValueL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (s + 1) T₀' T₁' p' =
      lowerValueL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀ T₁ ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍U : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).IsWellFormed :=
    MarkedIdealRestrictOpen.IsWellFormed.pullback_val h𝔍 U
  have hJU := isWellFormed_barMarked (X := CMfd.of (n := n) U) _ h𝔍U
  have hbarU : barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) :=
    ContactStageKept.barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  have hwf : (geoTransformAlong (barMarked 𝔍) T₀).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hd𝔫 : 1 ≤ (geoTransformAlong (barMarked 𝔍) T₀).d := by
    rw [d_geoTransformAlong]; exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hE₀𝔫 : ∀ H ∈ origMembers 𝔍 T₀, H ∈ (geoTransformAlong (barMarked 𝔍) T₀).E :=
    fun H hH => List.mem_of_mem_take hH
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
    T₀ hT₀
  -- the restricted towers and the test tower on the side of `𝔍|_U`
  have hT₀U : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T₀) := by
    rw [hbarU]
    exact isGeoTestTower_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hgU : geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T₀) = MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) (geoTransformAlong (barMarked 𝔍) T₀) := by
    rw [hbarU]
    exact geoTransformAlong_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hRU : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      ((restrict U T₀).append (restrict (openPreimage T₀ U) T₁)) := by
    refine (isGeoTestTower_append_iff _ _ _).mpr ⟨hT₀U, ?_⟩
    rw [hgU]
    exact isGeoTestTower_restrict (openPreimage T₀ U) hNT hcT T₁ hT₁
  have hiso' := hiso.append hχ
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) =
      barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) :=
    ContactCanonicalAlong.pullback_id _ hJU.isCoherent
  have hT' : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (T₀'.append T₁') := by
    have h1 := (IsTowerIso.isGeoTestTower_iff _ hJU.isClosedSubmanifold_N hJU.isCoherent hiso').mpr hRU
    rwa [hpb] at h1
  -- the stage `T₀'` and its original members
  have h𝔫' : geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) T₀' =
      MarkedIdeal.pullback χ₀ (MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) (geoTransformAlong (barMarked 𝔍) T₀)) := by
    have h1 := IsTowerIso.geoTransformAlong_eq _ hJU.isClosedSubmanifold_N hJU.isCoherent hiso hT₀U
    rw [hpb, hgU] at h1
    exact h1
  have hOrig : origMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀' =
      ((origMembers 𝔍 T₀).map ((Subtype.val : (openPreimage T₀ U) → Y₀) ⁻¹' ·)).map (χ₀ ⁻¹' ·) := by
    have e := ContactLowerValue.origMembers_isTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      _ h𝔍U hd hiso hT₀U
    have hpbU : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
        (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) = MarkedIdeal.pullback (Subtype.val : U → X) 𝔍 :=
      ContactCanonicalAlong.pullback_id _ h𝔍U.isCoherent
    rw [hpbU, ContactLowerValue.origMembers_restrict U 𝔍 h𝔍 hd hT₀] at e
    exact e
  -- the points
  have hy : χ₀ (T₁'.proj p') = (restrict (openPreimage T₀ U) T₁).proj (χ p') := hχ.proj_comm p'
  have hy' : (((restrict (openPreimage T₀ U) T₁).proj (χ p') : (openPreimage T₀ U)) : Y₀) = T₁.proj ((χ p') : Z) := proj_restrict _ T₁ (χ p')
  -- Step 1ab's restricted marked ideal of `𝔍|_U` at the image of `p'`
  set 𝔐 : MarkedIdeal n Y₀ := memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
    (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj ((χ p') : Z))) with h𝔐def
  have hwfS : 𝔐.IsWellFormed := isWellFormed_memberRestrict hn hwf _
  have hM : memberRestrict (geoTransformAlong (barMarked (X := CMfd.of (n := n) U)
        (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) T₀')
      (membersThrough (geoTransformAlong (barMarked (X := CMfd.of (n := n) U)
          (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) T₀').E
        (origMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀') (T₁'.proj p')) =
      MarkedIdeal.pullback χ₀ (MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) 𝔐) := by
    rw [h𝔫', hOrig]
    rw [← pullback_diffeo_memberRestrict_membersThrough χ₀ (IsWellFormed.pullback_val hwf (openPreimage T₀ U)) hd𝔫 _ (T₁'.proj p'), hy]
    congr 1
    have e := InvDomainRebase.pullback_val_memberRestrict_membersThrough hwf hd𝔫 hE₀𝔫 (openPreimage T₀ U) ((restrict (openPreimage T₀ U) T₁).proj (χ p'))
    rw [hy'] at e
    exact e.symm
  -- the data on the side of `𝔍`: the mask `A` of `(χ p')`, shrunk to `W₁ = A ∩ (openPreimage T₀ U)`
  obtain ⟨h, hdom, hcan, hcos⟩ := hD
  set A : Opens Y₀ := lowerMask 𝔍 (s + 1) T₀ (T₁.proj ((χ p') : Z)) with hAdef
  have hdomA : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : A → Y₀) 𝔐) := hdom
  have hcanA : IsCanonical (MarkedIdeal.pullback (Subtype.val : A → Y₀) 𝔐)
      (R.inv (MarkedIdeal.pullback (Subtype.val : A → Y₀) 𝔐)) (restrict A T₁) := hcan
  have hcosA : (⟨((χ p') : Z), h⟩ : openPreimage T₁ A) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : A → Y₀) 𝔐) (restrict A T₁)).cosupp := hcos
  set W₁ : Opens Y₀ := A ⊓ (openPreimage T₀ U) with hW₁def
  have hW₁A : W₁ ≤ A := inf_le_left
  have hW₁V : W₁ ≤ (openPreimage T₀ U) := inf_le_right
  obtain ⟨hdom₁, hcan₁, -⟩ := MaxLocusLocal.restrict_nestedOpens R hwfS.isCoherent hW₁A hdomA T₁ hcanA
  have hz₁ : T₁.proj ((χ p') : Z) ∈ W₁ := ⟨h, (χ p').2⟩
  obtain ⟨hv₁, hcos₁⟩ := inv_eq_of_two_opens R hwfS.isClosedSubmanifold_N hwfS.isCoherent T₁ hdomA hcanA hdom₁ hcan₁
    h hz₁ hcosA
  -- `(𝔐|_V)|_{W₂}` is `𝔐|_{W₁}` transported along `nestedOpensDiffeo`
  set W₂ : Opens (CMfd.of (n := n) (openPreimage T₀ U)) := MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁ with hW₂def
  have hiso₂ := MaxLocusLocal.isTowerIso_restrict_nestedOpens (X := Y₀) hW₁V T₁
  obtain ⟨hdom₂, hcan₂, hval₂⟩ := inv_pullback_isTowerIso R hdom₁ (MaxLocusLocal.nestedOpensDiffeo (n := n) hW₁V)
    hiso₂ hcan₁
  have hpb₂ := MaxLocusLocal.pullback_val_pullback_val (M := Y₀) hwfS.isCoherent hW₁V
  rw [← hpb₂] at hdom₂ hcan₂ hval₂
  have hq₂ : (χ p') ∈ openPreimage (restrict (openPreimage T₀ U) T₁) W₂ :=
    (MaxLocusLocal.mem_openPreimage_restrict_nestedOpens (openPreimage T₀ U) W₁ T₁ (χ p')).mpr hz₁
  have hξ₂ : MaxLocusLocal.nestedDiffeo (n := n) (openPreimage T₁ (openPreimage T₀ U)) (openPreimage (restrict (openPreimage T₀ U) T₁) W₂) (openPreimage T₁ W₁)
      (MaxLocusLocal.mem_openPreimage_restrict_nestedOpens (openPreimage T₀ U) W₁ T₁) (MaxLocusLocal.openPreimage_mono T₁ hW₁V)
      ⟨(χ p'), hq₂⟩ = ⟨((χ p') : Z), hz₁⟩ := rfl
  obtain ⟨hcosq₂, hvq₂⟩ := hval₂ ⟨(χ p'), hq₂⟩ (by rw [hξ₂]; exact hcos₁)
  rw [hξ₂] at hvq₂
  -- transport along `χ₀` to `W' = χ₀⁻¹ W₂`
  set W' : Opens Y₀' := ⟨χ₀ ⁻¹' (W₂ : Set (CMfd.of (n := n) (openPreimage T₀ U))), W₂.isOpen.preimage χ₀.continuous⟩ with hW'def
  have hW' : ∀ r, r ∈ W' ↔ χ₀ r ∈ W₂ := fun _ => Iff.rfl
  have hξ := isTowerIso_restrictOpens hW' hχ (isTowerIso_mem_openPreimage_iff hχ hW')
  have hwfV : (MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) 𝔐).ideal.IsCoherent :=
    (IsWellFormed.pullback_val hwfS (openPreimage T₀ U)).isCoherent
  obtain ⟨hdom₃, hcan₃, hval₃⟩ := inv_pullback_isTowerIso R hdom₂ (diffeoOpens χ₀ W' W₂ hW') hξ hcan₂
  have hpb₃ : MarkedIdeal.pullback (Subtype.val : W' → Y₀')
      (MarkedIdeal.pullback χ₀ (MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) 𝔐)) =
      MarkedIdeal.pullback (diffeoOpens χ₀ W' W₂ hW')
        (MarkedIdeal.pullback (Subtype.val : W₂ → CMfd.of (n := n) (openPreimage T₀ U)) (MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) 𝔐)) :=
    ContactMarkedCanonical.pullback_pullback_of_comp_eq hwfV χ₀.contMDiff contMDiff_subtype_val
      (diffeoOpens χ₀ W' W₂ hW').contMDiff contMDiff_subtype_val fun _ => rfl
  rw [← hpb₃, ← hM] at hdom₃ hcan₃ hval₃
  have hpW' : T₁'.proj p' ∈ W' := by
    show χ₀ (T₁'.proj p') ∈ W₂
    rw [hy]
    exact hq₂
  have hξp : diffeoOpens χ (openPreimage T₁' W') (openPreimage (restrict (openPreimage T₀ U) T₁) W₂) (isTowerIso_mem_openPreimage_iff hχ hW')
      ⟨p', hpW'⟩ = ⟨(χ p'), hq₂⟩ := Subtype.ext rfl
  obtain ⟨-, hvp⟩ := hval₃ ⟨p', hpW'⟩ (by rw [hξp]; exact hcosq₂)
  rw [hξp] at hvp
  -- the anchors on both sides
  have key' := lowerValueL_succ_eq (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) h𝔍U hn
    T₀' T₁' hT' hD' W' hpW' hdom₃ hcan₃
  rw [key', lowerValueL_eq_of_mem R 𝔍 _ h]
  congr 1
  exact hvp.trans (hvq₂.trans hv₁.symm)

end Restrict

/-! ### Property (7): independence of the representative -/

section Representative

open MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Step 1ab's restricted marked ideal does not depend on the representative**: for `𝔍` well formed and `𝔍 ≃ 𝔍'`
restricted-equivalent with `𝔍'` coherent, at the last stage of every tower `T₀` and at every point `y₀`, Step 1ab's restricted
marked ideals of `J̄_{T₀}` and `J̄'_{T₀}` at the original members through `y₀` are restricted-equivalent (the coefficient ideals of
the transforms are restricted-equivalent, `ContactCanonicalAlong.restrictEquiv_coeffMarkedAlong_geoTransformAlong`; the
divisors and the original members agree, `ContactLowerValue.origMembers_restrictEquiv`). -/
theorem restrictEquiv_memberRestrict_membersThrough {𝔍 𝔍' : MarkedIdeal n X} (h𝔍 : 𝔍.IsWellFormed)
    (h𝔞' : 𝔍'.ideal.IsCoherent) (hEq : RestrictEquiv 𝔍 𝔍') {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    RestrictEquiv
      (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
        (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) y₀))
      (memberRestrict (geoTransformAlong (barMarked 𝔍') T₀)
        (membersThrough (geoTransformAlong (barMarked 𝔍') T₀).E (origMembers 𝔍' T₀) y₀)) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hJJ : RestrictEquiv (barMarked 𝔍) (barMarked 𝔍') :=
    ContactRepresentative.restrictEquiv_barMarked hEq h𝔍.isClosedSubmanifold_N h𝔍.isCoherent h𝔞'
  have hJ'c : (barMarked 𝔍').ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞' (hEq.N_eq ▸ h𝔍.isClosedSubmanifold_N))
      (hEq.N_eq ▸ h𝔍.isClosedSubmanifold_N)
  have hc := ContactCanonicalAlong.restrictEquiv_coeffMarkedAlong_geoTransformAlong hJJ hJ.isClosedSubmanifold_N.1
    hJ.isCoherent hJ'c T₀
  have hE := MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := barMarked 𝔍) (𝔫 := barMarked 𝔍')
    hJJ.E_eq T₀
  have hN : (geoTransformAlong (barMarked 𝔍) T₀).N = (geoTransformAlong (barMarked 𝔍') T₀).N := hc.N_eq
  have hO := ContactLowerValue.origMembers_restrictEquiv hEq T₀
  refine ⟨?_, ?_, hc.d_eq, ?_, ?_⟩
  · rw [memberRestrict_membersThrough_N, memberRestrict_membersThrough_N, hN, hE, hO]
  · rw [memberRestrict_membersThrough_E, memberRestrict_membersThrough_E, hE, hO]
  · exact MarkedIdealOperationsAlong.restrictLe_mono (fun _ hx => hx.1) hc.le
  · exact MarkedIdealOperationsAlong.restrictLe_mono (fun _ hx => hx.1) hc.ge

/-- **Property (7) of the masked Step 1 value function at the levels `s + 1`, lower values** (`(t7)` shape): let `𝔍` be
well formed with `d ≥ 1` (`n > 0`) and `𝔍 ≃ 𝔍'` restricted-equivalent with `𝔍'` coherent, and `T₀ T₁` a multiple
test blow-up of `J̄`. If `p` has lower data at level `s + 1` at the split `T₀ T₁` both for `𝔍` and for `𝔍'`, the two
lower values agree. (Step 1ab's restricted marked ideals of the two sides are restricted-equivalent
(`restrictEquiv_memberRestrict_membersThrough`); on the intersection `W` of the two masks both lie in the domain of
`R` with the restricted tail a canonical segment (`MaxLocusLocal.restrict_nestedOpens`), the values agree by
property (7) of `R`, and the anchor `lowerValueL_succ_eq` on both sides.) -/
theorem lowerValueL_succ_representative (R : ResolutionInvariant.{u, v} n k Λ) {𝔍 𝔍' : MarkedIdeal n X}
    (h𝔍 : 𝔍.IsWellFormed) (h𝔞' : 𝔍'.ideal.IsCoherent) (hn : 0 < n) (hEq : RestrictEquiv 𝔍 𝔍') {s : ℕ}
    {Y₀ Z : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Z)
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {p : Z}
    (hD : LowerDataL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀ T₁ p) (hD' : LowerDataL R 𝔍' (lowerMarkedM 𝔍') (s + 1) T₀ T₁ p) :
    lowerValueL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀ T₁ p = lowerValueL R 𝔍' (lowerMarkedM 𝔍') (s + 1) T₀ T₁ p := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍' : 𝔍'.IsWellFormed := by
    obtain ⟨hN, -, hS, hTr⟩ := h𝔍
    refine ⟨hEq.N_eq ▸ hN, h𝔞', hEq.E_eq ▸ hS, ?_⟩
    rw [← hEq.N_eq, ← hEq.E_eq]
    exact hTr
  have hJ' := isWellFormed_barMarked 𝔍' h𝔍'
  -- `J̄` and `J̄'` are restricted-equivalent: the same multiple test blow-ups
  have hJJ : RestrictEquiv (barMarked 𝔍) (barMarked 𝔍') :=
    ContactRepresentative.restrictEquiv_barMarked hEq h𝔍.isClosedSubmanifold_N h𝔍.isCoherent h𝔞'
  have hW := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hJJ hJ.isClosedSubmanifold_N.1 hJ.isCoherent
    hJ'.isCoherent
  have hT' : IsGeoTestTower (barMarked 𝔍') (T₀.append T₁) := ((hW.2 _).1).mp hT
  have hT₀ : IsGeoTestTower (barMarked 𝔍) T₀ := ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1
  have hT₀' : IsGeoTestTower (barMarked 𝔍') T₀ := ((isGeoTestTower_append_iff _ T₀ T₁).mp hT').1
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hwf' := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ' T₀ hT₀'
  -- Step 1ab's restricted marked ideals of the two sides
  set 𝔐 : MarkedIdeal n Y₀ := memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
    (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj p)) with h𝔐def
  set 𝔐' : MarkedIdeal n Y₀ := memberRestrict (geoTransformAlong (barMarked 𝔍') T₀)
    (membersThrough (geoTransformAlong (barMarked 𝔍') T₀).E (origMembers 𝔍' T₀) (T₁.proj p)) with h𝔐'def
  have hwfS : 𝔐.IsWellFormed := isWellFormed_memberRestrict hn hwf _
  have hwfS' : 𝔐'.IsWellFormed := isWellFormed_memberRestrict hn hwf' _
  have hMM : RestrictEquiv 𝔐 𝔐' := restrictEquiv_memberRestrict_membersThrough h𝔍 h𝔞' hEq T₀ (T₁.proj p)
  -- the data of both sides on their masks `A`, `A'`
  obtain ⟨h, hdom, hcan, hcos⟩ := id hD
  obtain ⟨h', hdom', hcan', -⟩ := id hD'
  set A : Opens Y₀ := lowerMask 𝔍 (s + 1) T₀ (T₁.proj p) with hAdef
  set A' : Opens Y₀ := lowerMask 𝔍' (s + 1) T₀ (T₁.proj p) with hA'def
  have hdomA : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : A → Y₀) 𝔐) := hdom
  have hcanA : IsCanonical (MarkedIdeal.pullback (Subtype.val : A → Y₀) 𝔐)
      (R.inv (MarkedIdeal.pullback (Subtype.val : A → Y₀) 𝔐)) (restrict A T₁) := hcan
  have hcosA : (⟨p, h⟩ : openPreimage T₁ A) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : A → Y₀) 𝔐) (restrict A T₁)).cosupp := hcos
  have hdomA' : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : A' → Y₀) 𝔐') := hdom'
  have hcanA' : IsCanonical (MarkedIdeal.pullback (Subtype.val : A' → Y₀) 𝔐')
      (R.inv (MarkedIdeal.pullback (Subtype.val : A' → Y₀) 𝔐')) (restrict A' T₁) := hcan'
  -- the intersection `W` of the masks
  set W : Opens Y₀ := A ⊓ A' with hWdef
  have hpW : T₁.proj p ∈ W := ⟨h, h'⟩
  obtain ⟨hdomW, hcanW, -⟩ := MaxLocusLocal.restrict_nestedOpens R hwfS.isCoherent (inf_le_left : W ≤ A) hdomA T₁ hcanA
  obtain ⟨hdomW', hcanW', -⟩ :=
    MaxLocusLocal.restrict_nestedOpens R hwfS'.isCoherent (inf_le_right : W ≤ A') hdomA' T₁ hcanA'
  obtain ⟨-, hcosW⟩ := inv_eq_of_two_opens R hwfS.isClosedSubmanifold_N hwfS.isCoherent T₁ hdomA hcanA hdomW hcanW
    h hpW hcosA
  -- the anchors on both sides, and property (7) of `R` on `W`
  have key := lowerValueL_succ_eq R 𝔍 h𝔍 hn T₀ T₁ hT hD W hpW hdomW hcanW
  have key' := lowerValueL_succ_eq R 𝔍' h𝔍' hn T₀ T₁ hT' hD' W hpW hdomW' hcanW'
  rw [key, key']
  congr 1
  exact R.representative _ _ hdomW hdomW'
    (ContactRepresentative.restrictEquiv_pullback_val W hMM hwfS.isCoherent hwfS'.isCoherent) _ hcanW _ hcosW

end Representative

end

end Hironaka.MemberRestrictTowerIso
