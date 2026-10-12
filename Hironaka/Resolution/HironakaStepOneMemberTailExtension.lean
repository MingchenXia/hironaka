/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneMemberLowerExtension
import Hironaka.Resolution.HironakaCoherentTransformExtension

import Hironaka.Invariant.MemberStrictPartitionExact

/-!
# Entire actual positive-level member transforms on the original canonical tail

Actual remaining/selected smooth components give a closed strict partition,
projection and local germ dictionary. Original genuine SNC test geometry
internally supplies every candidate strict carrier and deleted boundary.
Actual coherent colon and strict accumulation preserve coherence/nonzero
without centre containment in the candidate. Entire lower domains and exact
literal mask identities are produced along the whole original tail and every
prefix from original constructed General3 inputs. Candidate global canonicality,
deeper companion histories, zero-contact and whole General3/G3 remain open.
Blueprint: `hironaka-step-one-member-tail-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneMemberTailExtension
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction
  InvDomainMemberRestriction GermIdealOrder DivisorExponentAlong NormalCrossings
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupStrictSubmanifold
  MarkedIdealBiholomorphism MemberInterTowerAlong HironakaStepOneMemberLowerExtension
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaCoherentTransformExtension
open BoundaryCount HironakaStepOneSpecialAnalyticLoci
open HomogenizedGlueingTower GermIdealPullbackCalculus IdealWeightPowers
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem strictAlong_eq_inter_preimage_of_closed_partition {H A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B) (heq : H = A ∪ B)
    (T : BlowupTower X Y) : strictAlong T A = strictAlong T H ∩ T.proj ⁻¹' A := by
  have hu : strictAlong T H = strictAlong T A ∪ strictAlong T B := by
    rw [heq, strictAlong_union]
  refine Subset.antisymm (fun x hx => ⟨?_, strictAlong_subset_preimage T hA hx⟩) ?_
  · rw [hu]
    exact Or.inl hx
  · intro x hx
    rw [hu] at hx
    rcases hx.1 with h | h
    · exact h
    · exact False.elim (Set.disjoint_left.mp hdis hx.2 (strictAlong_subset_preimage T hB h))

theorem eventually_mem_strictAlong_iff_of_closed_partition {H A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B) (heq : H = A ∪ B)
    (T : BlowupTower X Y) {x : Y} (hx : x ∈ strictAlong T A) :
    ∀ᶠ y in 𝓝 x, y ∈ strictAlong T A ↔ y ∈ strictAlong T H := by
  have hd := disjoint_strictAlong T hA hB hdis
  have hnot : x ∉ strictAlong T B := fun hb => Set.disjoint_left.mp hd hx hb
  filter_upwards [(isClosed_strictAlong T hB).isOpen_compl.mem_nhds hnot] with y hy
  rw [heq, strictAlong_union]
  exact (or_iff_left hy).symm

theorem isCoherent_geoTransform_ideal_of_smooth_strict (m : MarkedIdeal n X)
    {C : Set X} {π : Y → X} (hI : m.ideal.IsCoherent)
    (hπ : IsBlowupAlong n C π)
    (hN' : IsClosedSubmanifold n (m.geoTransform C π).N) :
    (m.geoTransform C π).ideal.IsCoherent := by
  have hC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  exact isCoherent_colonAlong_without_inclusion (isCoherent_pullback hπ.contMDiff hI)
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
    (isCoherent_idealPow (isCoherent_pullback hπ.contMDiff hC) m.d)

theorem isNonzeroAlongAt_geoTransform_of_smooth_strict (m : MarkedIdeal n X)
    {C : Set X} {π : Y → X} (hN : IsClosedSubmanifold n m.N)
    (hI : m.ideal.IsCoherent) (hπ : IsBlowupAlong n C π)
    (hN' : IsClosedSubmanifold n (m.geoTransform C π).N)
    (hnz : ∀ x ∈ m.N, IsNonzeroAlongAt m.N m.ideal x) :
    ∀ y ∈ (m.geoTransform C π).N,
      IsNonzeroAlongAt (m.geoTransform C π).N (m.geoTransform C π).ideal y := by
  have hoff : ∀ y ∈ (m.geoTransform C π).N, π y ∉ C →
      IsNonzeroAlongAt (m.geoTransform C π).N (m.geoTransform C π).ideal y := fun y hy hyC =>
    InvDomainTowerAlong.isNonzeroAlongAt_geoTransform_of_notMem hπ m hI hyC
      (hnz (π y) (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy))
  intro y hy
  by_cases hyC : π y ∈ C
  · by_contra hcon
    have hcoh := isCoherent_geoTransform_ideal_of_smooth_strict m hI hπ hN'
    have hev := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt hcoh hcon
    have hfreq : ∃ᶠ z in 𝓝 y, z ∈ π ⁻¹' (m.N \ C) := mem_closure_iff_frequently.mp hy
    obtain ⟨z, hz, hzev⟩ := (hfreq.and_eventually hev).exists
    have hzN' : z ∈ (m.geoTransform C π).N := subset_closure hz
    obtain ⟨g, hg, hgfreq⟩ := hoff z hzN' hz.2
    obtain ⟨w, ⟨hwN, hgw⟩, hw⟩ := (hgfreq.and_eventually (hzev g hg)).exists
    exact hgw (hw hwN)
  · exact hoff y hy hyC

private theorem remaining_partition {H A : Set X} (hH : IsClosedSubmanifold n H) :
    H = remainingComponents (n := n) H A ∪ HironakaStepOneSpecialAnalyticLoci.selectedComponents (n := n) H A ∧
      Disjoint (remainingComponents (n := n) H A) (HironakaStepOneSpecialAnalyticLoci.selectedComponents (n := n) H A) := by
  rw [remainingComponents_eq_diff_selected hH]
  have hsub : HironakaStepOneSpecialAnalyticLoci.selectedComponents (n := n) H A ⊆ H := by
    rintro x ⟨B, ⟨hB, _⟩, hx⟩
    exact GlobalComponents.subset_of_mem_globalComponents (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hH) hB hx
  exact ⟨(sdiff_union_of_subset hsub).symm, disjoint_sdiff_left⟩

theorem memberRemainder_strict_carrier_geometry (hn : 0 < n) (m : MarkedIdeal n X)
    (hw : m.IsWellFormed) (S : Finset (Fin m.E.length)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower m T) :
    IsClosedSubmanifold n (geoTransformAlong (memberRemainderMarked m S) T).N ∧
      ∀ x ∈ (geoTransformAlong (memberRemainderMarked m S) T).N,
        ∀ᶠ y in 𝓝 x,
          y ∈ (geoTransformAlong (memberRemainderMarked m S) T).N ↔
            y ∈ (memberRestrict (geoTransformAlong m T)
              (S.map (Fin.castLEEmb (length_E_le_length_E_geoTransformAlong m T)))).N := by
  let H := m.N ∩ memberInter m.E S
  have hH := MemberInterAlong.isClosedSubmanifold_inter_memberInter hn
    hw.isClosedSubmanifold_N.1 hw.isSNCDivisor hw.isTransverse S
  have hR := isClosedSubmanifold_remainingComponents hH m.cosupp
  have hSel := HironakaStepOneSpecialAnalyticLoci.isClosedSubmanifold_selectedComponents hH m.cosupp
  obtain ⟨hpart, hdis⟩ := remaining_partition (A := m.cosupp) hH
  have hcarrier : (geoTransformAlong (memberRemainderMarked m S) T).N =
      strictAlong T (remainingComponents (n := n) H m.cosupp) :=
    N_geoTransformAlong (memberRemainderMarked m S) T
  have hfull : strictAlong T H =
      (memberRestrict (geoTransformAlong m T)
        (S.map (Fin.castLEEmb (length_E_le_length_E_geoTransformAlong m T)))).N := by
    rw [strictAlong_inter_memberInter m hw S T hT,
      setOf_forall_strictAlong_eq_memberInter, memberRestrict_N]
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  have hfullSM := (isWellFormed_memberRestrict hn hwT
    (S.map (Fin.castLEEmb (length_E_le_length_E_geoTransformAlong m T)))).isClosedSubmanifold_N
  have hev : ∀ x ∈ (geoTransformAlong (memberRemainderMarked m S) T).N,
      ∀ᶠ y in 𝓝 x,
        y ∈ (geoTransformAlong (memberRemainderMarked m S) T).N ↔
          y ∈ (memberRestrict (geoTransformAlong m T)
            (S.map (Fin.castLEEmb (length_E_le_length_E_geoTransformAlong m T)))).N := by
    intro x hx
    rw [hcarrier] at hx ⊢
    rw [← hfull]
    exact eventually_mem_strictAlong_iff_of_closed_partition hR.1 hSel.1 hdis hpart T hx
  refine ⟨⟨?_, ?_⟩, hev⟩
  · rw [hcarrier]
    exact isClosed_strictAlong T hR.1
  · intro x hx
    have hxF := (hev x hx).self_of_nhds.mp hx
    obtain ⟨d, hd⟩ := hfullSM.2 x hxF
    exact ⟨d, CodimOneSupport.regularAtDim_of_eventually_mem_iff
      ((hev x hx).mono fun _ h => h.symm) hd⟩

private theorem E_geoTransformAlong_sublist {a m : MarkedIdeal n X} (hE : a.E.Sublist m.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong a T).E.Sublist (geoTransformAlong m T).E
  | _, .refl => hE
  | _, .step T C π _hπ =>
    (List.Sublist.map (geoStrictTransform π C) (E_geoTransformAlong_sublist hE T)).append
      (List.Sublist.refl _)

private theorem E_memberRemainder_sublist (m : MarkedIdeal n X) (S : Finset (Fin m.E.length)) :
    (memberRemainderMarked m S).E.Sublist m.E := by
  classical
  change (((List.finRange m.E.length).filter fun i => i ∉ S).map m.E.get).Sublist m.E
  simpa only [List.map_get_finRange] using
    (List.Sublist.map m.E.get (List.filter_sublist (p := fun i => decide (i ∉ S))
      (l := List.finRange m.E.length)))

private theorem E_drop_eq (a m : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong a T).E.drop a.E.length = (geoTransformAlong m T).E.drop m.E.length
  | _, .refl => by simp
  | _, .step T C π hπ => by
    rw [drop_E_geoTransformAlong_step, drop_E_geoTransformAlong_step, E_drop_eq a m T]

private theorem E_memberRemainder_transform_eq (m : MarkedIdeal n X)
    (S : Finset (Fin m.E.length)) (T : BlowupTower X Y) :
    (geoTransformAlong (memberRemainderMarked m S) T).E =
      (memberRemainderMarked m S).E.map (strictAlong T) ++
        (geoTransformAlong m T).E.drop m.E.length := by
  rw [← take_E_geoTransformAlong (memberRemainderMarked m S) T, ← E_drop_eq (memberRemainderMarked m S) m T]
  exact (List.take_append_drop _ _).symm

private theorem exists_get_index_of_mem_drop {α : Type*} (L : List α) (r : ℕ) {a : α}
    (ha : a ∈ L.drop r) : ∃ j : Fin L.length, r ≤ j.1 ∧ L.get j = a := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  have hj : r + i.1 < L.length := by have := i.2; simp only [List.length_drop] at this; omega
  refine ⟨⟨r+i.1, hj⟩, by change r ≤ r + i.1; omega, ?_⟩
  simpa only [List.get_eq_getElem, List.getElem_drop] using hi

private theorem E_memberRemainder_mem_deleted_current (m : MarkedIdeal n X)
    (S : Finset (Fin m.E.length)) (T : BlowupTower X Y) :
    ∀ H ∈ (geoTransformAlong (memberRemainderMarked m S) T).E,
      H ∈ (memberRestrict (geoTransformAlong m T)
        (S.map (Fin.castLEEmb (length_E_le_length_E_geoTransformAlong m T)))).E := by
  classical
  let e := Fin.castLEEmb (length_E_le_length_E_geoTransformAlong m T)
  intro H hH
  rw [E_memberRemainder_transform_eq] at hH
  obtain h | h := List.mem_append.mp hH
  · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp h
    change B ∈ ((List.finRange m.E.length).filter fun i => i ∉ S).map m.E.get at hB
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hB
    have hinot : i ∉ S := by simpa only [List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hi).2
    have hjnot : e i ∉ S.map e := by simpa only [Finset.mem_map, e.injective.eq_iff, exists_eq_right] using hinot
    change strictAlong T (m.E.get i) ∈ ((List.finRange (geoTransformAlong m T).E.length).filter
      fun j => j ∉ S.map e).map (geoTransformAlong m T).E.get
    exact List.mem_map.mpr ⟨e i, List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using hjnot⟩,
      get_E_geoTransformAlong m T i⟩
  · obtain ⟨j, hj, hget⟩ := exists_get_index_of_mem_drop _ _ h
    have hjnot : j ∉ S.map e := by
      rintro hjS
      obtain ⟨i, hi, he⟩ := Finset.mem_map.mp hjS
      have hv := congrArg Fin.val he
      have := i.2
      change i.1 = j.1 at hv
      omega
    change H ∈ ((List.finRange (geoTransformAlong m T).E.length).filter
      fun j => j ∉ S.map e).map (geoTransformAlong m T).E.get
    exact List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using hjnot⟩, hget⟩


theorem memberRemainder_transform_geometry (hn : 0 < n) (m : MarkedIdeal n X)
    (hw : m.IsWellFormed) {k : ℕ} (hdim : ResolutionInvariantSpec.DimLE n m.N k)
    (S : Finset (Fin m.E.length)) (hS : S.Nonempty) (T : BlowupTower X Y)
    (hT : IsGeoTestTower m T) :
    IsClosedSubmanifold n (geoTransformAlong (memberRemainderMarked m S) T).N ∧
      IsSNCDivisor n (geoTransformAlong (memberRemainderMarked m S) T).E ∧
      IsTransverse n (geoTransformAlong (memberRemainderMarked m S) T).N
        (geoTransformAlong (memberRemainderMarked m S) T).E ∧
      ResolutionInvariantSpec.DimLE n (geoTransformAlong (memberRemainderMarked m S) T).N (k-1) := by
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  obtain ⟨hRN, hev⟩ := memberRemainder_strict_carrier_geometry hn m hw S T hT
  have hE := E_memberRemainder_mem_deleted_current m S T
  have hF := isWellFormed_memberRestrict hn hwT
    (S.map (Fin.castLEEmb (length_E_le_length_E_geoTransformAlong m T)))
  have hdimT := InvDomainTowerAlong.dimLE_geoTransformAlong hw.isClosedSubmanifold_N hw.isCoherent hdim T hT
  have hdimF := dimLE_memberRestrict hn hwT
    (S := S.map (Fin.castLEEmb (length_E_le_length_E_geoTransformAlong m T))) hS.map hdimT
  refine ⟨hRN, ?_, ?_, ?_⟩
  · exact NormalCrossingsComparison.isSNCDivisor_of_sublist hwT.isSNCDivisor
      (E_geoTransformAlong_sublist (E_memberRemainder_sublist m S) T)
  · apply CodimOneAdmissibleAlong.isTransverse_of_forall_eventually
    intro x hx
    exact ⟨_, (hev x hx).self_of_nhds.mp hx, hev x hx,
      NormalCrossingsComparison.isTransverse_of_forall_mem hF.isTransverse hE⟩
  · intro x hx
    obtain ⟨d, hd⟩ := hRN.2 x hx
    obtain ⟨j, hj, hjR⟩ := hdimF x ((hev x hx).self_of_nhds.mp hx)
    have hsub : (geoTransformAlong (memberRemainderMarked m S) T).N ⊆
        (memberRestrict (geoTransformAlong m T)
          (S.map (Fin.castLEEmb (length_E_le_length_E_geoTransformAlong m T)))).N :=
      fun x hx => (hev x hx).self_of_nhds.mp hx
    exact ⟨d, (le_of_regularAtDim_subset hd hjR hsub).trans hj, hd⟩

private theorem coherent_nonzero_memberRemainder_transform (hn : 0 < n) (m : MarkedIdeal n X)
    (hw : m.IsWellFormed) (hd : 1 ≤ m.d) {k : ℕ}
    (hdim : ResolutionInvariantSpec.DimLE n m.N k) (S : Finset (Fin m.E.length)) (hS : S.Nonempty) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower m T →
      (geoTransformAlong (memberRemainderMarked m S) T).ideal.IsCoherent ∧
        ∀ x ∈ (geoTransformAlong (memberRemainderMarked m S) T).N,
          IsNonzeroAlongAt (geoTransformAlong (memberRemainderMarked m S) T).N
            (geoTransformAlong (memberRemainderMarked m S) T).ideal x
  | _, .refl, _ => by
    have hR := isInvDomain_memberRemainderMarked hn m hw hd hdim S hS
    exact ⟨hR.isWellFormed.isCoherent, hR.isNonzeroAlongAt⟩
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := hT
    obtain ⟨hIT, hnzT⟩ := coherent_nonzero_memberRemainder_transform hn m hw hd hdim S hS T hTT
    have hN := (memberRemainder_transform_geometry hn m hw hdim S hS T hTT).1
    have hN' := (memberRemainder_transform_geometry hn m hw hdim S hS (.step T C π hπ) ⟨hTT,hC⟩).1
    exact ⟨isCoherent_geoTransform_ideal_of_smooth_strict _ hIT hπ hN',
      isNonzeroAlongAt_geoTransform_of_smooth_strict _ hN hIT hπ hN' hnzT⟩

theorem isInvDomain_geoTransformAlong_memberRemainder (hn : 0 < n) (m : MarkedIdeal n X)
    (hw : m.IsWellFormed) (hd : 1 ≤ m.d) {k : ℕ}
    (hdim : ResolutionInvariantSpec.DimLE n m.N k) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) :
    IsInvDomain (k-1) (geoTransformAlong (memberRemainderMarked m S) T) := by
  obtain ⟨hN, hE, htr, hD⟩ := memberRemainder_transform_geometry hn m hw hdim S hS T hT
  obtain ⟨hI, hnz⟩ := coherent_nonzero_memberRemainder_transform hn m hw hd hdim S hS T hT
  refine ⟨⟨hN,hI,hE,htr⟩, hD, ?_, hnz⟩
  rw [d_geoTransformAlong]
  exact one_le_memberRestrict_d m S


theorem geoTransformAlong_restrict_memberRemainder (hn : 0 < n) (m : MarkedIdeal n X)
    (hw : m.IsWellFormed) (hd : 1 ≤ m.d) {k : ℕ}
    (hdim : ResolutionInvariantSpec.DimLE n m.N k) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (U : TopologicalSpace.Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower m T →
      geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S)) (restrict U T) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
          (geoTransformAlong (memberRemainderMarked m S) T)
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := hT
    have hIT := (coherent_nonzero_memberRemainder_transform hn m hw hd hdim S hS T hTT).1
    have hI' := (coherent_nonzero_memberRemainder_transform hn m hw hd hdim S hS
      (.step T C π hπ) ⟨hTT,hC⟩).1
    have ih := geoTransformAlong_restrict_memberRemainder hn m hw hd hdim S hS U T hTT
    change (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S))
      (restrict U T)).geoTransform ((↑) ⁻¹' C : Set (openPreimage T U)) _ = _
    rw [ih]
    exact MarkedIdealRestrictOpen.geoTransform_pullback_val hIT hπ hI' (openPreimage T U) _

open StepOneValue StepOneLowerDomain HomogenizedIdealAlong

theorem memberLowerExtension_tail_domain_and_mask_identity (hn : 0 < n)
    (m : MarkedIdeal n X) {k : ℕ} (h : IsInvDomain k m)
    {Y₀ : CMfd.{u} n} (H : BlowupTower X Y₀) (hH : IsGeoTestTower (barMarked m) H)
    (y₀ : Y₀) {s : ℕ} (hl : level m H y₀ = s+1)
    (T : BlowupTower Y₀ Y) (hT : IsGeoTestTower (geoTransformAlong (barMarked m) H) T) :
    IsInvDomain (k-1) (geoTransformAlong (memberLowerExtension m H y₀) T) ∧
      geoTransformAlong (lowerMarked m (s+1) H y₀) (restrict (maskA m H y₀) T) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T (maskA m H y₀) → Y)
          (geoTransformAlong (memberLowerExtension m H y₀) T) := by
  have hbar := isWellFormed_barMarked m h.isWellFormed
  have hwH := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hbar H hH
  have hdH : 1 ≤ (geoTransformAlong (barMarked m) H).d := by
    rw [d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hdimH := InvDomainTowerAlong.dimLE_geoTransformAlong hbar.isClosedSubmanifold_N hbar.isCoherent h.dimLE H hH
  let S := membersThrough (geoTransformAlong (barMarked m) H).E (origMembers m H) y₀
  have hE₀ : ∀ B ∈ origMembers m H, B ∈ (geoTransformAlong (barMarked m) H).E :=
    fun B hB => List.mem_of_mem_take hB
  have hS : S.Nonempty := membersThrough_nonempty hE₀ (by change 1 ≤ level m H y₀; rw [hl]; omega)
  refine ⟨isInvDomain_geoTransformAlong_memberRemainder hn _ hwH hdH hdimH S hS T hT, ?_⟩
  rw [← pullback_memberLowerExtension_eq_lowerMarked_succ hn m h.isWellFormed H hH y₀ hl]
  exact geoTransformAlong_restrict_memberRemainder hn _ hwH hdH hdimH S hS _ T hT


open StepOneRegime HironakaGeneralThreeNonspecialAnalyticLoci
open Hironaka.ResolutionInvariantSpec (IsCanonical)

private theorem regime_at_actual_run_start (P : Regime X) (T : BlowupTower X Y)
    (y : Y) (hy : P T y) :
    P (head T (regimeRun P T y)) ((tail T (regimeRun P T y)).proj y) := by
  by_cases hr : regimeRun P T y = 0
  · rw [hr]
    cases T <;> exact hy
  · exact regime_head_of_le_regimeRun P T y _ (by omega) le_rfl

theorem exists_actual_companion_member_tail_extension (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((CanonicalCentres.invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hnsp : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (hpos : 1 ≤ level (companionAt m T x) (companionTailAt m T x) p) :
    let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
    let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
      (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    ∃ s : ℕ, level K R p = s+1 ∧ p₀ ∈ maskA K H p₀ ∧
      IsInvDomain 2 (geoTransformAlong (memberLowerExtension K H p₀) Q) ∧
      geoTransformAlong (lowerMarked K (s+1) H p₀) (restrict (maskA K H p₀) Q) =
        MarkedIdeal.pullback (Subtype.val : openPreimage Q (maskA K H p₀) → CMfd.of (n := n) (patchAt m T x))
          (geoTransformAlong (memberLowerExtension K H p₀) Q) ∧
      ∀ i : ℕ,
        IsInvDomain 2 (geoTransformAlong (memberLowerExtension K H p₀) (head Q i)) ∧
        geoTransformAlong (lowerMarked K (s+1) H p₀) (restrict (maskA K H p₀) (head Q i)) =
          MarkedIdeal.pullback (Subtype.val : openPreimage (head Q i) (maskA K H p₀) → (split Q i).1)
            (geoTransformAlong (memberLowerExtension K H p₀) (head Q i)) := by
  dsimp only
  let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
  let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
    (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  obtain ⟨_, hK, hmax, hcanK, _⟩ :=
    actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (CanonicalCentres.invFamily hn 2)
    K hK hmax hn R hcanK
  obtain ⟨s, hs, hmask, _, _⟩ := exists_actual_companion_member_lower_extension hn m h T hcan x hx hq p hp hnsp hpos
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail (barMarked K) R r).mp hb.1
  have hreg : stepRegime K (level K R p) H p₀ :=
    regime_at_actual_run_start (stepRegime K (level K R p)) R p ⟨rfl, hnsp⟩
  have hl : level K H p₀ = s+1 := hreg.1.trans hs
  have hfull := memberLowerExtension_tail_domain_and_mask_identity hn K hK H hhead p₀ hl Q htail
  refine ⟨s, hs, hmask, hfull.1, hfull.2, ?_⟩
  intro i
  have hprefix := (isGeoTestTower_iff_head_tail (geoTransformAlong (barMarked K) H) Q i).mp htail
  exact memberLowerExtension_tail_domain_and_mask_identity hn K hK H hhead p₀ hl (head Q i) hprefix.1


end
end Hironaka.HironakaStepOneMemberTailExtension
