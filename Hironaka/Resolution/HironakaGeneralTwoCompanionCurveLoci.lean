/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaCoherentTransformExtension

set_option autoImplicit false

/-!
# Actual entire companion curve loci in dimension two

Actual global component germs, coherent nonzero, true SNC traces and finite
analytic predicates internally produce a global analytic zero-dimensional
exception to Step 1 specialness. The entire coefficient-companion transform
is exactly the literal masked transform; its actual special predicate also
restricts exactly. No outside-mask maximal-order or exception certificate is
assumed. Whole General2 superlevel descent and G3 remain open.
Blueprint: `hironaka-general-two-companion-curve-loci-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaGeneralTwoCompanionCurveLoci

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GlobalComponents RegularLocusComponent AnalyticDimensionBasics
  HironakaCurveAnalyticPredicates HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaOneDimensionalCanonicalSuperlevels HironakaCoherentTransformExtension
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder DivisorExponentAlong
  CodimOneSupportAlong CodimOneSupport NormalCrossings BoundaryCount MemberInterLocusAlong

open Hironaka
noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem eventually_mem_iff_globalComponent_of_regular {A B : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hB : B ∈ globalComponents (n := n) A)
    {x : M} {k : ℕ} (hxB : x ∈ B) (hx : RegularAtDim (n := n) A x k) :
    ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ B := by
  obtain ⟨c, ⟨j, hc⟩, rfl⟩ := hB
  obtain ⟨U, hU, hxU, hUC⟩ := exists_open_inter_subset_component hx (mem_component_self hx)
  obtain ⟨y, hyU, hyC⟩ := mem_closure_iff.mp hxB U hU hxU
  have hyCx := hUC ⟨component_subset (n := n) A c hyC, hyU⟩
  have heq : component (n := n) A c = component (n := n) A x :=
    (connectedComponentIn_eq hyC).trans (connectedComponentIn_eq hyCx).symm
  have hxC : x ∈ component (n := n) A c := heq.symm ▸ mem_component_self hx
  obtain ⟨V, hV, hxV, hVC⟩ := exists_open_inter_subset_component hc hxC
  filter_upwards [hV.mem_nhds hxV] with y hyV
  exact ⟨fun hyA => subset_closure (hVC ⟨hyA, hyV⟩),
    fun hyB => subset_of_mem_globalComponents hA (closure_component_mem_globalComponents hc) hyB⟩

omit [IsComplexManifold n M] in
private theorem thin_cosupport_of_nonzeroAlong (N : Set M) (I : GermIdeal n M)
    (hI : I.IsCoherent) (hne : ∀ x ∈ N, IsNonzeroAlongAt N I x) (d : ℕ) (hd : 1 ≤ d) :
    ∀ O : Set M, IsOpen O → O ∩ N ⊆ cosupport n N I d → O ∩ N = ∅ := by
  intro O hO hsub
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxO, hxN⟩
  obtain ⟨g, hg, hfreq⟩ := hne x hxN
  obtain ⟨U, hU, hxU, r, s, hs, hgen⟩ := hI x
  obtain ⟨_, q, t, a, ht, _, hsum⟩ := (hgen x hxU g).mp hg
  have hzero : ∀ y ∈ U ∩ O, y ∈ N → ∀ i : Fin r, s i y = 0 := by
    intro y hy hyN i
    have hhol : HolomorphicAt n (s i) y := by
      filter_upwards [hU.mem_nhds hy.1] with z hz
      exact (hs i z hz).mdifferentiableAt (hU.mem_nhds hz)
    have hmem : I.mem y (s i) := (hgen y hy.1 (s i)).mpr
      (isInSpanAt_of_eq_mul (s := s i) (a := fun _ => 1)
        ⟨i, rfl⟩ hhol (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp))
    exact (vanishesToOrderOn_one_iff hyN hhol).mp (((hsub ⟨hy.2, hyN⟩).2 _ hmem).mono hd)
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧ y ∈ O ∧ g y = ∑ i, a i y * t i y := by
    filter_upwards [hU.mem_nhds hxU, hO.mem_nhds hxO, hsum] with y hyU hyO hys
    exact ⟨hyU, hyO, hys⟩
  obtain ⟨y, ⟨hyN, hyg⟩, hyU, hyO, hysum⟩ := (hfreq.and_eventually hev).exists
  apply hyg
  rw [hysum]
  have htz : ∀ j : Fin q, t j y = 0 := by
    intro j
    obtain ⟨i, hi⟩ := ht j
    rw [← hi]
    exact hzero y ⟨hyU, hyO⟩ hyN i
  simp [htz]

theorem regularAtDim_carrier_two_of_cosupport_one {J : MarkedIdeal n M}
    (hJ : ResolutionInvariantSpec.IsInvDomain 2 J) {x : M}
    (hx : RegularAtDim (n := n) J.cosupp x 1) : RegularAtDim (n := n) J.N x 2 := by
  obtain ⟨j, hj, hxN⟩ := hJ.dimLE x (J.cosupp_subset_N hx.2.1)
  have hjlo : 1 ≤ j := BlowupStrictSubmanifold.le_of_regularAtDim_subset hx hxN J.cosupp_subset_N
  have hjne : j ≠ 1 := by
    intro heq
    subst j
    have hA : IsComplexAnalyticSubset (n := n) J.cosupp :=
      isComplexAnalyticSubset_cosupport_along hJ.isWellFormed.isCoherent
      hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d
    have hfill := eventually_mem_iff_of_regularAtDim_of_locDimGE hA hxN
      (Eventually.of_forall fun y => J.cosupp_subset_N (a := y)) (locDimGE_of_regularAtDim hx)
    obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hfill
    have hemp := thin_cosupport_of_nonzeroAlong J.N J.ideal hJ.isWellFormed.isCoherent
      hJ.isNonzeroAlongAt J.d hJ.one_le_d U hU (fun y hy => (hUsub hy.1).mpr hy.2)
    have hm : x ∈ U ∩ J.N := ⟨hxU, hxN.2.1⟩
    rw [hemp] at hm
    exact hm
  have hj2 : j = 2 := by omega
  exact hj2 ▸ hxN

theorem mem_memberInterLocus_of_regular_component_subset_member (hn : 0 < n)
    {J : MarkedIdeal n M} (hJ : ResolutionInvariantSpec.IsInvDomain 2 J)
    (F : List (Set M)) (hF : ∀ W ∈ F, W ∈ J.E)
    {B : Set M} (hB : B ∈ globalComponents (n := n) J.cosupp)
    {x : M} (hxB : x ∈ B) (hx : RegularAtDim (n := n) J.cosupp x 1)
    {W : Set M} (hWF : W ∈ F) (hBW : B ⊆ W) :
    x ∈ memberInterLocus J.N F J.cosupp := by
  have hA : IsComplexAnalyticSubset (n := n) J.cosupp :=
      isComplexAnalyticSubset_cosupport_along hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d
  have hBA := subset_of_mem_globalComponents hA hB
  have hBa := (isComplexAnalyticallyIrreducible_of_mem_globalComponents hA hB).1
  have hBx := regularAtDim_of_eventually_mem_iff
    (eventually_mem_iff_globalComponent_of_regular hA hB hxB hx) hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (hF W hWF)
  have hH := MemberInterAlong.isClosedSubmanifold_inter_memberInter hn
    hJ.isWellFormed.isClosedSubmanifold_N.1 hJ.isWellFormed.isSNCDivisor
    hJ.isWellFormed.isTransverse {i}
  rw [memberInter_singleton, hi] at hH
  obtain ⟨j, hxH⟩ := hH.2 x ⟨J.cosupp_subset_N hx.2.1, hBW hxB⟩
  have hdH := dimLE_inter_get_of_dimLE_two hn hJ.dimLE
    hJ.isWellFormed.isSNCDivisor hJ.isWellFormed.isTransverse i
  rw [hi] at hdH
  have hjlo : 1 ≤ j := BlowupStrictSubmanifold.le_of_regularAtDim_subset hBx hxH
    (fun y hy => ⟨J.cosupp_subset_N (hBA hy), hBW hy⟩)
  have hj : j = 1 := by have := hdH x j hxH; omega
  subst j
  have hfill := eventually_mem_iff_of_regularAtDim_of_locDimGE hBa hxH
    (Eventually.of_forall fun y hy => ⟨J.cosupp_subset_N (hBA hy), hBW hy⟩)
    (locDimGE_of_regularAtDim hBx)
  apply mem_memberInterLocus_iff.mpr
  refine ⟨hx.2.1, ?_⟩
  filter_upwards [hfill] with y hy hyN hall
  exact hBA (hy.mpr ⟨hyN, hall W hWF (hBW hxB)⟩)

theorem exists_analytic_dimzero_stage_special_exception (hn : 0 < n)
    {J : MarkedIdeal n M} (hJ : ResolutionInvariantSpec.IsInvDomain 2 J)
    (F : List (Set M)) (hF : ∀ W ∈ F, W ∈ J.E) :
    ∃ Z : Set M, IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 0 ∧
      Z ⊆ J.cosupp ∧ ∀ x ∈ J.cosupp \ Z,
        (boundaryCount F x = 0 ∧ x ∈ codimOnePartAlong J.N J.ideal J.d) ∨
        (1 ≤ boundaryCount F x ∧ x ∈ memberInterLocus J.N F J.cosupp) := by
  classical
  have hA : IsComplexAnalyticSubset (n := n) J.cosupp :=
      isComplexAnalyticSubset_cosupport_along hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d
  have hdim : DimLE (n := n) J.cosupp 1 := dimLE_cosupport_of_isInvDomain hJ
  obtain ⟨S, hS, hdS, hSA, -, hreg⟩ := exists_analytic_dimzero_regular_curve_envelope hA hdim
  have hP : ∀ i : Fin F.length, IsComplexAnalyticSubset (n := n) (F.get i) := by
    intro i
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (hF (F.get i) (List.get_mem F i))
    have hH := isClosedSubmanifold_memberInter hn hJ.isWellFormed.isSNCDivisor {j}
    rw [memberInter_singleton, hj] at hH
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hH
  obtain ⟨P, hPa, hdP, hPA, hpred⟩ := exists_analytic_dimzero_predicate_exception hA hdim F.get hP
  obtain ⟨hZ, hdZ⟩ := analytic_dimzero_union hS hdS hPa hdP
  refine ⟨S ∪ P, hZ, hdZ, union_subset hSA hPA, ?_⟩
  intro x hx
  have hxS : x ∈ J.cosupp \ S := ⟨hx.1, fun hs => hx.2 (Or.inl hs)⟩
  have hxP : x ∉ P := fun hp => hx.2 (Or.inr hp)
  have hxreg := hreg x hxS
  by_cases hs : boundaryCount F x = 0
  · exact Or.inl ⟨hs, 1, regularAtDim_carrier_two_of_cosupport_one hJ hxreg, hxreg⟩
  · have hspos : 0 < boundaryCount F x := Nat.pos_of_ne_zero hs
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hspos
    have hxi : x ∈ F.get i := (Finset.mem_filter.mp hi).2
    have hxU : x ∈ ⋃₀ globalComponents (n := n) J.cosupp := by
      rw [sUnion_globalComponents hA]
      exact hx.1
    obtain ⟨B, hB, hxB⟩ := hxU
    have hBi : B ⊆ F.get i := (hpred B hB x ⟨hxB, hxP⟩ i).mp hxi
    exact Or.inr ⟨hspos, mem_memberInterLocus_of_regular_component_subset_member hn hJ F hF
      hB hxB hxreg (List.get_mem F i) hBi⟩

section ActualCompanion

universe u
open BlowupTowers BlowupTowerTransforms StepOneValue CompanionRebase CompanionReductionAlong
  GeneralValue InvDomainCompanion MarkedIdealBiholomorphism HomogenizedIdealAlong
  MarkedIdealRestrictOpen CodimOnePartCanonical

variable {X Y₀ Y : CMfd.{u} n}

theorem exists_analytic_dimzero_entire_companion_exception (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (o : ℕ) (ho : 1 ≤ o) (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower m T₀)
    (T₁ : BlowupTower Y₀ Y) (hT₁ : IsGeoTestTower (geoTransformAlong m T₀) T₁) :
    ∃ Z : Set Y, IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 0 ∧
      Z ⊆ (geoTransformAlong (barMarked (companionOf n (geoTransformAlong m T₀) o)) T₁).cosupp ∧
      ∀ y ∈ (geoTransformAlong (barMarked (companionOf n (geoTransformAlong m T₀) o)) T₁).cosupp \ Z,
        IsSpecial (companionOf n (geoTransformAlong m T₀) o) T₁ y := by
  have hD := (coherent_coefficient_transform_and_mask_identity hn m h o ho T₀ hT₀ T₁ hT₁).1
  exact exists_analytic_dimzero_stage_special_exception hn hD
    (origMembers (companionOf n (geoTransformAlong m T₀) o) T₁)
    (fun _ hW => List.mem_of_mem_take hW)

theorem isSpecial_literal_companion_mask_iff (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (o : ℕ) (ho : 1 ≤ o) (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower m T₀)
    (T₁ : BlowupTower Y₀ Y) (hT₁ : IsGeoTestTower (geoTransformAlong m T₀) T₁)
    (p : openPreimage T₁ (NonmonomialOrderTail.ordMask (geoTransformAlong m T₀) o)) :
    IsSpecial (compAt m o T₀)
        (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m T₀) o) T₁) p ↔
      IsSpecial (companionOf n (geoTransformAlong m T₀) o) T₁ (p : Y) := by
  let W := NonmonomialOrderTail.ordMask (geoTransformAlong m T₀) o
  let K := companionOf n (geoTransformAlong m T₀) o
  let J := geoTransformAlong (barMarked K) T₁
  let V := openPreimage T₁ W
  obtain ⟨hJ, hid⟩ := coherent_coefficient_transform_and_mask_identity hn m h o ho T₀ hT₀ T₁ hT₁
  have hd₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  have hinit : compAt m o T₀ = MarkedIdeal.pullback (Subtype.val : W → Y₀) K :=
    (pullback_val_companionOf hn hd₀.isWellFormed hd₀.isNonzeroAlongAt _ o).symm
  have hlen : (compAt m o T₀).E.length = K.E.length := by
    rw [hinit]
    exact List.length_map _
  have hF : origMembers (compAt m o T₀) (restrict W T₁) =
      (origMembers K T₁).map ((Subtype.val : V → Y) ⁻¹' ·) := by
    unfold origMembers
    rw [hid, hlen]
    exact (List.map_take).symm
  have hlev : level (compAt m o T₀) (restrict W T₁) p = level K T₁ (p : Y) := by
    unfold level
    rw [hF]
    exact boundaryCount_map_preimage _ _ p
  have hhol : ∀ y g, J.ideal.mem y g → HolomorphicAt n g y :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hJ.isWellFormed.isCoherent hg
  have hcs : (MarkedIdeal.pullback (Subtype.val : V → Y) J).cosupp =
      (Subtype.val : V → Y) ⁻¹' J.cosupp := cosupp_pullback_val J hhol V
  have hc : codimOnePartAlong (MarkedIdeal.pullback (Subtype.val : V → Y) J).N
      (MarkedIdeal.pullback (Subtype.val : V → Y) J).ideal
      (MarkedIdeal.pullback (Subtype.val : V → Y) J).d =
      (Subtype.val : V → Y) ⁻¹' codimOnePartAlong J.N J.ideal J.d :=
    codimOnePartAlong_pullback_val V hhol J.d
  have hm : p ∈ memberInterLocus (MarkedIdeal.pullback (Subtype.val : V → Y) J).N
      ((origMembers K T₁).map ((Subtype.val : V → Y) ⁻¹' ·))
      (MarkedIdeal.pullback (Subtype.val : V → Y) J).cosupp ↔
      (p : Y) ∈ memberInterLocus J.N (origMembers K T₁) J.cosupp := by
    rw [hcs]
    exact mem_memberInterLocus_preimage_iff Subtype.val
      (V.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p) _ _ _
  unfold IsSpecial
  rw [hlev, hF, hid, hc]
  exact or_congr Iff.rfl (and_congr_right fun _ => hm)

theorem exists_analytic_dimzero_literal_companion_exception (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (o : ℕ) (ho : 1 ≤ o) (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower m T₀)
    (T₁ : BlowupTower Y₀ Y) (hT₁ : IsGeoTestTower (geoTransformAlong m T₀) T₁) :
    ∃ Z : Set Y, IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 0 ∧
      Z ⊆ (geoTransformAlong (barMarked (companionOf n (geoTransformAlong m T₀) o)) T₁).cosupp ∧
      ∀ p : openPreimage T₁ (NonmonomialOrderTail.ordMask (geoTransformAlong m T₀) o),
        p ∈ (geoTransformAlong (barMarked (compAt m o T₀))
          (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m T₀) o) T₁)).cosupp →
        ¬ IsSpecial (compAt m o T₀)
          (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m T₀) o) T₁) p → (p : Y) ∈ Z := by
  obtain ⟨Z, hZ, hdZ, hsub, hspecial⟩ := exists_analytic_dimzero_entire_companion_exception
    hn m h o ho T₀ hT₀ T₁ hT₁
  refine ⟨Z, hZ, hdZ, hsub, ?_⟩
  intro p hp hnot
  by_contra hpZ
  obtain ⟨hJ, hid⟩ := coherent_coefficient_transform_and_mask_identity hn m h o ho T₀ hT₀ T₁ hT₁
  rw [hid, cosupp_pullback_val _
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hJ.isWellFormed.isCoherent hg) _] at hp
  exact hnot ((isSpecial_literal_companion_mask_iff hn m h o ho T₀ hT₀ T₁ hT₁ p).mpr
    (hspecial p ⟨hp, hpZ⟩))

end ActualCompanion
end
end Hironaka.HironakaGeneralTwoCompanionCurveLoci
