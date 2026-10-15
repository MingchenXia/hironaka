/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFirstAmbientStrictTraceFactor

/-! True first-step ambient strict trace exponent, from actual transverse
member order and the literal nearby-order exponent definition. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFirstAmbientStrictExponent
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFirstAmbientStrictTraceFactor HironakaSharpActualFirstGoodExceptionalTraceDensity
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProduct
  HironakaSharpActualRelativeProductOrder RelativePrincipalizationSpan RestrictedIdealExtension
  DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder IdealWeightPowers MonomialPartAlong MarkedIdealOperationsAlong
  RestrictedIdealWeight RestrictLeCalculus
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Genuine SNC coordinates give actual normalized member geometry, including
nonzero restriction and true order one, with no order model supplied. -/
theorem actual_normalized_transverse_member_geometry (hn : 0 < n)
    {N H : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hT : IsTransverse n N [H]) :
    let A := restrictOn n N (vanishingIdeal (n := n) H)
    A.IsCoherent ∧ (∀ y ∈ N,IsNonzeroAlongAt N A y) ∧
      (∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ g,A.mem y g ↔
        HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g) ∧
      ∀ x ∈ N ∩ H,ordinaryTraceOrder N A x=1 := by
  let A := restrictOn n N (vanishingIdeal (n := n) H)
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHc
  have hcA : A.IsCoherent := isCoherent_restrictOn hcH (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)
  have hnorm (q : ℕ) : cosupport n N A q=cosupport n N (vanishingIdeal (n := n) H) q :=
    Subset.antisymm (cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hcH) q)
      (cosupport_subset_of_restrictLe restrictLe_restrictOn q)
  have hnz : ∀ y ∈ N,IsNonzeroAlongAt N A y := by
    intro y hy
    by_cases hyH : y ∈ H
    · obtain ⟨f,hf,hfH,hnot⟩ := exists_actual_transverse_member_not_second_order hn hH hT hy
        (0 : Fin [H].length) hyH
      refine ⟨f,le_restrictOn hcH y f hfH,?_⟩
      apply frequently_iff.mpr
      intro U hU
      by_contra hno
      apply hnot
      have hz : (idealPow (pointIdeal n y) 2).mem y (0 : X → ℂ) :=
        ⟨holomorphicAt_const 0,0,Fin.elim0,Fin.elim0,(fun i => i.elim0),(fun i => i.elim0),
          Eventually.of_forall fun _ => by simp⟩
      refine ⟨0,hz,?_⟩
      filter_upwards [hU] with z hz hzN
      by_contra hne
      exact hno ⟨z,hz,hzN,hne⟩
    · have hOne : (vanishingIdeal (n := n) H).mem y (1 : X → ℂ) := by
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [hHc.1.isOpen_compl.mem_nhds hyH] with z hz hzH
        exact (hz hzH).elim
      refine ⟨1,le_restrictOn hcH y 1 hOne,frequently_iff.mpr ?_⟩
      intro U hU
      exact ⟨y,mem_of_mem_nhds hU,hy,one_ne_zero⟩
  refine ⟨hcA,hnz,?_,?_⟩
  · intro y _hy
    obtain ⟨f,hf,hgen⟩ := exists_originalMember_principal hn hH (List.mem_singleton_self H) y
    exact ⟨f,hf,fun g => and_congr_right fun _ => restricted_span_iff_principal hf hgen g⟩
  · intro x hx
    obtain ⟨f,_hf,hfH,hnot⟩ := exists_actual_transverse_member_not_second_order hn hH hT hx.1
      (0 : Fin [H].length) hx.2
    have hnot2 : x ∉ cosupport n N A 2 := by
      rw [hnorm]
      exact fun h => hnot (h.2 f hfH)
    have hholH : ∀ y g,(vanishingIdeal (n := n) H).mem y g → HolomorphicAt n g y := fun _ _ hg => hg.1
    have hOne : x ∈ cosupport n N A 1 := by
      rw [hnorm,cosupport_one hholH]
      exact ⟨hx.1,fun g hg => hg.2.self_of_nhds hx.2⟩
    rw [←ordGe_ordinaryTraceMarked_eq_cosupport N A hcA] at hnot2 hOne
    have hup := NonmonomialOrderLocal.nmOrd_le_of_notMem hnot2
    have hlo := NonmonomialOrderLocal.succ_le_nmOrd_of_mem (show ∃ q,x ∉ NonmonomialOrderLocal.ordGe (ordinaryTraceMarked N A) (q+1) from ⟨1,hnot2⟩) hOne
    exact hup.antisymm hlo

/-- Actual pointwise order additivity on the whole incident carrier gives the
literal nearby divisibility shift and the TRUE greatest exceptional exponent. -/
theorem actual_transverse_member_product_exponent_add_one (hn : 0 < n)
    {N H : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hT : IsTransverse n N [H]) {B : GermIdeal n X} (hcB : B.IsCoherent)
    (hnzB : ∀ y ∈ N,IsNonzeroAlongAt N B y)
    (hprB : ∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ g,B.mem y g ↔
      HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g) :
    let A := restrictOn n N (vanishingIdeal (n := n) H)
    ∀ x ∈ N ∩ H,ordinaryTraceOrder N (A.mul B) x=1+ordinaryTraceOrder N B x ∧
      divExpAlong n N (A.mul B) H x=1+divExpAlong n N B H x := by
  let A := restrictOn n N (vanishingIdeal (n := n) H)
  obtain ⟨hcA,hnzA,hprA,hordA⟩ := actual_normalized_transverse_member_geometry hn hN hH hT
  have hcP := isCoherent_mul hcA hcB
  have hnzP : ∀ y ∈ N,IsNonzeroAlongAt N (A.mul B) y := by
    intro y hy
    obtain ⟨f,hf,hfA⟩ := hprA y hy
    obtain ⟨g,hg,hgB⟩ := hprB y hy
    exact isNonzeroAlongAt_mul_of_relative_principal hN hcA hcB hnzA hnzB hy hf hg hfA hgB
  have hord : ∀ x ∈ N ∩ H,ordinaryTraceOrder N (A.mul B) x=1+ordinaryTraceOrder N B x := by
    intro x hx
    obtain ⟨f,hf,hfA⟩ := hprA x hx.1
    obtain ⟨g,hg,hgB⟩ := hprB x hx.1
    rw [ordinaryTraceOrder_mul_of_relative_principal hN hcA hcB hnzA hnzB hx.1 hf hg hfA hgB,hordA x hx]
  have hshift (x : X) (e : ℕ) : IsDivNearAlong n N (A.mul B) H (e+1) x ↔ IsDivNearAlong n N B H e x := by
    constructor
    · intro h
      filter_upwards [h] with z hz hzN hzH
      apply (ordinaryTraceOrder_cosupport_iff hN hcB hnzB hzN e).mpr
      have hh := (ordinaryTraceOrder_cosupport_iff hN hcP hnzP hzN (e+1)).mp (hz hzN hzH)
      rw [hord z ⟨hzN,hzH⟩] at hh
      omega
    · intro h
      filter_upwards [h] with z hz hzN hzH
      apply (ordinaryTraceOrder_cosupport_iff hN hcP hnzP hzN (e+1)).mpr
      have hh := (ordinaryTraceOrder_cosupport_iff hN hcB hnzB hzN e).mp (hz hzN hzH)
      rw [hord z ⟨hzN,hzH⟩]
      omega
  change ∀ x ∈ N ∩ H,ordinaryTraceOrder N (A.mul B) x=1+ordinaryTraceOrder N B x ∧
    divExpAlong n N (A.mul B) H x=1+divExpAlong n N B H x
  intro x hx
  refine ⟨hord x hx,?_⟩
  obtain ⟨d,hd⟩ := hN.2 x hx.1
  obtain ⟨r,hr⟩ := exists_isLocalRetraction hd
  have hholB : ∀ x g,B.mem x g → HolomorphicAt n g x := fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcB hg
  have hholP : ∀ x g,(A.mul B).mem x g → HolomorphicAt n g x := fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcP hg
  have hlow := (isDivNearAlong_iff_le_divExpAlong hr hx.2 (hnzP x hx.1) hholP).mp
    ((hshift x _).mpr (isDivNearAlong_divExpAlong hholB x))
  have hupp : divExpAlong n N (A.mul B) H x ≤ divExpAlong n N B H x+1 := by
    by_contra hgt
    have hp := (isDivNearAlong_divExpAlong hholP x).mono (show divExpAlong n N B H x+1+1 ≤ divExpAlong n N (A.mul B) H x by omega)
    exact not_isDivNearAlong_divExpAlong_succ hr hx.2 (hnzB x hx.1) hholB ((hshift x _).mp hp)
  omega

/-- The SAME actual blowup internally supplies all strict-trace relative
geometry from original SNC/density and actual centre containment. -/
theorem actual_first_ambient_strict_trace_relative_geometry (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H))
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hCH : C ⊆ H) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let D := π ⁻¹' C
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    IsClosedSubmanifold n N' ∧ IsSNCDivisor n [D] ∧ IsTransverse n N' [D] ∧
      I'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' I' y) ∧
      ∀ y ∈ N',∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,I'.mem y g ↔
        HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N' (·=f) y g := by
  let M : MarkedIdeal n X := ⟨N,[],vanishingIdeal (n := n) H,0⟩
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHc
  have hwM : M.IsWellFormed := ⟨hN,hcH,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hC : M.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
    change C ⊆ cosupport n N (vanishingIdeal (n := n) H) 0
    have hhol : ∀ x g,(vanishingIdeal (n := n) H).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
    rw [cosupport_zero hhol]
    exact hCN
  have hwQ := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwM hC hπ
  have hNC : HasNormalCrossings n C [H] :=
    NormalCrossingsComparison.hasNormalCrossings_of_forall_notMem hH
      (hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1) (by
        intro K hK _
        obtain rfl : K=H := List.mem_singleton.mp hK
        exact hCH)
  have hAmbient := SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hH hNC
  obtain ⟨hcI,hnzI,_⟩ := actual_first_ambient_strict_trace_factor_dictionary hn hN hH hdense hπ hCN hCH
  refine ⟨hwQ.isClosedSubmanifold_N,hwQ.isSNCDivisor,hwQ.isTransverse,hcI,hnzI,?_⟩
  intro y _hy
  obtain ⟨f,hf,hgen⟩ := exists_originalMember_principal hn hAmbient
    (H := BlowupStrictSubmanifold.geoStrictTransform π C H) (by simp) y
  exact ⟨f,hf,fun g => and_congr_right fun _ => restricted_span_iff_principal hf hgen g⟩

/-- The raw TOTAL is independently normalized from the genuine ambient product;
its actual order and greatest exceptional exponent exceed the strict trace by one. -/
theorem actual_first_raw_total_strict_trace_exponent_shift (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H))
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hCH : C ⊆ H) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let D := π ⁻¹' C
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    let P := (HironakaSharpOriginalFirstMemberExceptionalFactor.memberTotalMarked N H C π).ideal
    ∀ x ∈ N' ∩ D,ordinaryTraceOrder N' P x=1+ordinaryTraceOrder N' I' x ∧
      divExpAlong n N' P D x=1+divExpAlong n N' I' D x := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let D := π ⁻¹' C
  let B0 := vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H)
  let A0 := vanishingIdeal (n := n) D
  let A := restrictOn n N' A0
  let B := restrictOn n N' B0
  obtain ⟨hN',hD,hTD,hcB,hnzB,hprB⟩ :=
    actual_first_ambient_strict_trace_relative_geometry hn hN hH hdense hπ hCN hCH
  obtain ⟨hcA,hnzA,hprA,_hordA⟩ := actual_normalized_transverse_member_geometry hn hN' hD hTD
  have hcA0 : A0.IsCoherent := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hD (0 : Fin [D].length))
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcB0 : B0.IsCoherent := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hHc hCH)
  have hForward : RestrictLe N' (A0.mul B0) (A.mul B) := restrictLe_mul
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcA hg)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcB hg)
    (restrictLe_self_restrictOn hcA0) (restrictLe_self_restrictOn hcB0)
  have hBackward : RestrictLe N' (A.mul B) (A0.mul B0) := restrictLe_mul
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcA0 hg)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcB0 hg)
    restrictLe_restrictOn restrictLe_restrictOn
  have hFactor : restrictOn n N' (A0.mul B0)=restrictOn n N' (A.mul B) :=
    restrictOn_eq_of_restrictLe hN'.1 hForward hBackward
  have hTotal : (HironakaSharpOriginalFirstMemberExceptionalFactor.memberTotalMarked N H C π).ideal=
      restrictOn n N' (A.mul B) := by
    change ((⟨N,[],vanishingIdeal (n := n) H,0⟩ : MarkedIdeal n X).geoTransform C π).ideal=_
    rw [HironakaSharpOriginalFirstMemberExceptionalFactor.geoTransform_zeroMark_ideal_eq_restricted_total
      (⟨N,[],vanishingIdeal (n := n) H,0⟩ : MarkedIdeal n X) rfl C π]
    change restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))=_
    rw [BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul hπ hHc hCH]
    change restrictOn n N' ((GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mul B0)=_
    rw [HironakaSharpActualControlledRelativeSaturation.actual_pullback_centre_ideal_eq_exceptional_vanishing hπ]
    exact hFactor
  have hcP := isCoherent_mul hcA hcB
  have hnzP : ∀ y ∈ N',IsNonzeroAlongAt N' (A.mul B) y := by
    intro y hy
    obtain ⟨f,hf,hfA⟩ := hprA y hy
    obtain ⟨g,hg,hgB⟩ := hprB y hy
    exact isNonzeroAlongAt_mul_of_relative_principal hN' hcA hcB hnzA hnzB hy hf hg hfA hgB
  have hCos (q : ℕ) : cosupport n N' (restrictOn n N' (A.mul B)) q=cosupport n N' (A.mul B) q :=
    Subset.antisymm (cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hcP) q)
      (cosupport_subset_of_restrictLe restrictLe_restrictOn q)
  have hExp := MonomialPartEtale.divExpAlong_congr hCos
  change ∀ x ∈ N' ∩ D,ordinaryTraceOrder N' (HironakaSharpOriginalFirstMemberExceptionalFactor.memberTotalMarked N H C π).ideal x=1+ordinaryTraceOrder N' B x ∧
    divExpAlong n N' (HironakaSharpOriginalFirstMemberExceptionalFactor.memberTotalMarked N H C π).ideal D x=1+divExpAlong n N' B D x
  intro x hx
  obtain ⟨hOrd,hDiv⟩ := actual_transverse_member_product_exponent_add_one hn hN' hD hTD hcB hnzB hprB x hx
  rw [hTotal]
  exact ⟨(HironakaSharpActualFiniteMemberProduct.ordinaryTraceOrder_restrictOn_eq hN' hcP hnzP hx.1).trans hOrd,
    (congrFun (congrFun hExp D) x).trans hDiv⟩

end
end Hironaka.HironakaSharpActualFirstAmbientStrictExponent
