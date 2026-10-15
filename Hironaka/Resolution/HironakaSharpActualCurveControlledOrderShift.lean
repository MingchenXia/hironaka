/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualNormalizedControlledPrincipalHistory

/-! Genuine WHOLE controlled mark-one factor and actual curve ordinary-order
shift; no driver, desired factor or invariant reset certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveControlledOrderShift
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualNormalizedControlledPrincipalHistory HironakaSharpActualControlledRelativeSaturation
  HironakaSharpActualFirstAmbientStrictExponent HironakaSharpActualCurveStrictTraceContactDrop
  HironakaSharpActualFiniteMemberProduct HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualRelativeProductOrder
  HironakaSharpActualChronologicalAmbientTrace HironakaSharpActualFirstGoodLowerDimension
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  RestrictLeCalculus MonomialPartAlong DivisorExponentAlong NormalCrossings
  InvertibleIdealQuotient IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder MarkedIdealOperationsAlong
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual coherent finite-span closure proves the genuine whole first power. -/
theorem actual_coherent_first_power_eq {I : GermIdeal n X} (hcI : I.IsCoherent) : idealPow I 1=I := by
  ext x g
  constructor
  · intro hg
    change IsInSpanAt (n := n) (fun a => ∃ u v,(unitIdeal n X).mem x u ∧ I.mem x v ∧ a=u*v) x g at hg
    apply HomogenizedIdeal.mem_of_isInSpanAt hcI
    apply IsInSpanAt.mono (T := I.mem x) ?_ hg
    rintro a ⟨u,v,hu,hv,rfl⟩
    have hvh := GermIdeal.IsCoherent.holomorphicAt_mem hcI hv
    exact HomogenizedIdeal.mem_of_isInSpanAt hcI
      (isInSpanAt_of_eq_mul hv (hu.mul hvh) hu (Eventually.of_forall fun _ => rfl))
  · intro hg
    change IsInSpanAt (n := n) (fun a => ∃ u v,(unitIdeal n X).mem x u ∧ I.mem x v ∧ a=u*v) x g
    exact isInSpanAt_self ⟨1,g,holomorphicAt_const 1,hg,by ext;simp⟩
      (GermIdeal.IsCoherent.holomorphicAt_mem hcI hg)

/-- Genuine original admissibility supplies real restricted divisibility
before BOTH relative-colon directions construct the WHOLE factor identity. -/
theorem actual_controlled_mark_one_whole_factor (M : MarkedIdeal n X) (hd : M.d=1)
    (hN : IsClosedSubmanifold n M.N) (hcI : M.ideal.IsCoherent)
    {C : Set X} (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π) :
    restrictOn n (M.geoTransform C π).N (GermIdeal.pullback (m := n) π M.ideal)=
      restrictOn n (M.geoTransform C π).N
        ((vanishingIdeal (n := n) (π ⁻¹' C)).mul (M.geoTransform C π).ideal) := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C M.N
  let P := GermIdeal.pullback (m := n) π M.ideal
  let D := vanishingIdeal (n := n) (π ⁻¹' C)
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hC.subset_N
  have hcP : P.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hcI
  have hcPB := GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff
    (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)
  have hPow : idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d=D := by
    rw [hd,actual_coherent_first_power_eq hcPB,actual_pullback_centre_ideal_eq_exceptional_vanishing hπ]
  have hdiv : RestrictLe N' P D := by
    have h1 := HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport hcI hN hC.1
      hC.subset_N hC.2.1
    have h2 := RestrictLeCalculus.restrictLe_pullback hπ.contMDiff (W := N')
      (fun y hy => BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy)
      (GermIdealPullbackCalculus.isCoherent_idealPow (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ) _) h1
    rw [BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff
      (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ),hPow] at h2
    exact h2
  have hInv : IsInvertibleAlong n N' D := by
    have h := isInvertibleAlong_geoStrictTransform hπ M.N M.d
    rw [hPow] at h
    exact h
  have hControlled : (M.geoTransform C π).ideal=colonAlong n N' P D := by
    rw [geoTransform_ideal,hPow]
  have hFactor := restrictOn_eq_of_restrictLe hN'.1
    (restrictLe_mul_colon hcP hInv hdiv)
    (restrictLe_mul_colon' hcP (VanishingIdealCoherent.isCoherent_vanishingIdeal hN'))
  change restrictOn n N' P=restrictOn n N' (D.mul (M.geoTransform C π).ideal)
  rw [hControlled]
  exact hFactor

/-- Genuine factor normalization, actual controlled generators and real curve
raw order transport prove the EXISTING ordinary controlled order shift. -/
theorem actual_curve_controlled_mark_one_order_drop (hn : 0 < n) (M : MarkedIdeal n X)
    (hd : M.d=1) (hw : M.IsWellFormed)
    (hnz : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x)
    (hp : ∀ x ∈ M.N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,
      (restrictOn n M.N M.ideal).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) M.N (·=f) x g)
    (hrN : ∀ x ∈ M.N,RegularAtDim (n := n) M.N x 1)
    {C : Set X} (hC : M.IsAdmissibleCentre C)
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {π : Y → X} (hπ : IsBlowupAlong n C π) {z : Y} (hz : z ∈ (M.geoTransform C π).N) (hzC : π z ∈ C) :
    ordinaryTraceOrder (M.geoTransform C π).N (M.geoTransform C π).ideal z+1=
      ordinaryTraceOrder M.N M.ideal (π z) := by
  let N' := (M.geoTransform C π).N
  let D := π ⁻¹' C
  let D0 := vanishingIdeal (n := n) D
  let A := restrictOn n N' D0
  let B := (M.geoTransform C π).ideal
  have hwNew := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hC hπ
  have hN' : IsClosedSubmanifold n N' := hwNew.isClosedSubmanifold_N
  have hcB : B.IsCoherent := hwNew.isCoherent
  have hnzB : ∀ x ∈ N',IsNonzeroAlongAt N' B x :=
    isNonzeroAlongAt_geoTransform_without_admissibility M hw.isClosedSubmanifold_N hw.isCoherent hπ hC.subset_N hnz
  have hprB : ∀ x ∈ N',∃ f : Y → ℂ,HolomorphicAt n f x ∧ ∀ g,B.mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N' (·=f) x g := by
    intro x hx
    obtain ⟨f,hf,hgen⟩ := actual_admissible_geoTransform_relative_principal_of_normalized_source
      M hw.isClosedSubmanifold_N hw.isCoherent hp hC hπ x hx
    exact ⟨f,((hgen f).mp hf).1,hgen⟩
  have hD : IsSNCDivisor n [D] := BlowupSNCTransform.isSNCDivisor_preimage_centre hπ
  have hTrans : IsTransverse n N' [D] := BlowupSNCTransform.isTransverse_preimage_centre hπ hw.isClosedSubmanifold_N hC.subset_N
  obtain ⟨hcA,hnzA,hprA,_hOrdA⟩ := actual_normalized_transverse_member_geometry hn hN' hD hTrans
  have hcD : D0.IsCoherent := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hD (0 : Fin [D].length))
  have hForward : RestrictLe N' (D0.mul B) (A.mul B) := restrictLe_mul
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcA hg)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcB hg)
    (restrictLe_self_restrictOn hcD) (restrictLe_refl hcB)
  have hBackward : RestrictLe N' (A.mul B) (D0.mul B) := restrictLe_mul
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcD hg)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcB hg)
    restrictLe_restrictOn (restrictLe_refl hcB)
  have hNormProduct : restrictOn n N' (D0.mul B)=restrictOn n N' (A.mul B) :=
    restrictOn_eq_of_restrictLe hN'.1 hForward hBackward
  have hcMul := isCoherent_mul hcA hcB
  have hnzMul : ∀ x ∈ N',IsNonzeroAlongAt N' (A.mul B) x := by
    intro x hx
    obtain ⟨f,hf,hgenF⟩ := hprA x hx
    obtain ⟨g,hg,hgenG⟩ := hprB x hx
    exact isNonzeroAlongAt_mul_of_relative_principal hN' hcA hcB hnzA hnzB hx hf hg hgenF hgenG
  have hFactor := actual_controlled_mark_one_whole_factor M hd hw.isClosedSubmanifold_N hw.isCoherent hC hπ
  change restrictOn n N' (GermIdeal.pullback (m := n) π M.ideal)=restrictOn n N' (D0.mul B) at hFactor
  have hOrd := (actual_transverse_member_product_exponent_add_one hn hN' hD hTrans hcB hnzB hprB z ⟨hz,hzC⟩).1
  have hRawOrder : ordinaryTraceOrder N' (restrictOn n N' (GermIdeal.pullback (m := n) π M.ideal)) z=
      1+ordinaryTraceOrder N' B z := by
    rw [hFactor,hNormProduct,ordinaryTraceOrder_restrictOn_eq hN' hcMul hnzMul hz]
    exact hOrd
  have hRaw := actual_curve_raw_total_order_eq_above_centre hw.isClosedSubmanifold_N hrN hrC hw.isCoherent hnz
    hπ hC.subset_N hz hzC
  change ordinaryTraceOrder N' (restrictOn n N' (GermIdeal.pullback (m := n) π M.ideal)) z=
    ordinaryTraceOrder M.N M.ideal (π z) at hRaw
  change ordinaryTraceOrder N' B z+1=ordinaryTraceOrder M.N M.ideal (π z)
  omega

/-- ONLY original smooth curve/SNC/density ANYTEST supplies every actual
current geometry/principal/discrete condition for the genuine next shift. -/
theorem original_curve_product_next_controlled_order_drop (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {C : Set Y} (hC : (geoTransformAlong (originalMemberProductMarked W E 1) T).IsAdmissibleCentre C)
    {π : Z → Y} (hπ : IsBlowupAlong n C π)
    {z : Z} (hz : z ∈ (geoTransformAlong (originalMemberProductMarked W E 1) (.step T C π hπ)).N)
    (hzC : π z ∈ C) :
    ordinaryTraceOrder (geoTransformAlong (originalMemberProductMarked W E 1) (.step T C π hπ)).N
      (geoTransformAlong (originalMemberProductMarked W E 1) (.step T C π hπ)).ideal z+1=
      ordinaryTraceOrder (geoTransformAlong (originalMemberProductMarked W E 1) T).N
        (geoTransformAlong (originalMemberProductMarked W E 1) T).ideal (π z) := by
  let M := originalMemberProductMarked W E 1
  let Q := geoTransformAlong M T
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit T hT
  have hGeom := actual_original_test_history_template M hInit.isWellFormed T hT
  have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
  have hPure : ∀ x ∈ Q.N,RegularAtDim (n := n) Q.N x 1 := by
    rw [hQN]
    exact actual_template_regular_dimension hW 1 hr T hGeom
  have hStep : IsGeoTestTower M (.step T C π hπ) := ⟨hT,hC⟩
  have hrC := (original_domain_one_test_actual_discrete_centres M hInit (.step T C π hπ) hStep).2
  have hp := original_product_actual_normalized_principal_history hn hW hE 1 T hT
  have hd : Q.d=1 := d_geoTransformAlong M T
  exact actual_curve_controlled_mark_one_order_drop hn Q hd hDom.isWellFormed hDom.isNonzeroAlongAt hp hPure hC hrC hπ hz hzC

end
end Hironaka.HironakaSharpActualCurveControlledOrderShift
