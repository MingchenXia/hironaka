/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFirstGoodCurveBase

/-! Genuine chronological curve residual units at EVERY accumulated exceptional
point, without FIRST-good/order/reducedness/unit certificates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveExceptionalResidualUnit
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFirstGoodLowerDimension HironakaSharpActualFirstGoodReducedTraces
  HironakaSharpActualChronologicalNoOldFactor HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteMemberProduct
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProduct
  RelativePrincipalizationSpan DivisorExponentAlong NormalCrossings MemberTraceIdealAlong
  BlowupFlatCoordinates MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder IdealWeightPowers
  BoundaryCount InvertibleIdealQuotient
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual pure curve dimension forces a genuine transverse boundary trace
isolating neighborhood from the SAME real SNC coordinates. -/
theorem exists_actual_curve_member_isolating_open (hn : 0 < n)
    {N : Set Y} {E : List (Set Y)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {x : Y} (hr : RegularAtDim (n := n) N x 1) (i : Fin E.length) (hi : x ∈ E.get i) :
    ∃ U : Set Y,IsOpen U ∧ x ∈ U ∧ (N ∩ E.get i) ∩ U ⊆ {x} := by
  have hx := hr.2.1
  obtain ⟨k,Φ,σ,_hsrc,hNflat,hfree,_hinj,hA,_hp,_hgen,_hres⟩ :=
    exists_actual_original_member_product_normal_form hn hE hT hx
  have hxD : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hNk : RegularAtDim (n := n) N x (min k n) :=
    RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
      (fun {y} hy hyΦ => by
        have h := hNflat hy hyΦ
        rw [←complexCoordinatePlane_min] at h
        exact h) hx (mem_chart_source _ x) Φ.center_mem_source
  have hk : min k n=1 := Nat.le_antisymm
    (RegularPointDimension.le_of_regularAtDim hNk hr) (RegularPointDimension.le_of_regularAtDim hr hNk)
  have hslt : (σ i).val < min k n := Nat.lt_min.mpr ⟨hfree i hi,(σ i).isLt⟩
  rw [hk] at hslt
  have hs0 : (σ i).val=0 := by omega
  have hzero : ∀ y ∈ N ∩ E.get i,y ∈ flatDomain Φ → Φ.toFun (chartAt (ComplexModel n) x y)=0 := by
    intro y hy hyD
    ext j
    by_cases hji : j=σ i
    · subst j
      exact (hA i hi hyD.1 hyD.2).mp hy.2
    · have hj1 : 1 ≤ j.val := by
        have hj0 : j.val ≠ 0 := fun h => hji (Fin.ext (h.trans hs0.symm))
        omega
      have hjn := j.isLt
      have hkj : k ≤ j.val := by omega
      exact ((hNflat hyD.1 hyD.2).mp hy.1) j hkj
  refine ⟨flatDomain Φ,isOpen_flatDomain Φ,hxD,?_⟩
  intro y hy
  apply mem_singleton_iff.mpr
  have heq := (hzero y hy.1 hy.2).trans (hzero x ⟨hx,hi⟩ hxD).symm
  have hinv := congrArg (fun z => (chartAt (ComplexModel n) x).symm (Φ.invFun z)) heq
  simpa only [Φ.left_inv _ hy.2.2,Φ.left_inv _ hxD.2,
    (chartAt (ComplexModel n) x).left_inv hy.2.1,(chartAt (ComplexModel n) x).left_inv hxD.1] using hinv

/-- No actual common member factor on a curve forces a true unit at an
incident transverse boundary point, without an order or FIRST-good premise. -/
theorem actual_curve_no_factor_member_unit (hn : 0 < n)
    {N : Set Y} {E : List (Set Y)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n Y} (hI : I.IsCoherent) {x : Y}
    (hr : RegularAtDim (n := n) N x 1) (i : Fin E.length) (hi : x ∈ E.get i)
    (hnd : ∃ a,I.mem x a ∧ ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a) :
    I.mem x (1 : Y → ℂ) := by
  obtain ⟨U,hU,hxU,hsub⟩ := exists_actual_curve_member_isolating_open hn hE hT hr i hi
  obtain ⟨a,ha,hna⟩ := hnd
  have hah := GermIdeal.IsCoherent.holomorphicAt_mem hI ha
  have hax : a x ≠ 0 := by
    intro h0
    apply hna
    apply (isInSpanOnAt_vanishingIdeal_iff_mem hE hT hr.2.1 i hah).mpr
    refine ⟨hah,?_⟩
    filter_upwards [hU.mem_nhds hxU] with y hy hyNH
    have hyx : y=x := mem_singleton_iff.mp (hsub ⟨hyNH,hy⟩)
    exact hyx ▸ h0
  apply HomogenizedIdeal.mem_of_isInSpanAt hI
  refine isInSpanAt_of_eq_mul ha (holomorphicAt_const 1) (holomorphicAt_inv hah hax) ?_
  filter_upwards [hah.continuousAt.eventually_ne hax] with y hy
  exact (inv_mul_cancel₀ hy).symm

private theorem unit_mem_relativeProduct_at (N : Set Y) (L : List (GermIdeal n Y)) (x : Y)
    (hL : ∀ I ∈ L,I.mem x (1 : Y → ℂ)) : (relativeIdealListProduct N L).mem x (1 : Y → ℂ) := by
  induction L with
  | nil => exact holomorphicAt_const 1
  | cons I L ih =>
    have hi := hL I (by simp)
    have ht := ih (fun J hJ => hL J (List.mem_cons_of_mem I hJ))
    have hm : (I.mul (relativeIdealListProduct N L)).mem x (1 : Y → ℂ) := by
      change IsInSpanAt (n := n) (fun s => ∃ a b,I.mem x a ∧
        (relativeIdealListProduct N L).mem x b ∧ s=a*b) x (1 : Y → ℂ)
      exact isInSpanAt_self ⟨1,1,hi,ht,by ext; simp⟩ (holomorphicAt_const 1)
    exact ⟨holomorphicAt_const 1,IsInSpanAt.restrict (isInSpanAt_self hm (holomorphicAt_const 1))⟩

/-- ONLY original curve inputs supply units in EVERY actual chronological
member at EVERY accumulated exceptional point, true product order0 and Z avoidance. -/
theorem original_curve_exceptional_residual_units_and_defect_disjoint (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    let F := (geoTransformAlong (geometricTemplate W []) T).E
    ∀ y ∈ N,y ∈ ⋃ H ∈ F,H →
      (∀ i : Fin E.length,(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.mem y (1 : Y → ℂ)) ∧
      ordinaryTraceOrder N (chronologicalMemberProduct W E T) y=0 ∧ y ∉ chronologicalDistinctDefect W E T := by
  dsimp only
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hT
  have hPure := actual_template_regular_dimension hW 1 hr T hT
  intro y hy hyE
  obtain ⟨H,hH,hyH⟩ := mem_iUnion₂.mp hyE
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hH
  have hUnits : ∀ i : Fin E.length,(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.mem y (1 : Y → ℂ) := by
    intro i
    obtain ⟨hNi,hEi,_hmi,hwi,_hnzi,_hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
    have hnd := original_members_actual_finite_chronological_no_exceptional_factor hn hW hE hdense i T hT
    dsimp only at hnd
    rw [hNi,hEi] at hnd
    exact actual_curve_no_factor_member_unit hn hwT.isSNCDivisor hwT.isTransverse hwi.isCoherent
      (hPure y hy) j hyH (hnd y hy j hyH)
  have hP1 : (chronologicalMemberProduct W E T).mem y (1 : Y → ℂ) := by
    apply unit_mem_relativeProduct_at
    intro I hIL
    obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hIL
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    exact hUnits i
  obtain ⟨hcP,hnzP,_hprP,_hOrdP⟩ := original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  have hP0 : ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) y=0 := by
    have hnot : ¬1 ≤ ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) y := by
      intro h
      have hcos := (ordinaryTraceOrder_cosupport_iff hwT.isClosedSubmanifold_N hcP hnzP hy 1).mpr h
      exact one_ne_zero ((vanishesToOrderOn_one_iff hy (holomorphicAt_const 1)).mp (hcos.2 1 hP1))
    omega
  refine ⟨hUnits,hP0,?_⟩
  intro hZ
  have hbad := hZ.2
  rw [←chronological_product_eq_actual_family_product W E T,hP0] at hbad
  exact Nat.not_lt_zero _ hbad

end
end Hironaka.HironakaSharpActualCurveExceptionalResidualUnit
