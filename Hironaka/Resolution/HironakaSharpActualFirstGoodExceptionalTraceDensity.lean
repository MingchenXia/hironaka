/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFirstGoodLowerProduct

/-! Genuine FIRST-good trace density outside ALL actual accumulated exceptional
members. No trace transversality, joint SNC or desired density certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFirstGoodExceptionalTraceDensity
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFirstGoodReducedTraces HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualPrincipalOrderOneTrace
  HironakaSharpActualChronologicalNoOldFactor HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  DivisorExponentAlong NormalCrossings NormalCrossingsInvariance BlowupFlatCoordinates
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder IdealWeightPowers
  InvertibleIdealQuotient MonomialPartAlong MonomialCase OrderTaylor MemberPullback
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Original actual transverse SNC coordinates construct a true member germ
whose restriction has genuine next-power exclusion on the actual carrier. -/
theorem exists_actual_transverse_member_not_second_order (hn : 0 < n)
    {N : Set Y} {E : List (Set Y)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {x : Y} (hx : x ∈ N) (i : Fin E.length) (hi : x ∈ E.get i) :
    ∃ f : Y → ℂ,HolomorphicAt n f x ∧ (vanishingIdeal (n := n) (E.get i)).mem x f ∧
      ¬VanishesToOrderOn n N x 2 f := by
  obtain ⟨k,Φ,σ,hsrc,hNflat,hfree,_hinj,hA,_hp,_hgen,_hres⟩ :=
    exists_actual_original_member_product_normal_form hn hE hT hx
  have hxD : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  let f := flatCoord Φ (σ i)
  have hf : HolomorphicAt n f x := holomorphicAt_flatCoord Φ (σ i) hxD
  have hflatH : ∀ {y : Y},y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i)=0) := hA i hi
  have hfH : (vanishingIdeal (n := n) (E.get i)).mem x f :=
    (vanishingIdeal_mem_iff_flatCoord Φ hflatH hxD f).mpr (isInSpanAt_eq_iff.mpr
      ⟨hf,1,holomorphicAt_const 1,Eventually.of_forall fun _ => by simp [f]⟩)
  have hf0 : f x=0 := hfH.2.self_of_nhds hi
  have hnot : ¬(idealPow (pointIdeal n x) 2).mem x f := by
    have hh := prod_flatCoord_pow_order Φ (fun _ : Fin 1 => σ i) (fun _ => 1) hxD
      (Finset.univ : Finset (Fin 1)) (fun _ _ => hf0)
    simpa [f] using hh.2
  have hr : IsLocalRetraction n N (flatRetract Φ k) x :=
    isLocalRetraction_flatRetract hsrc hNflat hxD hx
  have hfix : f ∘ flatRetract Φ k =ᶠ[𝓝 x] f :=
    (eventually_flatMap_flatRetract hsrc hNflat hxD hx (hfree i hi)).mono fun y hy => hy.2
  refine ⟨f,hf,hfH,fun h => hnot ?_⟩
  exact mem_idealPow_congr (hr.vanishesToOrderOn_iff.mp h) hfix

/-- Real no-factor witness and actual reduced order1 construct genuine trace
points outside a true transverse member in EVERY original neighborhood. -/
theorem actual_orderOne_no_factor_trace_outside_member (hn : 0 < n)
    {N : Set Y} (hN : IsClosedSubmanifold n N) {E : List (Set Y)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {I : GermIdeal n Y}
    (hI : I.IsCoherent) (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y)
    {x : Y} (hx : x ∈ N ∩ I.zeroLocus) (f : Y → ℂ) (hf : HolomorphicAt n f x)
    (hgen : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (hord : ordinaryTraceOrder N I x=1) (i : Fin E.length)
    (hnd : x ∈ E.get i → ∃ a,I.mem x a ∧
      ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a) :
    ∃ᶠ y in 𝓝 x,y ∈ N ∩ I.zeroLocus ∧ y ∉ E.get i := by
  by_cases hxi : x ∈ E.get i
  · obtain ⟨b,hb,hbH,hbnot⟩ := exists_actual_transverse_member_not_second_order hn hE hT hx.1 i hxi
    obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,hRed,_hReg⟩ :=
      actual_orderOne_relative_reduced_trace hN hI hnz hx.1 f hf hgen hord
    have hfI : I.mem x f := (hgen f).mpr ⟨hf,isInSpanOnAt_eq_iff.mpr
      ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
    have hfx : f x=0 := hx.2 f hfI
    by_contra hfreq
    have hContain : ∀ᶠ y in 𝓝 x,y ∈ N ∩ I.zeroLocus → y ∈ E.get i :=
      (not_frequently.mp hfreq).mono fun y hy hyS => by_contra fun hne => hy ⟨hyS,hne⟩
    have hbS : (vanishingIdeal (n := n) (N ∩ I.zeroLocus)).mem x b := by
      refine ⟨hb,?_⟩
      filter_upwards [hContain,hbH.2] with y hy hyb hyS
      exact hyb (hy hyS)
    have hbI := (hRed b).mpr hbS
    obtain ⟨c,hc,hbc⟩ := isInSpanOnAt_eq_iff.mp ((hgen b).mp hbI).2
    have hcx : c x ≠ 0 := CodimOneCentreAlong.apply_ne_zero_of_not_vanishesToOrderOn_on hx.1 hf hfx hc
      (d := 1) (by simpa only [pow_one] using hbc) hbnot
    have hfB : IsInSpanOnAt (n := n) N (·=b) x f := by
      refine isInSpanOnAt_eq_iff.mpr ⟨fun y => (c y)⁻¹,holomorphicAt_inv hc hcx,?_⟩
      filter_upwards [hbc,hc.continuousAt.eventually_ne hcx] with y hy hyc hyN
      rw [hy hyN,inv_mul_cancel_left₀ hyc]
    have hfH : IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x f :=
      IsInSpanOnAt.mono (S := (·=b)) (fun a ha => ha ▸ hbH) hfB
    obtain ⟨a,ha,hna⟩ := hnd hxi
    exact hna (IsInSpanOnAt.trans (S := (·=f)) (fun d hd => hd ▸ hfH) ((hgen a).mp ha).2)
  · apply frequently_iff.mpr
    intro U hU
    exact ⟨x,mem_of_mem_nhds hU,hx,hxi⟩

private theorem dense_finite_closed_avoidance {Z : Type*} [TopologicalSpace Z]
    (S : Set Z) (E : List (Set Z)) (hc : ∀ H ∈ E,IsClosed H)
    (hf : ∀ x ∈ S,∀ H ∈ E,∃ᶠ y in 𝓝 x,y ∈ S ∧ y ∉ H) :
    S ⊆ closure (S \ ⋃ H ∈ E,H) := by
  induction E with
  | nil => simpa using (subset_closure : S ⊆ closure S)
  | cons H E ih =>
    intro x hx
    apply mem_closure_iff.mpr
    intro U hU hxU
    obtain ⟨y,⟨hyS,hyH⟩,hyU⟩ := ((hf x hx H (by simp)).and_eventually (hU.mem_nhds hxU)).exists
    have hyTail := ih (fun A hA => hc A (List.mem_cons_of_mem H hA))
      (fun z hz A hA => hf z hz A (List.mem_cons_of_mem H hA)) hyS
    obtain ⟨z,hzU,hzS,hzE⟩ := mem_closure_iff.mp hyTail (U \ H) (hU.sdiff (hc H (by simp))) ⟨hyU,hyH⟩
    refine ⟨z,hzU.1,hzS,?_⟩
    intro hzAll
    obtain ⟨A,hA,hzA⟩ := mem_iUnion₂.mp hzAll
    rcases List.mem_cons.mp hA with rfl | hA
    · exact hzU.2 hzA
    · exact hzE (mem_iUnion₂.mpr ⟨A,hA,hzA⟩)

/-- ONLY original inputs construct the computed first-good open, actual smooth
lower traces, real accumulated SNC boundary, and WHOLE-boundary density there. -/
theorem exists_original_first_good_exceptional_trace_density (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    ∃ O : Opens Y,(O : Set Y)=(chronologicalDistinctDefect W E T)ᶜ ∧
      IsSNCDivisor n ((geoTransformAlong (geometricTemplate W []) T).E.map ((Subtype.val : O → Y) ⁻¹' ·)) ∧
      ∀ i : Fin E.length,
        let S := (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T
        let F := (geoTransformAlong (geometricTemplate W []) T).E.map ((Subtype.val : O → Y) ⁻¹' ·)
        IsClosedSubmanifold n S ∧ S ⊆ closure (S \ ⋃ H ∈ F,H) := by
  obtain ⟨O,hO,hTraces⟩ := exists_actual_first_good_open_reduced_traces hn hW hE hdense d hr T hT
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hT
  have hFo := isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hwT.isSNCDivisor
  refine ⟨O,hO,hFo,?_⟩
  intro i
  refine ⟨(hTraces i).1,?_⟩
  apply dense_finite_closed_avoidance _ _ hFo.1
  intro x hx H hH
  obtain ⟨H0,hH0,rfl⟩ := List.mem_map.mp hH
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hH0
  obtain ⟨hNi,hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  have hnd := original_members_actual_finite_chronological_no_exceptional_factor hn hW hE hdense i T hT
  dsimp only at hnd
  rw [hNi,hEi] at hnd
  rw [hNi] at hnzi hpri
  have hxGood : (x : Y) ∉ chronologicalDistinctDefect W E T := by
    change (x : Y) ∈ (chronologicalDistinctDefect W E T)ᶜ
    rw [←hO]
    exact x.property
  have hFam : ∀ a : Fin E.length,(chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal.IsCoherent := by
    intro a
    exact (original_members_actual_finite_chronological_geometry hn hW hE hdense a T hT).2.2.2.1.isCoherent
  have hp := (actual_proper_iff_zeroLocus hFam i (x : Y)).mpr hx.2
  have hOrd := (original_first_good_factor_rigidity hn hW hE hdense T hT hx.1 hxGood).1 i hp
  obtain ⟨f,hf,hgen⟩ := hpri x hx.1
  have hfreq := actual_orderOne_no_factor_trace_outside_member hn hwT.isClosedSubmanifold_N
    hwT.isSNCDivisor hwT.isTransverse hwi.isCoherent hnzi hx f hf hgen hOrd j (hnd x hx.1 j)
  rw [← O.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x] at hfreq
  exact Filter.frequently_map.mp hfreq

end
end Hironaka.HironakaSharpActualFirstGoodExceptionalTraceDensity
