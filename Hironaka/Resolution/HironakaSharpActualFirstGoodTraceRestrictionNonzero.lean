/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFirstGoodReducedTraces

/-! Genuine OTHER-member nonzero on actual FIRST-good reduced traces.
True order-one cofactors and full germ injection precede noncontainment. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFirstGoodTraceRestrictionNonzero
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFirstGoodReducedTraces HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualPrincipalOrderOneTrace
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualFiniteMemberProduct
  RelativePrincipalizationSpan RestrictedIdealExtension DivisorExponentAlong NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder IdealWeightPowers
  InvertibleIdealQuotient HironakaSharpActualRelativeProductOrder MonomialPartAlong
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem frequent_nonzero_of_not_vanishing {S : Set X} {x : X} {f : X → ℂ}
    (hf : HolomorphicAt n f x) (hnot : ¬(vanishingIdeal (n := n) S).mem x f) :
    ∃ᶠ y in 𝓝 x,y ∈ S ∧ f y ≠ 0 := by
  by_contra hfreq
  apply hnot
  refine ⟨hf,?_⟩
  have hh := not_frequently.mp hfreq
  filter_upwards [hh] with y hy hyS
  by_contra hyf
  exact hy ⟨hyS,hyf⟩

/-- Actual unit cofactor proves nonzero on a literal trace from true order1
and genuine distinct whole relative ideal germs, with no trace-model input. -/
theorem actual_orderOne_distinct_trace_nonzero {N : Set X} (hN : IsClosedSubmanifold n N)
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hnzI : ∀ y ∈ N,IsNonzeroAlongAt N I y) (hnzJ : ∀ y ∈ N,IsNonzeroAlongAt N J y)
    {x : X} (hx : x ∈ N)
    (f : X → ℂ) (hf : HolomorphicAt n f x)
    (hgenI : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (g : X → ℂ) (hg : HolomorphicAt n g x)
    (hgenJ : ∀ a,J.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=g) x a)
    (hordI : ordinaryTraceOrder N I x=1) (hordJ : ordinaryTraceOrder N J x=1)
    (hDistinct : ¬∀ a,I.mem x a ↔ J.mem x a) :
    IsNonzeroAlongAt (N ∩ I.zeroLocus) J x := by
  have hfI : I.mem x f := (hgenI f).mpr
    ⟨hf,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  have hgJ : J.mem x g := (hgenJ g).mpr
    ⟨hg,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  have hcosI : x ∈ cosupport n N I 1 :=
    (ordinaryTraceOrder_cosupport_iff hN hI hnzI hx 1).mpr (by rw [hordI])
  have hfx : f x=0 := (vanishesToOrderOn_one_iff hx hf).mp (hcosI.2 f hfI)
  have hnot2 : ¬VanishesToOrderOn n N x 2 g := by
    intro hh
    have htwo : 2 ≤ ordinaryTraceOrder N J x :=
      (ordinaryTraceOrder_cosupport_iff hN hJ hnzJ hx 2).mp
        ((cosupport_relative_principal_iff_vanishes hx hg hgenJ 2).mpr hh)
    rw [hordJ] at htwo
    omega
  obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,hRed,_hReg⟩ :=
    actual_orderOne_relative_reduced_trace hN hI hnzI hx f hf hgenI hordI
  have hnot : ¬(vanishingIdeal (n := n) (N ∩ I.zeroLocus)).mem x g := by
    intro hgv
    have hgI := (hRed g).mpr hgv
    obtain ⟨c,hc,hgc⟩ := isInSpanOnAt_eq_iff.mp ((hgenI g).mp hgI).2
    have hcx : c x ≠ 0 := CodimOneCentreAlong.apply_ne_zero_of_not_vanishesToOrderOn_on hx hf hfx hc
      (d := 1) (by simpa only [pow_one] using hgc) hnot2
    have hfG : IsInSpanOnAt (n := n) N (·=g) x f := by
      refine isInSpanOnAt_eq_iff.mpr ⟨fun y => (c y)⁻¹,holomorphicAt_inv hc hcx,?_⟩
      filter_upwards [hgc,hc.continuousAt.eventually_ne hcx] with y hy hyc hyN
      rw [hy hyN,inv_mul_cancel_left₀ hyc]
    apply hDistinct
    intro a
    constructor
    · intro ha
      exact (hgenJ a).mpr ⟨((hgenI a).mp ha).1,
        IsInSpanOnAt.trans (S := (·=f)) (fun b hb => hb ▸ hfG) ((hgenI a).mp ha).2⟩
    · intro ha
      exact (hgenI a).mpr ⟨((hgenJ a).mp ha).1,
        IsInSpanOnAt.trans (S := (·=g)) (fun b hb => hb ▸ ((hgenI g).mp hgI).2) ((hgenJ a).mp ha).2⟩
  exact ⟨g,hgJ,frequent_nonzero_of_not_vanishing hg hnot⟩

/-- ONLY original inputs construct true remaining-member nonzero on EACH
actual reduced trace at EVERY FIRST-good point; no distinctness cert supplied. -/
theorem original_first_good_other_member_nonzero (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (i j : Fin E.length) (hij : i ≠ j) {x : Y}
    (hx : x ∈ actualChronologicalTrace W E i T) (hxZ : x ∉ chronologicalDistinctDefect W E T) :
    IsNonzeroAlongAt (actualChronologicalTrace W E i T)
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal x := by
  let N := (geoTransformAlong (geometricTemplate W []) T).N
  let F := fun a : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hN := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hT).isClosedSubmanifold_N
  have hFam : ∀ a : Fin E.length,(F a).IsCoherent ∧ (∀ y ∈ N,IsNonzeroAlongAt N (F a) y) ∧
      ∀ y ∈ N,∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,(F a).mem y g ↔
        HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g := by
    intro a
    obtain ⟨hNa,_hEa,_hma,hwa,hnza,hpra⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense a T hT
    rw [hNa] at hnza hpra
    exact ⟨hwa.isCoherent,hnza,hpra⟩
  have hpi := (actual_proper_iff_zeroLocus (fun a => (hFam a).1) i x).mpr hx.2
  obtain ⟨hOrder,hInj⟩ := original_first_good_factor_rigidity hn hW hE hdense T hT hx.1 hxZ
  by_cases hpj : j ∈ actualProperPositions F x
  · have hDistinct : ¬∀ a,(F i).mem x a ↔ (F j).mem x a := by
      intro heq
      exact hij (hInj hpi hpj (Quotient.sound heq))
    obtain ⟨f,hf,hgenI⟩ := (hFam i).2.2 x hx.1
    obtain ⟨g,hg,hgenJ⟩ := (hFam j).2.2 x hx.1
    exact actual_orderOne_distinct_trace_nonzero hN (hFam i).1 (hFam j).1
      (hFam i).2.1 (hFam j).2.1 hx.1 f hf hgenI g hg hgenJ (hOrder i hpi) (hOrder j hpj) hDistinct
  · have h1 : (F j).mem x (1 : Y → ℂ) := by
      by_contra hh
      exact hpj (by simpa only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and] using hh)
    refine ⟨1,h1,frequent_nonzero_of_not_vanishing (holomorphicAt_const 1) ?_⟩
    intro hv
    exact one_ne_zero (hv.2.self_of_nhds hx)

/-- Genuine coherence converts the constructed nonzero restricted member to
actual OTHER-zero-locus avoidance in EVERY neighborhood of the same trace point. -/
theorem original_first_good_trace_not_contained_in_other_zero (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (i j : Fin E.length) (hij : i ≠ j) {x : Y}
    (hx : x ∈ actualChronologicalTrace W E i T) (hxZ : x ∉ chronologicalDistinctDefect W E T) :
    ∃ᶠ y in 𝓝 x,y ∈ actualChronologicalTrace W E i T ∧
      y ∉ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus := by
  obtain ⟨g,hg,hfreq⟩ := original_first_good_other_member_nonzero hn hW hE hdense T hT i j hij hx hxZ
  obtain ⟨_hN,_hE,_hm,hw,_hnz,_hpr⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense j T hT
  exact (hfreq.and_eventually (HadamardBridge.eventually_mem_of_isCoherent hw.isCoherent hg)).mono
    (fun y hy => ⟨hy.1.1,fun hzero => hy.1.2 (hzero g hy.2)⟩)

end
end Hironaka.HironakaSharpActualFirstGoodTraceRestrictionNonzero
