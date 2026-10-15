/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpNestedNormalCrossingsInheritance

/-! Actual original order-one member trace contact geometry, with true unit
cofactor and SAME literal support regularity. Source-first full mathematics
precedes Lean; whole-Z analyticity and driver/history remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalOrderOneTraceGeometry
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers RelativePrincipalizationSpan
  GermIdealOrder DerivativeIdealAlong GiraudAlong TangentDirectionAlong
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalMemberProductDomain MonomialPartAlong MemberPullback MonomialCase
  BlowupFlatCoordinates OrderTaylor
variable {n : ℕ} {X : CMfd.{u} n}

/-- Individual real restricted jets, not an assumed derivative-order dictionary. -/
theorem vanishesToOrderOn_fieldDeriv {W : Set X} {x : X} {f : X → ℂ}
    (hf : HolomorphicAt n f x) {e : ComplexChart n X} {ξ : Fin n → X → ℂ}
    (hξ : IsTangentField W e ξ x) {q : ℕ} (hvan : VanishesToOrderOn n W x (q+1) f) :
    VanishesToOrderOn n W x q (fieldDeriv e ξ f) := by
  obtain ⟨h,hh,hfh⟩ := hvan
  have hhhol : HolomorphicAt n h x := holomorphicAt_of_mem_idealPow hh
  have hd : (vanishingIdeal (n := n) W).mem x (fun y => f y-h y) :=
    ⟨holomorphicAt_sub hf hhhol,hfh.mono fun y hy hyW => by simp only [hy hyW,sub_self]⟩
  have hξd := hξ.preserves _ hd
  refine ⟨fieldDeriv e ξ h,?_,?_⟩
  · exact mem_idealPow_sum Finset.univ fun i _ => mul_mem_idealPow (hξ.holomorphicAt i)
      (DerivativeIdeal.chartDeriv_mem_idealPow hξ.mem_source q h hh)
  · have hsplit := fieldDeriv_add_eventuallyEq (ξ := ξ) hξ.mem_source (holomorphicAt_sub hf hhhol) hhhol
    have heq : (fun y => (f y-h y)+h y)=f := funext fun y => sub_add_cancel _ _
    rw [heq] at hsplit
    filter_upwards [hsplit,hξd.2] with y hy hy0 hyW
    rw [hy,hy0 hyW,zero_add]

/-- Actual multiplicity-one contact geometry independently rules out true restricted order two. -/
theorem not_vanishesToOrderOn_two_of_tangent_contact {W : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong W I 1 U u)
    {x : X} (hxU : x ∈ U) (hxW : x ∈ W) (hux : u x=0) :
    ¬VanishesToOrderOn n W x 2 u := by
  intro htwo
  have huhol := holomorphicAt_of_mem_iterDerivIdealAlong
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) (1-1) x u (hu.mem x hxU)
  obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one x hxU hux
  obtain ⟨h,hh,hdu⟩ := vanishesToOrderOn_fieldDeriv huhol hξ htwo
  exact hne ((hdu.self_of_nhds hxW).trans (apply_eq_zero_of_mem_idealPow_pointIdeal le_rfl hh))

/-- ONLY genuine original order-one member data construct actual contact, true
unit cofactor, SAME support germ and real relative hypersurface regularity. -/
theorem exists_actual_original_orderOne_trace_contact (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hxW : x ∈ W) (i : Fin E.length)
    (hord : ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x=1) :
    ∃ (U : Set X) (u c f : X → ℂ),x ∈ U ∧
      IsTangentDirectionAlong W (vanishingIdeal (n := n) (E.get i)) 1 U u ∧
      HolomorphicAt n f x ∧ (∀ g,(vanishingIdeal (n := n) (E.get i)).mem x g ↔ IsInSpanAt (n := n) (·=f) x g) ∧
      HolomorphicAt n c x ∧ c x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x,y ∈ W → u y=c y*f y) ∧
      (∀ᶠ y in 𝓝 x,y ∈ W ∩ E.get i ↔ y ∈ W ∩ {y | u y=0} ∩ U) := by
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  have hne : ∀ y ∈ W,DivisorExponentAlong.IsNonzeroAlongAt W (vanishingIdeal (n := n) (E.get i)) y :=
    fun _ hy => originalMemberIdeal_isNonzeroAlongAt hE hdense (List.get_mem E i) hy
  have hxH : x ∈ E.get i := (one_le_originalMemberTraceOrder_iff hn hW hE hdense hxW i).mp (by rw [hord])
  have hxcos : x ∈ cosupport n W (vanishingIdeal (n := n) (E.get i)) 1 :=
    (ordinaryTraceOrder_cosupport_iff hW hI hne hxW 1).mpr (by rw [hord])
  have hnGE : ¬OrderGE n W (vanishingIdeal (n := n) (E.get i)) x 2 := by
    intro hh
    have hc := (ordinaryTraceOrder_cosupport_iff hW hI hne hxW 2).mp ⟨hxW,hh⟩
    rw [hord] at hc
    omega
  obtain ⟨U,u,hxU,hu⟩ := exists_isTangentDirectionAlong hI hW (show 1 ≤ 1 from le_rfl) hxcos hnGE
  obtain ⟨Φ,σ,_hsrc,_h0,_hinj,hA⟩ := exists_snc_chart hn hE x
  let f := flatCoord Φ (σ i)
  have hxD := mem_flatDomain_self Φ
  have hf : HolomorphicAt n f x := holomorphicAt_flatCoord Φ (σ i) hxD
  have hgen : ∀ g,(vanishingIdeal (n := n) (E.get i)).mem x g ↔ IsInSpanAt (n := n) (·=f) x g :=
    vanishingIdeal_mem_iff_flatCoord Φ (hA i hxH) hxD
  have hfx : f x=0 := (hA i hxH hxD.1 hxD.2).mp hxH
  have hru : (vanishingIdeal (n := n) (E.get i)).mem x u := hu.mem x hxU
  obtain ⟨_huhol,c,hc,hcuAmbient⟩ := isInSpanAt_eq_iff.mp ((hgen u).mp hru)
  have hcu : ∀ᶠ y in 𝓝 x,y ∈ W → u y=c y*f y := hcuAmbient.mono fun _ hh _ => hh
  have hux : u x=0 := by rw [hcu.self_of_nhds hxW,hfx,mul_zero]
  have hcx : c x ≠ 0 := CodimOneCentreAlong.apply_ne_zero_of_not_vanishesToOrderOn_on hxW hf hfx hc
    (d := 1) (by simpa only [pow_one] using hcu) (not_vanishesToOrderOn_two_of_tangent_contact hI hu hxU hxW hux)
  have hcg : ∀ᶠ y in 𝓝 x,c y ≠ 0 := hc.self_of_nhds.continuousAt.eventually (isOpen_ne.mem_nhds hcx)
  have hsupport : ∀ᶠ y in 𝓝 x,y ∈ W ∩ E.get i ↔ y ∈ W ∩ {y | u y=0} ∩ U := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD,hu.isOpen.mem_nhds hxU,hcu,hcg]
      with y hyD hyU hyEq hyc
    constructor
    · rintro ⟨hyW,hyH⟩
      refine ⟨⟨hyW,?_⟩,hyU⟩
      change u y=0
      rw [hyEq hyW]
      have hf0 : f y=0 := (hA i hxH hyD.1 hyD.2).mp hyH
      rw [hf0,mul_zero]
    · rintro ⟨⟨hyW,hyu⟩,_⟩
      refine ⟨hyW,(hA i hxH hyD.1 hyD.2).mpr ?_⟩
      change u y=0 at hyu
      rw [hyEq hyW] at hyu
      exact (mul_eq_zero.mp hyu).resolve_left hyc
  exact ⟨U,u,c,f,hxU,hu,hf,hgen,hc,hcx,hcu,hsupport⟩

/-- The SAME literal original order-one trace support is genuinely regular of relative codimension one. -/
theorem original_orderOne_member_trace_regularAt (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hxW : x ∈ W) (i : Fin E.length)
    (hord : ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x=1) :
    ∃ k,RegularAtDim (n := n) W x k ∧ RegularAtDim (n := n) (W ∩ E.get i) x (k-1) := by
  obtain ⟨U,u,c,f,hxU,hu,hf,_hgen,_hc,_hcx,hcu,hsupport⟩ :=
    exists_actual_original_orderOne_trace_contact hn hW hE hdense hxW i hord
  have hxH : x ∈ E.get i := (one_le_originalMemberTraceOrder_iff hn hW hE hdense hxW i).mp (by rw [hord])
  have hux : u x=0 := ((hsupport.self_of_nhds).mp ⟨hxW,hxH⟩).1.2
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  obtain ⟨k,hWk,hcontact⟩ := hu.regularAtDim_contact
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hW ⟨⟨hxW,hux⟩,hxU⟩
  exact ⟨k,hWk,CodimOneSupport.regularAtDim_of_eventually_mem_iff
    (hsupport.mono fun _ h => h.symm) hcontact⟩

end
end Hironaka.HironakaSharpOriginalOrderOneTraceGeometry
