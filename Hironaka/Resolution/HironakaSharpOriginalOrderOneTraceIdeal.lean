/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalOrderOneTraceGeometry

/-! Genuine BOTH-direction reduced ideal dictionary for SAME original order-one
member traces. Actual principal contact and true Hadamard geometry precede it;
no desired reduced-ideal or shared-branch dictionary is supplied. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalOrderOneTraceIdeal
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  RelativePrincipalizationSpan RestrictedIdealExtension GermIdealOrder
  HironakaSharpOriginalOrderOneTraceGeometry HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalDistinctDefectPhase TangentDirectionAlong DerivativeIdealAlong GiraudAlong
  MonomialPartAlong InvertibleIdealQuotient BlowupFlatCoordinates BlowupTowers
variable {n : ℕ} {X : CMfd.{u} n}

/-- ONLY original data internally construct true whole ideal generation by the SAME actual contact function. -/
theorem exists_actual_original_orderOne_principal_contact (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hxW : x ∈ W) (i : Fin E.length)
    (hord : ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x=1) :
    ∃ (U : Set X) (u : X → ℂ),x ∈ U ∧ IsTangentDirectionAlong W (vanishingIdeal (n := n) (E.get i)) 1 U u ∧
      (∀ g,(vanishingIdeal (n := n) (E.get i)).mem x g ↔ IsInSpanAt (n := n) (·=u) x g) ∧
      (∀ᶠ y in 𝓝 x,y ∈ W ∩ E.get i ↔ y ∈ W ∩ {y | u y=0} ∩ U) := by
  obtain ⟨U,u,_c,f,hxU,hu,hf,hgen,_hc,_hcx,_hcu,hsupport⟩ :=
    exists_actual_original_orderOne_trace_contact hn hW hE hdense hxW i hord
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  have hru : (vanishingIdeal (n := n) (E.get i)).mem x u := hu.mem x hxU
  obtain ⟨huhol,c,hc,hcu⟩ := isInSpanAt_eq_iff.mp ((hgen u).mp hru)
  have hxH : x ∈ E.get i := (one_le_originalMemberTraceOrder_iff hn hW hE hdense hxW i).mp (by rw [hord])
  have hfmem : (vanishingIdeal (n := n) (E.get i)).mem x f := (hgen f).mpr
    (isInSpanAt_eq_iff.mpr ⟨hf,1,holomorphicAt_const 1,Eventually.of_forall fun _ => (one_mul _).symm⟩)
  have hfx : f x=0 := hfmem.2.self_of_nhds hxH
  have hux : u x=0 := hru.2.self_of_nhds hxH
  have hcx : c x ≠ 0 := CodimOneCentreAlong.apply_ne_zero_of_not_vanishesToOrderOn_on hxW hf hfx hc (d := 1)
    (by simpa only [pow_one] using hcu.mono (fun y h (_hyW : y ∈ W) => h))
    (not_vanishesToOrderOn_two_of_tangent_contact hI hu hxU hxW hux)
  have hFu : IsInSpanAt (n := n) (·=u) x f := by
    refine isInSpanAt_eq_iff.mpr ⟨hf,fun y => (c y)⁻¹,holomorphicAt_inv hc hcx,?_⟩
    filter_upwards [hcu,hc.self_of_nhds.continuousAt.eventually (isOpen_ne.mem_nhds hcx)] with y hy hyc
    rw [hy,inv_mul_cancel_left₀ hyc]
  refine ⟨U,u,hxU,hu,?_,hsupport⟩
  intro g
  constructor
  · intro hg
    exact IsInSpanAt.trans (fun a ha => by subst a; exact hFu) ((hgen g).mp hg)
  · intro hg
    exact HomogenizedIdeal.mem_of_isInSpanAt hI (IsInSpanAt.mono (S := (·=u))
      (T := fun a => (vanishingIdeal (n := n) (E.get i)).mem x a) (fun a ha => ha ▸ hru) hg)

/-- True contact Hadamard generators reduce to the SAME actual restricted ideal. -/
theorem contact_vanishingIdeal_mem_iff_restrictOn {W : Set X} {I : GermIdeal n X}
    (hW : IsClosedSubmanifold n W) (hI : I.IsCoherent) {U : Set X} {u : X → ℂ}
    (hu : IsTangentDirectionAlong W I 1 U u) {x : X} (hxU : x ∈ U) (hxW : x ∈ W) (hux : u x=0)
    (hgen : ∀ g,I.mem x g ↔ IsInSpanAt (n := n) (·=u) x g) (g : X → ℂ) :
    (vanishingIdeal (n := n) (W ∩ {y | u y=0} ∩ U)).mem x g ↔ (restrictOn n W I).mem x g := by
  have huhol : ∀ y ∈ U,HolomorphicAt n u y :=
    fun y hy => GermIdeal.IsCoherent.holomorphicAt_mem hI (hu.mem y hy)
  have hru : I.mem x u := hu.mem x hxU
  obtain ⟨k,hkn,_hxW,Φ,hΦsrc,_h0,hflat⟩ := hW.2 x hxW
  obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one x hxU hux
  obtain ⟨V,_hV,hxV,_hVU,hContact⟩ := exists_vanishingIdeal_inter_zeroSet_mem_iff hΦsrc hflat hkn
    hu.isOpen huhol hxU hxW hux hξ hne
  constructor
  · intro hg
    have hspan := (hContact x hxV g).mp hg
    refine ⟨hg.1,IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict hspan)⟩
    rintro a (rfl | ⟨j,hj,rfl⟩)
    · exact IsInSpanAt.restrict (isInSpanAt_self hru (huhol x hxU))
    · have hxD := mem_flatDomain_self Φ
      have hz : IsInSpanOnAt (n := n) W (·=u) x (flatCoord Φ j) := by
        refine isInSpanOnAt_eq_iff.mpr ⟨fun _ => 0,holomorphicAt_const 0,?_⟩
        filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD] with y hy hyW
        simp only [zero_mul]
        exact ((hflat hy.1 hy.2).mp hyW) j hj
      exact IsInSpanOnAt.mono (S := (·=u)) (T := I.mem x) (fun a ha => ha ▸ hru) hz
  · intro hg
    have hspan : IsInSpanOnAt (n := n) W (·=u) x g :=
      IsInSpanOnAt.trans (fun a ha => IsInSpanAt.restrict ((hgen a).mp ha)) hg.2
    obtain ⟨c,_hc,hcu⟩ := isInSpanOnAt_eq_iff.mp hspan
    refine ⟨hg.1,?_⟩
    filter_upwards [hcu] with y hy hyS
    rw [hy hyS.1.1,hyS.1.2,mul_zero]

/-- BOTH entire original germ directions of the SAME actual reduced trace ideal. -/
theorem original_orderOne_restrictOn_mem_iff_vanishingIdeal_trace (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hxW : x ∈ W) (i : Fin E.length)
    (hord : ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x=1) (g : X → ℂ) :
    (restrictOn n W (vanishingIdeal (n := n) (E.get i))).mem x g ↔
      (vanishingIdeal (n := n) (W ∩ E.get i)).mem x g := by
  obtain ⟨U,u,hxU,hu,hgen,hsupport⟩ := exists_actual_original_orderOne_principal_contact hn hW hE hdense hxW i hord
  have hxH : x ∈ E.get i := (one_le_originalMemberTraceOrder_iff hn hW hE hdense hxW i).mp (by rw [hord])
  have hux : u x=0 := ((hsupport.self_of_nhds).mp ⟨hxW,hxH⟩).1.2
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  rw [← contact_vanishingIdeal_mem_iff_restrictOn hW hI hu hxU hxW hux hgen g]
  constructor
  · rintro ⟨hg,hg0⟩
    refine ⟨hg,?_⟩
    filter_upwards [hg0,hsupport] with y hy hyS hyA
    exact hy ((hyS).mp hyA)
  · rintro ⟨hg,hg0⟩
    refine ⟨hg,?_⟩
    filter_upwards [hg0,hsupport] with y hy hyS hyA
    exact hy ((hyS).mpr hyA)

end
end Hironaka.HironakaSharpOriginalOrderOneTraceIdeal
