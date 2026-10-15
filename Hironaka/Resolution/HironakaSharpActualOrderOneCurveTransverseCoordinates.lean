/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalOrderOneTraceGeometry

/-! Actual ordinary order-one contact yields AMBIENT unit contact and genuine
common curve/member coordinates, without a transversality certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualOrderOneCurveTransverseCoordinates
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpOriginalOrderOneTraceGeometry HironakaSharpOriginalProductTraceOrder
  RelativePrincipalizationSpan GermIdealOrder TangentDirectionAlong NormalCrossings
  BlowupFlatCoordinates MonomialPart MonomialPartAlong InvertibleIdealQuotient
  OrderTaylor DivisorExponentAlong MonomialCase BlowupSNCTransform MemberPullback GiraudAlong
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual ambient ideal membership supplies a TRUE ambient cofactor; the
real tangent derivative internally forces that cofactor to be a unit. -/
theorem exists_actual_order_one_member_ambient_unit_contact (hn : 0<n)
    {N H : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) {x : X} (hxN : x ∈ N) (hxH : x ∈ H)
    (hOrd : ordinaryTraceOrder N (vanishingIdeal (n := n) H) x=1) :
    ∃ (U : Set X) (u f c : X → ℂ),x ∈ U ∧
      IsTangentDirectionAlong N (vanishingIdeal (n := n) H) 1 U u ∧ u x=0 ∧
      HolomorphicAt n f x ∧ (∀ g,(vanishingIdeal (n := n) H).mem x g ↔ IsInSpanAt (n := n) (·=f) x g) ∧
      HolomorphicAt n c x ∧ c x ≠ 0 ∧ (∀ᶠ y in 𝓝 x,u y=c y*f y) ∧
      (∀ᶠ y in 𝓝 x,y ∈ H ↔ u y=0) := by
  have hdense' : N ⊆ closure (N \ ⋃ A ∈ [H],A) := by simpa using hdense
  obtain ⟨U,u,_c,_f,hxU,hu,_hf,_hgen,_hc,_hcx,_hcu,_hSupp⟩ :=
    exists_actual_original_orderOne_trace_contact hn hN hH hdense' hxN (0 : Fin [H].length) hOrd
  obtain ⟨Φ,σ,_hsrc,_h0,_hinj,hA⟩ := exists_snc_chart hn hH x
  let i : Fin [H].length := 0
  let f := flatCoord Φ (σ i)
  have hxD := mem_flatDomain_self Φ
  have hf : HolomorphicAt n f x := holomorphicAt_flatCoord Φ (σ i) hxD
  have hFlat : ∀ {y : X},y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source → (y ∈ H ↔ f y=0) := hA i hxH
  have hGen : ∀ g,(vanishingIdeal (n := n) H).mem x g ↔ IsInSpanAt (n := n) (·=f) x g :=
    vanishingIdeal_mem_iff_flatCoord Φ hFlat hxD
  have hfx : f x=0 := (hFlat hxD.1 hxD.2).mp hxH
  have hru : (vanishingIdeal (n := n) H).mem x u := hu.mem x hxU
  have hux : u x=0 := hru.2.self_of_nhds hxH
  obtain ⟨_huhol,c,hc,hcu⟩ := isInSpanAt_eq_iff.mp ((hGen u).mp hru)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hH i)
  have hcuOn : ∀ᶠ y in 𝓝 x,y ∈ N → u y=c y*f y := hcu.mono (fun y hy (_hyN : y ∈ N) => hy)
  have hcx : c x ≠ 0 := CodimOneCentreAlong.apply_ne_zero_of_not_vanishesToOrderOn_on hxN hf hfx hc
    (d := 1) (by simpa only [pow_one] using hcuOn)
    (not_vanishesToOrderOn_two_of_tangent_contact hcH hu hxU hxN hux)
  have hSupport : ∀ᶠ y in 𝓝 x,y ∈ H ↔ u y=0 := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD,hcu,hc.self_of_nhds.continuousAt.eventually_ne hcx]
      with y hyD hyEq hyc
    rw [hyEq,mul_eq_zero,or_iff_right hyc]
    exact hFlat hyD.1 hyD.2
  exact ⟨U,u,f,c,hxU,hu,hux,hf,hGen,hc,hcx,hcu,hSupport⟩


/-- Actual holomorphic contact-coordinate inverse gives BOTH entire N/H
memberships in the SAME chart, with genuinely disjoint normal/member indices. -/
theorem actual_order_one_curve_member_simultaneous_coordinates (hn : 0<n)
    {N H : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) {x : X} (hxN : x ∈ N) (hxH : x ∈ H)
    (hrN : RegularAtDim (n := n) N x 1)
    (hOrd : ordinaryTraceOrder N (vanishingIdeal (n := n) H) x=1) :
    ∃ (S₀ : Finset (Fin n)) (S : Fin [H].length → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun t : Option (Fin [H].length) => t.elim N (fun i => [H].get i))
        (fun t => t.elim S₀ S) x ∧
      ∀ i,x ∈ [H].get i → (S i).card=1 ∧ Disjoint (S i) S₀ := by
  obtain ⟨U,u,_f,_c,hxU,hu,hux,_hf,_hgen,_hc,_hcx,_hcu,hSupp⟩ :=
    exists_actual_order_one_member_ambient_unit_contact hn hN hH hdense hxN hxH hOrd
  obtain ⟨_h1n,_hx,Φ,hΦsrc,hΦ0,hflat⟩ := hrN
  change LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x) at Φ
  change Φ.source ⊆ (chartAt (ComplexModel n) x).target at hΦsrc
  change Φ.toFun (chartAt (ComplexModel n) x x)=0 at hΦ0
  change ∀ {y : X},y ∈ (chartAt (ComplexModel n) x).source →
    chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n 1) at hflat
  let o : Fin n := ⟨0,hn⟩
  have huhol : ∀ y ∈ U,HolomorphicAt n u y := fun y hy =>
    (show (vanishingIdeal (n := n) H).mem y u from hu.mem y hy).1
  obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one x hxU hux
  obtain ⟨j,hj,hjne⟩ := exists_flatPartial_ne_zero hΦsrc hflat (mem_flatDomain_self Φ) hxN (huhol x hxU) hξ hne
  have hjo : j=o := Fin.ext (by dsimp only [o];omega)
  rw [hjo] at hjne
  obtain ⟨G,hGsub,hGo,hxG⟩ := mem_nhds_iff.mp hSupp
  let O := (U ∩ flatDomain Φ) ∩ G
  have hO : IsOpen O := (hu.isOpen.inter (isOpen_flatDomain Φ)).inter hGo
  have hxO : x ∈ O := ⟨⟨hxU,mem_flatDomain_self Φ⟩,hxG⟩
  have hWs : ∀ y ∈ O,ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (contactCoords Φ o o u) y := by
    intro y hy
    exact contMDiffAt_of_eventually_mdifferentiableAt (eventually_of_mem (hO.mem_nhds hy) fun z hz =>
      mdifferentiableAt_contactCoords o o hz.1.2 (huhol z hz.1.1))
  have hWx : contactCoords Φ o o u x=0 := by
    ext r
    change contactCoords Φ o o u x r=0
    rw [contactCoords_apply]
    split_ifs
    · exact hux
    · simpa [flatMap] using congrArg (fun v : ComplexModel n => v r) hΦ0
  obtain ⟨Θ,hΘsrc,hΘ0,hΘ⟩ := exists_recentred_coords hO hWs hxO
    (injective_fderiv_contactCoords (l := o) hΦsrc (huhol x hxU) hjne)
  let S₀ : Finset (Fin n) := Finset.univ.filter fun r => 1≤r.val
  let S : Fin [H].length → Finset (Fin n) := fun _ => {o}
  refine ⟨S₀,S,⟨Θ,hΘsrc,hΘ0,?_⟩,?_⟩
  · rintro (_ | i) _hxi y hy hyΘ
    · obtain ⟨hyO,hΘy⟩ := hΘ hy hyΘ
      rw [hWx,sub_zero] at hΘy
      change Θ.toFun (chartAt (ComplexModel n) x y)=contactCoords Φ o o u y at hΘy
      change y ∈ N ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace S₀
      rw [hΘy]
      change y ∈ N ↔ contactCoords Φ o o u y ∈ coordSubspace (Finset.univ.filter fun r : Fin n => 1≤r.val)
      rw [coordSubspace_eq_complexCoordinatePlane]
      constructor
      · intro hyN r hr
        rw [contactCoords_apply,if_neg (by intro he;subst r;exact Nat.not_succ_le_zero _ hr),Equiv.swap_self,Equiv.refl_apply]
        exact ((hflat hyO.1.2.1 hyO.1.2.2).mp hyN) r hr
      · intro h
        apply (hflat hyO.1.2.1 hyO.1.2.2).mpr
        intro r hr
        have hh := h r hr
        rw [contactCoords_apply,if_neg (by intro he;subst r;exact Nat.not_succ_le_zero _ hr),Equiv.swap_self,Equiv.refl_apply] at hh
        exact hh
    · obtain ⟨hyO,hΘy⟩ := hΘ hy hyΘ
      rw [hWx,sub_zero] at hΘy
      change Θ.toFun (chartAt (ComplexModel n) x y)=contactCoords Φ o o u y at hΘy
      change y ∈ [H].get i ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace {o}
      rw [hΘy]
      have hi0 : i=(0 : Fin [H].length) := Fin.eq_zero i
      subst i
      rw [show [H].get (0 : Fin [H].length)=H from rfl]
      change y ∈ H ↔ ∀ r ∈ ({o} : Finset (Fin n)),contactCoords Φ o o u y r=0
      simp only [Finset.mem_singleton,forall_eq]
      rw [contactCoords_apply,if_pos rfl]
      exact hGsub hyO.2
  · intro i _hi
    refine ⟨Finset.card_singleton o,Finset.disjoint_left.mpr ?_⟩
    intro r hro hrN
    have he : r=o := Finset.mem_singleton.mp hro
    subst r
    have hh := (Finset.mem_filter.mp hrN).2
    exact Nat.not_succ_le_zero _ hh

/-- True pointwise ordinary-order data internally construct the EXISTING
whole singleton transversality predicate, including absent-member points. -/
theorem actual_curve_singleton_transverse_of_order_one (hn : 0<n)
    {N H : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H))
    (hr : ∀ x ∈ N,RegularAtDim (n := n) N x 1)
    (hOrd : ∀ x ∈ N,x ∈ H → ordinaryTraceOrder N (vanishingIdeal (n := n) H) x=1) :
    IsTransverse n N [H] := by
  intro x hx
  by_cases hxH : x ∈ H
  · exact actual_order_one_curve_member_simultaneous_coordinates hn hN hH hdense hx hxH (hr x hx) (hOrd x hx hxH)
  · refine ⟨Finset.univ.filter (fun r : Fin n => 1≤r.val),fun _ => ∅,
      isCoordinateFamilyAt_of_regularAtDim (hr x hx) [H] (fun _ => ∅) ?_,?_⟩
    · intro i hi
      exact hxH (by simpa using hi)
    · intro i hi
      exact (hxH (by simpa using hi)).elim

end
end Hironaka.HironakaSharpActualOrderOneCurveTransverseCoordinates
