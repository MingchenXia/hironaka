/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.HolGermMulExact
import Hironaka.Resolution.HironakaSharpOriginalFirstMemberResidualPrincipal
import Hironaka.Analytic.HolomorphicCoordinatePrime

/-! Actual coordinate/member/relative member prime cancellation from genuine
Hadamard division, coordinate primeness and real member-preserving retractions.
No desired-prime/domain certificate is supplied. Complete source-first math
precedes this producer; arbitrary-power strict saturation/history remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualRelativeMemberPrime
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpOriginalFirstMemberExceptionalFactor HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain MarkedIdeals MarkedIdeals.MarkedIdeal
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong DivisorExponentAlong
  NormalCrossings MemberTraceIdealAlong MemberPullback BlowupFlatCoordinates HolomorphicGermReducednessBridge
variable {n : ℕ} {X : CMfd.{u} n}

private def identityFlatten (p : ComplexModel n) : LocalHolomorphicEquivAt (n := n) p where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ p
  toFun := id
  invFun := id
  toFun_holomorphic := differentiable_id.differentiableOn
  invFun_holomorphic := differentiable_id.differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

private theorem coordinate_vanishing_iff_span (j : Fin n) (f : ComplexModel n → ℂ) :
    (vanishingIdeal (n := n) {z : ComplexModel n | z j=0}).mem 0 f ↔
      IsInSpanAt (n := n) (·=fun z : ComplexModel n => z j) 0 f := by
  let Φ := identityFlatten (chartAt (ComplexModel n) (0 : ComplexModel n) 0)
  have hd : (0 : ComplexModel n) ∈ flatDomain Φ := mem_flatDomain_self Φ
  have h := vanishingIdeal_mem_iff_flatCoord Φ (t := j) (A := {z : ComplexModel n | z j=0})
    (fun _ _ => by simp [Φ,identityFlatten,chartAt_self_eq]) hd f
  have hcoord : BlowupFlatCoordinates.flatCoord Φ j = (fun z : ComplexModel n => z j) := by
    funext z
    change (chartAt (ComplexModel n) (0 : ComplexModel n) z) j=z j
    rw [chartAt_self_eq]
    rfl
  rw [hcoord] at h
  exact h

private theorem coordinate_dvd_iff_span (j : Fin n) (f : ComplexModel n → ℂ)
    (hf : HolomorphicAt n f 0) :
    HolGerm.mk (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j) ∣
      HolGerm.mk f (hf.mono fun _ h => h.differentiableAt) ↔
      IsInSpanAt (n := n) (·=fun z : ComplexModel n => z j) 0 f := by
  have he := eventually_differentiableAt_coordinate j
  constructor
  · rintro ⟨B,hB⟩
    obtain ⟨b,hb,hrep⟩ := HolGerm.exists_eq_mk B
    refine isInSpanAt_eq_iff.mpr ⟨hf,b,hb.mono fun _ h => h.mdifferentiableAt,?_⟩
    apply HolGerm.mk_eq_mk_iff.mp
    rw [HolGerm.mk_mul b (fun z : ComplexModel n => z j) hb he,← hrep,mul_comm]
    exact hB
  · intro hspan
    obtain ⟨_hf,b,hb,hfb⟩ := isInSpanAt_eq_iff.mp hspan
    refine ⟨HolGerm.mk b (hb.mono fun _ h => h.differentiableAt),?_⟩
    have heq : HolGerm.mk f (hf.mono fun _ h => h.differentiableAt) =
        HolGerm.mk (fun y => b y*y j)
          (eventually_differentiableAt_mul (hb.mono fun _ h => h.differentiableAt) he) :=
      HolGerm.mk_eq_mk_iff.mpr hfb
    rw [HolGerm.mk_mul b (fun z : ComplexModel n => z j)
      (hb.mono fun _ h => h.differentiableAt) he] at heq
    exact heq.trans (mul_comm _ _)

/-- Genuine coordinate Hadamard plus PROVED coordinate primeness gives actual factor vanishing. -/
theorem coordinate_vanishing_product_prime (j : Fin n) (f g : ComplexModel n → ℂ)
    (hf : HolomorphicAt n f 0) (hg : HolomorphicAt n g 0)
    (hfg : (vanishingIdeal (n := n) {z : ComplexModel n | z j=0}).mem 0 (f*g)) :
    (vanishingIdeal (n := n) {z : ComplexModel n | z j=0}).mem 0 f ∨
      (vanishingIdeal (n := n) {z : ComplexModel n | z j=0}).mem 0 g := by
  have hdiv := (coordinate_dvd_iff_span j (f*g) (hf.mul hg)).mpr ((coordinate_vanishing_iff_span j (f*g)).mp hfg)
  rw [HolGerm.mk_mul' f g (hf.mono fun _ h => h.differentiableAt) (hg.mono fun _ h => h.differentiableAt)] at hdiv
  rcases (HolomorphicCoordinatePrime.prime_coordinate_germ j).dvd_or_dvd hdiv with h | h
  · exact Or.inl ((coordinate_vanishing_iff_span j f).mpr ((coordinate_dvd_iff_span j f hf).mp h))
  · exact Or.inr ((coordinate_vanishing_iff_span j g).mpr ((coordinate_dvd_iff_span j g hg).mp h))

private theorem holomorphicAt_flatInverse_iff {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (f : X → ℂ) :
    HolomorphicAt n (fun z => f ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
      (Φ.toFun (chartAt (ComplexModel n) x x)) ↔ HolomorphicAt n f x := by
  have hxD := mem_flatDomain_self Φ
  constructor
  · intro hf
    have h := holomorphicAt_comp_flat Φ hxD (hf.mono fun _ hz => hz.differentiableAt)
    refine h.congr ?_
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD] with z hz
    exact congrArg f (flatInverse_flat Φ hz)
  · intro hf
    have hT := tendsto_flatInverse Φ hxD
    filter_upwards [Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun hxD.2),hT.eventually hf.eventually] with z hz hfz
    have hm := hfz.mdifferentiableAt.comp (Φ.invFun z) (mdifferentiableAt_chart_symm (hsrc (Φ.mapsTo_invFun hz)))
    exact ((mdifferentiableAt_iff_differentiableAt.mp hm).comp z
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz))).mdifferentiableAt

private theorem member_vanishing_flatInverse_iff {x : X} {H : Set X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) (j : Fin n)
    (hflat : ∀ {y : X},y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ H ↔ Φ.toFun (chartAt (ComplexModel n) x y) j=0)) (f : X → ℂ) :
    (vanishingIdeal (n := n) H).mem x f ↔
      (vanishingIdeal (n := n) {z : ComplexModel n | z j=0}).mem 0
        (fun z => f ((chartAt (ComplexModel n) x).symm (Φ.invFun z))) := by
  have hxD := mem_flatDomain_self Φ
  have hhol := holomorphicAt_flatInverse_iff Φ hsrc f
  rw [h0] at hhol
  have hInv : Tendsto (fun z => (chartAt (ComplexModel n) x).symm (Φ.invFun z)) (𝓝 0) (𝓝 x) := by
    simpa only [h0] using tendsto_flatInverse Φ hxD
  have hForward : Tendsto (fun y : X => Φ.toFun (chartAt (ComplexModel n) x y)) (𝓝 x) (𝓝 0) := by
    have ht := ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hxD.2)).continuousAt.comp
      ((chartAt (ComplexModel n) x).continuousAt hxD.1)).tendsto
    change Tendsto (fun y : X => Φ.toFun (chartAt (ComplexModel n) x y)) (𝓝 x)
      (𝓝 (Φ.toFun (chartAt (ComplexModel n) x x))) at ht
    rwa [h0] at ht
  have h0T : (0 : ComplexModel n) ∈ Φ.target := h0 ▸ Φ.mapsTo_toFun hxD.2
  constructor
  · rintro ⟨hf,hvan⟩
    refine ⟨hhol.mpr hf,?_⟩
    filter_upwards [Φ.isOpen_target.mem_nhds h0T,hInv.eventually hvan] with z hz hv hz0
    obtain ⟨hm,heq⟩ := flatInverse_mem Φ hz hsrc
    exact hv ((hflat hm.1 hm.2).mpr (by rw [heq]; exact hz0))
  · rintro ⟨hf,hvan⟩
    refine ⟨hhol.mp hf,?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD,hForward.eventually hvan] with y hy hv hyH
    have hh := hv ((hflat hy.1 hy.2).mp hyH)
    rwa [flatInverse_flat Φ hy] at hh

/-- Actual SAME SNC member vanishing law, from genuine coordinates and BOTH whole germ transport directions. -/
theorem snc_member_vanishing_product_prime (hn : 0 < n) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (i : Fin E.length) (x : X) (f g : X → ℂ)
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hfg : (vanishingIdeal (n := n) (E.get i)).mem x (f*g)) :
    (vanishingIdeal (n := n) (E.get i)).mem x f ∨ (vanishingIdeal (n := n) (E.get i)).mem x g := by
  by_cases hxi : x ∈ E.get i
  · obtain ⟨Φ,σ,hsrc,h0,_hinj,hmem⟩ := MonomialCase.exists_snc_chart hn hE x
    have hflat : ∀ {y : X},y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i)=0) := hmem i hxi
    let F : (X → ℂ) → ComplexModel n → ℂ := fun a z => a ((chartAt (ComplexModel n) x).symm (Φ.invFun z))
    have hprod := (member_vanishing_flatInverse_iff Φ hsrc h0 (σ i) hflat (f*g)).mp hfg
    have hFf : HolomorphicAt n (F f) 0 := by
      rw [← h0]
      exact (holomorphicAt_flatInverse_iff Φ hsrc f).mpr hf
    have hFg : HolomorphicAt n (F g) 0 := by
      rw [← h0]
      exact (holomorphicAt_flatInverse_iff Φ hsrc g).mpr hg
    rcases coordinate_vanishing_product_prime (σ i) (F f) (F g) hFf hFg hprod with h | h
    · exact Or.inl ((member_vanishing_flatInverse_iff Φ hsrc h0 (σ i) hflat f).mpr h)
    · exact Or.inr ((member_vanishing_flatInverse_iff Φ hsrc h0 (σ i) hflat g).mpr h)
  · left
    exact ⟨hf,Filter.Eventually.mono ((hE.1 _ (List.get_mem E i)).isOpen_compl.mem_nhds hxi) (fun _ hy hyH => False.elim (hy hyH))⟩

/-- Real member-preserving retraction constructs the actual relative smooth member prime law. -/
theorem transverse_member_relative_product_prime (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {x : X} (hx : x ∈ N)
    (i : Fin E.length) (f g : X → ℂ) (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hfg : IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x (f*g)) :
    IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x f ∨
      IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x g := by
  by_cases hxi : x ∈ E.get i
  · obtain ⟨r,hr,hpres⟩ := exists_isLocalRetraction_preserving hn hE hT hx
    have htrace := (isInSpanOnAt_vanishingIdeal_iff_mem hE hT hx i (hf.mul hg)).mp hfg
    have hproduct : (vanishingIdeal (n := n) (E.get i)).mem x ((f ∘ r)*(g ∘ r)) := by
      refine ⟨(hr.holomorphicAt_comp hf).mul (hr.holomorphicAt_comp hg),?_⟩
      filter_upwards [hr.tendsto.eventually htrace.2,hr.mem,hpres i hxi] with y hy hyN hyH hyHi
      exact hy ⟨hyN,hyH hyHi⟩
    have hback (a : X → ℂ) (ha : HolomorphicAt n a x)
        (har : (vanishingIdeal (n := n) (E.get i)).mem x (a ∘ r)) :
        IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x a := by
      apply (isInSpanOnAt_vanishingIdeal_iff_mem hE hT hx i ha).mpr
      refine ⟨ha,?_⟩
      filter_upwards [har.2,hr.eq_self] with y hy heq hyTrace
      have hh := hy hyTrace.2
      change a (r y)=0 at hh
      rwa [heq hyTrace.1] at hh
    rcases snc_member_vanishing_product_prime hn hE i x (f ∘ r) (g ∘ r)
      (hr.holomorphicAt_comp hf) (hr.holomorphicAt_comp hg) hproduct with h | h
    · exact Or.inl (hback f hf h)
    · exact Or.inr (hback g hg h)
  · left
    have hmem : (vanishingIdeal (n := n) (E.get i)).mem x f :=
      ⟨hf,Filter.Eventually.mono ((hE.1 _ (List.get_mem E i)).isOpen_compl.mem_nhds hxi) (fun _ hy hyH => False.elim (hy hyH))⟩
    exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hmem hf)

/-- Original-only SAME first blowup internally supplies actual exceptional relative prime laws. -/
theorem exists_actual_original_first_exceptional_relative_prime (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1 ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X),IsBlowupAlong n C π ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.invFamily hn (n+1)).inv
        (originalMemberProductMarked W E 1) (.refl : BlowupTower X X)) (originalDistinctDefectPhase W E) ∧
      ∀ i : Fin E.length,
        let P := memberTotalMarked W (E.get i) C π
        ∀ y ∈ P.N,∀ a : Fin P.E.length,∀ f g : Y → ℂ,
          HolomorphicAt n f y → HolomorphicAt n g y →
          IsInSpanOnAt (n := n) P.N ((vanishingIdeal (n := n) (P.E.get a)).mem y) y (f*g) →
          IsInSpanOnAt (n := n) P.N ((vanishingIdeal (n := n) (P.E.get a)).mem y) y f ∨
            IsInSpanOnAt (n := n) P.N ((vanishingIdeal (n := n) (P.E.get a)).mem y) y g := by
  obtain ⟨C,Y,π,hπ,hCeq,hgeom⟩ := exists_actual_original_first_member_exceptional_factor hn hW hE hd hreg hdense hcompact hne
  refine ⟨C,Y,π,hπ,hCeq,?_⟩
  intro i
  obtain ⟨hw,_⟩ := hgeom i
  exact fun y hy a f g hf hg hfg => transverse_member_relative_product_prime hn hw.isSNCDivisor hw.isTransverse hy a f g hf hg hfg

end
end Hironaka.HironakaSharpActualRelativeMemberPrime
