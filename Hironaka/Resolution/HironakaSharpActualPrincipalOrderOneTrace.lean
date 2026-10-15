/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualChronologicalResidualDictionary

/-! Genuine current coherent relative-principal order-one contact, literal
zero-support germ, BOTH reduced ideal directions and real trace regularity.
No initial ambient SNC hypersurface or desired support model is substituted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualPrincipalOrderOneTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalOrderOneTraceGeometry
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  GermIdealOrder DerivativeIdealAlong GiraudAlong TangentDirectionAlong
  DivisorExponentAlong MonomialPartAlong InvertibleIdealQuotient BlowupFlatCoordinates
  MarkedIdeals MarkedIdeals.MarkedIdeal
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual relative principal order1 constructs a real contact whose unit
cofactor and BOTH whole-relative-ideal directions are proved internally. -/
theorem exists_actual_orderOne_relative_contact {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y)
    {x : X} (hx : x ∈ N) (f : X → ℂ) (hf : HolomorphicAt n f x)
    (hgen : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (hord : ordinaryTraceOrder N I x=1) :
    ∃ (U : Set X) (u : X → ℂ),x ∈ U ∧ IsTangentDirectionAlong N I 1 U u ∧ u x=0 ∧
      I.mem x u ∧ ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=u) x g := by
  have hxcos : x ∈ cosupport n N I 1 := (ordinaryTraceOrder_cosupport_iff hN hI hnz hx 1).mpr (by rw [hord])
  have hnot2 : ¬OrderGE n N I x 2 := by
    intro hh
    have htwo := (ordinaryTraceOrder_cosupport_iff hN hI hnz hx 2).mp ⟨hx,hh⟩
    rw [hord] at htwo
    omega
  obtain ⟨U,u,hxU,hu⟩ := exists_isTangentDirectionAlong hI hN le_rfl hxcos hnot2
  have huI : I.mem x u := hu.mem x hxU
  have huhol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI huI
  have hux : u x=0 := (vanishesToOrderOn_one_iff hx huhol).mp (hxcos.2 u huI)
  have hfI : I.mem x f := (hgen f).mpr
    ⟨hf,isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  have hfx : f x=0 := (vanishesToOrderOn_one_iff hx hf).mp (hxcos.2 f hfI)
  have huF := ((hgen u).mp huI).2
  obtain ⟨c,hc,hcu⟩ := isInSpanOnAt_eq_iff.mp huF
  have hcx : c x ≠ 0 := CodimOneCentreAlong.apply_ne_zero_of_not_vanishesToOrderOn_on hx hf hfx hc (d := 1)
    (by simpa only [pow_one] using hcu) (not_vanishesToOrderOn_two_of_tangent_contact hI hu hxU hx hux)
  have hfU : IsInSpanOnAt (n := n) N (·=u) x f := by
    refine isInSpanOnAt_eq_iff.mpr ⟨fun y => (c y)⁻¹,holomorphicAt_inv hc hcx,?_⟩
    filter_upwards [hcu,hc.continuousAt.eventually_ne hcx] with y hy hyc hyN
    rw [hy hyN,inv_mul_cancel_left₀ hyc]
  refine ⟨U,u,hxU,hu,hux,huI,?_⟩
  intro g
  constructor
  · intro hg
    exact ⟨((hgen g).mp hg).1,IsInSpanOnAt.trans (S := (·=f)) (fun a ha => ha ▸ hfU) ((hgen g).mp hg).2⟩
  · rintro ⟨hg,hspan⟩
    exact (hgen g).mpr ⟨hg,IsInSpanOnAt.trans (S := (·=u)) (fun a ha => ha ▸ huF) hspan⟩

private theorem coherent_zero_support_contact_germ {N : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) {U : Set X} {u : X → ℂ} (hU : IsOpen U) {x : X} (hxU : x ∈ U)
    (huI : I.mem x u)
    (hgen : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=u) x g) :
    ∀ᶠ y in 𝓝 x,y ∈ N ∩ I.zeroLocus ↔ y ∈ N ∩ {y | u y=0} ∩ U := by
  obtain ⟨V,hVo,hxV,K,a,ha,hPres⟩ := hI x
  have hmem : ∀ j : Fin K,I.mem x (a j) := fun j => IdealWeightComparison.mem_of_isPresentation hVo hxV ha hPres j
  choose c _hc heq using fun j => isInSpanOnAt_eq_iff.mp ((hgen (a j)).mp (hmem j)).2
  have hall : ∀ᶠ y in 𝓝 x,∀ j : Fin K,y ∈ N → a j y=c j y*u y := eventually_all.mpr heq
  filter_upwards [hVo.mem_nhds hxV,hU.mem_nhds hxU,HadamardBridge.eventually_mem_of_isCoherent hI huI,hall]
    with y hyV hyU hyu hyEq
  constructor
  · rintro ⟨hyN,hyZ⟩
    exact ⟨⟨hyN,hyZ u hyu⟩,hyU⟩
  · rintro ⟨⟨hyN,hy0⟩,_⟩
    refine ⟨hyN,fun g hg => ?_⟩
    obtain ⟨_hg,L,s,b,hs,_hb,hsum⟩ := (hPres y hyV g).mp hg
    rw [hsum.self_of_nhds]
    apply Finset.sum_eq_zero
    intro j _hj
    obtain ⟨l,hl⟩ := hs j
    rw [← hl,hyEq l hyN,hy0,mul_zero,mul_zero]

private theorem contact_relative_ideal_mem_iff {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) {U : Set X} {u : X → ℂ}
    (hu : IsTangentDirectionAlong N I 1 U u) {x : X} (hxU : x ∈ U) (hx : x ∈ N) (hux : u x=0)
    (hgen : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=u) x g) (g : X → ℂ) :
    (vanishingIdeal (n := n) (N ∩ {y | u y=0} ∩ U)).mem x g ↔ I.mem x g := by
  have huhol := fun y (hy : y ∈ U) => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI (hu.mem y hy)
  have huI : I.mem x u := hu.mem x hxU
  obtain ⟨k,hkn,_hx,Φ,hsrc,_h0,hflat⟩ := hN.2 x hx
  obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one x hxU hux
  obtain ⟨V,_hVo,hxV,_hVU,hContact⟩ := exists_vanishingIdeal_inter_zeroSet_mem_iff hsrc hflat hkn
    hu.isOpen huhol hxU hx hux hξ hne
  constructor
  · intro hg
    apply HomogenizedIdeal.mem_of_isInSpanAt hI
    refine IsInSpanAt.mono (fun a ha => ?_) ((hContact x hxV g).mp hg)
    rcases ha with rfl | ⟨j,hj,rfl⟩
    · exact huI
    · have hxD := mem_flatDomain_self Φ
      have hz : IsInSpanOnAt (n := n) N (·=u) x (flatCoord Φ j) := by
        refine isInSpanOnAt_eq_iff.mpr ⟨0,holomorphicAt_const 0,?_⟩
        filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD] with y hy hyN
        change (Φ.toFun (chartAt (ComplexModel n) x y)) j = (0 : ℂ) * u y
        rw [zero_mul]
        exact ((hflat hy.1 hy.2).mp hyN) j hj
      exact (hgen (flatCoord Φ j)).mpr ⟨holomorphicAt_flatCoord Φ j hxD,hz⟩
  · intro hg
    obtain ⟨c,_hc,hcu⟩ := isInSpanOnAt_eq_iff.mp ((hgen g).mp hg).2
    refine ⟨RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg,?_⟩
    filter_upwards [hcu] with y hy hyS
    rw [hy hyS.1.1,hyS.1.2,mul_zero]

/-- Genuine current ideal has a literal reduced support germ and actual
codimension-one regularity; no smooth/reduced support field is supplied. -/
theorem actual_orderOne_relative_reduced_trace {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y)
    {x : X} (hx : x ∈ N) (f : X → ℂ) (hf : HolomorphicAt n f x)
    (hgen : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (hord : ordinaryTraceOrder N I x=1) :
    ∃ (U : Set X) (u : X → ℂ),x ∈ U ∧ IsTangentDirectionAlong N I 1 U u ∧ u x=0 ∧
      (∀ᶠ y in 𝓝 x,y ∈ N ∩ I.zeroLocus ↔ y ∈ N ∩ {y | u y=0} ∩ U) ∧
      (∀ g,I.mem x g ↔ (vanishingIdeal (n := n) (N ∩ I.zeroLocus)).mem x g) ∧
      ∃ k,RegularAtDim (n := n) N x k ∧ RegularAtDim (n := n) (N ∩ I.zeroLocus) x (k-1) := by
  obtain ⟨U,u,hxU,hu,hux,huI,hgenU⟩ := exists_actual_orderOne_relative_contact hN hI hnz hx f hf hgen hord
  have hs := coherent_zero_support_contact_germ hI hu.isOpen hxU huI hgenU
  refine ⟨U,u,hxU,hu,hux,hs,?_,?_⟩
  · intro g
    have hv : (vanishingIdeal (n := n) (N ∩ I.zeroLocus)).mem x g ↔
        (vanishingIdeal (n := n) (N ∩ {y | u y=0} ∩ U)).mem x g := by
      constructor
      · rintro ⟨hg,hg0⟩
        exact ⟨hg,by filter_upwards [hg0,hs] with y hy hys hyS; exact hy (hys.mpr hyS)⟩
      · rintro ⟨hg,hg0⟩
        exact ⟨hg,by filter_upwards [hg0,hs] with y hy hys hyS; exact hy (hys.mp hyS)⟩
    exact (contact_relative_ideal_mem_iff hN hI hu hxU hx hux hgenU g).symm.trans hv.symm
  · obtain ⟨k,hNk,hContact⟩ := hu.regularAtDim_contact
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hN ⟨⟨hx,hux⟩,hxU⟩
    exact ⟨k,hNk,CodimOneSupport.regularAtDim_of_eventually_mem_iff (hs.mono fun _ h => h.symm) hContact⟩

/-- ONLY original finite-history data internally provide actual current ideals
and relative generators before genuine chronological order1 recognition. -/
theorem original_chronological_orderOne_actual_reduced_trace (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    {y : Y} (hy : y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N)
    (hord : ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y=1) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    (∀ g,A.ideal.mem y g ↔ (vanishingIdeal (n := n) (A.N ∩ A.ideal.zeroLocus)).mem y g) ∧
      ∃ k,RegularAtDim (n := n) A.N y k ∧ RegularAtDim (n := n) (A.N ∩ A.ideal.zeroLocus) y (k-1) := by
  obtain ⟨_hN,_hE,_hm,hwA,hnzA,hprA⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  obtain ⟨f,hf,hgen⟩ := hprA y hy
  obtain ⟨U,u,_hyU,_hu,_huy,_hs,hred,hreg⟩ := actual_orderOne_relative_reduced_trace
    hwA.isClosedSubmanifold_N hwA.isCoherent hnzA hy f hf hgen hord
  exact ⟨hred,hreg⟩

end
end Hironaka.HironakaSharpActualPrincipalOrderOneTrace
