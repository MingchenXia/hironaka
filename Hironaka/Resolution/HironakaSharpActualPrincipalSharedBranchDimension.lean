/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualPrincipalOrderOneTrace

/-! Genuine pair-support dimension recognizes ACTUAL current relative-principal
ideal germs. True reduced ideal geometry precedes every branch dictionary. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualPrincipalSharedBranchDimension
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualPrincipalOrderOneTrace HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalDistinctTraceUSC HironakaSharpOriginalProductTraceOrder
  RelativePrincipalizationSpan RestrictedIdealExtension GermIdealOrder
  TangentDirectionAlong DerivativeIdealAlong GiraudAlong AnalyticDimensionBasics PureDimension
  RegularPointDimension DivisorExponentAlong MarkedIdeals MarkedIdeals.MarkedIdeal
variable {n : ℕ} {X : CMfd.{u} n}

private theorem vanishingIdeal_mem_iff_of_support_germ {A B : Set X} {x : X}
    (hs : ∀ᶠ y in 𝓝 x,y ∈ A ↔ y ∈ B) (g : X → ℂ) :
    (vanishingIdeal (n := n) A).mem x g ↔ (vanishingIdeal (n := n) B).mem x g := by
  constructor
  · rintro ⟨hg,hv⟩
    exact ⟨hg,by filter_upwards [hv,hs] with y hy hys hyB; exact hy (hys.mpr hyB)⟩
  · rintro ⟨hg,hv⟩
    exact ⟨hg,by filter_upwards [hv,hs] with y hy hys hyA; exact hy (hys.mp hyA)⟩

/-- Actual analytic pair support and real contact geometry force BOTH whole
ideal directions; no desired reduced/support relation is input. -/
theorem actual_orderOne_germ_eq_of_pair_locDimGE {N : Set X} (hN : IsClosedSubmanifold n N)
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hi : ∀ y ∈ N,IsNonzeroAlongAt N I y) (hj : ∀ y ∈ N,IsNonzeroAlongAt N J y)
    {x : X} (hx : x ∈ N) {d : ℕ} (hreg : RegularAtDim (n := n) N x (d+1))
    (f g : X → ℂ) (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hfi : ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a)
    (hgj : ∀ a,J.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=g) x a)
    (hoi : ordinaryTraceOrder N I x=1) (hoj : ordinaryTraceOrder N J x=1)
    (hdim : LocDimGE (n := n) (N ∩ I.zeroLocus ∩ J.zeroLocus) x d) :
    ∀ a,I.mem x a ↔ J.mem x a := by
  have hA := ((AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN).inter
    (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hI)).inter
    (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hJ)
  have hsupport : ∀ (K : GermIdeal n X),K.IsCoherent →
      (∀ y ∈ N,IsNonzeroAlongAt N K y) →
      (∃ v : X → ℂ,HolomorphicAt n v x ∧ ∀ a,K.mem x a ↔ HolomorphicAt n a x ∧
        IsInSpanOnAt (n := n) N (·=v) x a) → ordinaryTraceOrder N K x=1 →
      N ∩ I.zeroLocus ∩ J.zeroLocus ⊆ N ∩ K.zeroLocus →
      ∀ᶠ y in 𝓝 x,y ∈ N ∩ I.zeroLocus ∩ J.zeroLocus ↔ y ∈ N ∩ K.zeroLocus := by
    intro K hK hk hpr ho hsub
    obtain ⟨v,hv,hgen⟩ := hpr
    obtain ⟨U,u,hxU,hu,_hux,hs,_hred,_hreg⟩ := actual_orderOne_relative_reduced_trace hN hK hk hx v hv hgen ho
    have hAS : N ∩ I.zeroLocus ∩ J.zeroLocus ⊆ cosupport n N K 1 := by
      rw [cosupport_one (fun _ _ ha => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hK ha)]
      exact hsub
    filter_upwards [CodimOneSupportAlong.eventually_mem_iff_of_locDimGE_along hK hN le_rfl hA hAS hu hxU hreg hdim,
      hs,hu.isOpen.mem_nhds hxU] with y hy hyS hyU
    exact hy.trans ⟨fun h => hyS.mpr ⟨h,hyU⟩,fun h => (hyS.mp h).1⟩
  have hs : ∀ᶠ y in 𝓝 x,y ∈ N ∩ I.zeroLocus ↔ y ∈ N ∩ J.zeroLocus := by
    filter_upwards [hsupport I hI hi ⟨f,hf,hfi⟩ hoi (fun _ h => h.1),
      hsupport J hJ hj ⟨g,hg,hgj⟩ hoj (fun _ h => ⟨h.1.1,h.2⟩)] with y hyI hyJ
    exact hyI.symm.trans hyJ
  obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,hredI,_hreg⟩ := actual_orderOne_relative_reduced_trace hN hI hi hx f hf hfi hoi
  obtain ⟨_V,_v,_hxV,_hv,_hvx,_hs,hredJ,_hreg⟩ := actual_orderOne_relative_reduced_trace hN hJ hj hx g hg hgj hoj
  exact fun a => (hredI a).trans ((vanishingIdeal_mem_iff_of_support_germ hs a).trans (hredJ a).symm)

/-- Actual coherent equality persists before literal pair regularity/dimension. -/
theorem actual_orderOne_pair_locDimGE_of_germ_eq {N : Set X} (hN : IsClosedSubmanifold n N)
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hi : ∀ y ∈ N,IsNonzeroAlongAt N I y) {x : X} (hx : x ∈ N) {d : ℕ}
    (hreg : RegularAtDim (n := n) N x (d+1)) (f : X → ℂ) (hf : HolomorphicAt n f x)
    (hfi : ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a)
    (hoi : ordinaryTraceOrder N I x=1) (heq : ∀ a,I.mem x a ↔ J.mem x a) :
    LocDimGE (n := n) (N ∩ I.zeroLocus ∩ J.zeroLocus) x d := by
  have hs : ∀ᶠ y in 𝓝 x,y ∈ N ∩ I.zeroLocus ∩ J.zeroLocus ↔ y ∈ N ∩ I.zeroLocus := by
    filter_upwards [eventually_coherent_germ_eq hI hJ heq] with y hy
    constructor
    · exact fun h => h.1
    · rintro ⟨hyN,hyI⟩
      exact ⟨⟨hyN,hyI⟩,fun a ha => hyI a ((hy a).mpr ha)⟩
  obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,_hred,k,hNk,hIk⟩ := actual_orderOne_relative_reduced_trace hN hI hi hx f hf hfi hoi
  have hk : k=d+1 := eq_of_regularAtDim hNk hreg
  rw [hk,Nat.add_sub_cancel] at hIk
  exact locDimGE_of_regularAtDim (CodimOneSupport.regularAtDim_of_eventually_mem_iff (hs.mono fun _ h => h.symm) hIk)

/-- BOTH actual branch/dimension directions for genuine current ideals. -/
theorem actual_orderOne_germ_eq_iff_pair_locDimGE {N : Set X} (hN : IsClosedSubmanifold n N)
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hi : ∀ y ∈ N,IsNonzeroAlongAt N I y) (hj : ∀ y ∈ N,IsNonzeroAlongAt N J y)
    {x : X} (hx : x ∈ N) {d : ℕ} (hreg : RegularAtDim (n := n) N x (d+1))
    (f g : X → ℂ) (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hfi : ∀ a,I.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=f) x a)
    (hgj : ∀ a,J.mem x a ↔ HolomorphicAt n a x ∧ IsInSpanOnAt (n := n) N (·=g) x a)
    (hoi : ordinaryTraceOrder N I x=1) (hoj : ordinaryTraceOrder N J x=1) :
    (∀ a,I.mem x a ↔ J.mem x a) ↔ LocDimGE (n := n) (N ∩ I.zeroLocus ∩ J.zeroLocus) x d :=
  ⟨actual_orderOne_pair_locDimGE_of_germ_eq hN hI hJ hi hx hreg f hf hfi hoi,
    actual_orderOne_germ_eq_of_pair_locDimGE hN hI hJ hi hj hx hreg f g hf hg hfi hgj hoi hoj⟩

/-- ONLY original inputs supply the SAME current carrier and both genuine
relative generators BEFORE the actual shared-branch/dimension recognition. -/
theorem original_chronological_germ_eq_iff_pair_locDimGE (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i j : Fin E.length)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (y : Y) {d : ℕ}
    (hy : y ∈ (geoTransformAlong (geometricTemplate W []) T).N)
    (hreg : RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N y (d+1))
    (hoi : ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y=1)
    (hoj : ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y=1) :
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    let I := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal
    (∀ a,I.mem y a ↔ J.mem y a) ↔ LocDimGE (n := n) (N ∩ I.zeroLocus ∩ J.zeroLocus) y d := by
  obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  obtain ⟨hNj,_hEj,_hmj,hwj,hnzj,hprj⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense j T hT
  have hN := hwi.isClosedSubmanifold_N
  rw [hNi] at hN hnzi hpri
  rw [hNj] at hnzj hprj
  obtain ⟨f,hf,hfi⟩ := hpri y hy
  obtain ⟨g,hg,hgj⟩ := hprj y hy
  exact actual_orderOne_germ_eq_iff_pair_locDimGE hN hwi.isCoherent hwj.isCoherent hnzi hnzj hy hreg f g hf hg hfi hgj hoi hoj

end
end Hironaka.HironakaSharpActualPrincipalSharedBranchDimension
