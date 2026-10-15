/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCompositeTotalResidual

/-! Literal ORIGINAL full-product composite TOTAL and WHOLE ALL-accumulated
residual comparison. Actual finite multiplication/geometry precede induction.
Earlier ORIGINAL full-value/presentation/history comparison remains OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCompositeProductResidual
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCompositeTotalResidual HironakaSharpActualOriginalTotalHistoryResidual
  HironakaSharpActualTotalNonmonomialTransport HironakaSharpActualTotalAccumulatedResidual
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMemberProduct HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  IdealWeightPowers MarkedIdealOperationsAlong GermIdealOrder InvertibleIdealQuotient RestrictLeCalculus
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual finite original ideal multiplication has BOTH restricted directions
before WHOLE normalization; original positions and carrier-normal germs remain. -/
theorem relative_original_product_eq_restrictOn {W : Set X} (hW : IsClosedSubmanifold n W)
    (L : List (GermIdeal n X)) (hc : ∀ I ∈ L,I.IsCoherent) :
    relativeIdealListProduct W (L.map (restrictOn n W))=restrictOn n W (idealListProduct L) := by
  induction L with
  | nil =>
    ext x g
    exact ⟨fun hg => ⟨hg,IsInSpanAt.restrict (isInSpanAt_self hg hg)⟩,fun hg => hg.1⟩
  | cons I L ih =>
    have hcI := hc I (by simp)
    have hcL := isCoherent_idealListProduct L (fun J hJ => hc J (List.mem_cons_of_mem _ hJ))
    have hTail := ih (fun J hJ => hc J (List.mem_cons_of_mem _ hJ))
    have hcRI := isCoherent_restrictOn hcI (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)
    have hcRL : (relativeIdealListProduct W (L.map (restrictOn n W))).IsCoherent := by
      rw [hTail]
      exact isCoherent_restrictOn hcL (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)
    have hfL : RestrictLe W (relativeIdealListProduct W (L.map (restrictOn n W))) (idealListProduct L) := by
      rw [hTail]; exact restrictLe_restrictOn
    have hbL : RestrictLe W (idealListProduct L) (relativeIdealListProduct W (L.map (restrictOn n W))) := by
      rw [hTail]; exact restrictLe_self_restrictOn hcL
    change restrictOn n W ((restrictOn n W I).mul (relativeIdealListProduct W (L.map (restrictOn n W))))=
      restrictOn n W (I.mul (idealListProduct L))
    exact restrictOn_eq_of_restrictLe hW.1
      (restrictLe_mul (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcI hg)
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcL hg) restrictLe_restrictOn hfL)
      (restrictLe_mul (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcRI hg)
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcRL hg) (restrictLe_self_restrictOn hcI) hbL)

private theorem restrictOn_idempotent (W : Set X) (I : GermIdeal n X) :
    restrictOn n W (restrictOn n W I)=restrictOn n W I := by
  ext x g
  exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun s hs => hs.2) hg.2⟩,
    fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩

/-- Genuine original full-product geometry BEFORE real raw-history induction
and the independently constructed ALL-boundary product residual comparison. -/
theorem original_product_total_history_residual_eq (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate W []) T →
      let M : MarkedIdeal n X := ⟨W,[],restrictOn n W (originalMemberProduct (n := n) E),0⟩
      let Q := geoTransformAlong M T
      nonmonomialPartAlong n Q.N Q.ideal Q.E=chronologicalMemberProduct W E T
  | _, .refl, _ => by
    have hInit := relative_original_product_eq_restrictOn hW (E.map (vanishingIdeal (n := n))) (by
      intro I hI
      obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
      exact VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i))
    change nonmonomialPartAlong n W (restrictOn n W (originalMemberProduct (n := n) E)) []=_
    rw [HironakaSharpOriginalProductTraceOrder.nonmonomialPartAlong_nil_eq_restrictOn,restrictOn_idempotent]
    simpa only [originalMemberProduct,chronologicalMemberProduct,chronologicalMemberFamily,chronologicalMarked,
      originalRelativeMemberMarked,geoTransformAlong,geometricTemplate,List.map_map,Function.comp_def] using hInit.symm
  | _, .step T C π hπ, hT => by
    let M : MarkedIdeal n X := ⟨W,[],restrictOn n W (originalMemberProduct (n := n) E),0⟩
    let Q := geoTransformAlong M T
    have hcI := isCoherent_originalMemberProduct hn hE
    have hcM := isCoherent_restrictOn hcI (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)
    have hwM : M.IsWellFormed := ⟨hW,hcM,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hnzM : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x := by
      intro x hx
      obtain ⟨g,hg,hfreq⟩ := originalMemberProduct_isNonzeroAlongAt hn hE hdense hx
      exact ⟨g,le_restrictOn hcI x g hg,hfreq⟩
    obtain ⟨hwQ,hnzQ⟩ := raw_history_actual_geometry M hwM hnzM T hT.1
    have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
    have hQE := geoTransformAlong_E_eq_of_E_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
    have hCN : C ⊆ Q.N := by rw [hQN]; exact hT.2.subset_N
    have hNC : HasNormalCrossings n C Q.E := by rw [hQE]; exact hT.2.2.2
    have hStep := actual_whole_total_nonmonomial_parts_transport hn hwQ.isClosedSubmanifold_N hwQ.isSNCDivisor
      hwQ.isTransverse hwQ.isCoherent hnzQ hπ hCN hNC
    have hIH := original_product_total_history_residual_eq hn hW hE hdense T hT.1
    change nonmonomialPartAlong n Q.N Q.ideal Q.E=chronologicalMemberProduct W E T at hIH
    change nonmonomialPartAlong n (nextTotalMarked Q.N Q.ideal C π).N (nextTotalMarked Q.N Q.ideal C π).ideal
      (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) =
      nonmonomialPartAlong n (nextTotalMarked Q.N Q.ideal C π).N
        (nextTotalMarked Q.N (nonmonomialPartAlong n Q.N Q.ideal Q.E) C π).ideal
        (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) at hStep
    rw [hIH,hQN,hQE] at hStep
    have hNext := original_next_total_all_accumulated_residual_eq_product hn hW hE hdense T hT.1 hπ hT.2.subset_N hT.2.2.2
    have hZero : (Q.geoTransform C π).ideal=(nextTotalMarked Q.N Q.ideal C π).ideal := by
      change colonAlong n _ _ (idealPow _ Q.d)=colonAlong n _ _ (idealPow _ 0)
      rw [d_geoTransformAlong]
    change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C Q.N) (Q.geoTransform C π).ideal
      (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])=chronologicalMemberProduct W E (.step T C π hπ)
    rw [hZero,hQN,hQE]
    exact hStep.trans hNext

/-- WHOLE ALL-accumulated residual of the LITERAL ORIGINAL full-product
composite TOTAL, not a caller-provided product factor or history certificate. -/
theorem original_product_composite_total_residual_eq (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let A := geoTransformAlong (geometricTemplate W []) T
    nonmonomialPartAlong n A.N (GermIdeal.pullback T.proj (originalMemberProduct (n := n) E)) A.E=chronologicalMemberProduct W E T := by
  let M : MarkedIdeal n X := ⟨W,[],restrictOn n W (originalMemberProduct (n := n) E),0⟩
  let Q := geoTransformAlong M T
  have hcI := isCoherent_originalMemberProduct hn hE
  have hWhole := original_zero_history_eq_composite_total (E := []) hW hcI T hT
  have hHist := original_product_total_history_residual_eq hn hW hE hdense T hT
  change nonmonomialPartAlong n Q.N Q.ideal Q.E=chronologicalMemberProduct W E T at hHist
  change Q.ideal=restrictOn n Q.N (GermIdeal.pullback T.proj (originalMemberProduct (n := n) E)) at hWhole
  rw [hWhole] at hHist
  have hcM := isCoherent_restrictOn hcI (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)
  obtain ⟨hNc,_hcQ⟩ := isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier hW hcM
    (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T hT
  have hcB := GermIdealPullbackCalculus.isCoherent_pullback T.contMDiff_proj hcI
  have hAll := (MonomialPartEtale.nonmonomialPartAlong_congr hNc.1
    (restrictLe_self_restrictOn hcB) restrictLe_restrictOn).trans hHist
  rw [geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T,
    geoTransformAlong_E_eq_of_E_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T] at hAll
  exact hAll

end
end Hironaka.HironakaSharpActualCompositeProductResidual
