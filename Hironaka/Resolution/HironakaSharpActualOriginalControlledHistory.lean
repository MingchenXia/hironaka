/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualMonomialDivisionResidual

/-! The SAME ORIGINAL product marked input, with its unchanged positive mark
and genuine test history, has WHOLE chronological/composite residual dictionaries.
No current-reflexive rebase or higher full-invariant comparison is inferred. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualOriginalControlledHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualMonomialDivisionResidual HironakaSharpActualCompositeProductResidual
  HironakaSharpActualTotalNonmonomialTransport HironakaSharpActualTotalAccumulatedResidual
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMemberProduct HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  IdealWeightPowers MarkedIdealOperationsAlong GermIdealOrder InvertibleIdealQuotient
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The ACTUAL original test history internally supplies the SAME-map template
history, keeping every real original step and ENTIRE ordered boundary. -/
theorem actual_original_test_history_template (M : MarkedIdeal n X) (hw : M.IsWellFormed) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower M T → IsGeoTestTower (geometricTemplate M.N M.E) T
  | _, .refl, _ => trivial
  | _, .step T C π _hπ, hT => by
    have hTemp := actual_original_test_history_template M hw T hT.1
    have hwTemp : (geometricTemplate M.N M.E).IsWellFormed :=
      ⟨hw.isClosedSubmanifold_N,isCoherent_unitIdeal,hw.isSNCDivisor,hw.isTransverse⟩
    have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwTemp T hTemp
    have hN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate M.N M.E) rfl T
    have hE := geoTransformAlong_E_eq_of_E_eq (𝔍 := M) (𝔪 := geometricTemplate M.N M.E) rfl T
    refine ⟨hTemp,⟨hT.2.1,?_,?_⟩⟩
    · change C ⊆ cosupport n _ _ (geoTransformAlong (geometricTemplate M.N M.E) T).d
      rw [d_geoTransformAlong]
      change C ⊆ cosupport n _ _ 0
      rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwA.isCoherent hg),←hN]
      exact hT.2.subset_N
    · rw [←hE]
      exact hT.2.2.2

private theorem original_product_controlled_chrono_eq (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (q : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (originalMemberProductMarked W E q) T →
      let Q := geoTransformAlong (originalMemberProductMarked W E q) T
      nonmonomialPartAlong n Q.N Q.ideal Q.E=chronologicalMemberProduct W E T
  | _, .refl, _ => by
    have hInit := relative_original_product_eq_restrictOn hW (E.map (vanishingIdeal (n := n))) (by
      intro I hI
      obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
      exact VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i))
    change nonmonomialPartAlong n W (originalMemberProduct (n := n) E) []=_
    rw [HironakaSharpOriginalProductTraceOrder.nonmonomialPartAlong_nil_eq_restrictOn]
    simpa only [originalMemberProduct,chronologicalMemberProduct,chronologicalMemberFamily,chronologicalMarked,
      originalRelativeMemberMarked,geoTransformAlong,geometricTemplate,List.map_map,Function.comp_def] using hInit.symm
  | _, .step T C π hπ, hT => by
    let M := originalMemberProductMarked W E q
    let Q := geoTransformAlong M T
    have hcI := isCoherent_originalMemberProduct hn hE
    have hwM : M.IsWellFormed := ⟨hW,hcI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hnzM : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x := fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx
    have hwQ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwM T hT.1
    have hnzQ := isNonzeroAlongAt_geoTransformAlong_sameCarrier hW hcI (𝔍 := M) (𝔪 := M) rfl hnzM T hT.1
    have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
    have hQE := geoTransformAlong_E_eq_of_E_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
    have hControlled := actual_geoTransform_nonmonomial_eq_total hn Q hwQ hnzQ hT.2 hπ
    have hTransport := actual_whole_total_nonmonomial_parts_transport hn hwQ.isClosedSubmanifold_N hwQ.isSNCDivisor
      hwQ.isTransverse hwQ.isCoherent hnzQ hπ hT.2.subset_N hT.2.2.2
    have hIH := original_product_controlled_chrono_eq hn hW hE hdense q T hT.1
    change nonmonomialPartAlong n Q.N Q.ideal Q.E=chronologicalMemberProduct W E T at hIH
    change nonmonomialPartAlong n (nextTotalMarked Q.N Q.ideal C π).N (nextTotalMarked Q.N Q.ideal C π).ideal
      (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) =
      nonmonomialPartAlong n (nextTotalMarked Q.N Q.ideal C π).N
        (nextTotalMarked Q.N (nonmonomialPartAlong n Q.N Q.ideal Q.E) C π).ideal
        (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) at hTransport
    rw [hIH,hQN,hQE] at hTransport
    have hGeom := actual_original_test_history_template M hwM T hT.1
    have hCN : C ⊆ (geoTransformAlong (geometricTemplate W []) T).N := by rw [←hQN]; exact hT.2.subset_N
    have hNC : HasNormalCrossings n C (geoTransformAlong (geometricTemplate W []) T).E := by rw [←hQE]; exact hT.2.2.2
    have hNext := original_next_total_all_accumulated_residual_eq_product hn hW hE hdense T hGeom hπ hCN hNC
    have hAfter : nonmonomialPartAlong n (nextTotalMarked Q.N Q.ideal C π).N (nextTotalMarked Q.N Q.ideal C π).ideal
        (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])=chronologicalMemberProduct W E (.step T C π hπ) := by
      rw [hQN,hQE]
      exact hTransport.trans hNext
    exact hControlled.trans hAfter

/-- ONLY original geometry and a REAL SAME ORIGINAL test prefix supply WHOLE
controlled/chronological and literal composite TOTAL ALL-E residual identities. -/
theorem original_product_controlled_history_residual_dictionary (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (q : ℕ)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E q) T) :
    let Q := geoTransformAlong (originalMemberProductMarked W E q) T
    nonmonomialPartAlong n Q.N Q.ideal Q.E=chronologicalMemberProduct W E T ∧
      nonmonomialPartAlong n Q.N Q.ideal Q.E=
        nonmonomialPartAlong n Q.N (GermIdeal.pullback T.proj (originalMemberProduct (n := n) E)) Q.E := by
  let M := originalMemberProductMarked W E q
  have hcI := isCoherent_originalMemberProduct hn hE
  have hwM : M.IsWellFormed := ⟨hW,hcI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hGeom := actual_original_test_history_template M hwM T hT
  have hChrono := original_product_controlled_chrono_eq hn hW hE hdense q T hT
  have hRaw := original_product_composite_total_residual_eq hn hW hE hdense T hGeom
  have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
  have hQE := geoTransformAlong_E_eq_of_E_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
  change nonmonomialPartAlong n (geoTransformAlong (geometricTemplate W []) T).N
    (GermIdeal.pullback T.proj (originalMemberProduct (n := n) E))
    (geoTransformAlong (geometricTemplate W []) T).E=chronologicalMemberProduct W E T at hRaw
  rw [←hQN,←hQE] at hRaw
  exact ⟨hChrono,hChrono.trans hRaw.symm⟩

end
end Hironaka.HironakaSharpActualOriginalControlledHistory
