/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualOriginalControlledHistory

/-! General SAME ORIGINAL test histories compare WHOLE controlled residuals
with literal composite original TOTALs. No canonicality or principal numerator,
higher history-value equality or semicoherent-presentation certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalGeneralControlledCompositeResidual
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualOriginalTotalHistoryResidual
  HironakaSharpActualCompositeTotalResidual HironakaSharpActualMonomialDivisionResidual
  HironakaSharpActualTotalNonmonomialTransport HironakaSharpActualChronologicalStrictStep
  HironakaSharpActualFiniteChronologicalHistory HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  IdealWeightPowers MarkedIdealOperationsAlong GermIdealOrder InvertibleIdealQuotient RestrictLeCalculus
  NonmonomialOrderLocal
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

private theorem zero_transform_ideal_eq (M : MarkedIdeal n X) (hm : M.d=0)
    {Y : CMfd.{u} n} (C : Set X) (π : Y → X) :
    (M.geoTransform C π).ideal=(nextTotalMarked M.N M.ideal C π).ideal := by
  change colonAlong n _ _ (idealPow _ M.d)=colonAlong n _ _ (idealPow _ 0)
  rw [hm]

/-- Genuine controlled and independently normalized zero-mark histories have
WHOLE equal residuals, for ANY actual ORIGINAL test prefix and numerator. -/
theorem general_controlled_zero_history_nonmonomial_eq (hn : 0 < n) (M : MarkedIdeal n X)
    (hw : M.IsWellFormed) (hnz : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower M T →
      let R : MarkedIdeal n X := ⟨M.N,M.E,restrictOn n M.N M.ideal,0⟩
      let Q := geoTransformAlong M T
      let A := geoTransformAlong R T
      nonmonomialPartAlong n Q.N Q.ideal Q.E=nonmonomialPartAlong n A.N A.ideal A.E
  | _, .refl, _ =>
    MonomialPartEtale.nonmonomialPartAlong_congr hw.isClosedSubmanifold_N.1
      (restrictLe_self_restrictOn hw.isCoherent) restrictLe_restrictOn
  | _, .step T C π hπ, hT => by
    let R : MarkedIdeal n X := ⟨M.N,M.E,restrictOn n M.N M.ideal,0⟩
    let Q := geoTransformAlong M T
    let A := geoTransformAlong R T
    have hcR := isCoherent_restrictOn hw.isCoherent
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hw.isClosedSubmanifold_N)
    have hwR : R.IsWellFormed := ⟨hw.isClosedSubmanifold_N,hcR,hw.isSNCDivisor,hw.isTransverse⟩
    have hnzR : ∀ x ∈ R.N,IsNonzeroAlongAt R.N R.ideal x := by
      intro x hx
      obtain ⟨g,hg,hfreq⟩ := hnz x hx
      exact ⟨g,le_restrictOn hw.isCoherent x g hg,hfreq⟩
    have hGeom := actual_original_test_history_template M hw T hT.1
    obtain ⟨hwA,hnzA⟩ := raw_history_actual_geometry R hwR hnzR T hGeom
    have hwQ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT.1
    have hnzQ := isNonzeroAlongAt_geoTransformAlong_sameCarrier hw.isClosedSubmanifold_N hw.isCoherent
      (𝔍 := M) (𝔪 := M) rfl hnz T hT.1
    have hNA : Q.N=A.N := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := R) rfl T
    have hEA : Q.E=A.E := geoTransformAlong_E_eq_of_E_eq (𝔍 := M) (𝔪 := R) rfl T
    have hCN : C ⊆ A.N := by rw [←hNA]; exact hT.2.subset_N
    have hNC : HasNormalCrossings n C A.E := by rw [←hEA]; exact hT.2.2.2
    have hControlled := actual_geoTransform_nonmonomial_eq_total hn Q hwQ hnzQ hT.2 hπ
    have hQtotal := actual_whole_total_nonmonomial_parts_transport hn hwQ.isClosedSubmanifold_N
      hwQ.isSNCDivisor hwQ.isTransverse hwQ.isCoherent hnzQ hπ hT.2.subset_N hT.2.2.2
    have hAtotal := actual_whole_total_nonmonomial_parts_transport hn hwA.isClosedSubmanifold_N
      hwA.isSNCDivisor hwA.isTransverse hwA.isCoherent hnzA hπ hCN hNC
    have hIH := general_controlled_zero_history_nonmonomial_eq hn M hw hnz T hT.1
    change nonmonomialPartAlong n Q.N Q.ideal Q.E=nonmonomialPartAlong n A.N A.ideal A.E at hIH
    change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C Q.N) (nextTotalMarked Q.N Q.ideal C π).ideal
      (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) =
      nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C Q.N)
        (nextTotalMarked Q.N (nonmonomialPartAlong n Q.N Q.ideal Q.E) C π).ideal
        (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) at hQtotal
    change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C A.N) (nextTotalMarked A.N A.ideal C π).ideal
      (A.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) =
      nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C A.N)
        (nextTotalMarked A.N (nonmonomialPartAlong n A.N A.ideal A.E) C π).ideal
        (A.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) at hAtotal
    rw [hIH] at hQtotal
    change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C Q.N) (Q.geoTransform C π).ideal
      (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) =
      nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C Q.N) (nextTotalMarked Q.N Q.ideal C π).ideal
        (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) at hControlled
    change nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C Q.N) (Q.geoTransform C π).ideal
      (Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) =
      nonmonomialPartAlong n (BlowupStrictSubmanifold.geoStrictTransform π C A.N) (A.geoTransform C π).ideal
        (A.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C])
    rw [zero_transform_ideal_eq A (by rw [d_geoTransformAlong]) C π]
    exact hControlled.trans (hQtotal.trans (by simpa only [hNA,hEA] using hAtotal.symm))

/-- For ANY real ORIGINAL test history, strip ALL genuine accumulated factors
from the LITERAL composite pullback of the unchanged ORIGINAL numerator. -/
theorem general_controlled_history_composite_nonmonomial_eq (hn : 0 < n) (M : MarkedIdeal n X)
    (hw : M.IsWellFormed) (hnz : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    let Q := geoTransformAlong M T
    nonmonomialPartAlong n Q.N Q.ideal Q.E=
      nonmonomialPartAlong n Q.N (GermIdeal.pullback T.proj M.ideal) Q.E := by
  let R : MarkedIdeal n X := ⟨M.N,M.E,restrictOn n M.N M.ideal,0⟩
  let Q := geoTransformAlong M T
  let A := geoTransformAlong R T
  have hGeom := actual_original_test_history_template M hw T hT
  have hEq := general_controlled_zero_history_nonmonomial_eq hn M hw hnz T hT
  have hWhole := original_zero_history_eq_composite_total hw.isClosedSubmanifold_N hw.isCoherent T hGeom
  have hNA : Q.N=A.N := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := R) rfl T
  have hEA : Q.E=A.E := geoTransformAlong_E_eq_of_E_eq (𝔍 := M) (𝔪 := R) rfl T
  change A.ideal=restrictOn n A.N (GermIdeal.pullback T.proj M.ideal) at hWhole
  change nonmonomialPartAlong n Q.N Q.ideal Q.E=nonmonomialPartAlong n A.N A.ideal A.E at hEq
  rw [hWhole,←hNA,←hEA] at hEq
  have hwQ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  have hcB := GermIdealPullbackCalculus.isCoherent_pullback T.contMDiff_proj hw.isCoherent
  exact hEq.trans (MonomialPartEtale.nonmonomialPartAlong_congr hwQ.isClosedSubmanifold_N.1
    restrictLe_restrictOn (restrictLe_self_restrictOn hcB))

/-- Original domain plus ANY actual ORIGINAL test prefix internally gives the
whole composite ideal dictionary and EVERY true first-entry threshold/order. -/
theorem original_test_composite_nonmonomial_order_dictionary (hn : 0 < n)
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    let Q := geoTransformAlong M T
    let B : MarkedIdeal n Y := ⟨Q.N,Q.E,GermIdeal.pullback T.proj M.ideal,Q.d⟩
    Q.IsWellFormed ∧ (∀ y ∈ Q.N,IsNonzeroAlongAt Q.N Q.ideal y) ∧
      B.ideal.IsCoherent ∧ nmPart Q=nmPart B ∧
      (∀ q y,y ∈ ordGe Q q ↔ y ∈ ordGe B q) ∧ ∀ y,nmOrd Q y=nmOrd B y := by
  let Q := geoTransformAlong M T
  let B : MarkedIdeal n Y := ⟨Q.N,Q.E,GermIdeal.pullback T.proj M.ideal,Q.d⟩
  have hQ := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hEq := general_controlled_history_composite_nonmonomial_eq hn M hM.isWellFormed hM.isNonzeroAlongAt T hT
  change nmPart Q=nmPart B at hEq
  have hMem : ∀ q y,y ∈ ordGe Q q ↔ y ∈ ordGe B q := by
    intro q y
    change y ∈ cosupport n Q.N (nmPart Q) q ↔ y ∈ cosupport n Q.N (nmPart B) q
    rw [hEq]
  exact ⟨hQ.isWellFormed,hQ.isNonzeroAlongAt,
    GermIdealPullbackCalculus.isCoherent_pullback T.contMDiff_proj hM.isWellFormed.isCoherent,
    hEq,hMem,fun y => nmOrd_congr (fun q => hMem q y)⟩

end
end Hironaka.HironakaOriginalGeneralControlledCompositeResidual
