/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalBoundTwoStepOneLocality
import Hironaka.Resolution.HironakaOriginalFiniteStepOneCutMaskAvoidance
/-! Genuine local geometry transports literal StepOne-cut histories;
actual admissibility and cosupport precede each two-point value comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalBoundTwoStepOneCutLocality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HomogenizedIdealAlong CanonicalCentres HironakaOriginalFrozenRecursiveLower
  HironakaOriginalFiniteLevelCutLowerTests HironakaOriginalFiniteStepOneCutMaskAvoidance
  HironakaOriginalBoundTwoStepOneLocality
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X X' A Y Y' : CMfd.{u} n}

/-- Actual centre preimages and coherent TEST geometry are independent
of the StepOne value identities used only afterward at both real points. -/
theorem step_one_cut_of_towerIso (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    {Q : BlowupTower X' Y'} {T : BlowupTower X Y} (h : IsTowerIso Φ Q T χ)
    (hT : IsStepOneCutTower hn (k+1) M T) :
    IsStepOneCutTower hn (k+1) (MarkedIdeal.pullback Φ M) Q := by
  revert hT
  induction h with
  | refl => exact fun hT => hT
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hT
    have hTest := levelCutTower_geoTest M T (stepOneCutTower_levelCut hn M T hT.1)
    obtain ⟨_hNT,hcoh⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hTest
    refine ⟨ih hT.1,?_,?_⟩
    · rw [IsTowerIso.geoTransformAlong_eq Φ hM.isWellFormed.isClosedSubmanifold_N
        hM.isWellFormed.isCoherent h hTest,←hC]
      exact (MarkedIdealTowerTransport.isAdmissibleCentre_pullback_iff hcoh).mpr hT.2.1
    · intro y hy c hc
      have hCos := IsTowerIso.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N
        hM.isWellFormed.isCoherent h hTest
      have hyOld : χ y∈(geoTransformAlong M T).cosupp := by rw [hCos] at hy;exact hy
      have hcOld : χ c∈C := by change c∈χ ⁻¹' C;rw [hC];exact hc
      have hcCos : χ c∈(geoTransformAlong M T).cosupp := hT.2.1.2.1 hcOld
      rw [step_one_value_of_towerIso hn k M hM hmax T hTest h y hyOld,
        step_one_value_of_towerIso hn k M hM hmax T hTest h c hcCos]
      exact hT.2.2 (χ y) hyOld (χ c) hcOld

/-- The actual base identity and genuine append-restriction stagewise map
construct the whole flattened recipe without a flattened cut certificate. -/
theorem step_one_cut_restrict_append (hn : 0<n) (k : ℕ)
    (W : Opens X) (M : MarkedIdeal n (CMfd.of (n := n) W)) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (B : BlowupTower X A) (T : BlowupTower A Y)
    (hT : IsStepOneCutTower hn (k+1) M (restrict W (B.append T))) :
    IsStepOneCutTower hn (k+1) M ((restrict W B).append (restrict (openPreimage B W) T)) := by
  have hiso := (isTowerIso_restrict_append W B T).symm
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) W) ∞).symm M=M :=
    ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  have ht := step_one_cut_of_towerIso hn k M hM hmax hiso hT
  rwa [hpb] at ht

/-- Real open TEST restriction supplies actual admissibility separately;
only genuine old cosupport points are compared numerically. -/
theorem step_one_cut_restrict_open (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsStepOneCutTower hn (k+1) M T) (U : Opens X) :
    IsStepOneCutTower hn (k+1) (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    have hTest := levelCutTower_geoTest M T (stepOneCutTower_levelCut hn M T hT.1)
    have hFullTest := levelCutTower_geoTest M (.step T C π hπ)
      (stepOneCutTower_levelCut hn M (.step T C π hπ) hT)
    have hRestrictedTest := isGeoTestTower_restrict U hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent (.step T C π hπ) hFullTest
    obtain ⟨_hNT,hcoh⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hTest
    refine ⟨ih hT.1,hRestrictedTest.2,?_⟩
    intro y hy c hc
    have hyOld : y.val∈(geoTransformAlong M T).cosupp := by
      rw [geoTransformAlong_restrict U hM.isWellFormed.isClosedSubmanifold_N
        hM.isWellFormed.isCoherent T hTest,cosupp_pullback_val _
          (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg)] at hy
      exact hy
    have hcOld : c.val∈C := hc
    have hcCos : c.val∈(geoTransformAlong M T).cosupp := hT.2.1.2.1 hcOld
    rw [step_one_value_restrict_open hn k M hM hmax T hTest U y hyOld,
      step_one_value_restrict_open hn k M hM hmax T hTest U c hcCos]
    exact hT.2.2 y.val hyOld c.val hcOld

end
end Hironaka.HironakaOriginalBoundTwoStepOneCutLocality
