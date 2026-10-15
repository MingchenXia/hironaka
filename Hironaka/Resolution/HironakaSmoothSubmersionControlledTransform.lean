/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionCartesianTower
import Hironaka.Resolution.HironakaSmoothSubmersionInvertibleQuotients
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionControlledTransform
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupStrictSubmanifold BlowupExceptionalDivisor BlowupControlledTransform
  HironakaSmoothSubmersionBlowupLift HironakaSmoothSubmersionBlowupChoiceGeometry
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeOrder
  HironakaSmoothSubmersionOrder HironakaSmoothSubmersionInvertibleQuotients
  HironakaSmoothSubmersionNormalCrossings GermIdealPullbackCalculus
  HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionDivisorExponents GermIdealOrder RelativePrincipalizationSpan
  IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal
noncomputable section
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {C : Set X} {π : D → X} {ρ : D' → Y}

theorem geoStrictTransform_actual_preimage
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong m (f ⁻¹' C) ρ) (A : Set X) :
    (actualLift hf hπ hρ) ⁻¹' geoStrictTransform π C A =
      geoStrictTransform ρ (f ⁻¹' C) (f ⁻¹' A) := by
  unfold geoStrictTransform
  rw [(HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion
    (actualLift_isSubmersion hf hπ hρ)).preimage_closure_eq_closure_preimage
    (actualLift_contMDiff hf hπ hρ).continuous,
    ← preimage_comp,actualLift_proj_comm hf hπ hρ,preimage_comp,preimage_sdiff]

theorem boundary_actual_preimage
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong m (f ⁻¹' C) ρ) (E : List (Set X)) :
    (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).map ((actualLift hf hπ hρ) ⁻¹' ·) =
      (E.map (f ⁻¹' ·)).map (geoStrictTransform ρ (f ⁻¹' C)) ++ [ρ ⁻¹' (f ⁻¹' C)] := by
  simp only [List.map_append,List.map_map,List.map_cons,List.map_nil]
  congr 1
  · exact List.map_congr_left fun A _ => geoStrictTransform_actual_preimage hf hπ hρ A
  · exact congrArg (fun A => [A]) (actualLift_centre_preimage hf hπ hρ)

theorem isAdmissibleCentre_markedPullback
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hC : M.IsAdmissibleCentre C) :
    (markedPullback (m := m) f M).IsAdmissibleCentre (f ⁻¹' C) := by
  refine ⟨isClosedSubmanifold_preimage_submersion hf hC.1,?_,
    hasNormalCrossings_preimage_submersion hf hC.2.2⟩
  change f ⁻¹' C ⊆ cosupport m (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal) M.d
  rw [cosupport_preimage_eq hf hI M.N M.d]
  exact preimage_mono hC.2.1

theorem controlledTransform_actual_pullback
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong m (f ⁻¹' C) ρ)
    {I : GermIdeal n X} (hI : I.IsCoherent) (d : ℕ)
    (hC : C ⊆ cosupport n univ I d) :
    GermIdeal.pullback (m := m) (actualLift hf hπ hρ) (controlledTransform hπ I d) =
      controlledTransform hρ (GermIdeal.pullback (m := m) f I) d := by
  have hle := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hI hπ.1 hC
  have hprod := pullback_le_idealPow_exceptionalDivisor hπ hle
  rw [controlledTransform,pullback_colon_idealPow_eq (actualLift_isSubmersion hf hπ hρ)
    (isCoherent_pullback hπ.contMDiff hI) (exceptionalDivisor hπ).isInvertible d hprod]
  have hnum : GermIdeal.pullback (m := m) (actualLift hf hπ hρ)
      (GermIdeal.pullback (m := n) π I) =
      GermIdeal.pullback (m := m) ρ (GermIdeal.pullback (m := m) f I) := by
    rw [← coherent_pullback_comp hπ.contMDiff (actualLift_contMDiff hf hπ hρ) _ hI,
      actualLift_proj_comm hf hπ hρ,
      coherent_pullback_comp hf.contMDiff hρ.contMDiff _ hI]
  rw [hnum,exceptionalDivisor_ideal,actualLift_whole_ideal hf hπ hρ]
  rfl

theorem isCoherent_source_controlled
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong m (f ⁻¹' C) ρ)
    {I : GermIdeal n X} (hI : I.IsCoherent) (d : ℕ)
    (hC : C ⊆ cosupport n univ I d) :
    (controlledTransform hρ (GermIdeal.pullback (m := m) f I) d).IsCoherent := by
  rw [← controlledTransform_actual_pullback hf hπ hρ hI d hC]
  exact isCoherent_pullback (actualLift_contMDiff hf hπ hρ)
    (isCoherent_controlledTransform hπ hI
      (HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hI hπ.1 hC))

theorem controlledTransform_actual_cosupport
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong m (f ⁻¹' C) ρ)
    {I : GermIdeal n X} (hI : I.IsCoherent) (d : ℕ)
    (hC : C ⊆ cosupport n univ I d) (q : ℕ) :
    cosupport m univ (controlledTransform hρ (GermIdeal.pullback (m := m) f I) d) q =
      (actualLift hf hπ hρ) ⁻¹' cosupport n univ (controlledTransform hπ I d) q := by
  rw [← controlledTransform_actual_pullback hf hπ hρ hI d hC]
  exact cosupport_pullback_eq (actualLift_isSubmersion hf hπ hρ)
    (isCoherent_controlledTransform hπ hI
      (HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hI hπ.1 hC)) q

theorem markedPullback_geoTransform_actual
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong m (f ⁻¹' C) ρ)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : M.N = univ)
    (hC : M.IsAdmissibleCentre C) :
    (markedPullback (m := m) f M).geoTransform (f ⁻¹' C) ρ =
      markedPullback (m := m) (actualLift hf hπ hρ) (M.geoTransform C π) := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact (geoStrictTransform_actual_preimage hf hπ hρ M.N).symm
  · exact (boundary_actual_preimage hf hπ hρ M.E).symm
  · have hN' : (markedPullback (m := m) f M).N = univ := by
      change f ⁻¹' M.N = univ
      rw [hN,preimage_univ]
    have hI' := isCoherent_pullback hf.contMDiff hI
    change ((markedPullback (m := m) f M).geoTransform (f ⁻¹' C) ρ).ideal =
      GermIdeal.pullback (m := m) (actualLift hf hπ hρ) (M.geoTransform C π).ideal
    rw [geoTransform_ideal_eq_controlledTransform hN' hI' hρ,
      geoTransform_ideal_eq_controlledTransform hN hI hπ]
    exact (controlledTransform_actual_pullback hf hπ hρ hI M.d
      (by simpa only [MarkedIdeal.cosupp,hN] using hC.2.1)).symm
  · rfl

end
end Hironaka.HironakaSmoothSubmersionControlledTransform
