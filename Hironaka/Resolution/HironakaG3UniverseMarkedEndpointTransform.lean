import Hironaka.Resolution.HironakaG3UniverseGeoTransformBase
import Hironaka.Resolution.HironakaG3UniversePullbackPowers
import Hironaka.Blowup.BlowupBiholomorphismLift
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u v w
namespace Hironaka.HironakaG3UniverseMarkedEndpointTransform
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers IdealWeightPowers
  RestrictedIdealQuotient GermIdealPullbackCalculus
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionContactParameterCoefficientIdeals
  BlowupBiholomorphismLift HironakaG3UniverseGeoTransform
noncomputable section

/-- Fixed-base transform under an actual biholomorphic replacement of the endpoint. -/
theorem crossGeoTransform_comp_diffeo {n : ℕ} {X : Type u} {Y : Type v} {Y' : Type w}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace Y'] [ChartedSpace (ComplexModel n) Y'] [IsComplexManifold n Y']
    (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) (C : Set X)
    (hC : (vanishingIdeal (n := n) C).IsCoherent) {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    (hc : (crossGeoTransform M C π).ideal.IsCoherent) :
    crossGeoTransform M C (π ∘ χ) =
      markedPullback (m := n) χ (crossGeoTransform M C π) := by
  have hs (A : Set X) : closure ((π ∘ χ) ⁻¹' (A \ C)) =
      χ ⁻¹' closure (π ⁻¹' (A \ C)) := by
    rw [preimage_comp]
    exact (χ.toHomeomorph.preimage_closure _).symm
  have hpa := coherent_parameter_pullback_comp (X := CMfd.of (n := n) X)
    (Y := CMfd.of (n := n) Y) (Z := CMfd.of (n := n) Y') hπ χ.contMDiff M.ideal hM
  have hpC := coherent_parameter_pullback_comp (X := CMfd.of (n := n) X)
    (Y := CMfd.of (n := n) Y) (Z := CMfd.of (n := n) Y') hπ χ.contMDiff
    (vanishingIdeal (n := n) C) hC
  have hpCc := GermIdealPullbackCalculus.isCoherent_pullback hπ hC
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact hs M.N
  · simp only [crossGeoTransform, markedPullback, List.map_append, List.map_map, List.map_cons,
      List.map_nil]
    congr 1
    exact List.map_congr_left fun A _ => hs A
  · change colonAlong n (closure ((π ∘ χ) ⁻¹' (M.N \ C)))
      (GermIdeal.pullback (m := n) (π ∘ χ) M.ideal)
      (idealPow (GermIdeal.pullback (m := n) (π ∘ χ) (vanishingIdeal (n := n) C)) M.d) =
      GermIdeal.pullback (m := n) χ (colonAlong n (closure (π ⁻¹' (M.N \ C)))
        (GermIdeal.pullback (m := n) π M.ideal)
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d))
    rw [hs M.N, hpa, hpC, ← HironakaG3UniversePullbackPowers.pullback_idealPow χ.contMDiff hpCc]
    exact colonAlong_pullback_diffeo χ (GermIdealPullbackCalculus.isCoherent_pullback hπ hM)
      (GermIdealPullbackCalculus.isCoherent_idealPow hpCc _) hc
  · rfl
end
end Hironaka.HironakaG3UniverseMarkedEndpointTransform

namespace Hironaka.HironakaG3UniverseMarkedStageTransform
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaSmoothSubmersionCoefficientIdeals
  HironakaG3UniverseGeoTransform HironakaG3UniverseMarkedBaseTransform HironakaG3UniverseMarkedEndpointTransform
noncomputable section

/-- Actual one-step marked transform along the conjugate of a holomorphic map. -/
theorem geoTransform_conjugate_diffeos {n : ℕ} {X Y : Type u} {X' Y' : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace X'] [ChartedSpace (ComplexModel n) X'] [IsComplexManifold n X']
    [TopologicalSpace Y'] [ChartedSpace (ComplexModel n) Y'] [IsComplexManifold n Y']
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) (C : Set X)
    (hC : (vanishingIdeal (n := n) C).IsCoherent) {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    (hc : (M.geoTransform C π).ideal.IsCoherent) :
    (markedPullback (m := n) e M).geoTransform (e ⁻¹' C) (e.symm ∘ π ∘ χ) =
      markedPullback (m := n) χ (M.geoTransform C π) := by
  have hb := markedPullback_geoTransform_base e M hM C (hπ.comp χ.contMDiff)
  have he := crossGeoTransform_comp_diffeo χ M hM C hC hπ (by simpa only [crossGeoTransform_eq_geoTransform] using hc)
  rw [crossGeoTransform_eq_geoTransform] at hb
  rw [crossGeoTransform_eq_geoTransform] at he
  exact hb.trans he
end
end Hironaka.HironakaG3UniverseMarkedStageTransform
