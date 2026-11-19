import Hironaka.Resolution.HironakaG3UniverseVanishingIdeal
import Hironaka.Resolution.HironakaSmoothSubmersionContactParameterCoefficientIdeals
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u v w
namespace Hironaka.HironakaG3UniverseGeoTransform
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers RestrictedIdealQuotient
noncomputable section

/-- The centre-relative transform with independent source and target universes. -/
def crossGeoTransform {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (M : MarkedIdeal n X) (C : Set X) (π : Y → X) : MarkedIdeal n Y where
  N := closure (π ⁻¹' (M.N \ C))
  E := M.E.map (fun H => closure (π ⁻¹' (H \ C))) ++ [π ⁻¹' C]
  ideal := colonAlong n (closure (π ⁻¹' (M.N \ C))) (GermIdeal.pullback π M.ideal)
    (idealPow (GermIdeal.pullback π (vanishingIdeal (n := n) C)) M.d)
  d := M.d

/-- On one universe this is definitionally the actual existing transform. -/
theorem crossGeoTransform_eq_geoTransform {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (M : MarkedIdeal n X) (C : Set X) (π : Y → X) :
    crossGeoTransform M C π = M.geoTransform C π := rfl
end
end Hironaka.HironakaG3UniverseGeoTransform

set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3UniverseMarkedBaseTransform
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupStrictSubmanifold
  IdealWeightPowers GermIdealPullbackCalculus
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionContactParameterCoefficientIdeals
  G3UniverseVanishingIdeal HironakaG3UniverseGeoTransform
noncomputable section

/-- Actual controlled transform after replacing its base by a biholomorphic copy. -/
theorem markedPullback_geoTransform_base {n : ℕ} {X : Type u} {X' : Type v} {Z : Type w}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace X'] [ChartedSpace (ComplexModel n) X'] [IsComplexManifold n X']
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) (C : Set X) {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) :
    crossGeoTransform (markedPullback (m := n) e M) (e ⁻¹' C) (e.symm ∘ π) =
      crossGeoTransform M C π := by
  have hpre (A : Set X) : e.symm ⁻¹' (e ⁻¹' A) = A := by ext x; simp
  have hgeo (A : Set X) : closure ((e.symm ∘ π) ⁻¹' ((e ⁻¹' A) \ (e ⁻¹' C))) =
      closure (π ⁻¹' (A \ C)) := by
    simp only [← preimage_sdiff, preimage_comp, hpre]
  have hpb : GermIdeal.pullback (m := n) (e.symm ∘ π) (GermIdeal.pullback (m := n) e M.ideal) =
      GermIdeal.pullback (m := n) π M.ideal := by
    rw [← coherent_parameter_pullback_comp (X := CMfd.of (n := n) X)
      (Y := CMfd.of (n := n) X') (Z := CMfd.of (n := n) Z)
      e.contMDiff (e.symm.contMDiff.comp hπ) M.ideal hM]
    have heq : e ∘ (e.symm ∘ π) = π := funext fun z => e.apply_symm_apply (π z)
    rw [heq]
  have hI : GermIdeal.pullback (m := n) (e.symm ∘ π) (vanishingIdeal (n := n) (e ⁻¹' C)) =
      GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) := by
    rw [G3UniverseVanishingIdeal.pullback_vanishingIdeal_preimage e.contMDiff e.symm.contMDiff
      e.apply_symm_apply e.symm_apply_apply (e.symm.contMDiff.comp hπ) C]
    have heq : e ∘ (e.symm ∘ π) = π := funext fun z => e.apply_symm_apply (π z)
    rw [heq]
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact hgeo M.N
  · simp only [crossGeoTransform, markedPullback, List.map_map]
    congr 1
    · exact List.map_congr_left fun A _ => hgeo A
    · simp only [preimage_comp, hpre]
  · change RestrictedIdealQuotient.colonAlong n (closure ((e.symm ∘ π) ⁻¹' ((e ⁻¹' M.N) \ (e ⁻¹' C))))
      (GermIdeal.pullback (m := n) (e.symm ∘ π) (GermIdeal.pullback (m := n) e M.ideal))
      (idealPow (GermIdeal.pullback (m := n) (e.symm ∘ π) (vanishingIdeal (n := n) (e ⁻¹' C))) M.d) = _
    rw [hgeo, hpb, hI]
    rfl
  · rfl
end
end Hironaka.HironakaG3UniverseMarkedBaseTransform
