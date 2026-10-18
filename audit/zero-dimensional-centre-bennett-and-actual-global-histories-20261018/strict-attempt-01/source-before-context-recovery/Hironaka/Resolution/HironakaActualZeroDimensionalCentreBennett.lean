/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointBlowupCoordinates
import Hironaka.Resolution.HironakaActualOpenCoordinateStrictSquare
import Hironaka.Resolution.HironakaActualFlatCoordinateIntrinsicHS
import Hironaka.Resolution.HironakaActualPointGeometricBennett
import Hironaka.Resolution.HironakaActualBlowupOffCentreIntrinsicHS

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualZeroDimensionalCentreBennett
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates HironakaHolomorphicJetChartInvariance
  HironakaActualPointBlowupCoordinates HironakaActualOpenCoordinateStrictSquare
  HironakaActualFlatCoordinateIntrinsicHS HironakaActualVanishingIntrinsicHSTransport
  HironakaActualPointGeometricBennett HironakaActualAnalyticBlowupTaylor
  HironakaActualBlowupOffCentreIntrinsicHS
variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- ONLY original blowup geometry and zero-dimensional regularity give ALL intrinsic comparisons above the centre. -/
theorem hilbertSamuelAt_actual_point_centre_blowup_le {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (z : Y) (hCz : RegularAtDim (n := n) C (π z) 0)
    (W : Set X) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := n) W) (π z) ℓ := by
  obtain ⟨Φ,j,b,Θ,hΦsrc,hΦ0,hΘsrc,hΘ0,_hbj,hnormal⟩ :=
    exists_actual_point_blowup_coordinates hπ z hCz
  let DX : Opens X := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let DY : Opens Y := ⟨flatDomain Θ,isOpen_flatDomain Θ⟩
  let V : Opens (ComplexModel n) := ⟨Φ.target,Φ.isOpen_target⟩
  let U : Opens (ComplexModel n) := ⟨Θ.target,Θ.isOpen_target⟩
  let a : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ DX :=
    (actualFlatCoordinateDiffeomorph Φ hΦsrc).symm
  let c : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ DY :=
    (actualFlatCoordinateDiffeomorph Θ hΘsrc).symm
  let P := actualAnalyticBlowupMap univ j b
  have hnorm (q : U) : π (c q : Y) ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π (c q : Y)))=P q := by
    have hy := (c q).2
    have h := hnormal (c q) hy.1 hy.2
    have hc : Θ.toFun (chartAt (ComplexModel n) z (c q : Y))=(q : ComplexModel n) :=
      (flatInverse_mem Θ q.2 hΘsrc).2
    rw [hc] at h
    exact h
  have hPinto (q : U) : P q ∈ V := by
    change P q ∈ Φ.target
    rw [← (hnorm q).2]
    exact Φ.mapsTo_toFun (hnorm q).1.2
  let Q : U → V := fun q => ⟨P q,hPinto q⟩
  have hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P := by
    intro q
    apply MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt'
    exact Eventually.of_forall fun _ => (differentiable_actualAnalyticBlowupMap univ j b).differentiableAt.mdifferentiableAt
  have hQ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ Q :=
    BlowupRestrictOpen.contMDiff_opens_mk (hP.comp contMDiff_subtype_val) hPinto
  have hcomm (q : U) : π (c q : Y)=(a (Q q) : X) := by
    change π (c q : Y)=(chartAt (ComplexModel n) (π z)).symm (Φ.invFun (P q))
    rw [← (hnorm q).2]
    exact (flatInverse_flat Φ (hnorm q).1).symm
  let A : Set (ComplexModel n) := (Subtype.val : V → ComplexModel n) ''
    ((fun q : V => (a q : X)) ⁻¹' W)
  have hA : (Subtype.val : V → ComplexModel n) ⁻¹' A=(fun q : V => (a q : X)) ⁻¹' W := by
    ext q
    constructor
    · rintro ⟨r,hr,heq⟩
      have he : r=q := Subtype.ext heq
      simpa only [he] using hr
    · intro hq
      exact ⟨q,hq,rfl⟩
  have hpoint := hilbertSamuelAt_actual_geometric_point_strict_le (n := n) A j b ℓ
  have hglobal := strictTransform_actual_open_coordinate_square π Q hπ.contMDiff hQ DX DY a c hcomm W
  have hmodel := strictTransform_actual_open_coordinate_square P Q hP hQ V U
    (Diffeomorph.refl _ _ _) (Diffeomorph.refl _ _ _) (fun _ => rfl) A
  change strictTransform n Q ((Subtype.val : V → ComplexModel n) ⁻¹' A)=
    (Subtype.val : U → ComplexModel n) ⁻¹' strictTransform n P A at hmodel
  rw [hA] at hmodel
  have hstrict : (fun q : U => (c q : Y)) ⁻¹' strictTransform n π W=
      (Subtype.val : U → ComplexModel n) ⁻¹' strictTransform n P A :=
    hglobal.symm.trans hmodel
  have h0V : (0 : ComplexModel n) ∈ V := by
    have h := Φ.mapsTo_toFun Φ.center_mem_source
    rwa [hΦ0] at h
  have h0U : (0 : ComplexModel n) ∈ U := by
    have h := Θ.mapsTo_toFun Θ.center_mem_source
    rwa [hΘ0] at h
  let u0 : U := ⟨0,h0U⟩
  let v0 : V := ⟨0,h0V⟩
  have hczero : (c u0 : Y)=z := by
    change (chartAt (ComplexModel n) z).symm (Θ.invFun 0)=z
    simpa only [hΘ0] using flatInverse_flat Θ (mem_flatDomain_self Θ)
  have hazero : (a v0 : X)=π z := by
    change (chartAt (ComplexModel n) (π z)).symm (Φ.invFun 0)=π z
    simpa only [hΦ0] using flatInverse_flat Φ (mem_flatDomain_self Φ)
  have hleft := hilbertSamuelAt_vanishing_actual_flat_inverse Θ hΘsrc
    (strictTransform n π W) u0 ℓ
  change hilbertSamuelAt (vanishingIdeal (n := n) ((fun q : U => (c q : Y)) ⁻¹'
    strictTransform n π W)) u0 ℓ=hilbertSamuelAt (vanishingIdeal (n := n)
      (strictTransform n π W)) (c u0 : Y) ℓ at hleft
  rw [hczero] at hleft
  have hright := hilbertSamuelAt_vanishing_actual_flat_inverse Φ hΦsrc W v0 ℓ
  change hilbertSamuelAt (vanishingIdeal (n := n) ((fun q : V => (a q : X)) ⁻¹' W)) v0 ℓ=
    hilbertSamuelAt (vanishingIdeal (n := n) W) (a v0 : X) ℓ at hright
  rw [hazero] at hright
  calc
    _ = hilbertSamuelAt (vanishingIdeal (n := n) ((fun q : U => (c q : Y)) ⁻¹'
        strictTransform n π W)) u0 ℓ := hleft.symm
    _ = hilbertSamuelAt (vanishingIdeal (n := n) ((Subtype.val : U → ComplexModel n) ⁻¹'
        strictTransform n P A)) u0 ℓ := by rw [hstrict]
    _ = hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P A)) 0 ℓ :=
      hilbertSamuelAt_vanishing_actual_open_any U _ u0 ℓ
    _ ≤ hilbertSamuelAt (vanishingIdeal (n := n) A) 0 ℓ :=
      hpoint
    _ = hilbertSamuelAt (vanishingIdeal (n := n) ((Subtype.val : V → ComplexModel n) ⁻¹' A)) v0 ℓ :=
      (hilbertSamuelAt_vanishing_actual_open_any V A v0 ℓ).symm
    _ = hilbertSamuelAt (vanishingIdeal (n := n) ((fun q : V => (a q : X)) ⁻¹' W)) v0 ℓ := by rw [hA]
    _ = _ := hright

/-- Actual zero-dimensional smooth centres give all-point all-order original intrinsic Bennett. -/
theorem hilbertSamuelAt_actual_zero_dimensional_centre_blowup_le {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hC : ∀ x ∈ C, RegularAtDim (n := n) C x 0)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (z : Y) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := n) W) (π z) ℓ := by
  by_cases hz : π z ∈ C
  · exact hilbertSamuelAt_actual_point_centre_blowup_le hπ z (hC _ hz) W ℓ
  · exact (hilbertSamuelAt_actual_strict_blowup_off_centre
      (X := BlowupTowers.CMfd.of X) (Y := BlowupTowers.CMfd.of Y) hπ hW z hz ℓ).le

end
end Hironaka.HironakaActualZeroDimensionalCentreBennett
