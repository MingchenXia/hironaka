/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualSmoothCentreBlowupCoordinates
import Hironaka.Resolution.HironakaActualNormalBlowupExceptionalLocus
import Hironaka.Resolution.HironakaActualZeroDimensionalCentreBennett

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualHypersurfaceCentreBennett
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates HironakaHolomorphicJetChartInvariance
  HironakaActualSmoothCentreBlowupCoordinates HironakaActualOpenCoordinateStrictSquare
  HironakaActualFlatCoordinateIntrinsicHS HironakaActualVanishingIntrinsicHSTransport
  HironakaActualPointGeometricBennett HironakaActualAnalyticBlowupTaylor
  HironakaActualBlowupOffCentreIntrinsicHS HironakaActualNormalBlowupExceptionalLocus
  HironakaActualCoefficientPresentationCentrePower HironakaActualZeroDimensionalCentreBennett

section Hypersurface
variable {d : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (d+1)) X] [IsComplexManifold (d+1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+1)) Y] [IsComplexManifold (d+1) Y]

/-- ONLY the original full blowup and true hypersurface-centre regularity preserve EVERY original intrinsic HS value. -/
theorem hilbertSamuelAt_actual_hypersurface_centre_blowup_eq {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong (d+1) C π) (z : Y) (hCz : RegularAtDim (n := d+1) C (π z) d)
    (W : Set X) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := d+1) (strictTransform (d+1) π W)) z ℓ=
      hilbertSamuelAt (vanishingIdeal (n := d+1) W) (π z) ℓ := by
  obtain ⟨Φ,j,b,Θ,hΦsrc,hΦ0,_hflat,hΘsrc,hΘ0,hj,_hbt,_hbj,hnormal⟩ :=
    exists_actual_smooth_centre_blowup_coordinates hπ z d hCz
  let DX : Opens X := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let DY : Opens Y := ⟨flatDomain Θ,isOpen_flatDomain Θ⟩
  let V : Opens (ComplexModel (d+1)) := ⟨Φ.target,Φ.isOpen_target⟩
  let U : Opens (ComplexModel (d+1)) := ⟨Θ.target,Θ.isOpen_target⟩
  let a : V ≃ₘ⟮𝓘(ℂ,ComplexModel (d+1)),𝓘(ℂ,ComplexModel (d+1))⟯ DX :=
    (actualFlatCoordinateDiffeomorph Φ hΦsrc).symm
  let c : U ≃ₘ⟮𝓘(ℂ,ComplexModel (d+1)),𝓘(ℂ,ComplexModel (d+1))⟯ DY :=
    (actualFlatCoordinateDiffeomorph Θ hΘsrc).symm
  let P := actualAnalyticBlowupMap {i : Fin (d+1) | d ≤ i.val} j b
  have hnorm (q : U) : π (c q : Y) ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel (d+1)) (π z) (π (c q : Y)))=P q := by
    have hy := (c q).2
    have h := hnormal (c q) hy.1 hy.2
    have hc : Θ.toFun (chartAt (ComplexModel (d+1)) z (c q : Y))=(q : ComplexModel (d+1)) :=
      (flatInverse_mem Θ q.2 hΘsrc).2
    rw [hc] at h
    exact h
  have hPinto (q : U) : P q ∈ V := by
    change P q ∈ Φ.target
    rw [← (hnorm q).2]
    exact Φ.mapsTo_toFun (hnorm q).1.2
  let Q : U → V := fun q => ⟨P q,hPinto q⟩
  have hP : ContMDiff 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel (d+1)) ∞ P := by
    intro q
    apply MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt'
    exact Eventually.of_forall fun _ => (differentiable_actualAnalyticBlowupMap {i : Fin (d+1) | d ≤ i.val} j b).differentiableAt.mdifferentiableAt
  have hQ : ContMDiff 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel (d+1)) ∞ Q :=
    BlowupRestrictOpen.contMDiff_opens_mk (hP.comp contMDiff_subtype_val) hPinto
  have hcomm (q : U) : π (c q : Y)=(a (Q q) : X) := by
    change π (c q : Y)=(chartAt (ComplexModel (d+1)) (π z)).symm (Φ.invFun (P q))
    rw [← (hnorm q).2]
    exact (flatInverse_flat Φ (hnorm q).1).symm
  let A : Set (ComplexModel (d+1)) := (Subtype.val : V → ComplexModel (d+1)) ''
    ((fun q : V => (a q : X)) ⁻¹' W)
  have hA : (Subtype.val : V → ComplexModel (d+1)) ⁻¹' A=(fun q : V => (a q : X)) ⁻¹' W := by
    ext q
    constructor
    · rintro ⟨r,hr,heq⟩
      have he : r=q := Subtype.ext heq
      simpa only [he] using hr
    · intro hq
      exact ⟨q,hq,rfl⟩
  have hnormalset : {i : Fin (d+1) | d ≤ i.val}=actualTangentCentreVariables d 1 := by
    ext i
    constructor
    · intro hi
      change d ≤ i.val at hi
      have hilt := i.isLt
      refine ⟨(0 : Fin 1),Fin.ext ?_⟩
      simp only [Fin.val_natAdd,Fin.val_zero]
      omega
    · rintro ⟨i,rfl⟩
      change d ≤ (i.natAdd d).val
      simp only [Fin.val_natAdd]
      omega
  have hpivot : j=(0 : Fin 1).natAdd d := by
    apply Fin.ext
    simp only [Fin.val_natAdd,Fin.val_zero]
    have hjlt := j.isLt
    omega
  have hpoint : hilbertSamuelAt (vanishingIdeal (n := d+1) (strictTransform (d+1) P A)) 0 ℓ=
      hilbertSamuelAt (vanishingIdeal (n := d+1) A) 0 ℓ := by
    dsimp only [P]
    rw [hnormalset,hpivot]
    exact hilbertSamuelAt_actual_normal_blowup_one d 0 b A ℓ
  have hglobal := strictTransform_actual_open_coordinate_square π Q hπ.contMDiff hQ DX DY a c hcomm W
  have hmodel := strictTransform_actual_open_coordinate_square P Q hP hQ V U
    (Diffeomorph.refl _ _ _) (Diffeomorph.refl _ _ _) (fun _ => rfl) A
  change strictTransform (d+1) Q ((Subtype.val : V → ComplexModel (d+1)) ⁻¹' A)=
    (Subtype.val : U → ComplexModel (d+1)) ⁻¹' strictTransform (d+1) P A at hmodel
  rw [hA] at hmodel
  have hstrict : (fun q : U => (c q : Y)) ⁻¹' strictTransform (d+1) π W=
      (Subtype.val : U → ComplexModel (d+1)) ⁻¹' strictTransform (d+1) P A :=
    hglobal.symm.trans hmodel
  have h0V : (0 : ComplexModel (d+1)) ∈ V := by
    have h := Φ.mapsTo_toFun Φ.center_mem_source
    rwa [hΦ0] at h
  have h0U : (0 : ComplexModel (d+1)) ∈ U := by
    have h := Θ.mapsTo_toFun Θ.center_mem_source
    rwa [hΘ0] at h
  let u0 : U := ⟨0,h0U⟩
  let v0 : V := ⟨0,h0V⟩
  have hczero : (c u0 : Y)=z := by
    change (chartAt (ComplexModel (d+1)) z).symm (Θ.invFun 0)=z
    simpa only [hΘ0] using flatInverse_flat Θ (mem_flatDomain_self Θ)
  have hazero : (a v0 : X)=π z := by
    change (chartAt (ComplexModel (d+1)) (π z)).symm (Φ.invFun 0)=π z
    simpa only [hΦ0] using flatInverse_flat Φ (mem_flatDomain_self Φ)
  have hleft := hilbertSamuelAt_vanishing_actual_flat_inverse Θ hΘsrc
    (strictTransform (d+1) π W) u0 ℓ
  change hilbertSamuelAt (vanishingIdeal (n := d+1) ((fun q : U => (c q : Y)) ⁻¹'
    strictTransform (d+1) π W)) u0 ℓ=hilbertSamuelAt (vanishingIdeal (n := d+1)
      (strictTransform (d+1) π W)) (c u0 : Y) ℓ at hleft
  rw [hczero] at hleft
  have hright := hilbertSamuelAt_vanishing_actual_flat_inverse Φ hΦsrc W v0 ℓ
  change hilbertSamuelAt (vanishingIdeal (n := d+1) ((fun q : V => (a q : X)) ⁻¹' W)) v0 ℓ=
    hilbertSamuelAt (vanishingIdeal (n := d+1) W) (a v0 : X) ℓ at hright
  rw [hazero] at hright
  calc
    _ = hilbertSamuelAt (vanishingIdeal (n := d+1) ((fun q : U => (c q : Y)) ⁻¹'
        strictTransform (d+1) π W)) u0 ℓ := hleft.symm
    _ = hilbertSamuelAt (vanishingIdeal (n := d+1) ((Subtype.val : U → ComplexModel (d+1)) ⁻¹'
        strictTransform (d+1) P A)) u0 ℓ := by rw [hstrict]
    _ = hilbertSamuelAt (vanishingIdeal (n := d+1) (strictTransform (d+1) P A)) 0 ℓ :=
      hilbertSamuelAt_vanishing_actual_open_any U _ u0 ℓ
    _ = hilbertSamuelAt (vanishingIdeal (n := d+1) A) 0 ℓ :=
      hpoint
    _ = hilbertSamuelAt (vanishingIdeal (n := d+1) ((Subtype.val : V → ComplexModel (d+1)) ⁻¹' A)) v0 ℓ :=
      (hilbertSamuelAt_vanishing_actual_open_any V A v0 ℓ).symm
    _ = hilbertSamuelAt (vanishingIdeal (n := d+1) ((fun q : V => (a q : X)) ⁻¹' W)) v0 ℓ := by rw [hA]
    _ = _ := hright

end Hypersurface
section Surface
variable {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X] [IsComplexManifold 2 X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel 2) Y] [IsComplexManifold 2 Y]

/-- The original full surface blowup alone gives ALL-point ALL-order original Bennett, without a compatibility certificate. -/
theorem hilbertSamuelAt_actual_surface_blowup_le {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong 2 C π) (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (z : Y) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := 2) (strictTransform 2 π W)) z ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := 2) W) (π z) ℓ := by
  by_cases hz : π z ∈ C
  · obtain ⟨k,hk⟩ := hπ.1.2 (π z) hz
    by_cases hk0 : k=0
    · subst k
      exact hilbertSamuelAt_actual_point_centre_blowup_le hπ z hk W ℓ
    · by_cases hk1 : k=1
      · subst k
        exact (hilbertSamuelAt_actual_hypersurface_centre_blowup_eq (d := 1) hπ z hk W ℓ).le
      · obtain ⟨Φ,j,b,Θ,_,_,_,_,_,hj,_⟩ :=
          exists_actual_smooth_centre_blowup_coordinates hπ z k hk
        have hjlt := j.isLt
        omega
  · exact (hilbertSamuelAt_actual_strict_blowup_off_centre
      (X := BlowupTowers.CMfd.of X) (Y := BlowupTowers.CMfd.of Y) hπ hW z hz ℓ).le

end Surface
end
end Hironaka.HironakaActualHypersurfaceCentreBennett
