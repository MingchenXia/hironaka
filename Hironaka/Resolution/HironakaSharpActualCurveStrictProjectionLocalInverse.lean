/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFirstAmbientStrictExponent

/-! Genuine local inverse ALONG actual smooth curve carriers above a discrete
blowup centre. No ambient exceptional inverse or order certificate is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveStrictProjectionLocalInverse
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupStrictSubmanifold
  NestedFlattening PositiveDimensionalComponent
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Literal genuine monomial map on the actual one-dimensional carrier plane. -/
theorem actual_monomial_on_curve_plane_eq_self (j : Fin n) (hj : j.1 < 1)
    {w : ComplexModel n} (hw : w ∈ complexCoordinatePlane n 1) : monomial 0 j w=w := by
  ext i
  rw [monomial_apply]
  split_ifs with h
  · have hi : 1 ≤ i.1 := by
      by_contra hne
      have he : i=j := Fin.ext (by omega)
      exact h.2 he
    rw [hw i hi,zero_mul]
  · rfl

/-- Actual nested C0/N1 flattening and the real monomial lift give a genuine
holomorphic inverse ALONG both actual carriers, including above the centre. -/
theorem exists_actual_curve_strict_projection_local_inverse
    {N C : Set X} (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x 1)
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    {z : Y} (hz : z ∈ geoStrictTransform π C N) (hzC : π z ∈ C) :
    ∃ s : X → Y,ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ s (π z) ∧
      s (π z)=z ∧
      (∀ᶠ x in 𝓝 (π z),x ∈ N → s x ∈ geoStrictTransform π C N ∧ π (s x)=x) ∧
      ∀ᶠ y in 𝓝 z,y ∈ geoStrictTransform π C N → s (π y)=y := by
  have hzN : π z ∈ N := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz
  obtain ⟨Φ,hΦt,hΦ0,hflat⟩ := exists_nested_flattening (show 0≤1 by omega) (hrC _ hzC) (hrN _ hzN) hCN
  have hflatC : ∀ {x : X},x ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) x ∈ Φ.source →
      (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) x) ∈ complexCoordinatePlane n 0) :=
    fun hx hΦ => (hflat hx hΦ).1
  have hflatN : ∀ {x : X},x ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) x ∈ Φ.source →
      (x ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) x) ∈ complexCoordinatePlane n 1) :=
    fun hx hΦ => (hflat hx hΦ).2
  obtain ⟨j,_hj,O,hO,hzO,W,hWs,hWmem,hℓW,hiff⟩ :=
    exists_local_geoStrictTransform hπ hΦt hflatC hflatN (mem_flatDomain_self Φ)
  obtain ⟨hjN,_hWz⟩ := (hiff z hzO).mp hz
  obtain ⟨ℓ,⟨hℓs,hℓπ⟩,_hℓunique⟩ := existsUnique_monomialLift hπ hΦt hflatC (show 0 ≤ j.1 by omega)
  let F : X → ComplexModel n := fun x => Φ.toFun (chartAt (ComplexModel n) (π z) x)
  have hWF : ∀ y ∈ O,y ∈ geoStrictTransform π C N → W y=F (π y) := by
    intro y hy hyN
    have hwP := (hiff y hy).mp hyN |>.2
    let p := LiftedOpen.mk (monomialDomain Φ 0 j) (W y) (hWmem y hy)
    have hπy : π y=monomialChart Φ 0 j p := by
      rw [←hℓW ℓ hℓs hℓπ y hy (hWmem y hy)]
      exact congrFun hℓπ p
    ext i
    change W y i=flatCoord Φ i (π y)
    rw [hπy,flatCoord_monomialChart hΦt p i]
    exact congrArg (fun v : ComplexModel n => v i) (actual_monomial_on_curve_plane_eq_self j hjN hwP).symm
  have hF0 : F (π z)=0 := hΦ0
  have hW0 : W z=0 := (hWF z hzO hz).trans hF0
  let D := monomialDomain Φ 0 j
  have h0D : (0 : ComplexModel n) ∈ D := by simpa only [hW0] using hWmem z hzO
  let p0 : LiftedOpen.{u} D := LiftedOpen.mk D 0 h0D
  let G : ComplexModel n → LiftedOpen.{u} D := fun w => if h : w ∈ D then LiftedOpen.mk D w h else p0
  have hG0 : G 0=p0 := by simp only [G,dif_pos h0D]; rfl
  have hG : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ G 0 := by
    apply LiftedOpen.contMDiffAt_of_toModel
    have heq : (LiftedOpen.toModel D ∘ G)=ᶠ[𝓝 0] id := by
      filter_upwards [D.isOpen.mem_nhds h0D] with w hw
      change LiftedOpen.toModel D (G w)=w
      dsimp only [G]
      rw [dif_pos (show w ∈ D from hw)]
      rfl
    exact contMDiffAt_id.congr_of_eventuallyEq heq
  have hF : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ F (π z) :=
    (contDiffAt_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source Φ.center_mem_source).contMDiffAt.comp _
      ((contMDiffOn_chart (n := ∞)).contMDiffAt ((chartAt (ComplexModel n) (π z)).open_source.mem_nhds (mem_chart_source _ _)))
  let s : X → Y := ℓ ∘ G ∘ F
  have hs : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ s (π z) := by
    have hGF := hG
    rw [←hF0] at hGF
    have hcGF : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (G ∘ F) (π z) := hGF.comp _ hF
    exact (hℓs (G (F (π z)))).comp (π z) hcGF
  have hs0 : s (π z)=z := by
    change ℓ (G (F (π z)))=z
    rw [hF0,hG0]
    have h := hℓW ℓ hℓs hℓπ z hzO (hWmem z hzO)
    simpa only [hW0] using h
  have hFD : ∀ᶠ x in 𝓝 (π z),F x ∈ D := by
    have hFD0 : F (π z) ∈ D := by rw [hF0]; exact h0D
    exact hF.continuousAt.eventually (D.isOpen.mem_nhds hFD0)
  have hπs : ∀ᶠ x in 𝓝 (π z),x ∈ N → π (s x)=x := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ),hFD] with x hx hxD hxN
    change π (ℓ (G (F x)))=x
    dsimp only [G]
    rw [dif_pos hxD]
    have h := congrFun hℓπ (LiftedOpen.mk D (F x) hxD)
    change π (ℓ (LiftedOpen.mk D (F x) hxD))=monomialChart Φ 0 j (LiftedOpen.mk D (F x) hxD) at h
    rw [h]
    change (chartAt (ComplexModel n) (π z)).symm (Φ.invFun (monomial 0 j (F x)))=x
    rw [actual_monomial_on_curve_plane_eq_self j hjN ((hflatN hx.1 hx.2).mp hxN)]
    exact flatInverse_flat Φ hx
  obtain ⟨U,hU,hxU,hUC⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero (hrC _ hzC)
  have hsN : ∀ᶠ x in 𝓝 (π z),x ∈ N → s x ∈ geoStrictTransform π C N ∧ π (s x)=x := by
    filter_upwards [hπs,hU.mem_nhds hxU] with x hx hxU' hxN
    have hπx := hx hxN
    refine ⟨?_,hπx⟩
    by_cases hxC : x ∈ C
    · have he : x=π z := hUC ⟨hxC,hxU'⟩
      simpa only [he,hs0] using hz
    · have hsC : π (s x) ∉ C := by rw [hπx]; exact hxC
      have hsN : π (s x) ∈ N := by rw [hπx]; exact hxN
      exact (mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hN.1 hsC).mpr hsN
  refine ⟨s,hs,hs0,hsN,?_⟩
  filter_upwards [hO.mem_nhds hzO] with y hy hyN
  have hwF := hWF y hy hyN
  change ℓ (G (F (π y)))=y
  rw [←hwF]
  dsimp only [G]
  rw [dif_pos (hWmem y hy)]
  exact hℓW ℓ hℓs hℓπ y hy (hWmem y hy)

end
end Hironaka.HironakaSharpActualCurveStrictProjectionLocalInverse
