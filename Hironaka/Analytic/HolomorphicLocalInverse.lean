/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Manifold.HolomorphicMapsContDiffOn
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HolomorphicLocalInverse

open Hironaka
noncomputable section

open HolomorphicMaps BlowupSequences
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **Local holomorphic inverse at an unramified point.** -/
theorem exists_localInverse {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {z : Z}
    (hz : z ∉ exceptionalLocus n g) :
    ∃ (V : Set Y) (s : Y → Z), IsOpen V ∧ g z ∈ V ∧ s (g z) = z ∧
      (∀ y ∈ V, g (s y) = y) ∧
      (∀ y ∈ V, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s y) ∧
      ∀ᶠ z' in 𝓝 z, s (g z') = z' := by
  classical
  set e := complexChartAt (n := n) z
  set d := complexChartAt (n := n) (g z)
  set p := e.val z
  set F := coordinateMap g e d
  set D := coordinateDomain g e d
  have hD : IsOpen D := coordinateDomain_isOpen hg e d
  have hze : z ∈ e.val.source := mem_complexChartAt_source z
  have hpD : p ∈ D := ⟨e.val.map_source hze, by
    show g (e.val.symm (e.val z)) ∈ d.val.source
    rw [e.val.left_inv hze]; exact mem_complexChartAt_source _⟩
  have hFs : ContDiffOn ℂ ∞ F D := coordinateMap_contDiffOn hg e d
  have hFd : ∀ w ∈ D, DifferentiableAt ℂ F w := fun w hw =>
    (hFs.contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp)
  -- the derivative is invertible at `p`
  have hbij : Function.Bijective (fderiv ℂ F p) := by
    have hmd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g z :=
      (hg z).mdifferentiableAt (by simp)
    have h1 := BlowupFibreDirection.fderiv_coordinateMap_eq_mfderiv hg z
    have hz' := hz
    simp only [exceptionalLocus, mem_ofPred_eq, not_not] at hz'
    have heq : ∀ v, fderiv ℂ F p v = mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g z v :=
      fun v => by
        rw [← h1 v]
        change (fderiv ℂ F p) v = (fderiv ℝ F p) v
        rw [(hFd p hpD).fderiv_restrictScalars ℝ]; rfl
    have hfun : ⇑(fderiv ℂ F p) = ⇑(mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g z) :=
      funext heq
    rw [hfun]; exact hz'
  set Lp : ComplexModel n ≃L[ℂ] ComplexModel n :=
    (LinearEquiv.ofBijective (fderiv ℂ F p).toLinearMap hbij).toContinuousLinearEquiv
  have hstrict : HasStrictFDerivAt F (Lp : ComplexModel n →L[ℂ] ComplexModel n) p := by
    have h := (hFs.contDiffAt (hD.mem_nhds hpD)).hasStrictFDerivAt (by simp)
    have hLp : (Lp : ComplexModel n →L[ℂ] ComplexModel n) = fderiv ℂ F p :=
      ContinuousLinearMap.ext fun v => rfl
    rw [hLp]; exact h
  set Φ := hstrict.toOpenPartialHomeomorph F
  have hΦcoe : ⇑Φ = F := rfl
  have hpΦ : p ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  -- points where the derivative is invertible
  set G : Set (ComplexModel n) :=
    D ∩ (fun w => fderiv ℂ F w) ⁻¹' range ((↑) : (ComplexModel n ≃L[ℂ] ComplexModel n) →
      ComplexModel n →L[ℂ] ComplexModel n)
  have hG : IsOpen G :=
    (hFs.continuousOn_fderiv_of_isOpen hD (by simp)).isOpen_inter_preimage hD
      ContinuousLinearEquiv.isOpen
  have hpG : p ∈ G := ⟨hpD, ⟨Lp, rfl⟩⟩
  set V : Set Y := d.val.source ∩ d.val ⁻¹' (Φ.target ∩ Φ.symm ⁻¹' (G ∩ Φ.source))
  have hV : IsOpen V := d.val.isOpen_inter_preimage (Φ.isOpen_inter_preimage_symm (hG.inter Φ.open_source))
  set s : Y → Z := fun y => e.val.symm (Φ.symm (d.val y))
  have hFp : F p = d.val (g z) := by
    show d.val (g (e.val.symm (e.val z))) = _
    rw [e.val.left_inv hze]
  have hgzd : g z ∈ d.val.source := mem_complexChartAt_source _
  have hsym : Φ.symm (d.val (g z)) = p := by rw [← hFp, ← hΦcoe, Φ.left_inv hpΦ]
  refine ⟨V, s, hV, ⟨hgzd, ?_, ?_⟩, ?_, fun y hy => ?_, fun y hy => ?_, ?_⟩
  · rw [← hFp]; exact Φ.map_source hpΦ
  · rw [mem_preimage, hsym]; exact ⟨hpG, hpΦ⟩
  · show e.val.symm (Φ.symm (d.val (g z))) = z
    rw [hsym, e.val.left_inv hze]
  · -- `g ∘ s = id` on `V`
    obtain ⟨hyd, hyt, ⟨hwG, -⟩⟩ := hy
    set w := Φ.symm (d.val y)
    have hFw : F w = d.val y := by rw [← hΦcoe]; exact Φ.right_inv hyt
    have hwd : g (e.val.symm w) ∈ d.val.source := hwG.1.2
    exact d.val.injOn hwd hyd hFw
  · -- smoothness of `s`
    obtain ⟨hyd, hyt, ⟨hwG, hwΦ⟩⟩ := hy
    set w := Φ.symm (d.val y)
    obtain ⟨Lw, hLw⟩ := hwG.2
    have hΦs : ContDiffAt ℂ ∞ Φ.symm (d.val y) := by
      refine Φ.contDiffAt_symm hyt (f₀' := Lw) ?_ ?_
      · rw [hΦcoe]
        have hLw' : (Lw : ComplexModel n →L[ℂ] ComplexModel n) = fderiv ℂ F w := hLw
        rw [hLw']
        exact (hFd w hwG.1).hasFDerivAt
      · rw [hΦcoe]; exact hFs.contDiffAt (hD.mem_nhds hwG.1)
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ d.val y :=
      (contMDiffOn_chart (n := ∞)).contMDiffAt (d.val.open_source.mem_nhds hyd)
    have h3 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.val.symm w :=
      (contMDiffOn_chart_symm (n := ∞)).contMDiffAt (e.val.open_target.mem_nhds hwG.1.1)
    exact h3.comp y (hΦs.contMDiffAt.comp y h1)
  · -- `s ∘ g = id` near `z`
    have hcont : ContinuousAt (fun z' => e.val z') z := e.val.continuousAt hze
    filter_upwards [e.val.open_source.mem_nhds hze, hcont.eventually (Φ.open_source.mem_nhds hpΦ)]
      with z' hz'e hz'Φ
    show e.val.symm (Φ.symm (d.val (g z'))) = z'
    have hFz' : F (e.val z') = d.val (g z') := by
      show d.val (g (e.val.symm (e.val z'))) = _
      rw [e.val.left_inv hz'e]
    rw [← hFz', ← hΦcoe, Φ.left_inv hz'Φ, e.val.left_inv hz'e]


end
end Hironaka.HolomorphicLocalInverse
