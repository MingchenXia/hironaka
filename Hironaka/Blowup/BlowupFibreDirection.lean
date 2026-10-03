/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Manifold.HolomorphicMaps
import Hironaka.Manifold.ComplexManifold
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.LiftedOpenModel
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Kernel directions of a blowup are fibre directions of the monomial charts

Let `π : Z → M` be a blowup along `C`, and let `W` be a holomorphic local inverse of the lift of
the `j`-th monomial chart near `z` (`BlowupLocalSurjectivity.exists_monomialLocalInverse`):
`σⱼ ∘ W = Φ ∘ e ∘ π` and `ℓⱼ ∘ W = id`.  Write `D` for the derivative of `W` in the preferred
chart at `z`.  If `dπ_z v = 0` then

* `fderiv_monomialInverse_ne_zero`: `D v ≠ 0` for `v ≠ 0`, since `e ∘ ℓⱼ ∘ W ∘ e⁻¹ = id`.

So `D v` is a nonzero fibre direction, along which the Blanchard weight is Fubini–Study.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupFibreDirection

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.HolomorphicMaps BlowupFlatCoordinates BlowupMonomialCharts

noncomputable section

variable {n : ℕ}

/-- The derivative of a holomorphic map in preferred charts is its manifold derivative. -/
theorem fderiv_coordinateMap_eq_mfderiv {k : ℕ} {V M : Type*}
    [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {f : V → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) (y : V)
    (w : ComplexModel k) :
    fderiv ℝ (coordinateMap f (complexChartAt (n := k) y) (complexChartAt (n := n) (f y)))
      (chartAt (ComplexModel k) y y) w =
      mfderiv 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) f y w := by
  set e := complexChartAt (n := k) y
  set d := complexChartAt (n := n) (f y)
  have hz : chartAt (ComplexModel k) y y ∈ coordinateDomain f e d := by
    refine ⟨e.val.map_source (mem_complexChartAt_source y), ?_⟩
    show f (e.val.symm (e.val y)) ∈ d.val.source
    rw [e.val.left_inv (mem_complexChartAt_source y)]
    exact mem_complexChartAt_source (f y)
  have hd : DifferentiableAt ℂ (coordinateMap f e d) (chartAt (ComplexModel k) y y) :=
    (coordinateMap_contDiffAt hf e d hz).differentiableAt (by simp)
  have hmd : MDifferentiableAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) f y :=
    (hf y).mdifferentiableAt (by simp)
  rw [hmd.mfderiv]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  change fderiv ℝ (coordinateMap f e d) (chartAt (ComplexModel k) y y) w =
    fderiv ℂ (coordinateMap f e d) (chartAt (ComplexModel k) y y) w
  rw [hd.fderiv_restrictScalars ℝ]
  rfl

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M} {y₀ : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ} {j : Fin n}
  {O : Set Z} {W : Z → ComplexModel n}

theorem differentiableAt_chart_comp {z : Z}
    (hW : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z) :
    DifferentiableAt ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ))
      (chartAt (ComplexModel n) z z) := by
  have ht : chartAt (ComplexModel n) z z ∈ (chartAt (ComplexModel n) z).target :=
    (chartAt (ComplexModel n) z).map_source (mem_chart_source _ z)
  have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
    (chart_mem_atlas (ComplexModel n) z) ht
  have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W
      ((chartAt (ComplexModel n) z).symm (chartAt (ComplexModel n) z z)) := by
    rw [(chartAt (ComplexModel n) z).left_inv (mem_chart_source _ z)]
    exact hW.mdifferentiableAt (by simp)
  exact mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)

theorem liftedOpen_extChartAt_symm (S : TopologicalSpace.Opens (ComplexModel n))
    (p : LiftedOpen.{u} S) {w : ComplexModel n} (hw : w ∈ S) :
    (extChartAt 𝓘(ℂ, ComplexModel n) p).symm w = LiftedOpen.mk S w hw := by
  have hsrc : LiftedOpen.mk S w hw ∈ (extChartAt 𝓘(ℂ, ComplexModel n) p).source := by
    trivial
  have := (extChartAt 𝓘(ℂ, ComplexModel n) p).left_inv hsrc
  rwa [LiftedOpen.extChartAt_eq, LiftedOpen.toModel_mk] at this

/-- **The derivative of the local inverse is injective.** -/
theorem fderiv_monomialInverse_ne_zero (hO : IsOpen O)
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z')
    (hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ k j)
    {ℓ : LiftedOpen.{u} (monomialDomain Φ k j) → Z}
    (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (hℓW : ∀ z' ∈ O, ∀ hw : W z' ∈ monomialDomain Φ k j, ℓ (LiftedOpen.mk _ (W z') hw) = z')
    {z : Z} (hz : z ∈ O) {v : ComplexModel n} (hv : v ≠ 0) :
    fderiv ℝ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ)) (chartAt (ComplexModel n) z z)
      v ≠ 0 := by
  classical
  have hw₀ : W z ∈ monomialDomain Φ k j := hWmem z hz
  have hζt : chartAt (ComplexModel n) z z ∈ (chartAt (ComplexModel n) z).target :=
    (chartAt (ComplexModel n) z).map_source (mem_chart_source _ z)
  have hsymm : (chartAt (ComplexModel n) z).symm (chartAt (ComplexModel n) z z) = z :=
    (chartAt (ComplexModel n) z).left_inv (mem_chart_source _ z)
  set ζ₀ := chartAt (ComplexModel n) z z
  set G := fun ζ => W ((chartAt (ComplexModel n) z).symm ζ)
  have hGζ₀ : G ζ₀ = W z := by simp only [G, hsymm]
  set ℓ' : ComplexModel n → Z := fun w =>
    if h : w ∈ monomialDomain Φ k j then ℓ (LiftedOpen.mk _ w h) else z
  have hℓp : ℓ (LiftedOpen.mk _ (W z) hw₀) = z := hℓW z hz hw₀
  have hwr : (fun w => chartAt (ComplexModel n) z (ℓ' w)) =ᶠ[𝓝 (W z)]
      writtenInExtChartAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
        (LiftedOpen.mk _ (W z) hw₀) ℓ := by
    filter_upwards [(monomialDomain Φ k j).isOpen.mem_nhds hw₀] with w hw
    simp only [writtenInExtChartAt, Function.comp_apply,
      liftedOpen_extChartAt_symm _ (LiftedOpen.mk _ (W z) hw₀) hw, hℓp, extChartAt_coe,
      modelWithCornersSelf_coe, ℓ']
    rw [dif_pos (show w ∈ monomialDomain Φ k j from hw)]
    rfl
  have hd2 : DifferentiableAt ℝ (fun w => chartAt (ComplexModel n) z (ℓ' w)) (W z) := by
    have h := (hℓs (LiftedOpen.mk _ (W z) hw₀)).mdifferentiableAt (by simp)
      |>.differentiableWithinAt_writtenInExtChartAt
    simp only [modelWithCornersSelf_coe, range_id, differentiableWithinAt_univ,
      LiftedOpen.extChartAt_eq, LiftedOpen.toModel_mk] at h
    exact (h.restrictScalars ℝ).congr_of_eventuallyEq hwr
  have hd1 : DifferentiableAt ℝ G ζ₀ := (differentiableAt_chart_comp (hWs z hz)).restrictScalars ℝ
  have hid : (fun ζ => chartAt (ComplexModel n) z (ℓ' (G ζ))) =ᶠ[𝓝 ζ₀] id := by
    have hcont : ContinuousAt (chartAt (ComplexModel n) z).symm ζ₀ :=
      (chartAt (ComplexModel n) z).continuousAt_symm hζt
    rw [← hsymm] at hz
    filter_upwards [hcont.eventually (hO.mem_nhds hz),
      (chartAt (ComplexModel n) z).open_target.mem_nhds hζt] with ζ hζ hζe
    simp only [G, ℓ', dif_pos (hWmem _ hζ), id]
    exact (congrArg _ (hℓW _ hζ _)).trans ((chartAt (ComplexModel n) z).right_inv hζe)
  have hd2' : HasFDerivAt (fun w => chartAt (ComplexModel n) z (ℓ' w))
      (fderiv ℝ (fun w => chartAt (ComplexModel n) z (ℓ' w)) (W z)) (G ζ₀) := by
    rw [hGζ₀]; exact hd2.hasFDerivAt
  have hcomp := hd2'.comp ζ₀ hd1.hasFDerivAt
  have hidd : HasFDerivAt (fun ζ => chartAt (ComplexModel n) z (ℓ' (G ζ)))
      (ContinuousLinearMap.id ℝ _) ζ₀ :=
    (hasFDerivAt_id ζ₀).congr_of_eventuallyEq hid
  have huniq := hcomp.unique hidd
  intro h0
  apply hv
  have := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
  rw [← this]
  rw [show fderiv ℝ G ζ₀ v = 0 from h0, map_zero]

end

end Hironaka.BlowupFibreDirection
