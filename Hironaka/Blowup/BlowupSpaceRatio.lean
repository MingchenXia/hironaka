/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSpace
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupSpaceTangent
import Hironaka.Analytic.CoordinatePlaneDivision
import Hironaka.Analytic.HolomorphicGermAlgebra
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Extended quotients are holomorphic in the monomial charts

Source: Demailly, *Complex analytic and differential geometry*, VII.12.2 (`agbook.tex` lines 20306--20326).

Third module of the construction of the blowup. Demailly's key observation: if `g` vanishes on the centre,
Hadamard's lemma writes `g = ∑ zₖ Aₖ`, so `(g/zⱼ)~` is, in the coordinates `w` of the chart `τ̃ⱼ`, the holomorphic
function `Aⱼ(σⱼ w) + ∑_{k ≠ j} wₖ Aₖ(σⱼ w)`; hence every extended quotient `(f/g)~ = (f/zⱼ)~ / (g/zⱼ)~` is
holomorphic where `(g/zⱼ)~ ≠ 0`, and the coordinate changes of the blowup are holomorphic.

* `FlatChart.ratio c f w = extVal f (τ̃ⱼ⁻¹ w) / extVal τⱼ (τ̃ⱼ⁻¹ w)`, the function `(f/τⱼ)~` read in
  the chart;
* `FlatChart.ratio_of_ne` (off the exceptional divisor it is `f(x) / wⱼ`) and `FlatChart.ratio_of_eq`
  (on it, `d_xf(ξ_w)`);
* `FlatChart.differentiableAt_ratio`: **if `f` is holomorphic on an open set `V` and vanishes on
  `C ∩ V`, then `ratio c f` is holomorphic at every point of the target whose base lies in `V`.**
  On the exceptional divisor the two expressions are matched by one Hadamard formula
  `∑ᵢ vᵢ(w) Hᵢ(σⱼ w)`, using the chain rule `germDiff_flatVec` of `BlowupSpaceTangent`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupConstruction

open Hironaka.HolomorphicIdealSheaves BlowupFlatCoordinates BlowupMonomialCharts BlowupSpaceTangent

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {C : Set X}

namespace FlatChart

variable (c : FlatChart n C)

/-- `(f/τⱼ)~` read in the chart `τ̃ⱼ`. -/
def ratio (f : X → ℂ) (w : ComplexModel n) : ℂ :=
  extVal f (c.invFun w) / extVal (c.τ c.j) (c.invFun w)

/-- The flat representative `f ∘ e₀⁻¹ ∘ Φ⁻¹` of `f`. -/
def flatRep (f : X → ℂ) (u : ComplexModel n) : ℂ :=
  f ((chartAt (ComplexModel n) c.y₀).symm (c.Φ.invFun u))

theorem flatRep_monomial (f : X → ℂ) (w : ComplexModel n) :
    c.flatRep f (monomial c.k c.j w) = f (c.pt w) := rfl

theorem monomial_apply_j (w : ComplexModel n) : monomial c.k c.j w c.j = w c.j :=
  c.monomial_apply_of_not fun h => h.2 rfl

theorem ratio_of_ne {f : X → ℂ} {w : ComplexModel n} (hw : w ∈ c.target) (hj : w c.j ≠ 0) :
    c.ratio f w = f (c.pt w) / w c.j := by
  have hx : c.pt w ∉ C := fun h => hj ((c.pt_mem_iff hw).mp h)
  rw [ratio, c.invFun_of_ne hw hj, extVal_of_not_mem hx, extVal_of_not_mem hx]
  show f (c.pt w) / c.τ c.j (c.pt w) = _
  rw [c.τ_pt hw, c.monomial_apply_j]

theorem ratio_of_eq {f : X → ℂ} {w : ComplexModel n} (hw : w ∈ c.target) (hj : w c.j = 0)
    (hf : (vanishingIdeal (n := n) C).mem (c.pt w) f) :
    c.ratio f w = germDiff n f (c.pt w) (flatVec c.Φ (c.pt w) (c.normalVec w)) := by
  have hx := (c.pt_mem_iff hw).mpr hj
  obtain ⟨a, ha, hext⟩ := exists_extVal_excPoint_eq_mul (C := C) hx
    (c.flatVec_normalVec_not_mem hw hj)
  rw [ratio, c.invFun_of_eq hw hj, hext _ hf, hext _ (c.τ_mem_vanishingIdeal (c.pt_mem_dom hw) c.hj),
    germDiff_flatCoord_flatVec c.hsrc (c.pt_mem_dom hw), normalVec_j, mul_one]
  field_simp

theorem differentiableAt_flatRep {f : X → ℂ} {u : ComplexModel n} (hu : u ∈ c.Φ.target)
    (hf : HolomorphicAt n f ((chartAt (ComplexModel n) c.y₀).symm (c.Φ.invFun u))) :
    DifferentiableAt ℂ (c.flatRep f) u := by
  have h1 : DifferentiableAt ℂ (f ∘ (chartAt (ComplexModel n) c.y₀).symm) (c.Φ.invFun u) :=
    differentiableAt_comp_chart_symm (c.hsrc (c.Φ.mapsTo_invFun hu)) hf.mdifferentiableAt
  exact h1.comp u (c.Φ.invFun_holomorphic.differentiableAt (c.Φ.isOpen_target.mem_nhds hu))

theorem differentiableAt_comp_pt {f : X → ℂ} {w : ComplexModel n} (hw : w ∈ c.target)
    (hf : HolomorphicAt n f (c.pt w)) : DifferentiableAt ℂ (fun w' => f (c.pt w')) w :=
  (c.differentiableAt_flatRep hw hf).comp w ((contDiff_monomial c.k c.j).differentiable (by simp) w)

theorem continuousAt_pt {w : ComplexModel n} (hw : w ∈ c.target) :
    Tendsto c.pt (𝓝 w) (𝓝 (c.pt w)) := by
  have h := tendsto_flatInverse c.Φ (c.pt_mem_dom hw)
  rw [c.flat_pt hw] at h
  exact h.comp ((contDiff_monomial c.k c.j).continuous.tendsto w)

/-- The Hadamard expression `∑ᵢ vᵢ(w) Hᵢ(σⱼ w)`. -/
def hadamardExpr (H : Fin n → ComplexModel n → ℂ) (w : ComplexModel n) : ℂ :=
  ∑ i, c.normalVec w i * H i (monomial c.k c.j w)

theorem normalVec_apply (w : ComplexModel n) (i : Fin n) :
    c.normalVec w i = if i = c.j then 1 else if c.k ≤ i.1 then w i else 0 := by
  simp [normalVec]

/-- `σⱼ(w)ᵢ Hᵢ = wⱼ vᵢ(w) Hᵢ` for every `i`, when the tangential `Hᵢ` vanish. -/
theorem monomial_mul_eq {H : Fin n → ComplexModel n → ℂ} (hH0 : ∀ i : Fin n, i.1 < c.k → H i = 0)
    (w u : ComplexModel n) (i : Fin n) :
    monomial c.k c.j w i * H i u = w c.j * (c.normalVec w i * H i u) := by
  rw [monomial_apply, c.normalVec_apply]
  by_cases hij : i = c.j
  · subst hij; simp
  · by_cases hi : c.k ≤ i.1
    · rw [if_pos ⟨hi, hij⟩, if_neg hij, if_pos hi]; ring
    · rw [hH0 i (by omega)]; simp

/-- The derivative of `∑ uᵢ Hᵢ(u)` at a point of the plane, in a direction `v`. -/
theorem fderiv_sum_coord_mul {H : Fin n → ComplexModel n → ℂ}
    (hH0 : ∀ i : Fin n, i.1 < c.k → H i = 0) {u : ComplexModel n}
    (hu : ∀ i : Fin n, c.k ≤ i.1 → u i = 0) (hHd : ∀ i, DifferentiableAt ℂ (H i) u)
    (v : ComplexModel n) :
    fderiv ℂ (fun u' : ComplexModel n => ∑ i, u' i * H i u') u v = ∑ i, v i * H i u := by
  have hproj : ∀ i : Fin n, DifferentiableAt ℂ (fun u' : ComplexModel n => u' i) u := fun i =>
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hsum : (fun u' : ComplexModel n => ∑ i, u' i * H i u') =
      ∑ i, (fun u' : ComplexModel n => u' i * H i u') := by
    funext u'; simp [Finset.sum_apply]
  rw [hsum, fderiv_sum (A := fun i (u' : ComplexModel n) => u' i * H i u')
    fun i _ => (hproj i).fun_mul (hHd i)]
  simp only [_root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_fun_mul (hproj i) (hHd i)]
  have hpi : fderiv ℂ (fun u' : ComplexModel n => u' i) u =
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ) :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).fderiv
  rw [hpi]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  by_cases hi : c.k ≤ i.1
  · rw [hu i hi]; simp [mul_comm]
  · have h0 : H i = 0 := hH0 i (by omega)
    have hd : fderiv ℂ (H i) u = 0 := by rw [h0]; exact fderiv_const_apply 0
    rw [hd, h0]; simp

/-- **Demailly's lemma (VII.12.2).**  If `f` is holomorphic on the open set `V` and vanishes on
`C ∩ V`, then `(f/τⱼ)~` is holomorphic, in the coordinates of `τ̃ⱼ`, at every point `w₀` of the
target with `π(τ̃ⱼ⁻¹ w₀) ∈ V`. -/
theorem differentiableAt_ratio {V : Set X} {f : X → ℂ}
    (hfV : ∀ x ∈ V, (vanishingIdeal (n := n) C).mem x f) (hV : IsOpen V)
    {w₀ : ComplexModel n} (hw₀ : w₀ ∈ c.target) (hV₀ : c.pt w₀ ∈ V) :
    DifferentiableAt ℂ (c.ratio f) w₀ := by
  have hpt : ∀ᶠ w in 𝓝 w₀, w ∈ c.target ∧ c.pt w ∈ V :=
    (c.isOpen_target.eventually_mem hw₀).and ((c.continuousAt_pt hw₀).eventually (hV.mem_nhds hV₀))
  have hpj : DifferentiableAt ℂ (fun w : ComplexModel n => w c.j) w₀ :=
    (EuclideanSpace.proj c.j : ComplexModel n →L[ℂ] ℂ).differentiableAt
  by_cases hj₀ : w₀ c.j = 0
  swap
  · -- off the exceptional divisor: `f(x) / wⱼ`
    have hev : c.ratio f =ᶠ[𝓝 w₀] fun w => f (c.pt w) * (w c.j)⁻¹ := by
      filter_upwards [hpt, hpj.continuousAt.eventually (isOpen_ne.mem_nhds hj₀)] with w hw hwj
      rw [c.ratio_of_ne hw.1 hwj, div_eq_mul_inv]
    exact ((c.differentiableAt_comp_pt hw₀ (hfV _ hV₀).1).fun_mul (hpj.inv hj₀)).congr_of_eventuallyEq hev
  · -- on the exceptional divisor: Hadamard's lemma at `u₀ = σⱼ w₀ ∈ ℂᵏ × 0`
    set u₀ := monomial c.k c.j w₀ with hu₀def
    have hu₀T : u₀ ∈ c.Φ.target := hw₀
    have hx₀ : c.pt w₀ ∈ C := (c.pt_mem_iff hw₀).mpr hj₀
    have hflat₀ : c.Φ.toFun (chartAt (ComplexModel n) c.y₀ (c.pt w₀)) = u₀ := c.flat_pt hw₀
    have hq : u₀ ∈ complexCoordinatePlane n c.k := by
      rw [← hflat₀]; exact (c.hflat (c.pt_mem_dom hw₀).1 (c.pt_mem_dom hw₀).2).mp hx₀
    have hinvT : Tendsto (fun u => (chartAt (ComplexModel n) c.y₀).symm (c.Φ.invFun u)) (𝓝 u₀)
        (𝓝 (c.pt w₀)) := by
      have h := tendsto_flatInverse c.Φ (c.pt_mem_dom hw₀)
      rwa [hflat₀] at h
    have hU : ∀ᶠ u in 𝓝 u₀, u ∈ c.Φ.target ∧
        (chartAt (ComplexModel n) c.y₀).symm (c.Φ.invFun u) ∈ V :=
      (c.Φ.isOpen_target.eventually_mem hu₀T).and (hinvT.eventually (hV.mem_nhds hV₀))
    have hFd : ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (c.flatRep f) u := by
      filter_upwards [hU] with u hu
      exact c.differentiableAt_flatRep hu.1 (hfV _ hu.2).1
    have hFvan : ∀ᶠ u in 𝓝 u₀, u ∈ complexCoordinatePlane n c.k → c.flatRep f u = 0 := by
      filter_upwards [hU] with u hu hplane
      obtain ⟨hdom, hΦu⟩ := flatInverse_mem c.Φ hu.1 c.hsrc
      have hxC : (chartAt (ComplexModel n) c.y₀).symm (c.Φ.invFun u) ∈ C :=
        (c.hflat hdom.1 hdom.2).mpr (by rw [hΦu]; exact hplane)
      exact (hfV _ hu.2).2.self_of_nhds hxC
    obtain ⟨H, hH0, hHd, hHeq⟩ :=
      CoordinatePlaneDivision.exists_eq_sum_coord_mul (n - c.k) c.k rfl hq hFd hFvan
    -- the single holomorphic expression
    have hQd : DifferentiableAt ℂ (c.hadamardExpr H) w₀ := by
      unfold hadamardExpr
      refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_mul ?_ ?_
      · have : (fun w : ComplexModel n => c.normalVec w i) =
            fun w => if i = c.j then 1 else if c.k ≤ i.1 then w i else 0 := by
          funext w; exact c.normalVec_apply w i
        rw [this]
        split_ifs
        · exact differentiableAt_const _
        · exact (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt
        · exact differentiableAt_const _
      · exact ((hHd i).self_of_nhds).comp w₀ ((contDiff_monomial c.k c.j).differentiable (by simp) w₀)
    -- the eventual identities near `u₀`, pulled back by `σⱼ`
    have hnear : ∀ᶠ u in 𝓝 u₀, (∀ i, DifferentiableAt ℂ (H i) u) ∧
        c.flatRep f =ᶠ[𝓝 u] fun u' => ∑ i, u' i * H i u' :=
      (eventually_all.mpr fun i => (hHd i)).and hHeq.eventually_nhds
    have hσ : Tendsto (monomial c.k c.j) (𝓝 w₀) (𝓝 u₀) :=
      (contDiff_monomial c.k c.j).continuous.tendsto w₀
    have hev : c.ratio f =ᶠ[𝓝 w₀] c.hadamardExpr H := by
      filter_upwards [hpt, hσ.eventually hnear] with w hw hwH
      obtain ⟨hHdw, hFw⟩ := hwH
      by_cases hj : w c.j = 0
      · -- on the divisor: `d_xf(ξ_w) = DF(σⱼ w)(v)`
        rw [c.ratio_of_eq hw.1 hj (hfV _ hw.2), germDiff_flatVec c.hsrc (c.pt_mem_dom hw.1)
          (hfV _ hw.2).1, c.flat_pt hw.1]
        have hfd : fderiv ℂ (fun u => f ((chartAt (ComplexModel n) c.y₀).symm (c.Φ.invFun u)))
            (monomial c.k c.j w) = fderiv ℂ (fun u' : ComplexModel n => ∑ i, u' i * H i u')
            (monomial c.k c.j w) := hFw.fderiv_eq
        rw [hfd]
        have hplane : ∀ i : Fin n, c.k ≤ i.1 → monomial c.k c.j w i = 0 := by
          intro i hi
          rw [monomial_apply]
          split_ifs
          · rw [hj, mul_zero]
          · have : i = c.j := by by_contra hne; simp_all
            rw [this, hj]
        rw [c.fderiv_sum_coord_mul hH0 hplane hHdw]
        rfl
      · -- off the divisor: `F(σⱼ w)/wⱼ`
        rw [c.ratio_of_ne hw.1 hj, ← c.flatRep_monomial f w, hFw.self_of_nhds, hadamardExpr]
        rw [div_eq_iff hj]
        show (∑ i, (monomial c.k c.j w) i * H i (monomial c.k c.j w)) = _
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [c.monomial_mul_eq hH0]
        ring
    exact hQd.congr_of_eventuallyEq hev

end FlatChart

end

end Hironaka.BlowupConstruction
