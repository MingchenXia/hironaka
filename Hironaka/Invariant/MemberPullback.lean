/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.LocalGiraudTransform
import Hironaka.Blowup.SimultaneousNormalCrossings
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.Analytic.HolomorphicGermAlgebra
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The pullback of the ideal of a member of a normal crossings divisor along a blowup

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.1 and the monomial charts of the proof of `le: inclusions`
("`u_i' = u_i / u_m` for `i < m`, `u_i' = u_i` for `i ≥ m`"); Bierstone--Milman 2008, Definition 2.2 and §3
(monomial marked ideals).

Let `π : Y → X` be the blowup along `C`, `D = π⁻¹ C`, `E` a simple normal crossings divisor such
that `C` has normal crossings with `E`, `H` a member of `E` and `H' = closure (π⁻¹ (H \ C))`.  At
every `z ∈ Y`:

Proof, at a point `z` over `x ∈ C ∩ H`: adapted coordinates `Φ` at `x`
(`SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings`, `N = X`) in which `C = ℂ^k × 0`
and `H = {w_t = 0}`; `C ⊆ H` near `x` exactly when `t ≥ k`.  In a monomial chart `j ≥ k` with local
inverse `W` (`σ_j ∘ W = Φ ∘ e ∘ π`), `𝓘_H = (Φ_t)` (`vanishingIdeal_mem_iff_flatCoord`) pulls back
to `(σ_j(W)_t)`, which is `(W_t)` if `t < k`, `(W_t W_j)` if `t ≥ k`, `t ≠ j`, and `(W_j)` if
`t = j`; `𝒪(-D) = (W_j)`; and `𝓘_{H'} = (W_t)` if `t ≠ j` (`W_t` has multiplicity one, the
differential of `W` being injective), `= 𝒪` if `t = j` (`H'` misses the chart).

The second identity is false for members of higher codimension (`A = {z₁ = z₃ = 0}`,
`C = {z₁ = z₂ = 0}`: in the chart `z₁ = w₁` the pullback is `(w₁, w₃)` but `A'` misses the chart),
so everything here is about hypersurfaces.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MemberPullback

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupExceptionalDivisor BlowupStrictSubmanifold BlowupStrictIdeal BlowupSNCTransform NormalCrossings SimultaneousNormalCrossings RelativePrincipalizationSpan DerivativeIdeal

noncomputable section

variable {n : ℕ}

/-! ### Principal ideals -/

section Principal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- A unit generates every holomorphic germ. -/
theorem isInSpanAt_one_iff {x : M} (g : M → ℂ) :
    IsInSpanAt (n := n) (· = fun _ => (1 : ℂ)) x g ↔ HolomorphicAt n g x := by
  refine ⟨fun hg => hg.1, fun hg => isInSpanAt_of_eq_mul rfl hg hg
    (Eventually.of_forall fun _ => by simp)⟩

end Principal

/-! ### Coordinate hyperplanes -/

section Hyperplane

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {y₀ : M}
  (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀))

/-- The differential of a local biholomorphism is injective. -/
theorem injective_fderiv_toFun {p : ComplexModel n} (hp : p ∈ Φ.source) :
    Function.Injective (fderiv ℂ Φ.toFun p) := by
  have hd : DifferentiableAt ℂ Φ.toFun p :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hp)
  have hdi : DifferentiableAt ℂ Φ.invFun (Φ.toFun p) :=
    Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun hp))
  have hcomp : HasFDerivAt (fun w => Φ.invFun (Φ.toFun w))
      ((fderiv ℂ Φ.invFun (Φ.toFun p)).comp (fderiv ℂ Φ.toFun p)) p :=
    hdi.hasFDerivAt.comp p hd.hasFDerivAt
  have hid : HasFDerivAt (fun w => Φ.invFun (Φ.toFun w)) (ContinuousLinearMap.id ℂ _) p := by
    refine (hasFDerivAt_id p).congr_of_eventuallyEq ?_
    filter_upwards [Φ.isOpen_source.mem_nhds hp] with w hw
    exact Φ.left_inv w hw
  have heq := hcomp.unique hid
  intro v w hvw
  have := congrArg (fun L => L v) heq
  have h2 := congrArg (fun L => L w) heq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h2
  rw [← this, ← h2, hvw]

/-- **A flat coordinate has a nonvanishing partial derivative** at every point of the flat
domain. -/
theorem exists_chartDeriv_flatCoord_ne_zero (t : Fin n) {y : M} (hy : y ∈ flatDomain Φ) :
    ∃ v : ComplexModel n, chartDeriv (complexChartAt (n := n) y₀) v (flatCoord Φ t) y ≠ 0 := by
  have hpΦ : chartAt (ComplexModel n) y₀ y ∈ Φ.source := hy.2
  have hpt : chartAt (ComplexModel n) y₀ y ∈ (chartAt (ComplexModel n) y₀).target :=
    (chartAt (ComplexModel n) y₀).map_source hy.1
  have hsurj : Function.Surjective (fderiv ℂ Φ.toFun (chartAt (ComplexModel n) y₀ y)) :=
    LinearMap.injective_iff_surjective
      (f := ((fderiv ℂ Φ.toFun (chartAt (ComplexModel n) y₀ y) : ComplexModel n →L[ℂ]
        ComplexModel n) : ComplexModel n →ₗ[ℂ] ComplexModel n)) |>.mp
      (injective_fderiv_toFun Φ hpΦ)
  obtain ⟨v, hv⟩ := hsurj (EuclideanSpace.single t 1)
  refine ⟨v, ?_⟩
  have hd : DifferentiableAt ℂ Φ.toFun (chartAt (ComplexModel n) y₀ y) :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hpΦ)
  have heq : (flatCoord Φ t ∘ (chartAt (ComplexModel n) y₀).symm)
      =ᶠ[𝓝 (chartAt (ComplexModel n) y₀ y)] fun w => Φ.toFun w t := by
    filter_upwards [(chartAt (ComplexModel n) y₀).open_target.mem_nhds hpt] with w hw
    simp only [Function.comp_apply, flatCoord]
    rw [(chartAt (ComplexModel n) y₀).right_inv hw]
  have hderiv : HasFDerivAt (fun w => Φ.toFun w t)
      ((EuclideanSpace.proj t : ComplexModel n →L[ℂ] ℂ).comp
        (fderiv ℂ Φ.toFun (chartAt (ComplexModel n) y₀ y))) (chartAt (ComplexModel n) y₀ y) :=
    (EuclideanSpace.proj t : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.comp _ hd.hasFDerivAt
  unfold chartDeriv
  show fderiv ℂ (flatCoord Φ t ∘ (chartAt (ComplexModel n) y₀).symm)
      (chartAt (ComplexModel n) y₀ y) v ≠ 0
  rw [heq.fderiv_eq, hderiv.fderiv]
  simp [hv]

/-- **Hadamard for a coordinate hyperplane**: if `A = {Φ_t = 0}` on the flat domain of `Φ`, then
at every point of the flat domain `𝓘_A` is generated by the flat coordinate `Φ_t`. -/
theorem vanishingIdeal_mem_iff_flatCoord {A : Set M} {t : Fin n}
    (hflatA : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ A ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) t = 0))
    {y : M} (hy : y ∈ flatDomain Φ) (g : M → ℂ) :
    (vanishingIdeal (n := n) A).mem y g ↔ IsInSpanAt (n := n) (· = flatCoord Φ t) y g := by
  rw [← LocalGiraudTransform.vanishingIdeal_zeroSet_mem_iff (isOpen_flatDomain Φ)
    (fun y' hy' => holomorphicAt_flatCoord Φ t hy')
    (fun y' hy' _ => let ⟨v, hv⟩ := exists_chartDeriv_flatCoord_ne_zero Φ t hy'
      ⟨complexChartAt (n := n) y₀, v, hy'.1, hv⟩) hy g]
  refine vanishingIdeal_mem_congr ?_ g
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy] with y' hy'
  exact ⟨fun h => ⟨(hflatA hy'.1 hy'.2).mp h, hy'⟩, fun h => (hflatA hy'.1 hy'.2).mpr h.1⟩

end Hyperplane

/-! ### Members of a normal crossings divisor -/

section Member

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- A span over a single-element range is a span over the element. -/
theorem isInSpanAt_range_one_iff {x : Y} (f g : Y → ℂ) :
    IsInSpanAt (n := n) (· ∈ range fun _ : Fin 1 => f) x g ↔ IsInSpanAt (n := n) (· = f) x g :=
  ⟨IsInSpanAt.mono fun _ ⟨_, hs⟩ => hs.symm, IsInSpanAt.mono fun _ hs => ⟨0, hs.symm⟩⟩

/-- **The coordinates of a map with injective differential have multiplicity one.** -/
theorem exists_chartDeriv_coord_ne_zero {O : Set Y} {W : Y → ComplexModel n}
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z') {u : Y}
    (hu : u ∈ O)
    (hinj : Function.Injective
      (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ)) (chartAt (ComplexModel n) u u)))
    (t : Fin n) :
    ∃ v : ComplexModel n, chartDeriv (complexChartAt (n := n) u) v (fun y => W y t) u ≠ 0 := by
  have hdiff : DifferentiableAt ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ))
      (chartAt (ComplexModel n) u u) := by
    have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
      (chart_mem_atlas (ComplexModel n) u)
      ((chartAt (ComplexModel n) u).map_source (mem_chart_source _ u))
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W
        ((chartAt (ComplexModel n) u).symm (chartAt (ComplexModel n) u u)) := by
      rw [(chartAt (ComplexModel n) u).left_inv (mem_chart_source _ u)]
      exact (hWs _ hu).mdifferentiableAt (by simp)
    exact mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)
  have hsurj : Function.Surjective (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ))
      (chartAt (ComplexModel n) u u)) :=
    LinearMap.injective_iff_surjective
      (f := ((fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ))
        (chartAt (ComplexModel n) u u) : ComplexModel n →L[ℂ] ComplexModel n) :
          ComplexModel n →ₗ[ℂ] ComplexModel n)) |>.mp hinj
  obtain ⟨v, hv⟩ := hsurj (EuclideanSpace.single t 1)
  refine ⟨v, ?_⟩
  have hderiv : HasFDerivAt (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ) t)
      ((EuclideanSpace.proj t : ComplexModel n →L[ℂ] ℂ).comp
        (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ))
          (chartAt (ComplexModel n) u u))) (chartAt (ComplexModel n) u u) :=
    (EuclideanSpace.proj t : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.comp _ hdiff.hasFDerivAt
  unfold chartDeriv
  show fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ) t)
      (chartAt (ComplexModel n) u u) v ≠ 0
  rw [hderiv.fderiv]
  simp [hv]

end Member

end

end Hironaka.MemberPullback
