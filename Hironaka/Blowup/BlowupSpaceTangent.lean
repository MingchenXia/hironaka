/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.HolomorphicGermAlgebra
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Differentials of germs and the tangent space of a smooth centre

Source: Demailly, *Complex analytic and differential geometry*, VII.12.1 (`agbook.tex` line 20218).

First module of the construction of the blowup along a smooth centre. Demailly records a point of the exceptional
divisor over `y ∈ C` as a line in the normal space `T_yX / T_yC`. Here the tangent space `T_yX` is `ℂⁿ`, read in the
preferred chart at `y`, and

* `germDiff n f y` is the differential at `y` of a function `f`, i.e. the derivative of
  `f ∘ (chartAt y)⁻¹` at `chartAt y y`;
* `tangentSpace n C y` is the common kernel of the differentials of the germs of the ideal `𝓘_C`
  at `y` -- an intrinsic definition, needing no flattening.

In flattening coordinates `τᵢ = (Φ ∘ e₀)ᵢ` (`BlowupFlatCoordinates`):

* `germDiff_flatCoord_flatVec`: for every `v` the vector `flatVec Φ y v` has
  `d_y τᵢ (flatVec Φ y v) = vᵢ` (the flat coordinates are coordinates at `y`);
* `germDiff_flatVec`: `d_y f (flatVec Φ y v) = D(f ∘ e₀⁻¹ ∘ Φ⁻¹)(Φ (e₀ y)) v` (chain rule);
* `mem_tangentSpace_iff`: for `y ∈ C`, `ξ ∈ T_yC` iff `d_y τᵢ ξ = 0` for every normal index
  `i ≥ k` (Hadamard's lemma `BlowupFlatCoordinates.exists_eq_sum_flatCoord`);
* `exists_sub_smul_mem_of_sup_span_eq`, `sup_span_eq_of_sub_smul_mem`: two vectors outside `T`
  span the same line modulo `T` iff one is a nonzero multiple of the other modulo `T`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupSpaceTangent

open Hironaka.HolomorphicIdealSheaves BlowupFlatCoordinates

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Charts as differentiable maps -/

/-- A function holomorphic at `e.symm z` is differentiable at `z` in the chart `e = chartAt y₀`. -/
theorem differentiableAt_comp_chart_symm {f : X → ℂ} {y₀ : X} {z : ComplexModel n}
    (hz : z ∈ (chartAt (ComplexModel n) y₀).target)
    (hf : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f ((chartAt (ComplexModel n) y₀).symm z)) :
    DifferentiableAt ℂ (f ∘ (chartAt (ComplexModel n) y₀).symm) z :=
  mdifferentiableAt_iff_differentiableAt.mp (hf.comp z (mdifferentiableAt_chart_symm hz))

/-- A chart transition is differentiable. -/
theorem differentiableAt_chart_comp_chart_symm {y₀ y₁ : X} {z : ComplexModel n}
    (hz : z ∈ (chartAt (ComplexModel n) y₁).target)
    (hz' : (chartAt (ComplexModel n) y₁).symm z ∈ (chartAt (ComplexModel n) y₀).source) :
    DifferentiableAt ℂ ((chartAt (ComplexModel n) y₀) ∘ (chartAt (ComplexModel n) y₁).symm) z :=
  mdifferentiableAt_iff_differentiableAt.mp
    ((mdifferentiableAt_chart hz').comp z (mdifferentiableAt_chart_symm hz))

/-! ### The differential of a germ -/

variable (n) in
/-- The differential at `y` of `f`, read in the preferred chart at `y`. -/
def germDiff (f : X → ℂ) (y : X) : ComplexModel n →L[ℂ] ℂ :=
  fderiv ℂ (f ∘ (chartAt (ComplexModel n) y).symm) (chartAt (ComplexModel n) y y)

theorem chartAt_symm_self (y : X) :
    (chartAt (ComplexModel n) y).symm (chartAt (ComplexModel n) y y) = y :=
  (chartAt (ComplexModel n) y).left_inv (mem_chart_source _ y)

theorem differentiableAt_germ {f : X → ℂ} {y : X} (hf : HolomorphicAt n f y) :
    DifferentiableAt ℂ (f ∘ (chartAt (ComplexModel n) y).symm) (chartAt (ComplexModel n) y y) :=
  differentiableAt_comp_chart_symm ((chartAt (ComplexModel n) y).map_source (mem_chart_source _ y))
    (by rw [chartAt_symm_self]; exact hf.mdifferentiableAt)

theorem tendsto_chartAt_symm (y : X) :
    Tendsto (chartAt (ComplexModel n) y).symm (𝓝 (chartAt (ComplexModel n) y y)) (𝓝 y) := by
  have h := (chartAt (ComplexModel n) y).continuousAt_symm
    ((chartAt (ComplexModel n) y).map_source (mem_chart_source _ y))
  rw [ContinuousAt, chartAt_symm_self] at h
  exact h

/-- The differential only depends on the germ. -/
theorem germDiff_congr {f g : X → ℂ} {y : X} (h : f =ᶠ[𝓝 y] g) :
    germDiff n f y = germDiff n g y :=
  Filter.EventuallyEq.fderiv_eq ((tendsto_chartAt_symm y).eventually h)

theorem germDiff_zero (y : X) : germDiff n (fun _ : X => (0 : ℂ)) y = 0 := by
  simp [germDiff, Function.comp_def]

/-- The product rule. -/
theorem germDiff_mul {b f : X → ℂ} {y : X} (hb : HolomorphicAt n b y) (hf : HolomorphicAt n f y) :
    germDiff n (fun x => b x * f x) y = b y • germDiff n f y + f y • germDiff n b y := by
  have h := fderiv_fun_mul (differentiableAt_germ hb) (differentiableAt_germ hf)
  simp only [Function.comp_apply, chartAt_symm_self] at h
  exact h

theorem germDiff_sum {ι : Type*} (s : Finset ι) {F : ι → X → ℂ} {y : X}
    (hF : ∀ i ∈ s, HolomorphicAt n (F i) y) :
    germDiff n (fun x => ∑ i ∈ s, F i x) y = ∑ i ∈ s, germDiff n (F i) y := by
  have hfun : (fun x => ∑ i ∈ s, F i x) ∘ (chartAt (ComplexModel n) y).symm =
      ∑ i ∈ s, F i ∘ (chartAt (ComplexModel n) y).symm := by
    funext z; simp [Finset.sum_apply]
  unfold germDiff
  rw [hfun]
  exact fderiv_sum fun i hi => differentiableAt_germ (hF i hi)

/-! ### The tangent space of a centre -/

variable (n) in
/-- The tangent space of `C` at `y`: the common kernel of the differentials at `y` of the germs of
the ideal `𝓘_C`. -/
def tangentSpace (C : Set X) (y : X) : Submodule ℂ (ComplexModel n) :=
  ⨅ (f : X → ℂ) (_ : (vanishingIdeal (n := n) C).mem y f),
    LinearMap.ker (germDiff n f y : ComplexModel n →ₗ[ℂ] ℂ)

theorem mem_tangentSpace {C : Set X} {y : X} {ξ : ComplexModel n} :
    ξ ∈ tangentSpace n C y ↔ ∀ f, (vanishingIdeal (n := n) C).mem y f → germDiff n f y ξ = 0 := by
  simp only [tangentSpace, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

theorem germDiff_eq_zero_of_mem_tangentSpace {C : Set X} {y : X} {ξ : ComplexModel n}
    (hξ : ξ ∈ tangentSpace n C y) {f : X → ℂ} (hf : (vanishingIdeal (n := n) C).mem y f) :
    germDiff n f y ξ = 0 :=
  mem_tangentSpace.mp hξ f hf

/-! ### Flattening coordinates are coordinates -/

section Flat

variable {y₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀))

/-- `Φ ∘ e₀ ∘ e_y⁻¹`: the flattening read from the preferred chart at `y`. -/
def flatMap (y : X) (z : ComplexModel n) : ComplexModel n :=
  Φ.toFun (chartAt (ComplexModel n) y₀ ((chartAt (ComplexModel n) y).symm z))

/-- `e_y ∘ e₀⁻¹ ∘ Φ⁻¹`, the local inverse of `flatMap Φ y`. -/
def flatInvMap (y : X) (u : ComplexModel n) : ComplexModel n :=
  chartAt (ComplexModel n) y ((chartAt (ComplexModel n) y₀).symm (Φ.invFun u))

/-- The vector at `y` whose flat-coordinate differentials are `v`. -/
def flatVec (y : X) (v : ComplexModel n) : ComplexModel n :=
  fderiv ℂ (flatInvMap Φ y) (Φ.toFun (chartAt (ComplexModel n) y₀ y)) v

variable {Φ}

theorem flatInvMap_flat {y : X} (hy : y ∈ flatDomain Φ) :
    flatInvMap Φ y (Φ.toFun (chartAt (ComplexModel n) y₀ y)) = chartAt (ComplexModel n) y y := by
  simp only [flatInvMap]
  rw [Φ.left_inv _ hy.2, (chartAt (ComplexModel n) y₀).left_inv hy.1]

/-- `flatInvMap ∘ flatMap = id` near `e_y y`, read through `e₀⁻¹ ∘ Φ⁻¹`. -/
theorem flatInverse_flatMap_eventually {y : X} (hy : y ∈ flatDomain Φ) :
    ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) y y),
      (chartAt (ComplexModel n) y₀).symm (Φ.invFun (flatMap Φ y z)) =
        (chartAt (ComplexModel n) y).symm z := by
  have hev : ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) y y), (chartAt (ComplexModel n) y).symm z ∈ flatDomain Φ :=
    (tendsto_chartAt_symm y).eventually ((isOpen_flatDomain Φ).mem_nhds hy)
  filter_upwards [hev] with z hz
  exact flatInverse_flat Φ hz

variable (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
include hΦsrc

theorem differentiableAt_flatMap {y : X} (hy : y ∈ flatDomain Φ) :
    DifferentiableAt ℂ (flatMap Φ y) (chartAt (ComplexModel n) y y) := by
  have h1 : DifferentiableAt ℂ ((chartAt (ComplexModel n) y₀) ∘ (chartAt (ComplexModel n) y).symm)
      (chartAt (ComplexModel n) y y) :=
    differentiableAt_chart_comp_chart_symm
      ((chartAt (ComplexModel n) y).map_source (mem_chart_source _ y))
      (by rw [chartAt_symm_self]; exact hy.1)
  have h2 : DifferentiableAt ℂ Φ.toFun
      (((chartAt (ComplexModel n) y₀) ∘ (chartAt (ComplexModel n) y).symm)
        (chartAt (ComplexModel n) y y)) := by
    simp only [Function.comp_apply, chartAt_symm_self]
    exact Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)
  exact h2.comp _ h1

theorem differentiableAt_flatInvMap {y : X} (hy : y ∈ flatDomain Φ) :
    DifferentiableAt ℂ (flatInvMap Φ y) (Φ.toFun (chartAt (ComplexModel n) y₀ y)) := by
  set u₀ := Φ.toFun (chartAt (ComplexModel n) y₀ y)
  have hu₀ : u₀ ∈ Φ.target := Φ.mapsTo_toFun hy.2
  have hinv : Φ.invFun u₀ = chartAt (ComplexModel n) y₀ y := Φ.left_inv _ hy.2
  have h1 : DifferentiableAt ℂ Φ.invFun u₀ :=
    Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hu₀)
  have h2 : DifferentiableAt ℂ ((chartAt (ComplexModel n) y) ∘ (chartAt (ComplexModel n) y₀).symm)
      (Φ.invFun u₀) := by
    rw [hinv]
    exact differentiableAt_chart_comp_chart_symm
      ((chartAt (ComplexModel n) y₀).map_source hy.1)
      (by rw [(chartAt (ComplexModel n) y₀).left_inv hy.1]; exact mem_chart_source _ y)
  exact h2.comp u₀ h1

/-- `flatMap ∘ flatInvMap = id` near `Φ (e₀ y)`. -/
theorem flatMap_flatInvMap_eventually {y : X} (hy : y ∈ flatDomain Φ) :
    ∀ᶠ u in 𝓝 (Φ.toFun (chartAt (ComplexModel n) y₀ y)), flatMap Φ y (flatInvMap Φ y u) = u := by
  have hu₀ : Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ Φ.target := Φ.mapsTo_toFun hy.2
  filter_upwards [Φ.isOpen_target.mem_nhds hu₀,
    (tendsto_flatInverse Φ hy).eventually ((chartAt (ComplexModel n) y).open_source.mem_nhds
      (mem_chart_source _ y))] with u hu hus
  simp only [flatMap, flatInvMap]
  rw [(chartAt (ComplexModel n) y).left_inv hus,
    (chartAt (ComplexModel n) y₀).right_inv (hΦsrc (Φ.mapsTo_invFun hu)), Φ.right_inv u hu]

theorem fderiv_flatMap_flatVec {y : X} (hy : y ∈ flatDomain Φ) (v : ComplexModel n) :
    fderiv ℂ (flatMap Φ y) (chartAt (ComplexModel n) y y) (flatVec Φ y v) = v := by
  set u₀ := Φ.toFun (chartAt (ComplexModel n) y₀ y)
  have hcomp : fderiv ℂ (flatMap Φ y ∘ flatInvMap Φ y) u₀ =
      (fderiv ℂ (flatMap Φ y) (flatInvMap Φ y u₀)).comp (fderiv ℂ (flatInvMap Φ y) u₀) :=
    fderiv_comp u₀ (by rw [flatInvMap_flat hy]; exact differentiableAt_flatMap hΦsrc hy)
      (differentiableAt_flatInvMap hΦsrc hy)
  have hid : fderiv ℂ (flatMap Φ y ∘ flatInvMap Φ y) u₀ = ContinuousLinearMap.id ℂ _ := by
    have hev : (flatMap Φ y ∘ flatInvMap Φ y) =ᶠ[𝓝 u₀] id := flatMap_flatInvMap_eventually hΦsrc hy
    rw [hev.fderiv_eq, fderiv_id]
  rw [hid, flatInvMap_flat hy] at hcomp
  have := congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L v) hcomp
  simpa [flatVec] using this.symm

/-- The flat coordinates read from the preferred chart at `y`. -/
theorem germDiff_flatCoord {y : X} (hy : y ∈ flatDomain Φ) (i : Fin n) :
    germDiff n (flatCoord Φ i) y =
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).comp
        (fderiv ℂ (flatMap Φ y) (chartAt (ComplexModel n) y y)) := by
  have h : flatCoord Φ i ∘ (chartAt (ComplexModel n) y).symm =
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ) ∘ flatMap Φ y := rfl
  unfold germDiff
  rw [h, fderiv_comp _ (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt
    (differentiableAt_flatMap hΦsrc hy), ContinuousLinearMap.fderiv]

theorem germDiff_flatCoord_flatVec {y : X} (hy : y ∈ flatDomain Φ) (i : Fin n) (v : ComplexModel n) :
    germDiff n (flatCoord Φ i) y (flatVec Φ y v) = v i := by
  rw [germDiff_flatCoord hΦsrc hy, ContinuousLinearMap.comp_apply, fderiv_flatMap_flatVec hΦsrc hy]
  rfl

/-- **Chain rule.**  The differential of a germ at `y`, applied to `flatVec Φ y v`, is the
derivative of its flat representative `f ∘ e₀⁻¹ ∘ Φ⁻¹` in the direction `v`. -/
theorem germDiff_flatVec {f : X → ℂ} {y : X} (hy : y ∈ flatDomain Φ) (hf : HolomorphicAt n f y)
    (v : ComplexModel n) :
    germDiff n f y (flatVec Φ y v) =
      fderiv ℂ (fun u => f ((chartAt (ComplexModel n) y₀).symm (Φ.invFun u)))
        (Φ.toFun (chartAt (ComplexModel n) y₀ y)) v := by
  set F : ComplexModel n → ℂ := fun u => f ((chartAt (ComplexModel n) y₀).symm (Φ.invFun u))
  set u₀ := Φ.toFun (chartAt (ComplexModel n) y₀ y)
  have hu₀ : u₀ ∈ Φ.target := Φ.mapsTo_toFun hy.2
  have hinv : Φ.invFun u₀ = chartAt (ComplexModel n) y₀ y := Φ.left_inv _ hy.2
  have hFd : DifferentiableAt ℂ F u₀ := by
    have h1 : DifferentiableAt ℂ (f ∘ (chartAt (ComplexModel n) y₀).symm) (Φ.invFun u₀) := by
      rw [hinv]
      exact differentiableAt_comp_chart_symm ((chartAt (ComplexModel n) y₀).map_source hy.1)
        (by rw [(chartAt (ComplexModel n) y₀).left_inv hy.1]; exact hf.mdifferentiableAt)
    exact h1.comp u₀ (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hu₀))
  have hflat0 : flatMap Φ y (chartAt (ComplexModel n) y y) = u₀ := by
    simp only [flatMap, chartAt_symm_self, u₀]
  have hev : f ∘ (chartAt (ComplexModel n) y).symm =ᶠ[𝓝 (chartAt (ComplexModel n) y y)]
      F ∘ flatMap Φ y := by
    filter_upwards [flatInverse_flatMap_eventually hy] with z hz
    simp only [Function.comp_apply, F, hz]
  have hcomp : fderiv ℂ (F ∘ flatMap Φ y) (chartAt (ComplexModel n) y y) =
      (fderiv ℂ F u₀).comp (fderiv ℂ (flatMap Φ y) (chartAt (ComplexModel n) y y)) := by
    rw [fderiv_comp _ (by rw [hflat0]; exact hFd) (differentiableAt_flatMap hΦsrc hy), hflat0]
  unfold germDiff
  rw [hev.fderiv_eq, hcomp, ContinuousLinearMap.comp_apply, fderiv_flatMap_flatVec hΦsrc hy]

variable {C : Set X} {k : ℕ}
  (hflat : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) y₀).source →
    chartAt (ComplexModel n) y₀ x ∈ Φ.source →
      (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ x) ∈ complexCoordinatePlane n k))
include hflat

theorem flatCoord_eq_zero {y : X} (hy : y ∈ flatDomain Φ) (hyC : y ∈ C) {i : Fin n}
    (hi : k ≤ i.1) : flatCoord Φ i y = 0 :=
  (hflat hy.1 hy.2).mp hyC i hi

/-- **The tangent space in flattening coordinates**: at a point of `C`, `T_yC` is the common
kernel of the differentials of the normal flat coordinates. -/
theorem mem_tangentSpace_iff {y : X} (hy : y ∈ flatDomain Φ) (hyC : y ∈ C) {ξ : ComplexModel n} :
    ξ ∈ tangentSpace n C y ↔ ∀ i : Fin n, k ≤ i.1 → germDiff n (flatCoord Φ i) y ξ = 0 := by
  constructor
  · intro hξ i hi
    exact germDiff_eq_zero_of_mem_tangentSpace hξ (flatCoord_mem_vanishingIdeal Φ hflat hi hy)
  · intro h
    refine mem_tangentSpace.mpr fun f hf => ?_
    obtain ⟨b, hb0, hbh, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦsrc hflat hy hf
    rw [germDiff_congr hbeq, germDiff_sum _ fun i _ => (hbh i).mul (holomorphicAt_flatCoord Φ i hy)]
    simp only [_root_.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [germDiff_mul (hbh i) (holomorphicAt_flatCoord Φ i hy)]
    by_cases hi : k ≤ i.1
    · simp [flatCoord_eq_zero hΦsrc hflat hy hyC hi, h i hi]
    · have hbi : b i = fun _ => 0 := hb0 i (by omega)
      simp [hbi, germDiff_zero]

/-- A vector whose flat-coordinate differentials have a nonzero normal component is not tangent. -/
theorem flatVec_not_mem_tangentSpace {y : X} (hy : y ∈ flatDomain Φ) (hyC : y ∈ C)
    {v : ComplexModel n} {i : Fin n} (hi : k ≤ i.1) (hvi : v i ≠ 0) :
    flatVec Φ y v ∉ tangentSpace n C y := by
  rw [mem_tangentSpace_iff hΦsrc hflat hy hyC]
  intro h
  exact hvi ((germDiff_flatCoord_flatVec hΦsrc hy i v).symm.trans (h i hi))

end Flat

/-! ### Lines modulo a subspace -/

section Lines

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {T : Submodule ℂ E} {ξ ξ' : E}

theorem exists_sub_smul_mem_of_mem_sup_span (h : ξ' ∈ T ⊔ ℂ ∙ ξ) : ∃ a : ℂ, ξ' - a • ξ ∈ T := by
  obtain ⟨t, ht, z, hz, rfl⟩ := Submodule.mem_sup.mp h
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a, by simpa using ht⟩

theorem sup_span_eq_of_sub_smul_mem {a : ℂ} (ha : a ≠ 0) (h : ξ' - a • ξ ∈ T) :
    T ⊔ ℂ ∙ ξ' = T ⊔ ℂ ∙ ξ := by
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    have : ξ' = (ξ' - a • ξ) + a • ξ := by abel
    rw [SetLike.mem_coe, this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h)
      (Submodule.mem_sup_right (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self ξ)))
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    have : ξ = a⁻¹ • ξ' - a⁻¹ • (ξ' - a • ξ) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ha, one_smul]; abel
    rw [SetLike.mem_coe, this]
    exact Submodule.sub_mem _
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self ξ')))
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ h))

/-- Two vectors outside `T` spanning the same line modulo `T` differ by a nonzero factor
modulo `T`. -/
theorem exists_sub_smul_mem_of_sup_span_eq (hξ' : ξ' ∉ T) (h : T ⊔ ℂ ∙ ξ' = T ⊔ ℂ ∙ ξ) :
    ∃ a : ℂ, a ≠ 0 ∧ ξ' - a • ξ ∈ T := by
  obtain ⟨a, ha⟩ := exists_sub_smul_mem_of_mem_sup_span
    (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self ξ'))
  refine ⟨a, fun h0 => hξ' ?_, ha⟩
  simpa [h0] using ha

end Lines

/-- A differential vanishing on `T_yC` sees only the line modulo `T_yC`. -/
theorem germDiff_apply_of_sub_smul_mem {C : Set X} {y : X} {f : X → ℂ}
    (hf : (vanishingIdeal (n := n) C).mem y f) {ξ ξ' : ComplexModel n} {a : ℂ}
    (h : ξ' - a • ξ ∈ tangentSpace n C y) : germDiff n f y ξ' = a * germDiff n f y ξ := by
  have h0 := germDiff_eq_zero_of_mem_tangentSpace h hf
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0

end

end Hironaka.BlowupSpaceTangent
