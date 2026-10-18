/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.AnalyticSubsetPresentationsExact
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Analytic.FiniteMapDimension
import Hironaka.Analytic.GenericSections
import Hironaka.Analytic.CompactAnalyticFinite
import Hironaka.Analytic.AnalyticSubsetTopology

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Fibres of a map on a pure-dimensional analytic set are not too small

Blueprint `rem:fibre-dimension-lower-bound` (Demailly, *Complex analytic and differential geometry*,
II.8.2; step M8 of the route to Remmert's proper mapping theorem, `blueprint/src/remmert.tex`).

Let `A` be an analytic subset of pure dimension `m` of a complex manifold `X`, `F : X → Y`
holomorphic, and suppose `rank d(F|A) ≤ r` at every regular point of `A`.  Then every fibre
`A ∩ F⁻¹(F x)` has local dimension `≥ m - r` at `x` (`locDimGE_fibre`).

Proof.  Otherwise the fibre `Φ` has dimension `≤ k`, `k + r < m`, near `x`.  Generic linear forms
`ξ₁, …, ξ_k` in the chart `e` at `x` (`GenericSections.exists_forms_not_accPt`, on the open manifold
of a chart neighbourhood) make `x` isolated in `Φ ∩ {ξ ∘ e = ξ(e x)}`, i.e. in `A ∩ G⁻¹(G x)` for
`G = (e' ∘ F, ξ ∘ e) : X → ℂ^(n'+k)`.  On a small chart ball around `e x` the function `|G - G x|`
has a positive minimum `η` on the points of `A` over the boundary sphere; so for `|w - G x| < η` the
set of `z` in the closed ball with `e⁻¹ z ∈ A`, `G(e⁻¹ z) = w` is a compact analytic subset of `ℂⁿ`
(it avoids the sphere), hence finite (`CompactAnalyticFinite`).  Thus `G` has finite fibres on `A ∩ W`
for an open `W ∋ x`.  At a regular point of `A` in `W`, on the open manifold `W`, the parametrized
map `G ∘ param` has rank `m` somewhere (`FiniteMapDimension.exists_param_rank_eq`); but its rank is at
most the rank of `F ∘ param` plus `k`, i.e. `≤ r + k < m` (`RankDegeneracy.rankAt_param_eq`).

The source states the lemma for irreducible `A` and `r` the generic rank; pure dimension and an upper
bound `r` for the rank on the regular locus is what the proof uses (no rank-degeneracy set needed).

Sorry-free.
-/

open Set Filter Topology Metric Module TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.FibreDimensionLowerBound

open Hironaka.RegularLocusDense AnalyticDimensionBasics AnalyticSubsetOpens
  AnalyticSubsetPreimage RankDegeneracy FiniteMapDimension GenericSections CompactAnalyticFinite
  StokesSingularLocusAnalytic

/-! ### Points, finite sets -/

section Points

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A point of a complex manifold is an analytic subset. -/
theorem isComplexAnalyticSubset_singleton (y₀ : M) :
    IsComplexAnalyticSubset (n := n) ({y₀} : Set M) := by
  intro x
  by_cases hy : y₀ ∈ (complexChartAt (n := n) x).val.source
  · exact ⟨{
      generatorCount := n
      generator := fun i z => z i - (complexChartAt (n := n) x).val y₀ i
      coordinateNeighborhood := (complexChartAt (n := n) x).val.target
      isOpen_coordinateNeighborhood := (complexChartAt (n := n) x).val.open_target
      center_mem_coordinateNeighborhood :=
        (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
      coordinateNeighborhood_subset_target := subset_rfl
      generator_holomorphic := fun i =>
        ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiable.sub_const _).differentiableOn
      zeroLocus := by
        intro y hys _
        simp only [mem_singleton_iff, sub_eq_zero]
        constructor
        · rintro rfl i
          rfl
        · intro h
          exact (complexChartAt (n := n) x).val.injOn hys hy (by ext i; exact h i) }⟩
  · exact ⟨{
      generatorCount := 1
      generator := fun _ _ => 1
      coordinateNeighborhood := (complexChartAt (n := n) x).val.target
      isOpen_coordinateNeighborhood := (complexChartAt (n := n) x).val.open_target
      center_mem_coordinateNeighborhood :=
        (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
      coordinateNeighborhood_subset_target := subset_rfl
      generator_holomorphic := fun _ => differentiableOn_const 1
      zeroLocus := by
        intro y hys _
        simp only [mem_singleton_iff, one_ne_zero, forall_const, iff_false]
        rintro rfl
        exact hy hys }⟩

end Points

/-- A finite set has no accumulation point. -/
theorem not_accPt_of_finite {α : Type*} [TopologicalSpace α] [T1Space α] {s : Set α}
    (hs : s.Finite) (y : α) : ¬ AccPt y (𝓟 s) := by
  rw [accPt_iff_nhds]
  push Not
  refine ⟨(s \ {y})ᶜ, (hs.sdiff).isClosed.isOpen_compl.mem_nhds (by simp), fun z hz => ?_⟩
  by_contra hzy
  exact hz.1 ⟨hz.2, hzy⟩

/-! ### `ℂ^(a+b) = ℂ^a × ℂ^b` -/

section Stack

/-- `u ↦ (u, 0)`. -/
def inlCLM (a b : ℕ) : ComplexModel a →L[ℂ] ComplexModel (a + b) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => WithLp.toLp 2 (Fin.append (fun i => u i) (fun _ : Fin b => (0 : ℂ)))
      map_add' := fun u v => by
        ext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      map_smul' := fun c u => by
        ext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp }

/-- `v ↦ (0, v)`. -/
def inrCLM (a b : ℕ) : ComplexModel b →L[ℂ] ComplexModel (a + b) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Fin.append (fun _ : Fin a => (0 : ℂ)) (fun i => v i))
      map_add' := fun u v => by
        ext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      map_smul' := fun c u => by
        ext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp }

/-- The first `a` coordinates of `ℂ^(a+b)`. -/
def fstCLM (a b : ℕ) : ComplexModel (a + b) →L[ℂ] ComplexModel a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun i => w (Fin.castAdd b i))
      map_add' := fun u v => by ext i; simp
      map_smul' := fun c u => by ext i; simp }

/-- The last `b` coordinates of `ℂ^(a+b)`. -/
def sndCLM (a b : ℕ) : ComplexModel (a + b) →L[ℂ] ComplexModel b :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun i => w (Fin.natAdd a i))
      map_add' := fun u v => by ext i; simp
      map_smul' := fun c u => by ext i; simp }

variable {a b : ℕ}

@[simp] theorem fstCLM_inlCLM (u : ComplexModel a) : fstCLM a b (inlCLM a b u) = u := by
  ext i; simp [fstCLM, inlCLM]

@[simp] theorem fstCLM_inrCLM (v : ComplexModel b) : fstCLM a b (inrCLM a b v) = 0 := by
  ext i; simp [fstCLM, inrCLM]

@[simp] theorem sndCLM_inlCLM (u : ComplexModel a) : sndCLM a b (inlCLM a b u) = 0 := by
  ext i; simp [sndCLM, inlCLM]

@[simp] theorem sndCLM_inrCLM (v : ComplexModel b) : sndCLM a b (inrCLM a b v) = v := by
  ext i; simp [sndCLM, inrCLM]

theorem inlCLM_fstCLM_add_inrCLM_sndCLM (w : ComplexModel (a + b)) :
    inlCLM a b (fstCLM a b w) + inrCLM a b (sndCLM a b w) = w := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [fstCLM, sndCLM, inlCLM, inrCLM]

theorem finrank_ker_fstCLM_le :
    finrank ℂ (LinearMap.ker (fstCLM a b : ComplexModel (a + b) →ₗ[ℂ] ComplexModel a)) ≤ b := by
  have hle : LinearMap.ker (fstCLM a b : ComplexModel (a + b) →ₗ[ℂ] ComplexModel a) ≤
      LinearMap.range (inrCLM a b : ComplexModel b →ₗ[ℂ] ComplexModel (a + b)) := by
    intro w hw
    rw [LinearMap.mem_ker] at hw
    refine ⟨sndCLM a b w, ?_⟩
    have h := inlCLM_fstCLM_add_inrCLM_sndCLM w
    change fstCLM a b w = 0 at hw
    rw [hw, map_zero, zero_add] at h
    exact h
  refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le _).trans ?_)
  rw [finrank_euclideanSpace, Fintype.card_fin]

/-- The linear forms `ξ₁, …, ξ_k` as one map `ℂⁿ → ℂ^k`. -/
def formsCLM {n k : ℕ} (ξ : Fin k → (ComplexModel n →L[ℂ] ℂ)) : ComplexModel n →L[ℂ] ComplexModel k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => ξ i v)
      map_add' := fun u v => by ext i; simp
      map_smul' := fun c u => by ext i; simp }

@[simp] theorem formsCLM_apply {n k : ℕ} (ξ : Fin k → (ComplexModel n →L[ℂ] ℂ)) (v : ComplexModel n)
    (i : Fin k) : formsCLM ξ v i = ξ i v := rfl

end Stack

/-- `rank L ≤ rank (π ∘ L) + dim ker π`. -/
theorem finrank_range_le_finrank_range_comp_add {V W W' : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [AddCommGroup W'] [Module ℂ W']
    (L : V →ₗ[ℂ] W) (π : W →ₗ[ℂ] W') :
    finrank ℂ (LinearMap.range L) ≤
      finrank ℂ (LinearMap.range (π ∘ₗ L)) + finrank ℂ (LinearMap.ker π) := by
  set R := LinearMap.range L
  have h1 := LinearMap.finrank_range_add_finrank_ker (π.domRestrict R)
  have h2 : LinearMap.range (π.domRestrict R) = LinearMap.range (π ∘ₗ L) := by
    rw [LinearMap.range_domRestrict, LinearMap.range_comp]
  have h3 : finrank ℂ (LinearMap.ker (π.domRestrict R)) ≤ finrank ℂ (LinearMap.ker π) := by
    rw [← Submodule.finrank_map_subtype_eq R (LinearMap.ker (π.domRestrict R))]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : π.domRestrict R v = 0 := hv
    rw [LinearMap.mem_ker]
    simpa using hv'
  rw [h2] at h1
  omega

/-! ### The lower bound -/

section Main

variable {n n' : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n') Y]
  [IsComplexManifold n' Y]

/-- **The fibre dimension lower bound** (`rem:fibre-dimension-lower-bound`, `demailly-cadg:II.8.2`).
If `A` is analytic of pure dimension `m` and `rank d(F|A) ≤ r` at every regular point of `A`, then
`dim_x (A ∩ F⁻¹(F x)) ≥ m - r` for every `x ∈ A`. -/
theorem locDimGE_fibre {A : Set X} (hA : IsComplexAnalyticSubset (n := n) A) {m : ℕ}
    (hpure : IsPureDim (n := n) A m) {F : X → Y}
    (hF : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') ∞ F) {r : ℕ}
    (hr : ∀ y, RegularAtDim (n := n) A y m → rankAt (n := n) (n' := n') F A y ≤ r)
    {x : X} (hx : x ∈ A) : LocDimGE (n := n) (A ∩ F ⁻¹' {F x}) x (m - r) := by
  classical
  have hΦa : IsComplexAnalyticSubset (n := n) (A ∩ F ⁻¹' {F x}) :=
    hA.inter (isComplexAnalyticSubset_preimage hF (isComplexAnalyticSubset_singleton (F x)))
  by_contra hcon
  -- the fibre has dimension `< m - r` near `x`
  obtain ⟨V, hV, hVj⟩ : ∃ V ∈ 𝓝 x, ∀ y ∈ V, ∀ j, RegularAtDim (n := n) (A ∩ F ⁻¹' {F x}) y j →
      j + r < m := by
    unfold LocDimGE at hcon
    push Not at hcon
    obtain ⟨V, hV, hVj⟩ := hcon
    exact ⟨V, hV, fun y hy j hj => by
      by_contra h
      exact hVj y hy j (by omega) hj⟩
  have hrm : r < m := by
    obtain ⟨y, hyV, j, -, hy⟩ := locDimGE_zero hΦa ⟨hx, rfl⟩ V hV
    have := hVj y hyV j hy
    omega
  set k := m - r - 1 with hk
  -- charts at `x` and `F x`
  set e := chartAt (ComplexModel n) x with he
  set e' := chartAt (ComplexModel n') (F x) with he'
  have hxe : x ∈ e.source := mem_chart_source _ x
  have hU₁o : IsOpen (interior V ∩ e.source ∩ F ⁻¹' e'.source) :=
    (isOpen_interior.inter e.open_source).inter (e'.open_source.preimage hF.continuous)
  set U₁ : Opens X := ⟨_, hU₁o⟩ with hU₁
  have hxU₁ : x ∈ U₁ := ⟨⟨mem_interior_iff_mem_nhds.mpr hV, hxe⟩, mem_chart_source _ (F x)⟩
  set x₀ : U₁ := ⟨x, hxU₁⟩ with hx₀
  -- generic sections of the fibre
  set Φ' : Set U₁ := (↑) ⁻¹' (A ∩ F ⁻¹' {F x}) with hΦ'
  have hΦ'a : IsComplexAnalyticSubset (n := n) Φ' := isComplexAnalyticSubset_preimage_val hΦa U₁
  have hΦ'd : DimLE (n := n) Φ' k := fun y j hy => by
    have h1 := regularAtDim_preimage_val_iff.mp hy
    have := hVj y (interior_subset y.2.1.1) j h1
    omega
  set g : U₁ → ComplexModel n := fun y => e y with hg
  have hgs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g :=
    contMDiff_restrict (U := U₁) ((contMDiffOn_chart (n := ∞)).mono fun y hy => hy.1.2)
  have hsep : ∀ y ∈ Φ', y ≠ x₀ →
      ∃ ξ ∈ (⊤ : Submodule ℂ (ComplexModel n →L[ℂ] ℂ)), ξ (g y) ≠ ξ (g x₀) := by
    intro y _ hyx
    have hne : g y ≠ g x₀ := fun h => hyx (Subtype.ext (e.injOn y.2.1.2 hxe h))
    obtain ⟨i, hi⟩ : ∃ i, g y i ≠ g x₀ i := by
      by_contra h
      push Not at h
      exact hne (by ext i; exact h i)
    exact ⟨EuclideanSpace.proj i, Submodule.mem_top, by simpa using hi⟩
  obtain ⟨ξ, -, hξ⟩ := exists_forms_not_accPt hgs x₀ ⊤ k hΦ'a hΦ'd hsep
  have hiso := hξ x₀ ⟨⟨hx, rfl⟩, fun i => rfl⟩
  rw [accPt_iff_nhds] at hiso
  push Not at hiso
  obtain ⟨Ui, hUi, hUiS⟩ := hiso
  rw [nhds_opens_eq_comap, mem_comap] at hUi
  obtain ⟨Wi, hWi, hWiUi⟩ := hUi
  -- the map `G = (e' ∘ F, ξ ∘ e)`
  set G : X → ComplexModel (n' + k) := fun y => inlCLM n' k (e' (F y)) + inrCLM n' k (formsCLM ξ (e y))
    with hG
  have hGs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n' + k)) ∞ G U₁ := by
    have h1 : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') ∞ (fun y => e' (F y)) U₁ :=
      (contMDiffOn_chart (n := ∞)).comp (hF.contMDiffOn (s := (U₁ : Set X))) fun y hy => hy.2
    have h2 : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun y => e y) U₁ :=
      (contMDiffOn_chart (n := ∞)).mono fun y hy => hy.1.2
    exact ((inlCLM n' k).contDiff.contMDiff.comp_contMDiffOn h1).add
      (((inrCLM n' k).comp (formsCLM ξ)).contDiff.contMDiff.comp_contMDiffOn h2)
  have hGfst : ∀ y, fstCLM n' k (G y) = e' (F y) := fun y => by simp [hG]
  have hGsnd : ∀ y, sndCLM n' k (G y) = formsCLM ξ (e y) := fun y => by simp [hG]
  -- `x` is isolated in `A ∩ G⁻¹(G x)`
  set B : Set X := interior Wi ∩ U₁ with hB
  have hBo : IsOpen B := isOpen_interior.inter U₁.isOpen
  have hxB : x ∈ B := ⟨mem_interior_iff_mem_nhds.mpr hWi, hxU₁⟩
  have hBiso : ∀ y ∈ B, y ∈ A → G y = G x → y = x := by
    intro y hyB hyA hGy
    have hF1 : F y = F x := by
      have h := congrArg (fstCLM n' k) hGy
      rw [hGfst, hGfst] at h
      exact e'.injOn hyB.2.2 (mem_chart_source _ (F x)) h
    have hξ1 : ∀ i, ξ i (g ⟨y, hyB.2⟩) = ξ i (g x₀) := fun i => by
      have h := congrArg (fun w => sndCLM n' k w i) hGy
      simp only [hGsnd, formsCLM_apply] at h
      exact h
    have hyWi : y ∈ Wi := interior_subset hyB.1
    have hyUi : (⟨y, hyB.2⟩ : U₁) ∈ Ui := hWiUi hyWi
    have := hUiS ⟨y, hyB.2⟩ ⟨hyUi, ⟨hyA, hF1⟩, hξ1⟩
    exact congrArg Subtype.val this
  -- a chart ball around `e x`
  set p := e x with hp
  have hOpen : IsOpen (e.target ∩ e.symm ⁻¹' B) := e.isOpen_inter_preimage_symm hBo
  have hpO : p ∈ e.target ∩ e.symm ⁻¹' B :=
    ⟨e.map_source hxe, by rw [mem_preimage, hp, e.left_inv hxe]; exact hxB⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hOpen p hpO
  set ε := δ / 2 with hε
  have hε0 : 0 < ε := half_pos hδ
  have hcb : closedBall p ε ⊆ e.target ∩ e.symm ⁻¹' B :=
    (closedBall_subset_ball (by rw [hε]; linarith)).trans hball
  have hsymmB : ∀ z ∈ closedBall p ε, e.symm z ∈ B := fun z hz => (hcb hz).2
  have hsc : ContinuousOn e.symm (closedBall p ε) :=
    e.continuousOn_symm.mono fun z hz => (hcb hz).1
  have hGc : ContinuousOn (fun z => G (e.symm z)) (closedBall p ε) :=
    hGs.continuousOn.comp hsc fun z hz => (hsymmB z hz).2
  have hAc : IsClosed A := hA.isClosed
  -- the positive minimum `η` of `|G - G x|` over `A` on the sphere
  have hSphc : IsCompact (sphere p ε ∩ e.symm ⁻¹' A) :=
    (isCompact_sphere p ε).of_isClosed_subset
      ((hsc.mono sphere_subset_closedBall).preimage_isClosed_of_isClosed isClosed_sphere hAc)
      inter_subset_left
  have hfpos : ∀ z ∈ sphere p ε ∩ e.symm ⁻¹' A, 0 < ‖G (e.symm z) - G x‖ := by
    rintro z ⟨hzs, hzA⟩
    rw [norm_pos_iff, sub_ne_zero]
    intro hGz
    have hzx := hBiso _ (hsymmB z (sphere_subset_closedBall hzs)) hzA hGz
    have hzp : z = p := by
      rw [← e.right_inv (hcb (sphere_subset_closedBall hzs)).1, hzx]
    rw [hzp, mem_sphere, dist_self] at hzs
    linarith
  obtain ⟨η, hη, hηle⟩ : ∃ η > 0, ∀ z ∈ sphere p ε ∩ e.symm ⁻¹' A,
      η ≤ ‖G (e.symm z) - G x‖ := by
    rcases (sphere p ε ∩ e.symm ⁻¹' A).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hSphc.exists_isMinOn h
        ((continuous_norm.comp_continuousOn (hGc.sub continuousOn_const)).mono
          fun z hz => sphere_subset_closedBall hz.1)
      exact ⟨_, hfpos z₀ hz₀, fun z hz => hmin hz⟩
  -- the open set `W` on which `G` has finite fibres over `A`
  set W₀ : Set X := e.source ∩ e ⁻¹' ball p ε with hW₀
  have hW₀B : W₀ ⊆ B := fun y hy => by
    have := hsymmB (e y) (ball_subset_closedBall hy.2)
    rwa [e.left_inv hy.1] at this
  set W : Set X := W₀ ∩ G ⁻¹' ball (G x) η with hW
  have hWo : IsOpen W :=
    (hGs.continuousOn.mono fun y hy => (hW₀B hy).2).isOpen_inter_preimage
      (e.isOpen_inter_preimage isOpen_ball) isOpen_ball
  have hxW : x ∈ W := ⟨⟨hxe, mem_ball_self hε0⟩, mem_ball_self hη⟩
  have hfin : ∀ w : ComplexModel (n' + k), ‖w - G x‖ < η → (A ∩ W ∩ G ⁻¹' {w}).Finite := by
    intro w hw
    set K : Set (ComplexModel n) :=
      closedBall p ε ∩ (fun z => (e.symm z, G (e.symm z))) ⁻¹' (A ×ˢ {w}) with hK
    have hKc : IsCompact K :=
      (isCompact_closedBall p ε).of_isClosed_subset
        ((hsc.prodMk hGc).preimage_isClosed_of_isClosed isClosed_closedBall
          (hAc.prod isClosed_singleton)) inter_subset_left
    have hKball : K ⊆ ball p ε := by
      rintro z ⟨hzc, hzA, hzw⟩
      rw [mem_closedBall] at hzc
      rw [mem_ball]
      refine lt_of_le_of_ne hzc fun hzε => ?_
      have h1 := hηle z ⟨by rw [mem_sphere]; exact hzε, hzA⟩
      have hzw' : G (e.symm z) = w := hzw
      rw [hzw'] at h1
      linarith
    have hKfin : K.Finite := by
      set O : Opens (ComplexModel n) := ⟨ball p ε, isOpen_ball⟩ with hO
      set h : O → X := fun z => e.symm z with hh
      have hhs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ h :=
        contMDiff_restrict (U := O) ((contMDiffOn_chart_symm (n := ∞)).mono
          fun z hz => (hcb (ball_subset_closedBall hz)).1)
      have hGh : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n' + k)) ∞ (G ∘ h) :=
        hGs.comp_contMDiff hhs fun z => (hsymmB z (ball_subset_closedBall z.2)).2
      have hSa : IsComplexAnalyticSubset (n := n) (h ⁻¹' A ∩ (G ∘ h) ⁻¹' {w}) :=
        (isComplexAnalyticSubset_preimage hhs hA).inter
          (isComplexAnalyticSubset_preimage hGh (isComplexAnalyticSubset_singleton w))
      have hSK : ((↑) '' (h ⁻¹' A ∩ (G ∘ h) ⁻¹' {w}) : Set (ComplexModel n)) = K := by
        ext z
        constructor
        · rintro ⟨z', ⟨hz'A, hz'w⟩, rfl⟩
          exact ⟨ball_subset_closedBall z'.2, hz'A, hz'w⟩
        · intro hz
          exact ⟨⟨z, hKball hz⟩, ⟨hz.2.1, hz.2.2⟩, rfl⟩
      have hKa : IsComplexAnalyticSubset (n := n) (M := ComplexModel n) K := by
        rw [← hSK]
        exact isComplexAnalyticSubset_image_val hSa (by rw [hSK]; exact hKc.isClosed)
      exact finite_of_isCompact hKa hKc
    refine (hKfin.image e.symm).subset ?_
    rintro y ⟨⟨hyA, hyW⟩, hyw⟩
    refine ⟨e y, ⟨ball_subset_closedBall hyW.1.2, ?_, ?_⟩, e.left_inv hyW.1.1⟩
    · change e.symm (e y) ∈ A
      rw [e.left_inv hyW.1.1]
      exact hyA
    · change G (e.symm (e y)) ∈ ({w} : Set _)
      rw [e.left_inv hyW.1.1]
      exact hyw
  -- a regular point of `A` in `W`, on the open manifold `W`
  obtain ⟨y₀, hy₀W, j, hy₀⟩ := exists_regularAtDim_mem_nhds hA hx (hWo.mem_nhds hxW)
  have hjm : j = m := hpure y₀ j hy₀
  subst hjm
  set Wo : Opens X := ⟨W, hWo⟩ with hWo'
  set T' : Set Wo := (↑) ⁻¹' A with hT'
  set GW : Wo → ComplexModel (n' + k) := fun y => G y with hGW
  have hGWs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n' + k)) ∞ GW :=
    contMDiff_restrict (U := Wo) (hGs.mono fun y hy => (hW₀B hy.1).2)
  have hdisc : ∀ y ∈ T', ¬ AccPt y (𝓟 (T' ∩ GW ⁻¹' {GW y})) := by
    intro y hy
    refine not_accPt_of_finite ?_ y
    refine ((hfin (G y) (by simpa [dist_eq_norm] using y.2.2)).preimage
      Subtype.val_injective.injOn).subset ?_
    rintro y' ⟨hy'A, hy'G⟩
    exact ⟨⟨hy'A, y'.2⟩, hy'G⟩
  set y₀' : Wo := ⟨y₀, hy₀W⟩ with hy₀'def
  have hy₀' : RegularAtDim (n := n) T' y₀' j := regularAtDim_preimage_val_iff.mpr hy₀
  have hjn : j ≤ n := hy₀'.1
  set eW := complexChartAt (n := n) y₀' with heW
  obtain ⟨Ψ, hΨt, hΨ0, hflat⟩ := exists_chartFlattening hy₀' eW (mem_complexChartAt_source y₀')
  set e'' := complexChartAt (n := n' + k) (GW y₀') with he''
  have hw₀ : coordinateInclusion n j 0 ∈ Ψ.target := by
    rw [map_zero, ← hΨ0]
    exact Ψ.mapsTo_toFun Ψ.center_mem_source
  obtain ⟨w₁, V', hV'o, hw₁V', hV'mem, hHd, hrank⟩ := exists_param_rank_eq hjn eW e'' Ψ hΨt hflat
    (hGWs.mdifferentiable (by simp)) hdisc hw₀ (by simp [he'', complexChartAt, chartAt_self_eq]) univ_mem
  -- compare with the rank of `F`
  set pX := complexChartAt (n := n) (y₀ : X) with hpX
  have hsymm : ∀ z ∈ eW.val.target, ((eW.val.symm z : Wo) : X) = pX.val.symm z := fun z hz =>
    OpenPartialHomeomorph.subtypeRestr_symm_apply _ _ hz
  have hΨtX : Ψ.source ⊆ pX.val.target := hΨt.trans (chartAt_opens_target_subset y₀')
  have hflatX : ∀ z ∈ Ψ.source, (pX.val.symm z ∈ A ↔ Ψ.toFun z ∈ complexCoordinatePlane n j) :=
    fun z hz => by
      rw [← hsymm z (hΨt hz)]
      exact hflat z hz
  obtain ⟨hw₁t, -, -⟩ := hV'mem w₁ hw₁V'
  have hw₁s : Ψ.invFun (coordinateInclusion n j w₁) ∈ Ψ.source := Ψ.mapsTo_invFun hw₁t
  set y₁ : X := pX.val.symm (Ψ.invFun (coordinateInclusion n j w₁)) with hy₁
  have hy₁W : y₁ ∈ W := by
    rw [hy₁, ← hsymm _ (hΨt hw₁s)]
    exact (eW.val.symm _).2
  have hy₁U₁ : y₁ ∈ U₁ := (hW₀B hy₁W.1).2
  set e'C := complexChartAt (n := n') (F x) with he'C
  obtain ⟨hy₁A, hrk⟩ := rankAt_param_eq hjn pX e'C Ψ hΨtX hflatX hw₁t hy₁U₁.2
    (hF.mdifferentiable (by simp) y₁)
  have hy₁reg : RegularAtDim (n := n) A y₁ j := by
    refine regularAtDim_of_flattening_of_mem (x := (y₀ : X)) hjn Ψ (fun {y'} hy' hy'Ψ => ?_) hy₁A
      (pX.val.map_target (hΨtX hw₁s)) ?_
    · have h := hflatX _ hy'Ψ
      rwa [pX.val.left_inv hy'] at h
    · change pX.val (pX.val.symm _) ∈ Ψ.source
      rw [pX.val.right_inv (hΨtX hw₁s)]
      exact hw₁s
  have hr₁ := hr y₁ hy₁reg
  set HX : ComplexModel j → ComplexModel (n' + k) :=
    fun v => G (pX.val.symm (Ψ.invFun (coordinateInclusion n j v))) with hHX
  have hHeq : (fun v => e''.val (GW (param eW Ψ j v))) =ᶠ[𝓝 w₁] HX := by
    filter_upwards [(Ψ.isOpen_target.preimage (coordinateInclusion n j).continuous).mem_nhds hw₁t]
      with v hv
    change e''.val (G ((eW.val.symm (Ψ.invFun (coordinateInclusion n j v)) : Wo) : X)) = _
    rw [hsymm _ (hΨt (Ψ.mapsTo_invFun hv))]
    simp [he'', complexChartAt, hHX, chartAt_self_eq]
  have hHXd : DifferentiableAt ℂ HX w₁ :=
    ((hHd w₁ hw₁V').differentiableAt (hV'o.mem_nhds hw₁V')).congr_of_eventuallyEq hHeq.symm
  have hcomp : (fun v => fstCLM n' k (HX v)) =
      fun v => e'C.val (F (pX.val.symm (Ψ.invFun (coordinateInclusion n j v)))) := by
    funext v
    simp only [hHX, hGfst, he'C, complexChartAt, he']
  have hfd1 : fderiv ℂ (fun v => e'C.val (F (pX.val.symm (Ψ.invFun (coordinateInclusion n j v)))))
      w₁ = (fstCLM n' k).comp (fderiv ℂ HX w₁) := by
    rw [← hcomp]
    exact ((fstCLM n' k).hasFDerivAt.comp w₁ hHXd.hasFDerivAt).fderiv
  have hle : j ≤ rankAt (n := n) (n' := n') F A y₁ + k := by
    have h := hrank w₁ hw₁V'
    rw [hHeq.fderiv_eq] at h
    rw [← h, hrk, hfd1]
    exact (finrank_range_le_finrank_range_comp_add _ _).trans
      (Nat.add_le_add_left finrank_ker_fstCLM_le _)
  omega

end Main

end Hironaka.FibreDimensionLowerBound
