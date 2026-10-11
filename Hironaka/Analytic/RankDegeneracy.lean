/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.PureSingularLocus

set_option autoImplicit false

/-!
# Tangent spaces of analytic sets and the rank-degeneracy set of a map

Blueprint `rem:rank-degeneracy` (step M6 of the route to Remmert's proper mapping theorem,
`blueprint/src/remmert.tex`).

For an analytic subset `A` of a complex manifold `M` of dimension `n`, a point `y` and a chart `e`
of `M` at `y`, the *tangent space of `A` at `y` read in `e`* is the common kernel of the
differentials (in `e`) of all germs in the ideal `𝓘_A` at `y` (`tangentSpaceIn`).  For a
holomorphic `F : M → Y` the *rank of `F` on `A` at `y`* is the dimension of the image of that
space under the differential of `F` read in charts (`rankIn`, `rankAt` with the preferred charts).

* `tangentSpaceIn_eq_comap`, `rankIn_eq_rankIn`: both are independent of the charts (the rank
  exactly; the tangent space up to the derivative of the chart transition).
* `tangentSpaceIn_eq_range_of_flattening`: at a point of `A` covered by a flattening `Ψ` of `A`
  of dimension `m` (in any chart), the tangent space is the image of `ℂ^m` under the
  derivative of the parametrization `w ↦ Ψ⁻¹(w, 0)`; it has dimension `m`.
  `rankIn_eq_finrank_range_param` then computes the rank of `F` on `A` as the rank of the
  differential of `F` composed with the parametrization: this is how the constant-rank and
  generic-rank theorems for maps between vector spaces (`HolomorphicConstantRank`,
  `HolomorphicGenericRank`) are applied to `F` on the manifold of regular points.
* `tangentSpaceIn_eq_iInf_ker`: if `sᵢ` are Cartan generators of `𝓘_A` near `y ∈ A`, the
  tangent space is `⋂ ker dsᵢ`.
* `isComplexAnalyticSubset_rankDegeneracyLocus`: for `A` of pure dimension `m`,
  `S_r(F, A) = A_sing ∪ {y ∈ A_reg : rank_y (F|A) < r}` is analytic: near every point it is cut
  out by the generators `sᵢ` and the products of the `(n - m)`-minors of `(dsᵢ)` with the
  `(n - m + r)`-minors of the stacked Jacobian `(dsᵢ; dFⱼ)` (whose rank at a regular point is
  `n - m + rank`).

Sorry-free.
-/

open Set Filter Module
open scoped Topology Manifold

namespace Hironaka.RankDegeneracy

open AnalyticJacobianSingularCore StokesSingularLocusAnalytic AnalyticDimensionBasics
open RegularPatchNeighborhood RegularLocusDense HolomorphicIdealSheaves

open Hironaka

noncomputable section

variable {n n' : ℕ}

/-! ### Linear algebra -/

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **Rank of a finite family of functionals plus dimension of their common kernel.** -/
theorem finrank_span_add_finrank_iInf_ker [TopologicalSpace V] {ι : Type*} [Finite ι]
    (L : ι → (V →L[ℂ] ℂ)) :
    finrank ℂ (Submodule.span ℂ (range L)) +
      finrank ℂ (⨅ i, LinearMap.ker ((L i : V →L[ℂ] ℂ) : V →ₗ[ℂ] ℂ) : Submodule ℂ V) =
        finrank ℂ V := by
  set c : (V →L[ℂ] ℂ) →ₗ[ℂ] Module.Dual ℂ V := ContinuousLinearMap.coeLM ℂ with hc
  have hcinj : Function.Injective c := fun f g h => ContinuousLinearMap.coe_injective h
  set W : Submodule ℂ (Module.Dual ℂ V) := Submodule.span ℂ (range (c ∘ L)) with hW
  have hWmap : W = (Submodule.span ℂ (range L)).map c := by
    rw [hW, Submodule.map_span, range_comp]
  have hfin : finrank ℂ W = finrank ℂ (Submodule.span ℂ (range L)) := by
    rw [hWmap]
    exact ((Submodule.span ℂ (range L)).equivMapOfInjective c hcinj).finrank_eq.symm
  have hco : W.dualCoannihilator = ⨅ i, LinearMap.ker ((L i : V →L[ℂ] ℂ) : V →ₗ[ℂ] ℂ) := by
    ext v
    rw [Submodule.mem_dualCoannihilator, Submodule.mem_iInf]
    constructor
    · intro h i
      exact h _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro h φ hφ
      have hle : W ≤ LinearMap.ker (Module.Dual.eval ℂ V v) := by
        rw [hW, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simpa [hc] using h i
      simpa using hle hφ
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hco, hfin] at this
  exact this

/-- **Rank of a family of functionals on `ℂⁿ` by minors**: the span has dimension `< r` iff
every `r × r` minor of the matrix of values on the standard basis vanishes. -/
theorem finrank_span_lt_iff_minors_eq_zero {N r : ℕ} (L : Fin N → (ComplexModel n →L[ℂ] ℂ)) :
    finrank ℂ (Submodule.span ℂ (range L)) < r ↔
      ∀ (rows : Fin r → Fin N) (cols : Fin r → Fin n),
        (Matrix.of fun a b => L (rows a) (coordinateDirection (cols b))).det = 0 := by
  constructor
  · intro h rows cols
    by_contra hne
    set B : Matrix (Fin r) (Fin r) ℂ :=
      Matrix.of fun a b => L (rows a) (coordinateDirection (cols b)) with hB
    have hrow : LinearIndependent ℂ B.row :=
      Matrix.linearIndependent_rows_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det B).mpr (Ne.isUnit hne))
    let ev : (ComplexModel n →L[ℂ] ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
      { toFun := fun K b => K (coordinateDirection (cols b))
        map_add' := fun K K' => by ext b; simp
        map_smul' := fun c K => by ext b; simp }
    have hli : LinearIndependent ℂ (L ∘ rows) :=
      LinearIndependent.of_comp ev (show LinearIndependent ℂ (ev ∘ (L ∘ rows)) from hrow)
    have hle : Submodule.span ℂ (range (L ∘ rows)) ≤ Submodule.span ℂ (range L) :=
      Submodule.span_mono (range_comp_subset_range _ _)
    have := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hli, Fintype.card_fin] at this
    omega
  · intro h
    by_contra hge
    rw [not_lt] at hge
    obtain ⟨rows, cols, hrc⟩ := exists_minor_ne_zero_of_le_finrank L hge
    exact hrc (h rows cols)

end Linear

/-- The chain rule with the intermediate point named. -/
theorem fderiv_comp_of_eq {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    {f : E → F} {g : F → G} {x : E} {y : F} (hfx : f x = y) (hg : DifferentiableAt ℂ g y)
    (hf : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun z => g (f z)) x = (fderiv ℂ g y).comp (fderiv ℂ f x) := by
  subst hfx
  exact fderiv_comp x hg hf

/-! ### Charts -/

section Charts

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n') Y]
  [IsComplexManifold n' Y]

/-- A holomorphic map read in charts is differentiable. -/
theorem differentiableAt_chartReading {F : M → Y} (e : ComplexChart n M) (e' : ComplexChart n' Y)
    {y : M} (hye : y ∈ e.val.source) (hFy : F y ∈ e'.val.source)
    (hF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F y) :
    DifferentiableAt ℂ (fun w => e'.val (F (e.val.symm w))) (e.val y) := by
  have hq : e.val y ∈ e.val.target := e.val.map_source hye
  have hsq : e.val.symm (e.val y) = y := e.val.left_inv hye
  have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property hq
  have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F
      (e.val.symm (e.val y)) := by rw [hsq]; exact hF
  have h3 := mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n')) e'.property
    (show F (e.val.symm (e.val y)) ∈ e'.val.source by rw [hsq]; exact hFy)
  exact mdifferentiableAt_iff_differentiableAt.mp
    ((h3.comp (e.val.symm (e.val y)) h2).comp (e.val y) h1)

/-- The derivatives of the two chart transitions at a common point are mutually inverse. -/
theorem fderiv_transition_comp (e₁ e₂ : ComplexChart n M) {y : M} (hy₁ : y ∈ e₁.val.source)
    (hy₂ : y ∈ e₂.val.source) :
    (fderiv ℂ (fun w => e₁.val (e₂.val.symm w)) (e₂.val y)).comp
      (fderiv ℂ (fun w => e₂.val (e₁.val.symm w)) (e₁.val y)) =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
  have hq₁ : e₁.val y ∈ e₁.val.target := e₁.val.map_source hy₁
  have hd12 : DifferentiableAt ℂ (fun w => e₂.val (e₁.val.symm w)) (e₁.val y) := by
    simpa using differentiableAt_chartReading (F := id) e₁ e₂ hy₁ hy₂ mdifferentiableAt_id
  have hd21 : DifferentiableAt ℂ (fun w => e₁.val (e₂.val.symm w)) (e₂.val y) := by
    simpa using differentiableAt_chartReading (F := id) e₂ e₁ hy₂ hy₁ mdifferentiableAt_id
  have h12 : e₂.val (e₁.val.symm (e₁.val y)) = e₂.val y := by rw [e₁.val.left_inv hy₁]
  have hc := fderiv_comp_of_eq (g := fun w => e₁.val (e₂.val.symm w))
    (f := fun w => e₂.val (e₁.val.symm w)) h12 hd21 hd12
  have hev : (fun w => e₁.val (e₂.val.symm (e₂.val (e₁.val.symm w))))
      =ᶠ[𝓝 (e₁.val y)] id := by
    have hO : e₁.val.target ∩ e₁.val.symm ⁻¹' e₂.val.source ∈ 𝓝 (e₁.val y) :=
      (e₁.val.isOpen_inter_preimage_symm e₂.val.open_source).mem_nhds
        ⟨hq₁, by simpa [e₁.val.left_inv hy₁] using hy₂⟩
    filter_upwards [hO] with w hw
    simp [e₂.val.left_inv hw.2, e₁.val.right_inv hw.1]
  rw [← hc, hev.fderiv_eq, fderiv_id]

theorem injective_fderiv_transition (e₁ e₂ : ComplexChart n M) {y : M} (hy₁ : y ∈ e₁.val.source)
    (hy₂ : y ∈ e₂.val.source) :
    Function.Injective (fderiv ℂ (fun w => e₂.val (e₁.val.symm w)) (e₁.val y)) := by
  intro u v huv
  have h := fderiv_transition_comp e₁ e₂ hy₁ hy₂
  have hu := congrArg (fun L => L u) h
  have hv := congrArg (fun L => L v) h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hu hv
  rw [← hu, ← hv, huv]

theorem surjective_fderiv_transition (e₁ e₂ : ComplexChart n M) {y : M}
    (hy₁ : y ∈ e₁.val.source) (hy₂ : y ∈ e₂.val.source) :
    Function.Surjective (fderiv ℂ (fun w => e₂.val (e₁.val.symm w)) (e₁.val y)) :=
  (LinearMap.injective_iff_surjective
    (f := ((fderiv ℂ (fun w => e₂.val (e₁.val.symm w)) (e₁.val y) :
      ComplexModel n →L[ℂ] ComplexModel n) : ComplexModel n →ₗ[ℂ] ComplexModel n))).mp
    (injective_fderiv_transition e₁ e₂ hy₁ hy₂)

end Charts

/-! ### Tangent spaces and ranks -/

section Tangent

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n') Y]
  [IsComplexManifold n' Y]

/-- **The tangent space of `A` at `y`, read in the chart `e`**: the common kernel of the
differentials (in `e`, at `e y`) of all holomorphic germs vanishing on `A` near `y`. -/
def tangentSpaceIn (e : ComplexChart n M) (A : Set M) (y : M) : Submodule ℂ (ComplexModel n) :=
  ⨅ (g : M → ℂ) (_ : (vanishingIdeal (n := n) A).mem y g),
    LinearMap.ker ((fderiv ℂ (fun w => g (e.val.symm w)) (e.val y) : ComplexModel n →L[ℂ] ℂ) :
      ComplexModel n →ₗ[ℂ] ℂ)

omit [IsComplexManifold n M] in
theorem mem_tangentSpaceIn {e : ComplexChart n M} {A : Set M} {y : M} {v : ComplexModel n} :
    v ∈ tangentSpaceIn e A y ↔ ∀ g, (vanishingIdeal (n := n) A).mem y g →
      fderiv ℂ (fun w => g (e.val.symm w)) (e.val y) v = 0 := by
  simp [tangentSpaceIn, Submodule.mem_iInf]

/-- The differential of `F` at `y`, read in the charts `e` of `M` and `e'` of `Y`. -/
def chartDeriv (e : ComplexChart n M) (e' : ComplexChart n' Y) (F : M → Y) (y : M) :
    ComplexModel n →L[ℂ] ComplexModel n' :=
  fderiv ℂ (fun w => e'.val (F (e.val.symm w))) (e.val y)

/-- **The rank of `F` on `A` at `y`, read in charts**: the dimension of the image of the tangent
space of `A` under the differential of `F`. -/
def rankIn (e : ComplexChart n M) (e' : ComplexChart n' Y) (F : M → Y) (A : Set M) (y : M) : ℕ :=
  finrank ℂ ((tangentSpaceIn e A y).map
    ((chartDeriv e e' F y : ComplexModel n →L[ℂ] ComplexModel n') :
      ComplexModel n →ₗ[ℂ] ComplexModel n'))

/-- **The rank of `F` on `A` at `y`** (`rank d(F|_A)_y` at regular points), read in the
preferred charts. -/
def rankAt (F : M → Y) (A : Set M) (y : M) : ℕ :=
  rankIn (complexChartAt (n := n) y) (complexChartAt (n := n') (F y)) F A y

variable (n n') in
/-- **The rank-degeneracy set** `S_r(F, A) = A_sing ∪ {y ∈ A_reg : rank_y (F|A) < r}` of a set `A`
of pure dimension `m`. -/
def rankDegeneracyLocus (F : M → Y) (A : Set M) (m r : ℕ) : Set M :=
  (A \ regularLocus (n := n) A m) ∪
    {y | y ∈ regularLocus (n := n) A m ∧ rankAt (n := n) (n' := n') F A y < r}

omit [IsComplexManifold n M] [IsComplexManifold n' Y] in
theorem rankDegeneracyLocus_subset (F : M → Y) (A : Set M) (m r : ℕ) :
    rankDegeneracyLocus n n' F A m r ⊆ A := by
  rintro y (hy | hy)
  · exact hy.1
  · exact regularLocus_subset A m hy.1

/-- **Change of chart for the tangent space**: in the chart `e₁` it is the preimage of the
tangent space in `e₂` under the derivative of the chart transition. -/
theorem tangentSpaceIn_eq_comap (e₁ e₂ : ComplexChart n M) (A : Set M) {y : M}
    (hy₁ : y ∈ e₁.val.source) (hy₂ : y ∈ e₂.val.source) :
    tangentSpaceIn e₁ A y = (tangentSpaceIn e₂ A y).comap
      ((fderiv ℂ (fun w => e₂.val (e₁.val.symm w)) (e₁.val y) :
        ComplexModel n →L[ℂ] ComplexModel n) : ComplexModel n →ₗ[ℂ] ComplexModel n) := by
  set D := fderiv ℂ (fun w => e₂.val (e₁.val.symm w)) (e₁.val y) with hD
  have hq₁ : e₁.val y ∈ e₁.val.target := e₁.val.map_source hy₁
  have hd12 : DifferentiableAt ℂ (fun w => e₂.val (e₁.val.symm w)) (e₁.val y) := by
    have h := differentiableAt_chartReading (F := id) e₁ e₂ hy₁ hy₂ mdifferentiableAt_id
    simpa using h
  have h12 : e₂.val (e₁.val.symm (e₁.val y)) = e₂.val y := by rw [e₁.val.left_inv hy₁]
  -- the differential of a germ in `e₁` is its differential in `e₂` composed with `D`
  have hkey : ∀ g, (vanishingIdeal (n := n) A).mem y g →
      fderiv ℂ (fun w => g (e₁.val.symm w)) (e₁.val y) =
        (fderiv ℂ (fun w => g (e₂.val.symm w)) (e₂.val y)).comp D := by
    intro g hg
    have hq₂ : e₂.val y ∈ e₂.val.target := e₂.val.map_source hy₂
    have hgd : DifferentiableAt ℂ (fun w => g (e₂.val.symm w)) (e₂.val y) :=
      differentiableAt_chart e₂ hq₂ (by rw [e₂.val.left_inv hy₂]; exact hg.1.self_of_nhds)
    have hev : (fun w => g (e₁.val.symm w)) =ᶠ[𝓝 (e₁.val y)]
        fun w => g (e₂.val.symm (e₂.val (e₁.val.symm w))) := by
      have hO : e₁.val.target ∩ e₁.val.symm ⁻¹' e₂.val.source ∈ 𝓝 (e₁.val y) :=
        (e₁.val.isOpen_inter_preimage_symm e₂.val.open_source).mem_nhds
          ⟨hq₁, by simpa [e₁.val.left_inv hy₁] using hy₂⟩
      filter_upwards [hO] with w hw
      simp [e₂.val.left_inv hw.2]
    rw [hev.fderiv_eq, hD]
    exact fderiv_comp_of_eq (g := fun w => g (e₂.val.symm w))
      (f := fun w => e₂.val (e₁.val.symm w)) h12 hgd hd12
  ext v
  rw [Submodule.mem_comap, mem_tangentSpaceIn, mem_tangentSpaceIn]
  refine forall_congr' fun g => forall_congr' fun hg => ?_
  rw [hkey g hg]
  rfl

/-- **Change of chart in the target** does not change the dimension of the image. -/
theorem finrank_map_chartDeriv_target (e : ComplexChart n M) (e₁' e₂' : ComplexChart n' Y)
    {F : M → Y} {y : M} (hye : y ∈ e.val.source) (hF₁ : F y ∈ e₁'.val.source)
    (hF₂ : F y ∈ e₂'.val.source)
    (hF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F y)
    (T : Submodule ℂ (ComplexModel n)) :
    finrank ℂ (T.map ((chartDeriv e e₁' F y : ComplexModel n →L[ℂ] ComplexModel n') :
      ComplexModel n →ₗ[ℂ] ComplexModel n')) =
    finrank ℂ (T.map ((chartDeriv e e₂' F y : ComplexModel n →L[ℂ] ComplexModel n') :
      ComplexModel n →ₗ[ℂ] ComplexModel n')) := by
  set D' := fderiv ℂ (fun w => e₂'.val (e₁'.val.symm w)) (e₁'.val (F y)) with hD'
  have hd₁ := differentiableAt_chartReading e e₁' hye hF₁ hF
  have hq : e.val y ∈ e.val.target := e.val.map_source hye
  have hsq : e.val.symm (e.val y) = y := e.val.left_inv hye
  have hdT : DifferentiableAt ℂ (fun w => e₂'.val (e₁'.val.symm w)) (e₁'.val (F y)) := by
    have h := differentiableAt_chartReading (F := id) e₁' e₂' hF₁ hF₂ mdifferentiableAt_id
    simpa using h
  have hcont : ContinuousAt (fun w => F (e.val.symm w)) (e.val y) :=
    (show ContinuousAt F (e.val.symm (e.val y)) by rw [hsq]; exact hF.continuousAt).comp
      (e.val.continuousAt_symm hq)
  have hev : (fun w => e₂'.val (F (e.val.symm w))) =ᶠ[𝓝 (e.val y)]
      fun w => e₂'.val (e₁'.val.symm (e₁'.val (F (e.val.symm w)))) := by
    filter_upwards [hcont.preimage_mem_nhds (e₁'.val.open_source.mem_nhds
      (by rw [hsq]; exact hF₁))] with w hw
    rw [e₁'.val.left_inv hw]
  have hchain : chartDeriv e e₂' F y = D'.comp (chartDeriv e e₁' F y) := by
    rw [chartDeriv, hev.fderiv_eq, chartDeriv]
    exact fderiv_comp_of_eq (g := fun w => e₂'.val (e₁'.val.symm w))
      (f := fun w => e₁'.val (F (e.val.symm w))) (by rw [hsq]) hdT hd₁
  have hinj : Function.Injective D' := injective_fderiv_transition e₁' e₂' hF₁ hF₂
  rw [hchain, ContinuousLinearMap.toLinearMap_comp, Submodule.map_comp]
  exact (Submodule.equivMapOfInjective (D' : ComplexModel n' →ₗ[ℂ] ComplexModel n') hinj
    (T.map ((chartDeriv e e₁' F y : ComplexModel n →L[ℂ] ComplexModel n') :
      ComplexModel n →ₗ[ℂ] ComplexModel n'))).finrank_eq

/-- **The rank does not depend on the charts.** -/
theorem rankIn_eq_rankIn (e₁ e₂ : ComplexChart n M) (e₁' e₂' : ComplexChart n' Y) {F : M → Y}
    (A : Set M) {y : M} (hy₁ : y ∈ e₁.val.source) (hy₂ : y ∈ e₂.val.source)
    (hF₁ : F y ∈ e₁'.val.source) (hF₂ : F y ∈ e₂'.val.source)
    (hF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F y) :
    rankIn e₁ e₁' F A y = rankIn e₂ e₂' F A y := by
  -- first change the target chart of the first reading to `e₂'`
  have h1 : rankIn e₁ e₁' F A y = rankIn e₁ e₂' F A y :=
    finrank_map_chartDeriv_target e₁ e₁' e₂' hy₁ hF₁ hF₂ hF _
  rw [h1]
  -- then the source chart
  set D := fderiv ℂ (fun w => e₂.val (e₁.val.symm w)) (e₁.val y) with hD
  have hsq : e₁.val.symm (e₁.val y) = y := e₁.val.left_inv hy₁
  have hd₂ := differentiableAt_chartReading e₂ e₂' hy₂ hF₂ hF
  have hd12 : DifferentiableAt ℂ (fun w => e₂.val (e₁.val.symm w)) (e₁.val y) := by
    have h := differentiableAt_chartReading (F := id) e₁ e₂ hy₁ hy₂ mdifferentiableAt_id
    simpa using h
  have h12 : e₂.val (e₁.val.symm (e₁.val y)) = e₂.val y := by rw [hsq]
  have hq₁ : e₁.val y ∈ e₁.val.target := e₁.val.map_source hy₁
  have hev : (fun w => e₂'.val (F (e₁.val.symm w))) =ᶠ[𝓝 (e₁.val y)]
      fun w => e₂'.val (F (e₂.val.symm (e₂.val (e₁.val.symm w)))) := by
    have hO : e₁.val.target ∩ e₁.val.symm ⁻¹' e₂.val.source ∈ 𝓝 (e₁.val y) :=
      (e₁.val.isOpen_inter_preimage_symm e₂.val.open_source).mem_nhds
        ⟨hq₁, by simpa [hsq] using hy₂⟩
    filter_upwards [hO] with w hw
    rw [e₂.val.left_inv hw.2]
  have hchain : chartDeriv e₁ e₂' F y = (chartDeriv e₂ e₂' F y).comp D := by
    rw [chartDeriv, hev.fderiv_eq, chartDeriv]
    exact fderiv_comp_of_eq (g := fun w => e₂'.val (F (e₂.val.symm w)))
      (f := fun w => e₂.val (e₁.val.symm w)) h12 hd₂ hd12
  have hsurj : Function.Surjective D := surjective_fderiv_transition e₁ e₂ hy₁ hy₂
  unfold rankIn
  rw [tangentSpaceIn_eq_comap e₁ e₂ A hy₁ hy₂, hchain, ContinuousLinearMap.toLinearMap_comp,
    Submodule.map_comp, Submodule.map_comap_eq_of_surjective hsurj]

/-- **`rankAt` in arbitrary charts.** -/
theorem rankAt_eq_rankIn (e : ComplexChart n M) (e' : ComplexChart n' Y) {F : M → Y} (A : Set M)
    {y : M} (hye : y ∈ e.val.source) (hFy : F y ∈ e'.val.source)
    (hF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F y) :
    rankAt (n := n) (n' := n') F A y = rankIn e e' F A y :=
  rankIn_eq_rankIn _ _ _ _ A (mem_complexChartAt_source y) hye
    (mem_complexChartAt_source (F y)) hFy hF

end Tangent

/-! ### Tangent spaces at the points of a flattening -/

section Flattening

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n') Y]
  [IsComplexManifold n' Y]

/-- The derivative of the inverse of a local biholomorphism is a left inverse of its derivative. -/
theorem fderiv_invFun_comp_fderiv_toFun {p₀ : ComplexModel n}
    (Ψ : LocalHolomorphicEquivAt (n := n) p₀) {z : ComplexModel n} (hz : z ∈ Ψ.source) :
    (fderiv ℂ Ψ.invFun (Ψ.toFun z)).comp (fderiv ℂ Ψ.toFun z) =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
  have hzt : Ψ.toFun z ∈ Ψ.target := Ψ.mapsTo_toFun hz
  have hd : DifferentiableAt ℂ Ψ.toFun z :=
    Ψ.toFun_holomorphic.differentiableAt (Ψ.isOpen_source.mem_nhds hz)
  have hdi : DifferentiableAt ℂ Ψ.invFun (Ψ.toFun z) :=
    Ψ.invFun_holomorphic.differentiableAt (Ψ.isOpen_target.mem_nhds hzt)
  have hev : (fun w => Ψ.invFun (Ψ.toFun w)) =ᶠ[𝓝 z] id := by
    filter_upwards [Ψ.isOpen_source.mem_nhds hz] with w hw
    exact Ψ.left_inv w hw
  rw [← fderiv_comp_of_eq (g := Ψ.invFun) (f := Ψ.toFun) rfl hdi hd, hev.fderiv_eq, fderiv_id]

/-- **The tangent space at a point of a flattening.**  Let `Ψ` flatten `A` to the plane
`ℂ^m × 0` in the chart `e` (on all of `Ψ.source`).  At every point `y ∈ A` with `e y ∈ Ψ.source`,
the tangent space of `A` read in `e` is the image of the derivative of the parametrization
`w ↦ Ψ⁻¹(w, 0)` at `w₀ = pr(Ψ (e y))`. -/
theorem tangentSpaceIn_eq_range_of_flattening {A : Set M} {m : ℕ} (e : ComplexChart n M)
    {p₀ : ComplexModel n} (Ψ : LocalHolomorphicEquivAt (n := n) p₀)
    (hflat : ∀ z ∈ Ψ.source, (e.val.symm z ∈ A ↔ Ψ.toFun z ∈ complexCoordinatePlane n m))
    {y : M} (hye : y ∈ e.val.source) (hyΨ : e.val y ∈ Ψ.source) (hyA : y ∈ A) :
    tangentSpaceIn e A y = LinearMap.range
      ((fderiv ℂ (fun w => Ψ.invFun (coordinateInclusion n m w))
        (coordinateProjection n m (Ψ.toFun (e.val y))) : ComplexModel m →L[ℂ] ComplexModel n) :
        ComplexModel m →ₗ[ℂ] ComplexModel n) := by
  set q := e.val y with hq
  set w₀ := coordinateProjection n m (Ψ.toFun q) with hw₀
  have hqt : q ∈ e.val.target := e.val.map_source hye
  have hsq : e.val.symm q = y := e.val.left_inv hye
  have hqplane : Ψ.toFun q ∈ complexCoordinatePlane n m :=
    (hflat q hyΨ).mp (by rw [hsq]; exact hyA)
  have hincl : coordinateInclusion n m w₀ = Ψ.toFun q :=
    coordinateInclusion_coordinateProjection hqplane
  have hΨqt : Ψ.toFun q ∈ Ψ.target := Ψ.mapsTo_toFun hyΨ
  have hinv : Ψ.invFun (Ψ.toFun q) = q := Ψ.left_inv q hyΨ
  have hdΨ : DifferentiableAt ℂ Ψ.toFun q :=
    Ψ.toFun_holomorphic.differentiableAt (Ψ.isOpen_source.mem_nhds hyΨ)
  have hdinv : DifferentiableAt ℂ Ψ.invFun (Ψ.toFun q) :=
    Ψ.invFun_holomorphic.differentiableAt (Ψ.isOpen_target.mem_nhds hΨqt)
  have hdP : DifferentiableAt ℂ (fun w => Ψ.invFun (coordinateInclusion n m w)) w₀ := by
    have h := hdinv
    rw [← hincl] at h
    exact h.comp w₀ (coordinateInclusion n m).differentiableAt
  have hDP : fderiv ℂ (fun w => Ψ.invFun (coordinateInclusion n m w)) w₀ =
      (fderiv ℂ Ψ.invFun (Ψ.toFun q)).comp (coordinateInclusion n m) := by
    rw [fderiv_comp_of_eq (g := Ψ.invFun) (f := fun w => coordinateInclusion n m w) hincl hdinv
      (coordinateInclusion n m).differentiableAt]
    congr 1
    exact (coordinateInclusion n m).fderiv
  apply le_antisymm
  · intro v hv
    rw [mem_tangentSpaceIn] at hv
    -- the normal coordinates of `Ψ` lie in the ideal, so `dΨ v` lies in the plane
    have hnorm : fderiv ℂ Ψ.toFun q v ∈ complexCoordinatePlane n m := by
      intro j hj
      have hI : (vanishingIdeal (n := n) A).mem y (fun p => Ψ.toFun (e.val p) j) := by
        refine ⟨holomorphicAt_coord_chart Ψ e hye hyΨ j, ?_⟩
        have hO : IsOpen (e.val.source ∩ e.val ⁻¹' Ψ.source) :=
          e.val.isOpen_inter_preimage Ψ.isOpen_source
        filter_upwards [hO.mem_nhds ⟨hye, hyΨ⟩] with p hp hpA
        exact (hflat (e.val p) hp.2).mp (by rw [e.val.left_inv hp.1]; exact hpA) j hj
      have h := hv _ hI
      have hloc : (fun w => Ψ.toFun (e.val (e.val.symm w)) j) =ᶠ[𝓝 q]
          fun w => Ψ.toFun w j := by
        filter_upwards [e.val.open_target.mem_nhds hqt] with w hw
        rw [e.val.right_inv hw]
      rw [hloc.fderiv_eq, fderiv_coordinate_eq hdΨ j] at h
      simpa using h
    refine ⟨coordinateProjection n m (fderiv ℂ Ψ.toFun q v), ?_⟩
    change fderiv ℂ (fun w => Ψ.invFun (coordinateInclusion n m w)) w₀
      (coordinateProjection n m (fderiv ℂ Ψ.toFun q v)) = v
    rw [hDP, ContinuousLinearMap.comp_apply, coordinateInclusion_coordinateProjection hnorm]
    have h := congrArg (fun L => L v) (fderiv_invFun_comp_fderiv_toFun Ψ hyΨ)
    simpa using h
  · rintro _ ⟨u, rfl⟩
    rw [mem_tangentSpaceIn]
    intro g hg
    have hPq : Ψ.invFun (coordinateInclusion n m w₀) = q := by rw [hincl, hinv]
    have hgd : DifferentiableAt ℂ (fun w => g (e.val.symm w)) q :=
      differentiableAt_chart e hqt (by rw [hsq]; exact hg.1.self_of_nhds)
    -- `g` vanishes on the image of the parametrization near `w₀`
    have hT : ∀ᶠ w in 𝓝 w₀, coordinateInclusion n m w ∈ Ψ.target :=
      (coordinateInclusion n m).continuous.continuousAt.preimage_mem_nhds
        (by rw [hincl]; exact Ψ.isOpen_target.mem_nhds hΨqt)
    have hlim : Tendsto (fun w => e.val.symm (Ψ.invFun (coordinateInclusion n m w))) (𝓝 w₀)
        (𝓝 y) := by
      have h1 : ContinuousAt (fun w => Ψ.invFun (coordinateInclusion n m w)) w₀ :=
        hdP.continuousAt
      have h2 : ContinuousAt e.val.symm (Ψ.invFun (coordinateInclusion n m w₀)) := by
        rw [hPq]; exact e.val.continuousAt_symm hqt
      have h3 := ContinuousAt.comp (g := e.val.symm)
        (f := fun w => Ψ.invFun (coordinateInclusion n m w)) h2 h1
      have h4 : Tendsto (fun w => e.val.symm (Ψ.invFun (coordinateInclusion n m w))) (𝓝 w₀)
          (𝓝 (e.val.symm (Ψ.invFun (coordinateInclusion n m w₀)))) := h3.tendsto
      rwa [hPq, hsq] at h4
    have hzero : (fun w => g (e.val.symm (Ψ.invFun (coordinateInclusion n m w))))
        =ᶠ[𝓝 w₀] fun _ => 0 := by
      filter_upwards [hT, hlim.eventually hg.2] with w hw1 hw2
      apply hw2
      have hws : Ψ.invFun (coordinateInclusion n m w) ∈ Ψ.source := Ψ.mapsTo_invFun hw1
      refine (hflat _ hws).mpr ?_
      rw [Ψ.right_inv _ hw1]
      exact coordinateInclusion_mem_complexCoordinatePlane w
    have hc := fderiv_comp_of_eq (g := fun w => g (e.val.symm w))
      (f := fun w => Ψ.invFun (coordinateInclusion n m w)) hPq hgd hdP
    rw [hzero.fderiv_eq, fderiv_const_apply] at hc
    have h := congrArg (fun L => L u) hc
    simpa using h.symm

/-- **The tangent space at a point of a flattening has dimension `m`.** -/
theorem finrank_tangentSpaceIn_of_flattening {A : Set M} {m : ℕ} (hm : m ≤ n)
    (e : ComplexChart n M) {p₀ : ComplexModel n} (Ψ : LocalHolomorphicEquivAt (n := n) p₀)
    (hflat : ∀ z ∈ Ψ.source, (e.val.symm z ∈ A ↔ Ψ.toFun z ∈ complexCoordinatePlane n m))
    {y : M} (hye : y ∈ e.val.source) (hyΨ : e.val y ∈ Ψ.source) (hyA : y ∈ A) :
    finrank ℂ (tangentSpaceIn e A y) = m := by
  rw [tangentSpaceIn_eq_range_of_flattening e Ψ hflat hye hyΨ hyA]
  set q := e.val y with hq
  have hqplane : Ψ.toFun q ∈ complexCoordinatePlane n m :=
    (hflat q hyΨ).mp (by rw [e.val.left_inv hye]; exact hyA)
  have hincl : coordinateInclusion n m (coordinateProjection n m (Ψ.toFun q)) = Ψ.toFun q :=
    coordinateInclusion_coordinateProjection hqplane
  have hΨqt : Ψ.toFun q ∈ Ψ.target := Ψ.mapsTo_toFun hyΨ
  have hdinv : DifferentiableAt ℂ Ψ.invFun (Ψ.toFun q) :=
    Ψ.invFun_holomorphic.differentiableAt (Ψ.isOpen_target.mem_nhds hΨqt)
  have hDP : fderiv ℂ (fun w => Ψ.invFun (coordinateInclusion n m w))
      (coordinateProjection n m (Ψ.toFun q)) =
      (fderiv ℂ Ψ.invFun (Ψ.toFun q)).comp (coordinateInclusion n m) := by
    rw [fderiv_comp_of_eq (g := Ψ.invFun) (f := fun w => coordinateInclusion n m w) hincl hdinv
      (coordinateInclusion n m).differentiableAt]
    congr 1
    exact (coordinateInclusion n m).fderiv
  have hinj : Function.Injective (fderiv ℂ (fun w => Ψ.invFun (coordinateInclusion n m w))
      (coordinateProjection n m (Ψ.toFun q))) := by
    rw [hDP]
    intro u v huv
    -- `dΨ⁻¹` is injective because `dΨ ∘ dΨ⁻¹ = id`
    have hright : (fderiv ℂ Ψ.toFun q).comp (fderiv ℂ Ψ.invFun (Ψ.toFun q)) =
        ContinuousLinearMap.id ℂ (ComplexModel n) := by
      have hdΨ : DifferentiableAt ℂ Ψ.toFun q :=
        Ψ.toFun_holomorphic.differentiableAt (Ψ.isOpen_source.mem_nhds hyΨ)
      have hev : (fun w => Ψ.toFun (Ψ.invFun w)) =ᶠ[𝓝 (Ψ.toFun q)] id := by
        filter_upwards [Ψ.isOpen_target.mem_nhds hΨqt] with w hw
        exact Ψ.right_inv w hw
      have hc := fderiv_comp_of_eq (g := Ψ.toFun) (f := Ψ.invFun) (x := Ψ.toFun q)
        (Ψ.left_inv q hyΨ) hdΨ hdinv
      rw [hev.fderiv_eq, fderiv_id] at hc
      exact hc.symm
    have h2 := congrArg (fun x => fderiv ℂ Ψ.toFun q x) huv
    simp only [ContinuousLinearMap.comp_apply] at h2
    have hl := congrArg (fun L => L (coordinateInclusion n m u)) hright
    have hr := congrArg (fun L => L (coordinateInclusion n m v)) hright
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hl hr
    rw [hl, hr] at h2
    have := congrArg (coordinateProjection n m) h2
    rwa [coordinateProjection_coordinateInclusion hm, coordinateProjection_coordinateInclusion hm]
      at this
  rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace, Fintype.card_fin]

/-- **The rank of `F` on `A` through a parametrization.**  At a point `y ∈ A` covered by a
flattening `Ψ` of `A` (in the chart `e`), the rank of `F` on `A` is the rank of the differential of
`F` (read in `e'`) composed with the parametrization `w ↦ e⁻¹ Ψ⁻¹(w, 0)`. -/
theorem rankIn_eq_finrank_range_param {A : Set M} {m : ℕ} (e : ComplexChart n M)
    (e' : ComplexChart n' Y) {F : M → Y} {p₀ : ComplexModel n}
    (Ψ : LocalHolomorphicEquivAt (n := n) p₀)
    (hflat : ∀ z ∈ Ψ.source, (e.val.symm z ∈ A ↔ Ψ.toFun z ∈ complexCoordinatePlane n m))
    {y : M} (hye : y ∈ e.val.source) (hyΨ : e.val y ∈ Ψ.source) (hyA : y ∈ A)
    (hFy : F y ∈ e'.val.source)
    (hF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F y) :
    rankIn e e' F A y = finrank ℂ (LinearMap.range
      ((fderiv ℂ (fun w => e'.val (F (e.val.symm (Ψ.invFun (coordinateInclusion n m w)))))
        (coordinateProjection n m (Ψ.toFun (e.val y))) : ComplexModel m →L[ℂ] ComplexModel n') :
        ComplexModel m →ₗ[ℂ] ComplexModel n')) := by
  set q := e.val y with hq
  set w₀ := coordinateProjection n m (Ψ.toFun q) with hw₀
  have hqplane : Ψ.toFun q ∈ complexCoordinatePlane n m :=
    (hflat q hyΨ).mp (by rw [e.val.left_inv hye]; exact hyA)
  have hincl : coordinateInclusion n m w₀ = Ψ.toFun q :=
    coordinateInclusion_coordinateProjection hqplane
  have hΨqt : Ψ.toFun q ∈ Ψ.target := Ψ.mapsTo_toFun hyΨ
  have hPq : Ψ.invFun (coordinateInclusion n m w₀) = q := by rw [hincl, Ψ.left_inv q hyΨ]
  have hdinv : DifferentiableAt ℂ Ψ.invFun (Ψ.toFun q) :=
    Ψ.invFun_holomorphic.differentiableAt (Ψ.isOpen_target.mem_nhds hΨqt)
  have hdP : DifferentiableAt ℂ (fun w => Ψ.invFun (coordinateInclusion n m w)) w₀ := by
    have h := hdinv
    rw [← hincl] at h
    exact h.comp w₀ (coordinateInclusion n m).differentiableAt
  have hdF := differentiableAt_chartReading e e' hye hFy hF
  have hc := fderiv_comp_of_eq (g := fun w => e'.val (F (e.val.symm w)))
    (f := fun w => Ψ.invFun (coordinateInclusion n m w)) hPq hdF hdP
  unfold rankIn
  rw [tangentSpaceIn_eq_range_of_flattening e Ψ hflat hye hyΨ hyA, ← LinearMap.range_comp,
    hc, ContinuousLinearMap.toLinearMap_comp]
  rfl

/-- **The rank at a parametrized point.**  For every `w` with `(w, 0) ∈ Ψ.target`, the point
`y = e⁻¹ Ψ⁻¹(w, 0)` lies in `A`, and `rank_y (F|A)` is the rank at `w` of `F` composed with the
parametrization. -/
theorem rankAt_param_eq {A : Set M} {m : ℕ} (hm : m ≤ n) (e : ComplexChart n M)
    (e' : ComplexChart n' Y) {F : M → Y} {p₀ : ComplexModel n}
    (Ψ : LocalHolomorphicEquivAt (n := n) p₀) (hΨt : Ψ.source ⊆ e.val.target)
    (hflat : ∀ z ∈ Ψ.source, (e.val.symm z ∈ A ↔ Ψ.toFun z ∈ complexCoordinatePlane n m))
    {w : ComplexModel m} (hw : coordinateInclusion n m w ∈ Ψ.target)
    (hFw : F (e.val.symm (Ψ.invFun (coordinateInclusion n m w))) ∈ e'.val.source)
    (hF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F
      (e.val.symm (Ψ.invFun (coordinateInclusion n m w)))) :
    e.val.symm (Ψ.invFun (coordinateInclusion n m w)) ∈ A ∧
    rankAt (n := n) (n' := n') F A (e.val.symm (Ψ.invFun (coordinateInclusion n m w))) =
      finrank ℂ (LinearMap.range
        ((fderiv ℂ (fun v => e'.val (F (e.val.symm (Ψ.invFun (coordinateInclusion n m v))))) w :
          ComplexModel m →L[ℂ] ComplexModel n') : ComplexModel m →ₗ[ℂ] ComplexModel n')) := by
  set z := Ψ.invFun (coordinateInclusion n m w) with hz
  have hzs : z ∈ Ψ.source := Ψ.mapsTo_invFun hw
  have hzt : z ∈ e.val.target := hΨt hzs
  have hye : e.val.symm z ∈ e.val.source := e.val.map_target hzt
  have hez : e.val (e.val.symm z) = z := e.val.right_inv hzt
  have hΨz : Ψ.toFun z = coordinateInclusion n m w := Ψ.right_inv _ hw
  have hyA : e.val.symm z ∈ A :=
    (hflat z hzs).mpr (by rw [hΨz]; exact coordinateInclusion_mem_complexCoordinatePlane w)
  refine ⟨hyA, ?_⟩
  rw [rankAt_eq_rankIn e e' A hye hFw hF,
    rankIn_eq_finrank_range_param e e' Ψ hflat hye (by rw [hez]; exact hzs) hyA hFw hF, hez, hΨz,
    coordinateProjection_coordinateInclusion hm]

/-- **The tangent space at a regular point of dimension `m` has dimension `m`.** -/
theorem finrank_tangentSpaceIn_of_regularAtDim {A : Set M} {m : ℕ} (e : ComplexChart n M)
    {y : M} (hye : y ∈ e.val.source) (hy : RegularAtDim (n := n) A y m) :
    finrank ℂ (tangentSpaceIn e A y) = m := by
  obtain ⟨Ψ, -, -, hflat⟩ := exists_chartFlattening hy e hye
  exact finrank_tangentSpaceIn_of_flattening hy.1 e Ψ hflat hye Ψ.center_mem_source hy.2.1

omit [IsComplexManifold n' Y] in
/-- **The rank on `A` at a regular point of dimension `m` is at most `m`.** -/
theorem rankAt_le_of_regularAtDim {A : Set M} {m : ℕ} (F : M → Y) {y : M}
    (hy : RegularAtDim (n := n) A y m) : rankAt (n := n) (n' := n') F A y ≤ m := by
  unfold rankAt rankIn
  rw [← finrank_tangentSpaceIn_of_regularAtDim (complexChartAt (n := n) y)
    (mem_complexChartAt_source y) hy]
  exact Submodule.finrank_map_le _ _

end Flattening

/-! ### Cartan generators and the stacked Jacobian -/

section Cartan

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n') Y]
  [IsComplexManifold n' Y]

/-- **The tangent space from Cartan generators**: if the `sᵢ` generate `𝓘_A` on `U` and cut out
`A` there, then at `y ∈ A ∩ U` the tangent space is the common kernel of the `dsᵢ`. -/
theorem tangentSpaceIn_eq_iInf_ker {A U : Set M} (hU : IsOpen U) {N : ℕ} {s : Fin N → M → ℂ}
    (hs : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) U)
    (hspan : ∀ y ∈ U, ∀ g, (vanishingIdeal (n := n) A).mem y g ↔
      IsInSpanAt (n := n) (· ∈ range s) y g)
    (hzero : ∀ y ∈ U, (y ∈ A ↔ ∀ i, s i y = 0)) (e : ComplexChart n M) {y : M}
    (hyU : y ∈ U) (hye : y ∈ e.val.source) (hyA : y ∈ A) :
    tangentSpaceIn e A y = ⨅ i, LinearMap.ker
      ((fderiv ℂ (fun w => s i (e.val.symm w)) (e.val y) : ComplexModel n →L[ℂ] ℂ) :
        ComplexModel n →ₗ[ℂ] ℂ) := by
  have hs0 : ∀ i, s i y = 0 := (hzero y hyU).mp hyA
  have hsd : ∀ i, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) y := fun i =>
    (hs i).mdifferentiableAt (hU.mem_nhds hyU)
  apply le_antisymm
  · intro v hv
    rw [mem_tangentSpaceIn] at hv
    rw [Submodule.mem_iInf]
    intro i
    have hmem : (vanishingIdeal (n := n) A).mem y (s i) := by
      refine ⟨Filter.mem_of_superset (hU.mem_nhds hyU) fun z hz =>
        (hs i z hz).mdifferentiableAt (hU.mem_nhds hz), ?_⟩
      filter_upwards [hU.mem_nhds hyU] with z hz hzA
      exact (hzero z hz).mp hzA i
    exact hv _ hmem
  · intro v hv
    rw [Submodule.mem_iInf] at hv
    rw [mem_tangentSpaceIn]
    intro g hg
    have hmem := fderiv_mem_span_of_isInSpanAt e hye hs0 hsd ((hspan y hyU g).mp hg)
    have hle : Submodule.span ℂ (range fun i => fderiv ℂ (fun w => s i (e.val.symm w)) (e.val y))
        ≤ LinearMap.ker (((ContinuousLinearMap.apply ℂ ℂ v :
          (ComplexModel n →L[ℂ] ℂ) →L[ℂ] ℂ)) : (ComplexModel n →L[ℂ] ℂ) →ₗ[ℂ] ℂ) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa using hv i
    simpa using hle hmem

/-- The equations of `A` stacked with the components of `F`, read in charts. -/
def stackedEquations (e : ComplexChart n M) (e' : ComplexChart n' Y) (F : M → Y) {N : ℕ}
    (s : Fin N → M → ℂ) : Fin (N + n') → ComplexModel n → ℂ :=
  Fin.append (fun i w => s i (e.val.symm w)) (fun j w => e'.val (F (e.val.symm w)) j)

/-- **The rank of the stacked Jacobian** `(dsᵢ; dFⱼ)` at a regular point of dimension `m` is
`n - m + rank_y (F|A)`. -/
theorem finrank_span_fderiv_stackedEquations {A U : Set M} (hU : IsOpen U) {N : ℕ}
    {s : Fin N → M → ℂ} (hs : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) U)
    (hspan : ∀ y ∈ U, ∀ g, (vanishingIdeal (n := n) A).mem y g ↔
      IsInSpanAt (n := n) (· ∈ range s) y g)
    (hzero : ∀ y ∈ U, (y ∈ A ↔ ∀ i, s i y = 0)) (e : ComplexChart n M) (e' : ComplexChart n' Y)
    {F : M → Y} {y : M} (hyU : y ∈ U) (hye : y ∈ e.val.source) (hFy : F y ∈ e'.val.source)
    (hF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F y) {m : ℕ}
    (hy : RegularAtDim (n := n) A y m) :
    finrank ℂ (Submodule.span ℂ
      (range fun k => fderiv ℂ (stackedEquations e e' F s k) (e.val y))) =
      (n - m) + rankIn e e' F A y := by
  have hm : m ≤ n := hy.1
  have hyA : y ∈ A := hy.2.1
  set T := tangentSpaceIn e A y with hT
  set dF := chartDeriv e e' F y with hdF
  have hdFe := differentiableAt_chartReading e e' hye hFy hF
  have h1 := finrank_span_add_finrank_iInf_ker
    (fun k => fderiv ℂ (stackedEquations e e' F s k) (e.val y))
  -- the common kernel of the stacked differentials
  have hker : (⨅ k, LinearMap.ker ((fderiv ℂ (stackedEquations e e' F s k) (e.val y) :
      ComplexModel n →L[ℂ] ℂ) : ComplexModel n →ₗ[ℂ] ℂ)) =
      T ⊓ LinearMap.ker (dF : ComplexModel n →ₗ[ℂ] ComplexModel n') := by
    rw [hT, tangentSpaceIn_eq_iInf_ker hU hs hspan hzero e hyU hye hyA]
    ext v
    simp only [Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe]
    rw [Fin.forall_fin_add]
    simp only [stackedEquations, Fin.append_left, Fin.append_right]
    refine and_congr Iff.rfl ?_
    have hcomp : ∀ j : Fin n', fderiv ℂ (fun w => e'.val (F (e.val.symm w)) j) (e.val y) =
        (EuclideanSpace.proj (𝕜 := ℂ) j).comp dF := fun j =>
      ((EuclideanSpace.proj (𝕜 := ℂ) j).hasFDerivAt.comp (e.val y) hdFe.hasFDerivAt).fderiv
    simp only [hcomp, ContinuousLinearMap.comp_apply]
    constructor
    · intro h
      ext j
      simpa using h j
    · intro h j
      simp [h]
  -- the tangent space has dimension `m`
  have hTm : finrank ℂ T = m := finrank_tangentSpaceIn_of_regularAtDim e hye hy
  -- rank-nullity for `dF` on `T`
  have hrn : finrank ℂ (T ⊓ LinearMap.ker (dF : ComplexModel n →ₗ[ℂ] ComplexModel n') :
      Submodule ℂ (ComplexModel n)) +
      rankIn e e' F A y = m := by
    have h := LinearMap.finrank_range_add_finrank_ker
      ((dF : ComplexModel n →ₗ[ℂ] ComplexModel n').domRestrict T)
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, hTm] at h
    have h2 : finrank ℂ ((LinearMap.ker (dF : ComplexModel n →ₗ[ℂ] ComplexModel n')).comap
        T.subtype) = finrank ℂ (T ⊓ LinearMap.ker (dF : ComplexModel n →ₗ[ℂ] ComplexModel n') :
          Submodule ℂ (ComplexModel n)) := by
      rw [← Submodule.finrank_map_subtype_eq T, Submodule.map_comap_subtype]
    rw [h2] at h
    unfold rankIn
    rw [← hT, ← hdF]
    omega
  rw [hker, finrank_euclideanSpace, Fintype.card_fin] at h1
  omega

end Cartan

/-! ### The rank-degeneracy set is analytic -/

section Main

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n') Y]
  [IsComplexManifold n' Y]

/-- The products of the `p`-minors of `g` with the `q`-minors of `G`. -/
def productMinor {N K : ℕ} (g : Fin N → ComplexModel n → ℂ) (G : Fin K → ComplexModel n → ℂ)
    (p q : ℕ) (k : Fin (Fintype.card (JacobianMinorIndex N n p × JacobianMinorIndex K n q)))
    (w : ComplexModel n) : ℂ :=
  jacobianMinor g ((Fintype.equivFin _).symm k).1.1 ((Fintype.equivFin _).symm k).1.2 w *
    jacobianMinor G ((Fintype.equivFin _).symm k).2.1 ((Fintype.equivFin _).symm k).2.2 w

/-- The products vanish iff all `p`-minors of `g` or all `q`-minors of `G` vanish. -/
theorem productMinor_eq_zero_iff {N K : ℕ} (g : Fin N → ComplexModel n → ℂ)
    (G : Fin K → ComplexModel n → ℂ) (p q : ℕ) (z : ComplexModel n) :
    (∀ k, productMinor g G p q k z = 0) ↔
      (∀ a : JacobianMinorIndex N n p, jacobianMinor g a.1 a.2 z = 0) ∨
        (∀ b : JacobianMinorIndex K n q, jacobianMinor G b.1 b.2 z = 0) := by
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    obtain ⟨a, ha⟩ := not_forall.mp hc.1
    obtain ⟨b, hb⟩ := not_forall.mp hc.2
    have h1 := h (Fintype.equivFin _ (a, b))
    simp only [productMinor, Equiv.symm_apply_apply, mul_eq_zero] at h1
    exact h1.elim ha hb
  · rintro (h | h) k
    · simp only [productMinor]
      rw [h, zero_mul]
    · simp only [productMinor]
      rw [h, mul_zero]

/-- **The rank-degeneracy set is analytic** (`rem:rank-degeneracy`).  Let `A` be an analytic
subset of pure dimension `m` of `M` and `F : M → Y` holomorphic.  For every `r`,
`S_r(F, A) = A_sing ∪ {y ∈ A_reg : rank_y (F|A) < r}` is an analytic subset of `M`: in the preferred
chart at any point it is cut out by Cartan generators `sᵢ` of `𝓘_A` and the products of the
`(n - m)`-minors of their Jacobian with the `(n - m + r)`-minors of the Jacobian of
`(sᵢ, Fⱼ)`. -/
theorem isComplexAnalyticSubset_rankDegeneracyLocus {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {m : ℕ} (hpure : IsPureDim (n := n) A m)
    {F : M → Y} (hF : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F) (r : ℕ) :
    IsComplexAnalyticSubset (n := n) (rankDegeneracyLocus n n' F A m r) := by
  classical
  by_cases hm : m ≤ n
  swap
  · -- no regular point of dimension `m > n` exists, so `A = ∅`
    have hA0 : A = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
      obtain ⟨y, -, j, hy⟩ := exists_regularAtDim_mem_nhds hA hx univ_mem
      have hj := hpure y j hy
      exact hm (hj ▸ hy.1)
    have h0 : rankDegeneracyLocus n n' F A m r = ∅ :=
      subset_empty_iff.mp (hA0 ▸ rankDegeneracyLocus_subset F A m r)
    rw [h0]
    exact isComplexAnalyticSubset_empty
  intro x
  obtain ⟨U, hU, hxU, N, s, hs, hspan, hzeroU⟩ :=
    StokesSingularLocus.exists_cartanGenerators hA hA.isClosed x
  set e := complexChartAt (n := n) x with he
  set e' := complexChartAt (n := n') (F x) with he'
  set U' : Set M := U ∩ F ⁻¹' e'.val.source with hU'def
  have hU' : IsOpen U' := hU.inter (e'.val.open_source.preimage hF.continuous)
  set W : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' U' with hW
  have hWo : IsOpen W := e.val.isOpen_inter_preimage_symm hU'
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  set g : Fin N → ComplexModel n → ℂ := fun i w => s i (e.val.symm w) with hg
  set G := stackedEquations e e' F s with hG
  have hgd : ∀ i, DifferentiableOn ℂ (g i) W := fun i z hz =>
    (differentiableAt_chart e hz.1
      ((hs i).mdifferentiableAt (hU.mem_nhds hz.2.1))).differentiableWithinAt
  have hGd : ∀ k, DifferentiableOn ℂ (G k) W := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa [hG, stackedEquations] using hgd i
    · intro z hz
      have hyz : e.val.symm z ∈ e.val.source := e.val.map_target hz.1
      have hd := differentiableAt_chartReading e e' hyz hz.2.2 (hF _)
      rw [e.val.right_inv hz.1] at hd
      simp only [hG, stackedEquations, Fin.append_right]
      exact ((EuclideanSpace.proj (𝕜 := ℂ) j).differentiableAt.comp z hd).differentiableWithinAt
  refine ⟨{ generatorCount := N + Fintype.card
              (JacobianMinorIndex N n (n - m) × JacobianMinorIndex (N + n') n (n - m + r))
            generator := Fin.addCases g (productMinor g G (n - m) (n - m + r))
            coordinateNeighborhood := W
            isOpen_coordinateNeighborhood := hWo
            center_mem_coordinateNeighborhood :=
              ⟨e.val.map_source hxe, by
                rw [mem_preimage, e.val.left_inv hxe]
                exact ⟨hxU, mem_complexChartAt_source (F x)⟩⟩
            coordinateNeighborhood_subset_target := inter_subset_left
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · intro a
    refine Fin.addCases (fun i => ?_) (fun k => ?_) a
    · simpa using hgd i
    · simp only [Fin.addCases_right]
      exact (differentiableOn_jacobianMinor hWo hgd _ _).mul
        (differentiableOn_jacobianMinor hWo hGd _ _)
  · intro y hye hyW
    have hyU' : y ∈ U' := by
      have := hyW.2
      rwa [mem_preimage, e.val.left_inv hye] at this
    have hyU : y ∈ U := hyU'.1
    have hFy : F y ∈ e'.val.source := hyU'.2
    have hgy : ∀ i, g i (e.val y) = s i y := fun i => by simp [hg, e.val.left_inv hye]
    rw [Fin.forall_fin_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [productMinor_eq_zero_iff]
    have hAiff : y ∈ A ↔ ∀ i, g i (e.val y) = 0 := by
      rw [hzeroU y hyU]
      simp only [hgy]
    -- (a) at a regular point some `(n - m)`-minor of the `sᵢ` is nonzero
    have ha : RegularAtDim (n := n) A y m →
        ¬ ∀ a : JacobianMinorIndex N n (n - m), jacobianMinor g a.1 a.2 (e.val y) = 0 := by
      intro hreg hall
      obtain ⟨rows, cols, hrc⟩ := exists_minor_ne_zero_of_le_finrank _
        (le_finrank_span_fderiv_of_regularAtDim hU hs hspan hzeroU e hyU hye hreg)
      exact hrc (hall (rows, cols))
    -- (b) at a singular point of `A` every `(n - m)`-minor vanishes
    have hb : y ∈ A → ¬ RegularAtDim (n := n) A y m →
        ∀ a : JacobianMinorIndex N n (n - m), jacobianMinor g a.1 a.2 (e.val y) = 0 := by
      intro hyA hreg a
      by_contra hne
      exact hreg (PureSingularLocus.regularAtDim_of_minor_ne_zero_of_isPureDim hm hpure x hU hs
        hzeroU hyU hye hyA a.1 a.2 hne)
    -- (c) at a regular point the stacked minors detect the rank
    have hc : RegularAtDim (n := n) A y m →
        ((∀ b : JacobianMinorIndex (N + n') n (n - m + r),
          jacobianMinor G b.1 b.2 (e.val y) = 0) ↔ rankAt (n := n) (n' := n') F A y < r) := by
      intro hreg
      rw [rankAt_eq_rankIn e e' A hye hFy (hF y)]
      have hst := finrank_span_fderiv_stackedEquations hU hs hspan hzeroU e e' hyU hye hFy (hF y)
        hreg
      have hlt := finrank_span_lt_iff_minors_eq_zero (r := n - m + r)
        (fun k => fderiv ℂ (G k) (e.val y))
      rw [hst] at hlt
      constructor
      · intro hall
        have := hlt.mpr fun rows cols => hall (rows, cols)
        omega
      · intro hlt' b
        exact hlt.mp (by omega) b.1 b.2
    simp only [rankDegeneracyLocus, mem_union, Set.mem_sdiff, mem_ofPred_eq, mem_regularLocus]
    by_cases hreg : RegularAtDim (n := n) A y m
    · have hyA : y ∈ A := hreg.2.1
      rw [← hAiff, ← hc hreg]
      constructor
      · rintro (⟨-, h⟩ | ⟨-, h⟩)
        · exact absurd hreg h
        · exact ⟨hyA, Or.inr h⟩
      · rintro ⟨-, h | h⟩
        · exact absurd h (ha hreg)
        · exact Or.inr ⟨hreg, h⟩
    · rw [← hAiff]
      constructor
      · rintro (⟨hyA, -⟩ | ⟨h, -⟩)
        · exact ⟨hyA, Or.inl (hb hyA hreg)⟩
        · exact absurd h hreg
      · rintro ⟨hyA, -⟩
        exact Or.inl ⟨hyA, hreg⟩

end Main

end

end Hironaka.RankDegeneracy
