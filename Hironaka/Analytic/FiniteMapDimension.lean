/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.ConstantRankImageGraphExact
import Hironaka.Support.HolomorphicMaxRankDenseExact
import Hironaka.Analytic.RankDegeneracy
import Hironaka.Analytic.HolomorphicGenericRank
import Hironaka.Analytic.HolomorphicConstantRank
import Hironaka.Analytic.ConstantRankSubmanifold
import Hironaka.Analytic.DimensionMonotone

set_option autoImplicit false

/-!
# Maps with discrete fibres

Blueprint `rem:finite-map-dimension` (Demailly, *Complex analytic and differential geometry*, II.8.1;
step M8 of the route to Remmert's proper mapping theorem, `blueprint/src/remmert.tex`).

Let `T` be a subset of a complex manifold `M`, `G : M → Y` holomorphic with discrete fibres on `T`
(no point `y ∈ T` is an accumulation point of `T ∩ G⁻¹(G y)`).

* `exists_param_rank_eq` (the core): on a flattening `Ψ` of `T` of dimension `k` in a chart `e`,
  near every parametrized point there is an open set of parameters on which the parametrized map
  `w ↦ e' G e⁻¹ Ψ⁻¹(w, 0)` has rank `k` everywhere.  The maximal rank `ρ` of that map on a ball
  is attained on an open set (`HolomorphicGenericRank.isOpen_maxRank`); if `ρ < k`, the constant
  rank theorem (`HolomorphicConstantRank.exists_ne_mem_fibre`) makes the image of a max-rank point
  an accumulation point of its own fibre in `T`.
* `exists_regularAtDim_rankAt_eq` (part (1), local form): every neighbourhood of a regular point
  of `T` of dimension `k` contains a regular point of dimension `k` at which `rank (G|T) = k`.
* `dimLE_of_discrete_fibres` (part (2)): if `G(T) ⊆ D` with `D` analytic and `dim D ≤ a`, then
  `dim T ≤ a`: the image of the rank-`k` piece is a `k`-dimensional submanifold inside `D`
  (`ConstantRankSubmanifold.exists_image_eq_graph`, read in a chart of `Y`), so `D` has regular
  points of dimension `≥ k` (`DimensionMonotone.locDimGE_of_regularAtDim_subset`).

Sorry-free.
-/

open Set Filter Module Metric
open scoped Topology Manifold

namespace Hironaka.FiniteMapDimension

open RegularLocusDense StokesSingularLocusAnalytic AnalyticDimensionBasics RankDegeneracy

noncomputable section

variable {n n' : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n') Y]
  [IsComplexManifold n' Y]

/-- The parametrization `w ↦ e⁻¹ Ψ⁻¹(w, 0)` attached to a flattening `Ψ` read in the chart `e`. -/
def param (e : ComplexChart n M) {p₀ : ComplexModel n} (Ψ : LocalHolomorphicEquivAt (n := n) p₀)
    (k : ℕ) (w : ComplexModel k) : M :=
  e.val.symm (Ψ.invFun (coordinateInclusion n k w))

omit [IsComplexManifold n M] in
/-- The parametrization is continuous where `(w, 0)` lies in the target of `Ψ`. -/
theorem continuousOn_param (e : ComplexChart n M) {p₀ : ComplexModel n}
    (Ψ : LocalHolomorphicEquivAt (n := n) p₀) (hΨt : Ψ.source ⊆ e.val.target) (k : ℕ) :
    ContinuousOn (param e Ψ k) (coordinateInclusion n k ⁻¹' Ψ.target) := by
  have h1 : ContinuousOn (fun w => Ψ.invFun (coordinateInclusion n k w))
      (coordinateInclusion n k ⁻¹' Ψ.target) :=
    Ψ.invFun_holomorphic.continuousOn.comp (coordinateInclusion n k).continuous.continuousOn
      fun w hw => hw
  exact e.val.continuousOn_symm.comp h1 fun w hw => hΨt (Ψ.mapsTo_invFun hw)

omit [IsComplexManifold n M] in
/-- Parametrized points lie in `T`. -/
theorem param_mem {T : Set M} {k : ℕ} (e : ComplexChart n M) {p₀ : ComplexModel n}
    (Ψ : LocalHolomorphicEquivAt (n := n) p₀)
    (hflat : ∀ z ∈ Ψ.source, (e.val.symm z ∈ T ↔ Ψ.toFun z ∈ complexCoordinatePlane n k))
    {w : ComplexModel k} (hw : coordinateInclusion n k w ∈ Ψ.target) : param e Ψ k w ∈ T :=
  (hflat _ (Ψ.mapsTo_invFun hw)).mpr (by
    rw [Ψ.right_inv _ hw]; exact coordinateInclusion_mem_complexCoordinatePlane w)

omit [IsComplexManifold n M] in
/-- The parametrization is injective where `(w, 0)` lies in the target of `Ψ`. -/
theorem param_injOn (e : ComplexChart n M) {p₀ : ComplexModel n}
    (Ψ : LocalHolomorphicEquivAt (n := n) p₀) (hΨt : Ψ.source ⊆ e.val.target) {k : ℕ}
    (hk : k ≤ n) : InjOn (param e Ψ k) (coordinateInclusion n k ⁻¹' Ψ.target) := by
  intro z hz w hw hzw
  have h1 : Ψ.invFun (coordinateInclusion n k z) = Ψ.invFun (coordinateInclusion n k w) := by
    have := congrArg e.val hzw
    simp only [param] at this
    rwa [e.val.right_inv (hΨt (Ψ.mapsTo_invFun hz)),
      e.val.right_inv (hΨt (Ψ.mapsTo_invFun hw))] at this
  have h2 := congrArg Ψ.toFun h1
  rw [Ψ.right_inv _ hz, Ψ.right_inv _ hw] at h2
  have h3 := congrArg (coordinateProjection n k) h2
  rwa [coordinateProjection_coordinateInclusion hk, coordinateProjection_coordinateInclusion hk]
    at h3

/-- The parametrized map `w ↦ e' (G (e⁻¹ Ψ⁻¹(w, 0)))` is holomorphic where it is defined. -/
theorem differentiableAt_param {G : M → Y} (e : ComplexChart n M) (e' : ComplexChart n' Y)
    {p₀ : ComplexModel n} (Ψ : LocalHolomorphicEquivAt (n := n) p₀)
    (hΨt : Ψ.source ⊆ e.val.target) {k : ℕ}
    (hG : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') G) {w : ComplexModel k}
    (hw : coordinateInclusion n k w ∈ Ψ.target) (hGw : G (param e Ψ k w) ∈ e'.val.source) :
    DifferentiableAt ℂ (fun v => e'.val (G (param e Ψ k v))) w := by
  set v := Ψ.invFun (coordinateInclusion n k w) with hv
  have hvt : v ∈ e.val.target := hΨt (Ψ.mapsTo_invFun hw)
  have hd1 := differentiableAt_chartReading e e' (y := e.val.symm v) (e.val.map_target hvt) hGw
    (hG _)
  rw [e.val.right_inv hvt] at hd1
  have hd2 : DifferentiableAt ℂ (fun w => Ψ.invFun (coordinateInclusion n k w)) w :=
    (Ψ.invFun_holomorphic.differentiableAt (Ψ.isOpen_target.mem_nhds hw)).comp w
      (coordinateInclusion n k).differentiableAt
  exact DifferentiableAt.comp (g := fun u => e'.val (G (e.val.symm u)))
    (f := fun w => Ψ.invFun (coordinateInclusion n k w)) w hd1 hd2

/-- **The core of `rem:finite-map-dimension`.**  Let `Ψ` flatten `T` to `ℂ^k × 0` in the chart `e`,
`G` be holomorphic with discrete fibres on `T`, and `w₀` a parameter whose point is in `T` with
`G` of it in the chart `e'`.  For every neighbourhood `N` of the point of `w₀` there is a nonempty
open set `V` of parameters, mapped into `N` and into the domain of the chart reading, on which
the parametrized map `H = e' ∘ G ∘ param` is holomorphic of rank `k` everywhere. -/
theorem exists_param_rank_eq {T : Set M} {k : ℕ} (hk : k ≤ n) (e : ComplexChart n M)
    (e' : ComplexChart n' Y) {p₀ : ComplexModel n} (Ψ : LocalHolomorphicEquivAt (n := n) p₀)
    (hΨt : Ψ.source ⊆ e.val.target)
    (hflat : ∀ z ∈ Ψ.source, (e.val.symm z ∈ T ↔ Ψ.toFun z ∈ complexCoordinatePlane n k))
    {G : M → Y} (hG : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') G)
    (hdisc : ∀ y ∈ T, ¬ AccPt y (𝓟 (T ∩ G ⁻¹' {G y})))
    {w₀ : ComplexModel k} (hw₀ : coordinateInclusion n k w₀ ∈ Ψ.target)
    (hGw₀ : G (param e Ψ k w₀) ∈ e'.val.source) {N : Set M} (hN : N ∈ 𝓝 (param e Ψ k w₀)) :
    ∃ (w₁ : ComplexModel k) (V : Set (ComplexModel k)), IsOpen V ∧ w₁ ∈ V ∧
      (∀ z ∈ V, coordinateInclusion n k z ∈ Ψ.target ∧ G (param e Ψ k z) ∈ e'.val.source ∧
        param e Ψ k z ∈ N) ∧
      DifferentiableOn ℂ (fun v => e'.val (G (param e Ψ k v))) V ∧
      ∀ z ∈ V, finrank ℂ (LinearMap.range
        ((fderiv ℂ (fun v => e'.val (G (param e Ψ k v))) z :
          ComplexModel k →L[ℂ] ComplexModel n') : ComplexModel k →ₗ[ℂ] ComplexModel n')) = k := by
  classical
  set H : ComplexModel k → ComplexModel n' := fun v => e'.val (G (param e Ψ k v)) with hH
  set Ω₀ : Set (ComplexModel k) := coordinateInclusion n k ⁻¹' Ψ.target with hΩ₀
  have hΩ₀o : IsOpen Ω₀ := Ψ.isOpen_target.preimage (coordinateInclusion n k).continuous
  have hPc := continuousOn_param e Ψ hΨt k
  set Ω : Set (ComplexModel k) :=
    Ω₀ ∩ param e Ψ k ⁻¹' (G ⁻¹' e'.val.source ∩ interior N) with hΩ
  have hΩo : IsOpen Ω := hPc.isOpen_inter_preimage hΩ₀o
    ((e'.val.open_source.preimage hG.continuous).inter isOpen_interior)
  have hw₀Ω : w₀ ∈ Ω := ⟨hw₀, hGw₀, mem_interior_iff_mem_nhds.mpr hN⟩
  have hΩmem : ∀ z ∈ Ω, coordinateInclusion n k z ∈ Ψ.target ∧ G (param e Ψ k z) ∈ e'.val.source ∧
      param e Ψ k z ∈ N := fun z hz => ⟨hz.1, hz.2.1, interior_subset hz.2.2⟩
  have hHd : DifferentiableOn ℂ H Ω := fun z hz =>
    (differentiableAt_param e e' Ψ hΨt hG hz.1 hz.2.1).differentiableWithinAt
  -- the maximal rank on `Ω` is attained
  set R : ComplexModel k → ℕ := fun z => finrank ℂ (LinearMap.range
    ((fderiv ℂ H z : ComplexModel k →L[ℂ] ComplexModel n') :
      ComplexModel k →ₗ[ℂ] ComplexModel n')) with hR
  have hRk : ∀ z, R z ≤ k := fun z => by
    refine (LinearMap.finrank_range_le _).trans ?_
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hfin : (R '' Ω).Finite := (Set.finite_Iic k).subset fun j ⟨z, _, hz⟩ => hz ▸ hRk z
  have hne : (R '' Ω).Nonempty := ⟨R w₀, w₀, hw₀Ω, rfl⟩
  obtain ⟨w₁, hw₁Ω, hw₁R⟩ := hne.csSup_mem hfin
  set j₀ := sSup (R '' Ω) with hj₀
  have hmax : ∀ z ∈ Ω, R z ≤ j₀ := fun z hz => le_csSup hfin.bddAbove ⟨z, hz, rfl⟩
  set V : Set (ComplexModel k) := {z ∈ Ω | R z = j₀} with hV
  have hVo : IsOpen V := HolomorphicGenericRank.isOpen_maxRank hΩo hHd hmax
  have hw₁V : w₁ ∈ V := ⟨hw₁Ω, hw₁R⟩
  have hVΩ : V ⊆ Ω := fun z hz => hz.1
  -- the maximal rank is `k`
  have hj₀k : j₀ = k := by
    refine le_antisymm (hw₁R ▸ hRk w₁) ?_
    by_contra hlt
    rw [not_le] at hlt
    have hlt' : j₀ < finrank ℂ (ComplexModel k) := by
      rw [finrank_euclideanSpace, Fintype.card_fin]; exact hlt
    set y₁ := param e Ψ k w₁ with hy₁
    have hy₁T : y₁ ∈ T := param_mem e Ψ hflat hw₁Ω.1
    apply hdisc y₁ hy₁T
    rw [accPt_iff_nhds]
    intro U hU
    have hPw : ContinuousAt (param e Ψ k) w₁ := hPc.continuousAt (hΩ₀o.mem_nhds hw₁Ω.1)
    obtain ⟨z, hzN, hzw, hHz⟩ := HolomorphicConstantRank.exists_ne_mem_fibre hVo (hHd.mono hVΩ)
      (fun z hz => hz.2) hw₁V hlt' (inter_mem (hPw.preimage_mem_nhds hU) (hVo.mem_nhds hw₁V))
    have hzΩ : z ∈ Ω := hVΩ hzN.2
    refine ⟨param e Ψ k z, ⟨hzN.1, param_mem e Ψ hflat hzΩ.1, ?_⟩, ?_⟩
    · -- same image under `G`: `e'` is injective on its source
      show G (param e Ψ k z) = G y₁
      exact e'.val.injOn hzΩ.2.1 hw₁Ω.2.1 hHz
    · intro hzy
      exact hzw (param_injOn e Ψ hΨt hk hzΩ.1 hw₁Ω.1 hzy)
  refine ⟨w₁, V, hVo, hw₁V, fun z hz => hΩmem z (hVΩ hz), hHd.mono hVΩ, fun z hz => ?_⟩
  exact hz.2.trans hj₀k

/-- **`rem:finite-map-dimension` (1), local form.**  If `G` has discrete fibres on `T`, every
neighbourhood of a regular point of `T` of dimension `k` contains a regular point of `T` of
dimension `k` at which `rank (G|T) = k`. -/
theorem exists_regularAtDim_rankAt_eq {T : Set M} {G : M → Y}
    (hG : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') G)
    (hdisc : ∀ y ∈ T, ¬ AccPt y (𝓟 (T ∩ G ⁻¹' {G y}))) {y : M} {k : ℕ}
    (hy : RegularAtDim (n := n) T y k) {N : Set M} (hN : N ∈ 𝓝 y) :
    ∃ y₁ ∈ N, RegularAtDim (n := n) T y₁ k ∧ rankAt (n := n) (n' := n') G T y₁ = k := by
  have hk : k ≤ n := hy.1
  set e := complexChartAt (n := n) y with he
  set e' := complexChartAt (n := n') (G y) with he'
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  obtain ⟨Ψ, hΨt, hΨ0, hflat⟩ := exists_chartFlattening hy e hye
  have h0t : coordinateInclusion n k 0 ∈ Ψ.target := by
    rw [map_zero, ← hΨ0]; exact Ψ.mapsTo_toFun Ψ.center_mem_source
  have hP0 : param e Ψ k 0 = y := by
    simp only [param]
    rw [map_zero, ← hΨ0, Ψ.left_inv _ Ψ.center_mem_source, e.val.left_inv hye]
  obtain ⟨w₁, V, -, hw₁V, hVmem, -, hVrank⟩ := exists_param_rank_eq hk e e' Ψ hΨt hflat hG hdisc
    h0t (by rw [hP0]; exact mem_complexChartAt_source (G y)) (by rw [hP0]; exact hN)
  obtain ⟨hw₁t, hGw₁, hw₁N⟩ := hVmem w₁ hw₁V
  refine ⟨param e Ψ k w₁, hw₁N, ?_, ?_⟩
  · -- a point of the flattening is a regular point of dimension `k`
    have hs : Ψ.invFun (coordinateInclusion n k w₁) ∈ Ψ.source := Ψ.mapsTo_invFun hw₁t
    have hst : Ψ.invFun (coordinateInclusion n k w₁) ∈ e.val.target := hΨt hs
    refine regularAtDim_of_flattening_of_mem (x := y) hk Ψ (fun {y'} hy' hy'Ψ => ?_)
      (param_mem e Ψ hflat hw₁t) (e.val.map_target hst) ?_
    · have h := hflat _ hy'Ψ
      rwa [e.val.left_inv hy'] at h
    · simp only [param]
      rw [e.val.right_inv hst]
      exact hs
  · exact (rankAt_param_eq hk e e' Ψ hΨt hflat hw₁t hGw₁ (hG _)).2.trans (hVrank w₁ hw₁V)

/-- **`rem:finite-map-dimension` (2).**  If `G` has discrete fibres on `T` and maps `T` into an
analytic set `D` with `dim D ≤ a`, then `dim T ≤ a`. -/
theorem dimLE_of_discrete_fibres {T : Set M} {G : M → Y}
    (hG : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') G)
    (hdisc : ∀ y ∈ T, ¬ AccPt y (𝓟 (T ∩ G ⁻¹' {G y}))) {D : Set Y}
    (hD : IsComplexAnalyticSubset (n := n') D) (hTD : G '' T ⊆ D) {a : ℕ}
    (hDa : DimLE (n := n') D a) : DimLE (n := n) T a := by
  intro y k hy
  have hk : k ≤ n := hy.1
  set e := complexChartAt (n := n) y with he
  set e' := complexChartAt (n := n') (G y) with he'
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  obtain ⟨Ψ, hΨt, hΨ0, hflat⟩ := exists_chartFlattening hy e hye
  have h0t : coordinateInclusion n k 0 ∈ Ψ.target := by
    rw [map_zero, ← hΨ0]; exact Ψ.mapsTo_toFun Ψ.center_mem_source
  have hP0 : param e Ψ k 0 = y := by
    simp only [param]
    rw [map_zero, ← hΨ0, Ψ.left_inv _ Ψ.center_mem_source, e.val.left_inv hye]
  obtain ⟨w₁, V, hVo, hw₁V, hVmem, hHd, hVrank⟩ := exists_param_rank_eq hk e e' Ψ hΨt hflat hG
    hdisc h0t (by rw [hP0]; exact mem_complexChartAt_source (G y)) (N := univ) univ_mem
  -- the image of a neighbourhood of `w₁` is a `k`-dimensional submanifold of the chart of `Y`
  obtain ⟨O, -, -, -, hw₁O, hOV, -, -, -, hreg⟩ :=
    ConstantRankSubmanifold.exists_image_eq_graph hVo hHd hVrank hw₁V
  set H : ComplexModel k → ComplexModel n' := fun v => e'.val (G (param e Ψ k v)) with hH
  have hHt : H '' O ⊆ e'.val.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e'.val.map_source (hVmem z (hOV hz)).2.1
  have hGw₁ : G (param e Ψ k w₁) ∈ e'.val.source := (hVmem w₁ hw₁V).2.1
  -- read back in `Y`
  have hregY : RegularAtDim (n := n') (e'.val.source ∩ e'.val ⁻¹' (H '' O))
      (G (param e Ψ k w₁)) k := by
    rw [RegularAtDimChart.regularAtDim_chart_iff e' (H '' O) hGw₁, inter_eq_left.mpr hHt]
    exact hreg _ ⟨w₁, hw₁O, rfl⟩
  have hsub : e'.val.source ∩ e'.val ⁻¹' (H '' O) ⊆ D := by
    rintro q ⟨hq, z, hz, hzq⟩
    have hzV := hVmem z (hOV hz)
    have hq' : q = G (param e Ψ k z) := e'.val.injOn hq hzV.2.1 hzq.symm
    rw [hq']
    exact hTD ⟨_, param_mem e Ψ hflat hzV.1, rfl⟩
  obtain ⟨y', -, k', hkk', hy'⟩ :=
    DimensionMonotone.locDimGE_of_regularAtDim_subset hD hsub hregY univ univ_mem
  exact hkk'.trans (hDa y' k' hy')

end

end Hironaka.FiniteMapDimension
