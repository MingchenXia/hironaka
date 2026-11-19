import Hironaka.Analytic.Unibranch.HironakaG10GfNativeVanishing
import Hironaka.Analytic.Unibranch.HironakaG10MwNativeWindow

/-!
# Chart windows of a morphism for an arbitrary base chart (lane G10GF, run 0081, plan item G10-03-05.c2''.b2)

For a morphism `f : Y ⟶ X` of reduced complex spaces, a FIXED local embedding `eX` of the base and a point
`y` over a carrier point `c₀`, there are an open window `W ∋ y` of `Y`, a source chart dimension `m`, the graph
row `F = graphRow ψ 0 g` on `ℂᵈ × ℂᵐ` (lane G10MW, `HironakaG10MwGraphRow`), holomorphic on `ℂᵈ × Ω`, and a
compact `K ⊆ Ω` such that every point `y' ∈ W` over a carrier point `c` has a chart point `z ∈ K` at which,
for EVERY ideal `J` of the base stalk, chart flatness of `F` at `(c, z)` over the lifted ideal gives native
flatness of `f` at `y'` over `V(J)` (**`exists_window_dictionary`**).

This is the sufficiency half of the dictionary inside lane G10MW's `exists_native_window`, without the window
flattener and for the given base chart: `HironakaG10MwWindowFamily.exists_actual_window`,
`HironakaG10SbChartFlatDictionary.quotMap_fibre_flat_iff_graph` (lane G10SB) and
`HironakaG10MwGraphChartFlat.graphChart_flat_iff_chartFlat` with the graph row centred at `0`.
**`exists_window_chart`** is the two-sided version on a source chart (every carrier point with coordinate in
`K`); **`exists_window_chart_vanishing`** reads the relative non-flat locus `N_A` of the fibre-product family
over the reduced structure of ANY `A ⊆ X`: native flatness over `V(I_A)` ⟺ chart flatness over
`baseIdeal (trace eX A) c` (for lane G10FR's native Frisch (IV,9) and for hF2).
No named input.  Blueprint: `hironaka-g10gf-relative.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10GfWindow

noncomputable section

open Hironaka Hironaka OkaRelationSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaG10HirFlatQuotient
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10MwGraphRow Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily
  Hironaka.Analytic.Unibranch.HironakaG10MwGraphChartFlat Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk
  Hironaka.Analytic.Unibranch.HironakaG10SbChartFlatDictionary Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata

/-- **The chart window dictionary of a morphism over a fixed base chart.** -/
theorem exists_window_dictionary {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (eX : LocalEmbedding X)
    (y : Y.obj.left) (c₀ : eX.carrier) (hc : f.hom.left.base y = eX.toPoint c₀) :
    ∃ (W : Set Y.obj.left) (_ : IsOpen W) (_ : y ∈ W) (m b : ℕ)
      (F : Fin 1 → Fin b → ComplexModel eX.dim × ComplexModel m → ℂ) (Ω K : Set (ComplexModel m)),
      IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ (∀ i j, DifferentiableOn ℂ (F i j) (univ ×ˢ Ω)) ∧
      ∀ y' ∈ W, ∀ (c : eX.carrier) (h : f.hom.left.base y' = eX.toPoint c), ∃ z ∈ K,
        ∀ J : Ideal (X.obj.left.presheaf.stalk (eX.toPoint c)),
          ChartFlat eX.dim m F ((c.val : ComplexModel eX.dim), z)
              (J.comap (baseChartLiftAt eX c (eX.toPoint c) rfl)) →
            (quotMap (fibreStalkMap f (eX.toPoint c) y' h) J).Flat := by
  classical
  let eY := LocalEmbedding.ofPoint Y y
  obtain ⟨cy, hcy⟩ := LocalEmbedding.mem_range_ofPoint Y y
  have hc' : f.hom.left.base (eY.toPoint cy) = eX.toPoint c₀ := by
    change f.hom.left.base ((LocalEmbedding.ofPoint Y y).toPoint cy) = _
    rw [hcy, hc]
  obtain ⟨U, hUV, hcU, φ, hφ, hCD, hsq, ψ, hψ, Wz, r, g, K₁, hWo, hWU, hK₁W, hK₁n, hK₁c, hφW,
    hgW, hgen, -, -, -, -⟩ := exists_actual_window f eX eY cy c₀ hc'
  let e := eY.restrict U hUV
  refine ⟨e.toPoint '' {z : e.carrier | z.val.val ∈ interior K₁}, ?_, ?_, eY.dim, eX.dim + r,
    graphRow ψ 0 g, Wz, K₁, hWo, hK₁c, hK₁W, graphRow_differentiableOn ψ 0 g hφW hgW, ?_⟩
  · exact e.isOpenEmbedding_toPoint.isOpenMap _
      (isOpen_interior.preimage (continuous_subtype_val.comp continuous_subtype_val))
  · refine ⟨⟨⟨cy.val.val, hcU⟩, cy.property⟩, mem_interior_iff_mem_nhds.mpr hK₁n, ?_⟩
    exact hcy
  · rintro y' ⟨zC, hzK, rfl⟩ c h
    have hzW : zC.val.val ∈ Wz := hK₁W (interior_subset hzK)
    have hbase : (actualSubspaceMap hφ hCD).base zC = c :=
      square_base_eq f eX eY hUV hφ hCD hsq zC c _ h rfl
    subst hbase
    have hψz : ψ zC.val.val = ((actualSubspaceMap hφ hCD).base zC).val.val :=
      hψ zC.val.val zC.val.property
    refine ⟨zC.val.val, interior_subset hzK, fun J hJ => ?_⟩
    have hd1 := quotMap_fibre_flat_iff_graph f eX eY hUV hφ hCD hsq zC _ h rfl J
    have hd2 := graphChart_flat_iff_chartFlat φ hφ e.carrier zC ψ hψ
      (fun k => holAt_of_differentiableOn hWo
        ((EuclideanSpace.proj k : ComplexModel eX.dim →L[ℂ] ℂ).differentiable.comp_differentiableOn hφW) hzW)
      0 g (fun j => holAt_of_differentiableOn hWo (hgW j) hzW) (hgen zC.val hzW)
      (J.comap (baseChartLiftAt eX ((actualSubspaceMap hφ hCD).base zC)
        (eX.toPoint ((actualSubspaceMap hφ hCD).base zC)) rfl))
    rw [hψz, sub_zero] at hd2
    exact hd1.2 (hd2.2 hJ)

/-- **The chart reading of native flatness on a source chart window** (both directions, every base ideal):
a source local embedding `eW` (dimension `m`), the graph row `F` of `f` holomorphic on `ℂᵈ × Ω`, a compact
`K ⊆ Ω` whose interior contains the chart point of `y`, such that at every carrier point `zC` of `eW` with
coordinate in `K`, over every base carrier point `c` below it and for every ideal `J` of the base stalk,
native flatness of `f` at `eW zC` over `V(J)` is chart flatness of `F` at `(c, zC)` over the lifted ideal. -/
theorem exists_window_chart {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (eX : LocalEmbedding X)
    (y : Y.obj.left) (c₀ : eX.carrier) (hc : f.hom.left.base y = eX.toPoint c₀) :
    ∃ (eW : LocalEmbedding Y) (b : ℕ)
      (F : Fin 1 → Fin b → ComplexModel eX.dim × ComplexModel eW.dim → ℂ)
      (Ω K : Set (ComplexModel eW.dim)),
      IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ (∀ i j, DifferentiableOn ℂ (F i j) (univ ×ˢ Ω)) ∧
      y ∈ eW.toPoint '' {zC : eW.carrier | (zC.val : ComplexModel eW.dim) ∈ interior K} ∧
      ∀ zC : eW.carrier, (zC.val : ComplexModel eW.dim) ∈ K → ∀ (c : eX.carrier)
        (h : f.hom.left.base (eW.toPoint zC) = eX.toPoint c)
        (J : Ideal (X.obj.left.presheaf.stalk (eX.toPoint c))),
        (quotMap (fibreStalkMap f (eX.toPoint c) (eW.toPoint zC) h) J).Flat ↔
          ChartFlat eX.dim eW.dim F ((c.val : ComplexModel eX.dim), (zC.val : ComplexModel eW.dim))
            (J.comap (baseChartLiftAt eX c (eX.toPoint c) rfl)) := by
  classical
  let eY := LocalEmbedding.ofPoint Y y
  obtain ⟨cy, hcy⟩ := LocalEmbedding.mem_range_ofPoint Y y
  have hc' : f.hom.left.base (eY.toPoint cy) = eX.toPoint c₀ := by
    change f.hom.left.base ((LocalEmbedding.ofPoint Y y).toPoint cy) = _
    rw [hcy, hc]
  obtain ⟨U, hUV, hcU, φ, hφ, hCD, hsq, ψ, hψ, Wz, r, g, K₁, hWo, hWU, hK₁W, hK₁n, hK₁c, hφW,
    hgW, hgen, -, -, -, -⟩ := exists_actual_window f eX eY cy c₀ hc'
  refine ⟨eY.restrict U hUV, eX.dim + r, graphRow ψ 0 g, Wz, K₁, hWo, hK₁c, hK₁W,
    graphRow_differentiableOn ψ 0 g hφW hgW, ?_, ?_⟩
  · refine ⟨⟨⟨cy.val.val, hcU⟩, cy.property⟩, mem_interior_iff_mem_nhds.mpr hK₁n, ?_⟩
    exact hcy
  · intro zC hzK c h J
    have hzW : zC.val.val ∈ Wz := hK₁W hzK
    have hbase : (actualSubspaceMap hφ hCD).base zC = c :=
      square_base_eq f eX eY hUV hφ hCD hsq zC c _ h rfl
    subst hbase
    have hψz : ψ zC.val.val = ((actualSubspaceMap hφ hCD).base zC).val.val :=
      hψ zC.val.val zC.val.property
    have hd1 := quotMap_fibre_flat_iff_graph f eX eY hUV hφ hCD hsq zC _ h rfl J
    have hd2 := graphChart_flat_iff_chartFlat φ hφ (eY.restrict U hUV).carrier zC ψ hψ
      (fun k => holAt_of_differentiableOn hWo
        ((EuclideanSpace.proj k : ComplexModel eX.dim →L[ℂ] ℂ).differentiable.comp_differentiableOn hφW) hzW)
      0 g (fun j => holAt_of_differentiableOn hWo (hgW j) hzW) (hgen zC.val hzW)
      (J.comap (baseChartLiftAt eX ((actualSubspaceMap hφ hCD).base zC)
        (eX.toPoint ((actualSubspaceMap hφ hCD).base zC)) rfl))
    rw [hψz, sub_zero] at hd2
    exact hd1.trans hd2

/-- **The chart reading of the relative non-flat locus `N_A`**: the same window, with the base ideal of the
reduced structure of an arbitrary subset `A ⊆ X` identified with the ideal `baseIdeal (trace eX A) c` of ambient
germs vanishing on the trace of `A` (`HironakaG10GfNativeVanishing.comap_vanishingIdealAt_baseChartLiftAt`). -/
theorem exists_window_chart_vanishing {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (eX : LocalEmbedding X) (y : Y.obj.left) (c₀ : eX.carrier)
    (hc : f.hom.left.base y = eX.toPoint c₀) :
    ∃ (eW : LocalEmbedding Y) (b : ℕ)
      (F : Fin 1 → Fin b → ComplexModel eX.dim × ComplexModel eW.dim → ℂ)
      (Ω K : Set (ComplexModel eW.dim)),
      IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ (∀ i j, DifferentiableOn ℂ (F i j) (univ ×ˢ Ω)) ∧
      y ∈ eW.toPoint '' {zC : eW.carrier | (zC.val : ComplexModel eW.dim) ∈ interior K} ∧
      ∀ zC : eW.carrier, (zC.val : ComplexModel eW.dim) ∈ K → ∀ (c : eX.carrier)
        (h : f.hom.left.base (eW.toPoint zC) = eX.toPoint c) (A : Set X.obj.left),
        (quotMap (fibreStalkMap f (eX.toPoint c) (eW.toPoint zC) h)
            (vanishingIdealAt X.obj.left A (eX.toPoint c))).Flat ↔
          ChartFlat eX.dim eW.dim F ((c.val : ComplexModel eX.dim), (zC.val : ComplexModel eW.dim))
            (HironakaG10GfModStart.baseIdeal (HironakaG10GfNativeVanishing.trace eX A)
              (c.val : ComplexModel eX.dim)) := by
  obtain ⟨eW, b, F, Ω, K, hΩ, hK, hKΩ, hF, hy, hdict⟩ := exists_window_chart f eX y c₀ hc
  refine ⟨eW, b, F, Ω, K, hΩ, hK, hKΩ, hF, hy, fun zC hzK c h A => ?_⟩
  rw [hdict zC hzK c h, HironakaG10GfNativeVanishing.comap_vanishingIdealAt_baseChartLiftAt]

end

end Hironaka.Analytic.Unibranch.HironakaG10GfWindow
