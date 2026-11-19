import Hironaka.Analytic.Unibranch.HironakaG10NfTargetChart
import Hironaka.Analytic.Unibranch.HironakaG10NfRealOpenChartIdeal

/-!
# N5.b (S4 on the canonical chart): coordinates of the real-open target chart

Lane G10N5, run 0081.  In the setting of `HironakaG10NfTargetChart` (pivot strict chart point `p` with chart coordinates
`v`, `v_j = 0`, real-open chart recentred at `v`):

* `base_coords` — the base point `π(χ w)` of a real-open chart point has product coordinates `σ_j(w + v)`;
* `proj_val` — its tangential part is `u(w + v)`; `functions_proj_origin` — the graph functions vanish at the base
  point `s₀` of the origin (the origin lies over the centre);
* `pullback_proj` — the native germ pullback of the ambient representative at the origin is the tangential pullback;
* `graph_germ` — near the origin the recentred graph is the graph of `fG(u) = g(s₀ + u)` over the translated base
  carrier;
* **`strict_eq_chartIdeal`** — the whole strict ideal at the origin is the analytic graph chart ideal
  `chartIdeal (evPoly d r v') j (fG)_0 I_{C,s₀}` (`HironakaG10NfRealOpenChartIdeal.realOpen_strict_eq_chartIdeal`).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfTargetCoordinates

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance HironakaRelativeNormalIdeal
  HironakaActualWholeStalkHolomorphicPullback HironakaActualHolomorphicGraphIdeal HironakaActualCentreJointJets
  HironakaG10ChowFlatModelOpen HironakaFiniteSectionProductGraph
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict HironakaRealOpenGeometricStrictSaturation
  BlowupConstruction BlowupStrictSubmanifold BlowupMonomialCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateAnalytic
  Hironaka.Analytic.Unibranch.HironakaG10HtPolynomialGermFlat Hironaka.Analytic.Unibranch.HironakaG10HtChartSaturation
  Hironaka.Analytic.Unibranch.HironakaG10NfRealOpenChartIdeal
  Hironaka.Analytic.Unibranch.HironakaG10NfTargetChart

/-! ### Generic coordinate facts -/

theorem prodModelEquiv_symm_fst (n r : ℕ) (z : ComplexModel (n+r)) :
    ((ProductComplexManifold.prodModelEquiv n r).symm z).1 = tangentProjection n r z := by
  ext i
  simp [ProductComplexManifold.prodModelEquiv, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd]

theorem prodModelEquiv_symm_snd (n r : ℕ) (z : ComplexModel (n+r)) :
    ((ProductComplexManifold.prodModelEquiv n r).symm z).2 = actualJointNormalProjection n r z := by
  ext i
  simp [ProductComplexManifold.prodModelEquiv, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd]

theorem tangentProjection_monomial (n r : ℕ) (j : Fin r) (w : ComplexModel (n+r)) :
    tangentProjection n r (monomial n (j.natAdd n) w) = tangentProjection n r w := by
  ext i
  rw [tangentProjection_apply, tangentProjection_apply, monomial_apply, if_neg]
  rintro ⟨h, -⟩
  simp only [Fin.val_castAdd] at h
  exact absurd i.isLt (by omega)

/-- In a double open of a model space, charts are defined everywhere. -/
theorem double_chart_source {n : ℕ} (A : Opens (ComplexModel n)) (U : Opens A) (p : U) :
    (chartAt (ComplexModel n) p).source = univ := by
  rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
    TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
  rfl

/-- In a double open of a model space, the inverse chart has the literal value. -/
theorem double_chart_symm_val {n : ℕ} {A : Opens (ComplexModel n)} {U : Opens A} (x : U)
    {z : ComplexModel n} (hz : z ∈ (chartAt (ComplexModel n) x).target) :
    ((chartAt (ComplexModel n) x).symm z).val.val = z :=
  (chartAt (ComplexModel n) x).right_inv hz

theorem double_chart_symm_eq {n : ℕ} {A : Opens (ComplexModel n)} {U : Opens A} (x x' : U)
    {z : ComplexModel n} (hz : z ∈ (chartAt (ComplexModel n) x).target)
    (hz' : z ∈ (chartAt (ComplexModel n) x').target) :
    (chartAt (ComplexModel n) x).symm z = (chartAt (ComplexModel n) x').symm z :=
  Subtype.ext (Subtype.ext ((double_chart_symm_val x hz).trans (double_chart_symm_val x' hz').symm))

/-! ### The canonical chart -/

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
  (t : CanonicalTargetGraph B b y) (e : TargetExplicitGeometry B b t)
  (j : Fin t.rank) (p : strictChartCarrier e.charts (graph B b t) j)
  (hvj : coords B b t e j p (j.natAdd t.embedding.dim) = 0)

/-- **The base point of a real-open chart point** has product coordinates `σ_j(w + v)`. -/
theorem base_coords (w : domain B b t e j p) :
    ProductComplexManifold.prodModelEquiv t.embedding.dim t.rank
      (((blowupProj (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0}
          (chart B b t e j p hvj w).val).1 : t.embedding.ambient).val,
        (blowupProj (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0}
          (chart B b t e j p hvj w).val).2) =
      monomial t.embedding.dim (j.natAdd t.embedding.dim) (w.val + coords B b t e j p) := by
  have hs : (chart B b t e j p hvj w).val ∈ (productNormalChart (n := t.embedding.dim) e.charts.base j).source :=
    (chart B b t e j p hvj w).property
  have h := (productNormalChart (n := t.embedding.dim) e.charts.base j).monomial_toFun hs
  have hc : (productNormalChart (n := t.embedding.dim) e.charts.base j).toFun (chart B b t e j p hvj w).val =
      w.val + coords B b t e j p :=
    arbitrary_canonical_recentered_coordinates e.charts j (coords B b t e j p) hvj w
  rw [hc] at h
  exact h.symm

theorem proj_val (w : domain B b t e j p) :
    ((proj B b t e j p hvj w : t.embedding.ambient)).val =
      tangentProjection t.embedding.dim t.rank (w.val + coords B b t e j p) := by
  have h := congrArg (fun z => ((ProductComplexManifold.prodModelEquiv t.embedding.dim t.rank).symm z).1)
    (base_coords B b t e j p hvj w)
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  rw [prodModelEquiv_symm_fst, tangentProjection_monomial] at h
  exact h

theorem projSnd (w : domain B b t e j p) :
    (blowupProj (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0}
        (chart B b t e j p hvj w).val).2 =
      actualJointNormalProjection t.embedding.dim t.rank
        (monomial t.embedding.dim (j.natAdd t.embedding.dim) (w.val + coords B b t e j p)) := by
  have h := congrArg (fun z => ((ProductComplexManifold.prodModelEquiv t.embedding.dim t.rank).symm z).2)
    (base_coords B b t e j p hvj w)
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  rw [prodModelEquiv_symm_snd] at h
  exact h

/-- The base point `s₀` of the real-open origin. -/
abbrev basePt : t.domain := proj B b t e j p hvj (origin B b t e j p)

theorem basePt_val :
    ((basePt B b t e j p hvj : t.embedding.ambient)).val =
      tangentProjection t.embedding.dim t.rank (coords B b t e j p) := by
  rw [proj_val]
  simp [realOpenOrigin]

/-- **The origin lies over the centre**: the graph functions vanish at its base point. -/
theorem functions_basePt : t.functions (basePt B b t e j p hvj) = 0 := by
  have hmem := (mem_strict_iff B b t e j p hvj (origin B b t e j p)).mp (origin_mem_strict B b t e j p hvj)
  have h2 := geoStrictTransform_subset_preimage contMDiff_blowupProj.continuous t.analytic.isClosed hmem
  have h3 := h2.2
  change _ = t.functions (basePt B b t e j p hvj) at h3
  rw [← h3, projSnd]
  ext i
  rw [actualJointNormalProjection_apply]
  simp only [realOpenOrigin, zero_add]
  exact base_image_normal_zero t.embedding.dim t.rank j (coords B b t e j p) hvj _ (by simp)

/-! ### The germ pullback of the ambient representative -/

/-- **The ambient representative pulls germs back tangentially** at the origin. -/
theorem pullback_proj :
    actualHolomorphicGermPullback (proj_contMDiff B b t e j p hvj) (origin B b t e j p) =
      tangentPullback t.embedding.dim t.rank := by
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold actualHolomorphicGermPullback tangentPullback
    rw [compAlgHom_mk, compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    set o := origin B b t e j p
    have htarget : (chartAt (ComplexModel (t.embedding.dim+t.rank)) o).target ∈
        𝓝 (0 : ComplexModel (t.embedding.dim+t.rank)) :=
      (chartAt (ComplexModel (t.embedding.dim+t.rank)) o).open_target.mem_nhds
        ((chartAt (ComplexModel (t.embedding.dim+t.rank)) o).map_source (mem_chart_source _ o))
    filter_upwards [htarget] with z hz
    change F (((proj B b t e j p hvj ((chartAt (ComplexModel (t.embedding.dim+t.rank)) o).symm (z + 0)) :
        t.embedding.ambient)).val - ((proj B b t e j p hvj o : t.embedding.ambient)).val) =
      F (tangentProjection t.embedding.dim t.rank z)
    rw [add_zero, proj_val, proj_val, opens_chart_symm_val o hz]
    congr 1
    simp [o, realOpenOrigin]

/-! ### The recentred graph near the origin -/

/-- The recentred graph function `fG(u) = g(s₀ + u)`. -/
def graphFun (u : ComplexModel t.embedding.dim) : ComplexModel t.rank :=
  t.functions ((chartAt (ComplexModel t.embedding.dim) (basePt B b t e j p hvj)).symm
    (u + chartAt (ComplexModel t.embedding.dim) (basePt B b t e j p hvj) (basePt B b t e j p hvj)))

theorem graphFun_differentiable :
    ∀ᶠ x in 𝓝 (0 : ComplexModel t.embedding.dim), DifferentiableAt ℂ (graphFun B b t e j p hvj) x := by
  have h := actualTranslatedMap_holomorphic (n := t.rank) (m := t.embedding.dim) t.holomorphic
    (basePt B b t e j p hvj)
  have he : graphFun B b t e j p hvj = fun z => actualTranslatedMap (n := t.rank) (m := t.embedding.dim)
      t.functions (basePt B b t e j p hvj) z + t.functions (basePt B b t e j p hvj) := by
    funext z
    simp only [actualTranslatedMap, graphFun, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id,
      sub_add_cancel]
  rw [he]
  exact h.mono fun z hz => hz.add_const _

theorem graphFun_zero : graphFun B b t e j p hvj 0 = 0 := by
  unfold graphFun
  rw [zero_add, (chartAt (ComplexModel t.embedding.dim) (basePt B b t e j p hvj)).left_inv
    (mem_chart_source _ _)]
  exact functions_basePt B b t e j p hvj

include hvj in
/-- Membership in the recentred graph, in coordinates. -/
theorem mem_graph'_iff (q : targetOpen' B b t e j p) :
    q ∈ graph' B b t e j p ↔
      ((chartAt (ComplexModel t.embedding.dim) e.charts.base).symm
          (tangentProjection t.embedding.dim t.rank q.val +
            tangentProjection t.embedding.dim t.rank (coords B b t e j p)) : t.embedding.ambient) ∈
          t.embedding.carrier ∧
        actualJointNormalProjection t.embedding.dim t.rank q.val =
          t.functions ((chartAt (ComplexModel t.embedding.dim) e.charts.base).symm
            (tangentProjection t.embedding.dim t.rank q.val +
              tangentProjection t.embedding.dim t.rank (coords B b t e j p))) := by
  have hY1 : tangentProjection t.embedding.dim t.rank
      (q.val + monomial t.embedding.dim (j.natAdd t.embedding.dim) (coords B b t e j p)) =
      tangentProjection t.embedding.dim t.rank q.val +
        tangentProjection t.embedding.dim t.rank (coords B b t e j p) := by
    rw [map_add, tangentProjection_monomial]
  have hY2 : actualJointNormalProjection t.embedding.dim t.rank
      (q.val + monomial t.embedding.dim (j.natAdd t.embedding.dim) (coords B b t e j p)) =
      actualJointNormalProjection t.embedding.dim t.rank q.val := by
    rw [map_add]
    ext i
    simp only [PiLp.add_apply, actualJointNormalProjection_apply]
    rw [base_image_normal_zero t.embedding.dim t.rank j (coords B b t e j p) hvj (i.natAdd t.embedding.dim)
      (by simp), add_zero]
  change ((chartAt (ComplexModel t.embedding.dim) e.charts.base).symm
      ((ProductComplexManifold.prodModelEquiv t.embedding.dim t.rank).symm
        (q.val + monomial t.embedding.dim (j.natAdd t.embedding.dim) (coords B b t e j p))).1,
      ((ProductComplexManifold.prodModelEquiv t.embedding.dim t.rank).symm
        (q.val + monomial t.embedding.dim (j.natAdd t.embedding.dim) (coords B b t e j p))).2) ∈
      graph B b t ↔ _
  rw [prodModelEquiv_symm_fst, prodModelEquiv_symm_snd, hY1, hY2]
  rfl

include hvj in
/-- **Near the origin the recentred graph is the graph of `fG` over the translated base carrier.** -/
theorem graph_germ :
    translatedCarrier (N := t.embedding.dim+t.rank) (graph' B b t e j p)
        (baseOrigin t.embedding.dim t.rank (targetOpen' B b t e j p) (origin_mem B b t e j p)) =ᶠ[𝓝 0]
      graphCarrier (graphFun B b t e j p hvj)
        (translatedCarrier (N := t.embedding.dim) (baseSet B b t) (basePt B b t e j p hvj)) := by
  set s₀ := basePt B b t e j p hvj
  set o₀ := baseOrigin t.embedding.dim t.rank (targetOpen' B b t e j p) (origin_mem B b t e j p)
  set vu := tangentProjection t.embedding.dim t.rank (coords B b t e j p)
  have hs₀ : chartAt (ComplexModel t.embedding.dim) s₀ s₀ = vu := basePt_val B b t e j p hvj
  have hcont : Continuous (fun x : ComplexModel (t.embedding.dim+t.rank) => tangentProjection t.embedding.dim t.rank x + vu) :=
    (tangentProjection t.embedding.dim t.rank).continuous.add continuous_const
  have E1 : (chartAt (ComplexModel (t.embedding.dim+t.rank)) o₀).target ∈ 𝓝 (0 : ComplexModel (t.embedding.dim+t.rank)) :=
    (chartAt (ComplexModel (t.embedding.dim+t.rank)) o₀).open_target.mem_nhds
      ((chartAt (ComplexModel (t.embedding.dim+t.rank)) o₀).map_source (mem_chart_source _ o₀))
  have hT2 : (chartAt (ComplexModel t.embedding.dim) s₀).target ∈ 𝓝 vu := by
    rw [← hs₀]
    exact (chartAt (ComplexModel t.embedding.dim) s₀).open_target.mem_nhds
      ((chartAt (ComplexModel t.embedding.dim) s₀).map_source (mem_chart_source _ s₀))
  have hT3 : (chartAt (ComplexModel t.embedding.dim) e.charts.base).target ∈ 𝓝 vu := by
    have hsrc : s₀ ∈ (chartAt (ComplexModel t.embedding.dim) e.charts.base).source := by
      rw [double_chart_source]
      trivial
    have hv : chartAt (ComplexModel t.embedding.dim) e.charts.base s₀ = vu := hs₀
    rw [← hv]
    exact (chartAt (ComplexModel t.embedding.dim) e.charts.base).open_target.mem_nhds
      ((chartAt (ComplexModel t.embedding.dim) e.charts.base).map_source hsrc)
  have E2 : (fun x : ComplexModel (t.embedding.dim+t.rank) => tangentProjection t.embedding.dim t.rank x + vu) ⁻¹'
      (chartAt (ComplexModel t.embedding.dim) s₀).target ∈ 𝓝 (0 : ComplexModel (t.embedding.dim+t.rank)) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [map_zero, zero_add]; exact hT2)
  have E3 : (fun x : ComplexModel (t.embedding.dim+t.rank) => tangentProjection t.embedding.dim t.rank x + vu) ⁻¹'
      (chartAt (ComplexModel t.embedding.dim) e.charts.base).target ∈
        𝓝 (0 : ComplexModel (t.embedding.dim+t.rank)) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [map_zero, zero_add]; exact hT3)
  rw [Filter.eventuallyEq_set]
  filter_upwards [E1, E2, E3] with x h1 h2 h3
  change tangentProjection t.embedding.dim t.rank x + vu ∈ (chartAt (ComplexModel t.embedding.dim) s₀).target at h2
  change tangentProjection t.embedding.dim t.rank x + vu ∈ (chartAt (ComplexModel t.embedding.dim) e.charts.base).target at h3
  have hsymm := double_chart_symm_eq e.charts.base s₀ h3 h2
  have hq : ((chartAt (ComplexModel (t.embedding.dim+t.rank)) o₀).symm x).val = x := opens_chart_symm_val o₀ h1
  change (x + 0 ∈ (chartAt (ComplexModel (t.embedding.dim+t.rank)) o₀).target ∧
      (chartAt (ComplexModel (t.embedding.dim+t.rank)) o₀).symm (x + 0) ∈ graph' B b t e j p) ↔
    ((tangentProjection t.embedding.dim t.rank x + chartAt (ComplexModel t.embedding.dim) s₀ s₀ ∈ (chartAt (ComplexModel t.embedding.dim) s₀).target ∧
      (chartAt (ComplexModel t.embedding.dim) s₀).symm (tangentProjection t.embedding.dim t.rank x + chartAt (ComplexModel t.embedding.dim) s₀ s₀) ∈
        baseSet B b t) ∧
      actualJointNormalProjection t.embedding.dim t.rank x = graphFun B b t e j p hvj (tangentProjection t.embedding.dim t.rank x))
  rw [add_zero, mem_graph'_iff B b t e j p hvj, hq, hsymm]
  unfold graphFun
  rw [hs₀]
  exact ⟨fun h => ⟨⟨h2, h.2.1⟩, h.2.2⟩, fun h => ⟨h1, h.1.2, h.2⟩⟩

theorem graph'_analytic : IsComplexAnalyticSubset (n := t.embedding.dim+t.rank) (graph' B b t e j p) :=
  recenteredCoordinateSubset_analytic e.charts j (coords B b t e j p) (graph B b t) t.analytic

/-- **N5.b (S4 on the canonical chart).**  The whole strict ideal at the origin of the real-open target chart is
the analytic graph chart ideal over the base chart. -/
theorem strict_eq_chartIdeal :
    wholeChartStalkIdeal (vanishingIdeal (n := t.embedding.dim+t.rank) (strict B b t e j p))
        (origin B b t e j p) (origin B b t e j p) (mem_chart_source _ _) =
      chartIdeal (evPoly t.embedding.dim t.rank (fibreVec (coords B b t e j p))) j
        (graphGerms (graphFun B b t e j p hvj) (graphFun_differentiable B b t e j p hvj))
        (wholeChartStalkIdeal (vanishingIdeal (n := t.embedding.dim) (baseSet B b t))
          (basePt B b t e j p hvj) (basePt B b t e j p hvj) (mem_chart_source _ _)) := by
  have h := stalkIdeal_eq_vanishingIdeal (N := t.embedding.dim) (baseSet B b t) (basePt B b t e j p hvj)
  unfold stalkIdeal at h
  rw [h]
  exact realOpen_strict_eq_chartIdeal t.embedding.dim t.rank j (coords B b t e j p) hvj
    (targetOpen' B b t e j p) (origin_mem B b t e j p) (graph' B b t e j p) (graph'_analytic B b t e j p)
    (graphFun B b t e j p hvj) (graphFun_differentiable B b t e j p hvj) (graphFun_zero B b t e j p hvj)
    _ (graph_germ B b t e j p hvj)

end

end Hironaka.Analytic.Unibranch.HironakaG10NfTargetCoordinates
