import Hironaka.Analytic.Unibranch.HironakaG10GlChartPresentation
import Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy

/-!
# N3 coordinates: the four translated maps of the canonical charts are in normal form

Lane G10N34, run 0081 (G10GL's split-off N3+N4).  Generic over product normal charts `a`, `b` (no canonical data):
in translated chart germs

* `translated_realOpenProjection` — the real-open source chart projection is `(id, B)` with `B` the recentred normal
  monomial map `blowGerm`;
* `translated_coordProj` — the blowup projection read in the target product coordinates is `(id, B)`;
* `translated_liftCoords` — a monomial lift (`MonomialLiftLaws`) read in the recentred source chart and the target
  product coordinates is `(G, id)` with `G` the translated base map;
* `stalkIdeal_originalGraph` — the recentred graph `W` and the original graph have the same whole chart stalk ideal.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10GlChartCoordinates

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaHolomorphicJetChartInvariance HironakaActualWholeStalkHolomorphicPullback BlowupMonomialCharts
  HironakaRealOpenGeometricStrictSaturation HironakaG10ArbitraryBaseRecenter HironakaActualAnalyticBlowupTaylor
  HironakaG10ChowFlatModelOpen HironakaActualCoefficientPresentationCentrePower
  BlowupConstruction BlowupStrictSubmanifold HironakaHolomorphicJetRankLoci
  Hironaka.Analytic.Unibranch.HironakaG10NfRealOpenChartIdeal
  Hironaka.Analytic.Unibranch.HironakaG10GlFlattenerTransfer Hironaka.Analytic.Unibranch.HironakaG10GlChartPresentation

noncomputable section

/-! ### The normal monomial map -/

section Monomial

variable (n r : ℕ) (j : Fin r)

theorem np_monomial (p : ComplexModel (n+r)) :
    actualJointNormalProjection n r (monomial n (j.natAdd n) p) =
      monomial 0 j (actualJointNormalProjection n r p) := by
  ext i
  simp only [actualJointNormalProjection_apply, monomial_apply, Fin.val_natAdd, zero_le, true_and,
    le_add_iff_nonneg_right, ne_eq, Fin.natAdd_inj]

theorem tp_monomial (p : ComplexModel (n+r)) :
    tangentProjection n r (monomial n (j.natAdd n) p) = tangentProjection n r p := by
  ext i
  rw [tangentProjection_apply, tangentProjection_apply, monomial_apply, if_neg]
  rintro ⟨h, -⟩
  simp only [Fin.val_castAdd] at h
  exact absurd i.isLt (by omega)

/-- The recentred normal monomial map `B_{λ₀}(λ) = σ(λ₀ + λ) - σ(λ₀)`. -/
def blowGerm (l₀ : ComplexModel r) (l : ComplexModel r) : ComplexModel r :=
  monomial 0 j (l₀ + l) - monomial 0 j l₀

theorem blowGerm_differentiable (l₀ : ComplexModel r) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel r), DifferentiableAt ℂ (blowGerm r j l₀) z :=
  Eventually.of_forall fun z =>
    (((contDiff_monomial 0 j).differentiable (by simp)).comp (differentiable_const l₀ |>.add differentiable_id) z).sub_const _

theorem blowGerm_zero (l₀ : ComplexModel r) : blowGerm r j l₀ 0 = 0 := by
  simp [blowGerm]

/-- **A translated monomial map is in normal form.** -/
theorem monomial_sub_eq_blowMap (p₀ z : ComplexModel (n+r)) :
    monomial n (j.natAdd n) (p₀ + z) - monomial n (j.natAdd n) p₀ =
      blowMap n r (blowGerm r j (actualJointNormalProjection n r p₀)) z := by
  apply ext_blocks
  · rw [map_sub, tp_monomial, tp_monomial, tangentProjection_blowMap, map_add, add_sub_cancel_left]
  · rw [map_sub, np_monomial, np_monomial, normalProjection_blowMap, map_add]
    rfl

end Monomial

/-! ### Translated maps between opens of model spaces -/

section Opens

/-- The translated map of a map between opens of model spaces with an ambient extension. -/
theorem actualTranslatedMap_opens {k k' : ℕ} {V : Opens (ComplexModel k)} {V' : Opens (ComplexModel k')}
    (f : V → V') (F : ComplexModel k → ComplexModel k') (hF : ∀ y : V, (f y).val = F y.val) (x : V) :
    actualTranslatedMap (n := k') (m := k) f x =ᶠ[𝓝 0] fun z => F (x.val + z) - F x.val := by
  filter_upwards [eventually_translate_mem_target (N := k) x] with z hz
  unfold actualTranslatedMap
  change ((f ((chartAt (ComplexModel k) x).symm (z + x.val)))).val - (f x).val = _
  have h' : ((chartAt (ComplexModel k) x).symm (z + x.val)).val = z + x.val :=
    (chartAt (ComplexModel k) x).right_inv hz
  rw [hF, hF, h', add_comm]

end Opens

/-! ### The real-open source projection -/

section RealOpen

variable (d t : ℕ) (j : Fin t) (v : ComplexModel (d+t)) (hvj : v (j.natAdd d) = 0)
  (U : Opens (ComplexModel (d+t)))

include hvj in
/-- **The real-open chart projection, translated at `w`, is `(id, B)`.** -/
theorem translated_realOpenProjection (w : realOpenChartDomain d t j (fun i => v i) U) :
    actualTranslatedMap (n := d+t) (m := d+t) (realOpenProjection d t j (fun i => v i) U) w =ᶠ[𝓝 0]
      blowMap d t (blowGerm t j (actualJointNormalProjection d t (w.val + v))) := by
  refine (actualTranslatedMap_opens (realOpenProjection d t j (fun i => v i) U)
    (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) (fun i => v i))
    (fun _ => rfl) w).trans (Eventually.of_forall fun z => ?_)
  change actualAnalyticBlowupMap _ _ _ (w.val + z) - actualAnalyticBlowupMap _ _ _ w.val = _
  have h1 := recentered_projection_arbitrary_tangent d t j v hvj (w.val + z)
  have h2 := recentered_projection_arbitrary_tangent d t j v hvj w.val
  rw [← monomial_sub_eq_blowMap, eq_sub_iff_add_eq.mpr h1.symm, eq_sub_iff_add_eq.mpr h2.symm,
    sub_sub_sub_cancel_right]
  congr 2
  abel

end RealOpen

/-! ### Product normal charts -/

section Product

open Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift

variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  (a : ProductNormalCharts n r P) (j : Fin r)

/-- The base point of the product chart point with coordinates `w`. -/
theorem plot_base (w : productCoordinateOpen a j) :
    (productChartPlot a j w).base =
      (chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r)).symm (monomial n (j.natAdd n) w.val) :=
  (productNormalChart (n := n) a.base j).base_invFun w.property

/-- Product coordinates of the base point of a product chart point. -/
theorem chart_plot_base (w : productCoordinateOpen a j) :
    chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r) (productChartPlot a j w).base =
      monomial n (j.natAdd n) w.val := by
  rw [plot_base]
  exact (chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r)).right_inv w.property

/-- The blowup projection read in the product coordinates. -/
def coordProj (p : productCoordinateOpen a j) : P × ComplexModel r :=
  blowupProj (n+r) {q : P × ComplexModel r | q.2 = 0} ((productChartDiffeomorph a j).symm p).val

theorem coordProj_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel (n+r)) ∞ (coordProj a j) :=
  contMDiff_blowupProj.comp (contMDiff_subtype_val.comp (productChartDiffeomorph a j).symm.contMDiff)

theorem chart_coordProj (p : productCoordinateOpen a j) :
    chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r) (coordProj a j p) =
      monomial n (j.natAdd n) p.val := by
  change chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r) (productChartPlot a j p).base = _
  exact chart_plot_base a j p

/-- Uniform charts on the product with `ℂ^r`. -/
theorem chartAt_prod_uniform (hP : ∀ p p' : P, chartAt (ComplexModel n) p = chartAt (ComplexModel n) p')
    (s : P × ComplexModel r) :
    chartAt (ComplexModel (n+r)) s = chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r) := by
  rw [ProductComplexManifold.chartAt_prod, ProductComplexManifold.chartAt_prod, hP s.1 a.base]
  rfl

/-- **The blowup projection in product coordinates, translated at `p₀`, is `(id, B)`.** -/
theorem translated_coordProj (hP : ∀ p p' : P, chartAt (ComplexModel n) p = chartAt (ComplexModel n) p')
    (p₀ : productCoordinateOpen a j) :
    actualTranslatedMap (n := n+r) (m := n+r) (coordProj a j) p₀ =ᶠ[𝓝 0]
      blowMap n r (blowGerm r j (actualJointNormalProjection n r p₀.val)) := by
  filter_upwards [eventually_translate_mem_target (N := n+r) p₀] with z hz
  unfold actualTranslatedMap
  rw [chartAt_prod_uniform a hP]
  have h' : ((chartAt (ComplexModel (n+r)) p₀).symm (z + chartAt (ComplexModel (n+r)) p₀ p₀)).val = z + p₀.val :=
    (chartAt (ComplexModel (n+r)) p₀).right_inv hz
  rw [chart_coordProj, chart_coordProj, h', add_comm z p₀.val, monomial_sub_eq_blowMap]

/-- The base point of a recentred canonical chart point. -/
theorem recentredChart_base (v : ComplexModel (n+r)) (hvj : v (j.natAdd n) = 0)
    (w : realOpenChartDomain n r j (fun i => v i)
      (HironakaG10ArbitraryBaseRecenter.recenteredTargetOpen n r j v
        (Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart.canonicalTargetOpen a j))) :
    (Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart.arbitraryCanonicalRecenteredChart a j v hvj w).val.base =
      (chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r)).symm
        (monomial n (j.natAdd n) (w.val + v)) := by
  set z := Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart.arbitraryCanonicalRecenteredChart a j v hvj w
  have hc := Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart.arbitrary_canonical_recentered_coordinates
    a j v hvj w
  have hz : z.val = productChartPlot a j ((productChartDiffeomorph a j) z) :=
    congrArg Subtype.val ((productChartDiffeomorph a j).symm_apply_apply z).symm
  rw [hz, plot_base]
  exact congrArg (fun u => (chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r)).symm
    (monomial n (j.natAdd n) u)) hc

end Product

/-! ### The monomial lift in recentred coordinates -/

section Lift

open Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart

variable {n m r : ℕ} {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
  (a : ProductNormalCharts n r P) (b : ProductNormalCharts m r Q) {f : P → Q}
  (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
  (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2 = 0} → BlowupSpace (m+r) {q : Q × ComplexModel r | q.2 = 0})
  (hL : ContMDiff 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel (m+r)) ∞ L)
  (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2 = 0} ∘ L =
    Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2 = 0})
  (M : MonomialLiftLaws a b hf L hL hπ) (j : Fin r) (v : ComplexModel (n+r)) (hvj : v (j.natAdd n) = 0)

/-- The monomial lift, read in the recentred source chart and the target product coordinates. -/
abbrev liftMap : realOpenChartDomain n r j (fun i => v i)
    (HironakaG10ArbitraryBaseRecenter.recenteredTargetOpen n r j v (canonicalTargetOpen a j)) →
      productCoordinateOpen b j :=
  ⇑(productChartDiffeomorph b j) ∘
    (monomialLiftOnChart a b hf L hL hπ j ∘ ⇑(arbitraryCanonicalRecenteredChart a j v hvj))

include M in
/-- **The monomial lift in coordinates**: tangential part `f` of the base point, normal part kept. -/
theorem liftMap_val (w : realOpenChartDomain n r j (fun i => v i)
      (HironakaG10ArbitraryBaseRecenter.recenteredTargetOpen n r j v (canonicalTargetOpen a j))) :
    (liftMap a b hf L hL hπ j v hvj w).val =
      ProductComplexManifold.prodModelEquiv m r
        (chartAt (ComplexModel m) b.base (f ((chartAt (ComplexModel n) a.base).symm (tangentProjection n r (w.val + v)))),
          actualJointNormalProjection n r (w.val + v)) := by
  set z := arbitraryCanonicalRecenteredChart a j v hvj w
  have hc : (productChartDiffeomorph a j z).val = w.val + v :=
    arbitrary_canonical_recentered_coordinates a j v hvj w
  have hplot := congrFun (M.plot_formula j) (productChartDiffeomorph a j z)
  have hz : productChartPlot a j (productChartDiffeomorph a j z) = z.val :=
    congrArg Subtype.val ((productChartDiffeomorph a j).symm_apply_apply z)
  simp only [Function.comp_apply, hz] at hplot
  have hL' : (monomialLiftOnChart a b hf L hL hπ j z) =
      (productChartDiffeomorph b j).symm (monomialCoordinateMap a b f j (productChartDiffeomorph a j z)) :=
    Subtype.ext hplot
  change (productChartDiffeomorph b j (monomialLiftOnChart a b hf L hL hπ j z)).val = _
  rw [hL', (productChartDiffeomorph b j).apply_symm_apply]
  have hbase : ((chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r)).symm
      (monomial n (j.natAdd n) (productChartDiffeomorph a j z).val)).1 =
        (chartAt (ComplexModel n) a.base).symm (tangentProjection n r (w.val + v)) := by
    rw [ProductComplexManifold.chartAt_prod, ProductComplexManifold.prodChart_symm_apply, hc,
      prodModelEquiv_symm_fst', tp_monomial]
  ext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [M.tangent_slots, prodModelEquiv_eq_join, PiLp.add_apply, tangentInclusion_tangent,
      actualJointNormalInclusion_tangent, add_zero, plot_base, hbase]
  · rw [M.normal_slots, prodModelEquiv_eq_join, PiLp.add_apply, tangentInclusion_normal,
      actualJointNormalInclusion_normal, zero_add, hc, actualJointNormalProjection_apply]

include hvj in
/-- The recentred chart point lies in the product chart domain: its base point has coordinates in the chart target. -/
theorem tangent_mem_target (w : realOpenChartDomain n r j (fun i => v i)
      (HironakaG10ArbitraryBaseRecenter.recenteredTargetOpen n r j v (canonicalTargetOpen a j))) :
    tangentProjection n r (w.val + v) ∈ (chartAt (ComplexModel n) a.base).target := by
  have hw := (HironakaG10ArbitraryBaseRecenter.recentered_domain_arbitrary_tangent n r j v hvj
    (canonicalTargetOpen a j) w.val).mp w.property
  change monomial n (j.natAdd n) (w.val + v) ∈
    (chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r)).target at hw
  rw [ProductComplexManifold.chartAt_prod, ProductComplexManifold.prodChart_target] at hw
  have h1 := hw.1
  rwa [prodModelEquiv_symm_fst', tp_monomial] at h1

include M in
/-- **The monomial lift, translated at `w`, is `(G, id)`** with `G` the translated base map at the base point. -/
theorem translated_liftMap (hP : ∀ p p' : P, chartAt (ComplexModel n) p = chartAt (ComplexModel n) p')
    (hQ : ∀ q q' : Q, chartAt (ComplexModel m) q = chartAt (ComplexModel m) q')
    (w : realOpenChartDomain n r j (fun i => v i)
      (HironakaG10ArbitraryBaseRecenter.recenteredTargetOpen n r j v (canonicalTargetOpen a j))) :
    actualTranslatedMap (n := m+r) (m := n+r) (liftMap a b hf L hL hπ j v hvj) w =ᶠ[𝓝 0]
      srcMap m n r (actualTranslatedMap (n := m) (m := n) f
        ((arbitraryCanonicalRecenteredChart a j v hvj w).val.base.1)) := by
  set F₁ : ComplexModel (n+r) → ComplexModel (m+r) := fun p =>
    ProductComplexManifold.prodModelEquiv m r
      (chartAt (ComplexModel m) b.base (f ((chartAt (ComplexModel n) a.base).symm (tangentProjection n r (p + v)))),
        actualJointNormalProjection n r (p + v)) with hF₁
  refine (actualTranslatedMap_opens (liftMap a b hf L hL hπ j v hvj) F₁
    (fun y => liftMap_val a b hf L hL hπ M j v hvj y) w).trans (Eventually.of_forall fun z => ?_)
  have hγ : (arbitraryCanonicalRecenteredChart a j v hvj w).val.base.1 =
      (chartAt (ComplexModel n) a.base).symm (tangentProjection n r (w.val + v)) := by
    rw [recentredChart_base, ProductComplexManifold.chartAt_prod, ProductComplexManifold.prodChart_symm_apply,
      prodModelEquiv_symm_fst', tp_monomial]
  have hcγ : chartAt (ComplexModel n) a.base ((chartAt (ComplexModel n) a.base).symm
      (tangentProjection n r (w.val + v))) = tangentProjection n r (w.val + v) :=
    (chartAt (ComplexModel n) a.base).right_inv (tangent_mem_target a j v hvj w)
  simp only [hF₁]
  unfold actualTranslatedMap srcMap
  rw [hγ, hQ (f ((chartAt (ComplexModel n) a.base).symm (tangentProjection n r (w.val + v)))) b.base,
    hP ((chartAt (ComplexModel n) a.base).symm (tangentProjection n r (w.val + v))) a.base, hcγ, ← map_sub,
    Prod.mk_sub_mk, prodModelEquiv_eq_join]
  congr 2
  · congr 4
    rw [map_add, map_add, map_add, add_comm (tangentProjection n r z)]
    abel
  · simp only [map_add]
    abel

end Lift



/-! ### The recentred graph -/

section Graph

open Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict

/-- Germ vanishing ideals only depend on the germ of the set. -/
theorem vanishingIdeal_congr {k : ℕ} {A A' : Set (ComplexModel k)} (h : A =ᶠ[𝓝 (0 : ComplexModel k)] A') :
    AnalyticGermDecomposition.vanishingIdeal A = AnalyticGermDecomposition.vanishingIdeal A' := by
  ext g
  induction g using HolGerm.induction_on with
  | h F hF =>
    rw [AnalyticGermDecomposition.mem_vanishingIdeal_mk, AnalyticGermDecomposition.mem_vanishingIdeal_mk]
    rw [Filter.eventuallyEq_set] at h
    constructor
    · intro hA
      filter_upwards [hA, h] with z hz hzA hzA'
      exact hz (hzA.mpr hzA')
    · intro hA
      filter_upwards [hA, h] with z hz hzA hzA'
      exact hz (hzA.mp hzA')

variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  (a : ProductNormalCharts n r P) (j : Fin r) (v : ComplexModel (n+r)) (Wset : Set (P × ComplexModel r))

/-- **The recentred graph has the whole chart stalk ideal of the original graph** at the corresponding point. -/
theorem stalkIdeal_originalGraph (hP : ∀ p p' : P, chartAt (ComplexModel n) p = chartAt (ComplexModel n) p')
    (u₀ : HironakaG10ArbitraryBaseRecenter.recenteredTargetOpen n r j v (canonicalTargetOpen a j)) :
    wholeChartStalkIdeal (vanishingIdeal (n := n+r)
        ((HironakaG10ArbitraryBaseStrict.arbitraryBaseTargetMap n r j v (canonicalTargetOpen a j)) ⁻¹'
          coordinateSubset a j Wset)) u₀ u₀ (mem_chart_source _ _) =
      wholeChartStalkIdeal (vanishingIdeal (n := n+r) Wset)
        ((chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r)).symm
          (u₀.val + monomial n (j.natAdd n) v))
        ((chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r)).symm
          (u₀.val + monomial n (j.natAdd n) v)) (mem_chart_source _ _) := by
  set e := chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r) with he
  set W := (HironakaG10ArbitraryBaseStrict.arbitraryBaseTargetMap n r j v (canonicalTargetOpen a j)) ⁻¹'
    coordinateSubset a j Wset
  set γ := e.symm (u₀.val + monomial n (j.natAdd n) v)
  have hu : u₀.val + monomial n (j.natAdd n) v ∈ e.target := u₀.property
  have heγ : chartAt (ComplexModel (n+r)) γ = e := chartAt_prod_uniform a hP γ
  have hγ : e γ = u₀.val + monomial n (j.natAdd n) v := e.right_inv hu
  have h1 := stalkIdeal_eq_vanishingIdeal (N := n+r) W u₀
  have h2 := stalkIdeal_eq_vanishingIdeal (N := n+r) Wset γ
  unfold stalkIdeal at h1 h2
  rw [h1, h2]
  apply vanishingIdeal_congr
  rw [Filter.eventuallyEq_set]
  have hT : ∀ᶠ z in 𝓝 (0 : ComplexModel (n+r)), z + (u₀.val + monomial n (j.natAdd n) v) ∈ e.target := by
    have hc : ContinuousAt (fun z : ComplexModel (n+r) => z + (u₀.val + monomial n (j.natAdd n) v)) 0 :=
      continuousAt_id.add continuousAt_const
    exact hc.preimage_mem_nhds (by simpa using e.open_target.mem_nhds hu)
  filter_upwards [eventually_translate_mem_target (N := n+r) u₀, hT] with z hz1 hz2
  have hval : ((chartAt (ComplexModel (n+r)) u₀).symm (z + chartAt (ComplexModel (n+r)) u₀ u₀)).val = z + u₀.val :=
    (chartAt (ComplexModel (n+r)) u₀).right_inv hz1
  change (z + chartAt (ComplexModel (n+r)) u₀ u₀ ∈ (chartAt (ComplexModel (n+r)) u₀).target ∧
      e.symm (((chartAt (ComplexModel (n+r)) u₀).symm (z + chartAt (ComplexModel (n+r)) u₀ u₀)).val +
        monomial n (j.natAdd n) v) ∈ Wset) ↔
    (z + chartAt (ComplexModel (n+r)) γ γ ∈ (chartAt (ComplexModel (n+r)) γ).target ∧
      (chartAt (ComplexModel (n+r)) γ).symm (z + chartAt (ComplexModel (n+r)) γ γ) ∈ Wset)
  rw [hval, heγ, hγ, add_assoc]
  exact ⟨fun h => ⟨hz2, h.2⟩, fun h => ⟨hz1, h.2⟩⟩

end Graph

end

end Hironaka.Analytic.Unibranch.HironakaG10GlChartCoordinates
