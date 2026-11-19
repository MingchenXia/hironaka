import Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion
import Hironaka.Analytic.Unibranch.HironakaG10CanonicalExceptionalOrigin
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreChartLift

/-!
# H3 (1): the fibre-product locus of the source chart, and every nearby pair comes from it

Lane G10FI, run 0081 (H3 item (1) of `G10N5/hfib-H3-route.md`; consumer `HironakaG10NfFibreModel.FibreModel`).
Setting of `HironakaG10SbCanonicalStrictTorsion`: `F : X ⟶ Y`, a finite-type ideal `b : B ⟶ 𝒪_Y`, the geometric
blowup `π : Bl_B Y ⟶ Y`, canonical chart data `t c g d E` at `(x, y)`, a pivot `j`, a recentring `v` with zero pivot
coordinate.  In the recentred source chart (coordinates `w`, blow-down `proj w ∈ c.subdomain × ℂ^r`) the actual map
`actualMap w` to the target chart is the restriction of the ambient lift of `c.baseMap × id`; hence

* `locus` — the points `w` of the local saturation domain with `proj w ∈ Γ_X` and `actualMap w ∈ Bl_B Y`'s strict chart
  is (a chart of) the fibre product `X ×_Y Bl_B Y`;  `W` is it with the subspace topology;
* `pY w := c.chart (proj w)`, `pT w := targetChartMap ⟨actualMap w, _⟩` (the point of G10GL's `canonicalPsi`);
* `square` — `F (pY w) = π (pT w)`;
* `cover` — **every pair `(a, b)` of the fibre product near `(pY w₀, pT w₀)` is `(pY w, pT w)` for some `w` near `w₀`**
  (`HironakaG10NfFibreChartLift.liftPoint`: the source chart is the fibre product of `c.subdomain` and the target
  chart over `t.domain`);
* `exists_origin` — over a target strict chart point `p` with zero pivot coordinate and `F x = π p`, the recentring at
  the source chart point over `c.point` with the normal coordinates of `p` has its origin in `W`, over `(x, p)`.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFibreCover

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk BlowupConstruction BlowupStrictSubmanifold
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialStrictRestriction
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRealStrictLanding
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalExceptionalOrigin
  Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion
  Hironaka.Analytic.Unibranch.HironakaG10NfFibreChartLift

/-- The normal block of `liftCoords` is the normal block of the target chart point. -/
theorem liftCoords_normal {n m r : ℕ} {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
    [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
    (a : ProductNormalCharts n r P) (b' : ProductNormalCharts m r Q) (j : Fin r) (u : P)
    (p : productChartOpen b' j) (i : Fin r) :
    liftCoords a b' j u p (i.natAdd n) = productChartCoordinates b' j p (i.natAdd m) := by
  simp [liftCoords, monomialCandidateCoordinates, ProductComplexManifold.prodModelEquiv,
    EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

variable (t : CanonicalTargetGraph B b y)
  (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c)
  (d : CanonicalNormalSectionData B b F x t c g)
  (E : SameCanonicalExplicitProductModels B b F x t c g d)

/-! ### The graph relation of the two canonical charts -/

/-- **`F` on the source graph chart and `π` on the target strict chart agree iff the target chart point lies over
`(c.baseMap u, λ)`** (graph square of `c` and projection law of the explicit target geometry; `chartGraphMap` is an
open immersion). -/
theorem graph_rel (γ : sourceGraphSet B b F x t c) (j : Fin t.rank)
    (p : strictChartCarrier E.target.charts (targetGraphSet B b t) j) :
    F.hom.left.base (c.chart.hom.left.base γ) =
        (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
          ((targetChartMap B b F x t c g d E j).base p) ↔
      (c.baseMap γ.val.1, γ.val.2) = p.val.val.base := by
  have h1 := congrArg (fun φ => φ.hom.left.base γ) c.graph_square
  have h2 := congrArg (fun φ => φ.hom.left.base
    ((strictChartInclusion E.target.charts (targetGraphSet B b t) j).base p)) E.target_maps.projection
  have hinj := (chartGraphMap_isOpenImmersion t.embedding t.domain t.functions t.holomorphic).base_open.injective
  constructor
  · intro h
    exact congrArg Subtype.val (hinj (h1.trans (h.trans h2)))
  · intro h
    exact h1.symm.trans ((congrArg (chartGraphMap t.embedding t.domain t.functions t.holomorphic).base
      (Subtype.ext h)).trans h2.symm)

variable (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
  (hvj : v (j.natAdd c.embedding.dim) = 0)

/-- The ambient blow-down of a source chart point. -/
abbrev proj (w : sourceDomain B b F x t c g d E j v) : c.subdomain × ComplexModel t.rank :=
  blowupProj (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2=0}
    (arbitraryCanonicalRecenteredChart E.source.charts j v hvj w).val

/-- The actual map is the ambient lift of `c.baseMap × id` on the blow-down. -/
theorem actualMap_base (w : sourceDomain B b F x t c g d E j v) :
    (actualMap B b F x t c g d E j v hvj w).val.base =
      (c.baseMap (proj B b F x t c g d E j v hvj w).1, (proj B b F x t c g d E j v hvj w).2) :=
  congrFun E.square.ambient_projection (arbitraryCanonicalRecenteredChart E.source.charts j v hvj w).val

variable (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)

/-- **The fibre-product locus** of the recentred source chart (inside the local saturation domain). -/
def locus : Set (sourceDomain B b F x t c g d E j v) :=
  {w | w ∈ localDomain c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v)
        (originalGraph B b F x t c g d E j v) h0 (originalGraph_analytic B b F x t c g d E j v) ∧
      proj B b F x t c g d E j v hvj w ∈ sourceGraphSet B b F x t c ∧
      actualMap B b F x t c g d E j v hvj w ∈ targetStrict B b F x t c g d E j}

/-- The parameter space `W` of the local model of `X ×_Y Bl_B Y` (subspace topology). -/
abbrev W := ↥(locus B b F x t c g d E j v hvj h0)

/-- The source point of a pair. -/
def pY (w : W B b F x t c g d E j v hvj h0) : X.obj.left :=
  c.chart.hom.left.base ⟨proj B b F x t c g d E j v hvj w.1, w.2.2.1⟩

/-- The target point of a pair (the point of `HironakaG10GlCanonicalBaseSquare.canonicalPsi … w.1 w.2.2.2`). -/
def pT (w : W B b F x t c g d E j v hvj h0) : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left :=
  (targetChartMap B b F x t c g d E j).base ⟨actualMap B b F x t c g d E j v hvj w.1, w.2.2.2⟩

/-- **The square of the pair map.** -/
theorem square (w : W B b F x t c g d E j v hvj h0) :
    F.hom.left.base (pY B b F x t c g d E j v hvj h0 w) =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
        (pT B b F x t c g d E j v hvj h0 w) :=
  (graph_rel B b F x t c g d E ⟨proj B b F x t c g d E j v hvj w.1, w.2.2.1⟩ j
    ⟨actualMap B b F x t c g d E j v hvj w.1, w.2.2.2⟩).mpr
      (actualMap_base B b F x t c g d E j v hvj w.1).symm


/-- The source chart point over a base point `u` with the normal coordinates of a target chart point `p`. -/
def chartPt (u : c.subdomain) (p : productChartOpen E.target.charts j) : sourceDomain B b F x t c g d E j v :=
  (arbitraryCanonicalRecenteredChart E.source.charts j v hvj).symm (liftPoint E.source.charts E.target.charts j u p)

theorem continuous_chartPt :
    Continuous (fun q : c.subdomain × productChartOpen E.target.charts j =>
      chartPt B b F x t c g d E j v hvj q.1 q.2) :=
  (arbitraryCanonicalRecenteredChart E.source.charts j v hvj).symm.continuous.comp (continuous_liftPoint E.source.charts E.target.charts j)

theorem chartPt_self (w : sourceDomain B b F x t c g d E j v) :
    chartPt B b F x t c g d E j v hvj (proj B b F x t c g d E j v hvj w).1
      (actualMap B b F x t c g d E j v hvj w) = w :=
  (congrArg (arbitraryCanonicalRecenteredChart E.source.charts j v hvj).symm (liftPoint_self E.source.charts E.target.charts j c.holomorphic
    (explicitAmbientLift B b F x t c g E.target E.source) E.square.holomorphic E.square.ambient_projection
      ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj) w))).trans ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj).symm_apply_apply w)

theorem proj_chartPt (u : c.subdomain) (p : productChartOpen E.target.charts j) :
    proj B b F x t c g d E j v hvj (chartPt B b F x t c g d E j v hvj u p) = (u, p.val.base.2) := by
  change ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj) ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj).symm (liftPoint E.source.charts E.target.charts j u p))).val.base = _
  rw [(arbitraryCanonicalRecenteredChart E.source.charts j v hvj).apply_symm_apply]
  exact liftPoint_base E.source.charts E.target.charts j u p

theorem actualMap_chartPt (u : c.subdomain) (p : productChartOpen E.target.charts j)
    (hu : c.baseMap u = p.val.base.1) :
    actualMap B b F x t c g d E j v hvj (chartPt B b F x t c g d E j v hvj u p) = p := by
  apply Subtype.ext
  change explicitAmbientLift B b F x t c g E.target E.source
    ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj) ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj).symm (liftPoint E.source.charts E.target.charts j u p))).val = p.val
  rw [(arbitraryCanonicalRecenteredChart E.source.charts j v hvj).apply_symm_apply]
  exact lift_liftPoint E.source.charts E.target.charts j c.holomorphic
    (explicitAmbientLift B b F x t c g E.target E.source) E.square.holomorphic E.square.ambient_projection u p hu

theorem targetChartMap_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (targetChartMap B b F x t c g d E j) := by
  have := E.target_maps.open_immersion
  unfold targetChartMap
  infer_instance

theorem cover_aux (U' : Set (sourceDomain B b F x t c g d E j v)) (U : Set (W B b F x t c g d E j v hvj h0))
    (hU'U : Subtype.val ⁻¹' U' ⊆ U) (A : Set c.subdomain) (B' : Set (productChartOpen E.target.charts j))
    (hAB : A ×ˢ B' ⊆ (fun q : c.subdomain × productChartOpen E.target.charts j =>
      chartPt B b F x t c g d E j v hvj q.1 q.2) ⁻¹' (U' ∩ (localDomain c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v)
      (originalGraph B b F x t c g d E j v) h0 (originalGraph_analytic B b F x t c g d E j v) :
        Set (sourceDomain B b F x t c g d E j v))))
    (q : X.obj.left × (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (γ : sourceGraphSet B b F x t c) (hγ : γ.val.1 ∈ A) (hγq : c.chart.hom.left.base γ = q.1)
    (p : strictChartCarrier E.target.charts (targetGraphSet B b t) j) (hp : p.val ∈ B')
    (hpq : (targetChartMap B b F x t c g d E j).base p = q.2)
    (hrel : F.hom.left.base q.1 = (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base q.2) :
    ∃ w ∈ U, pY B b F x t c g d E j v hvj h0 w = q.1 ∧ pT B b F x t c g d E j v hvj h0 w = q.2 := by
  have hr := (graph_rel B b F x t c g d E γ j p).mp ((congrArg F.hom.left.base hγq).trans
    (hrel.trans (congrArg (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base hpq).symm))
  have hzN := hAB (show ((γ.val.1, p.val) : c.subdomain × productChartOpen E.target.charts j) ∈ A ×ˢ B' from
    ⟨hγ, hp⟩)
  have hproj : proj B b F x t c g d E j v hvj (chartPt B b F x t c g d E j v hvj γ.val.1 p.val) = γ.val :=
    (proj_chartPt B b F x t c g d E j v hvj γ.val.1 p.val).trans (Prod.ext rfl (congrArg Prod.snd hr).symm)
  have hact := actualMap_chartPt B b F x t c g d E j v hvj γ.val.1 p.val (congrArg Prod.fst hr)
  have hmem : chartPt B b F x t c g d E j v hvj γ.val.1 p.val ∈ locus B b F x t c g d E j v hvj h0 :=
    ⟨hzN.2, (congrArg (fun a => a ∈ sourceGraphSet B b F x t c) hproj).mpr γ.property,
      (congrArg (fun a => a ∈ targetStrict B b F x t c g d E j) hact).mpr p.property⟩
  refine ⟨⟨_, hmem⟩, hU'U hzN.1, ?_, ?_⟩
  · exact (congrArg c.chart.hom.left.base (Subtype.ext hproj)).trans hγq
  · exact (congrArg (targetChartMap B b F x t c g d E j).base
      (Subtype.ext hact)).trans hpq

/-- **Every pair of the fibre product near `(pY w₀, pT w₀)` comes from a chart point near `w₀`.** -/
theorem cover (w₀ : W B b F x t c g d E j v hvj h0) :
    ∀ U ∈ 𝓝 w₀, ∀ᶠ q in 𝓝 (pY B b F x t c g d E j v hvj h0 w₀, pT B b F x t c g d E j v hvj h0 w₀),
      F.hom.left.base q.1 = (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base q.2 →
        ∃ w ∈ U, pY B b F x t c g d E j v hvj h0 w = q.1 ∧ pT B b F x t c g d E j v hvj h0 w = q.2 := by
  intro U hU
  rw [nhds_subtype, Filter.mem_comap] at hU
  obtain ⟨U', hU', hU'U⟩ := hU
  have hD : (localDomain c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v)
      (originalGraph B b F x t c g d E j v) h0 (originalGraph_analytic B b F x t c g d E j v) :
        Set (sourceDomain B b F x t c g d E j v)) ∈ 𝓝 w₀.1 := IsOpen.mem_nhds (Opens.isOpen _) w₀.2.1
  have hcont : (fun q : c.subdomain × productChartOpen E.target.charts j =>
      chartPt B b F x t c g d E j v hvj q.1 q.2) ⁻¹' (U' ∩ (localDomain c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v)
      (originalGraph B b F x t c g d E j v) h0 (originalGraph_analytic B b F x t c g d E j v) :
        Set (sourceDomain B b F x t c g d E j v))) ∈
        𝓝 ((proj B b F x t c g d E j v hvj w₀.1).1, actualMap B b F x t c g d E j v hvj w₀.1) :=
    (continuous_chartPt B b F x t c g d E j v hvj).continuousAt.preimage_mem_nhds
      ((congrArg (fun z => U' ∩ (localDomain c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v)
      (originalGraph B b F x t c g d E j v) h0 (originalGraph_analytic B b F x t c g d E j v) :
        Set (sourceDomain B b F x t c g d E j v)) ∈ 𝓝 z) (chartPt_self B b F x t c g d E j v hvj w₀.1)).mpr
        (inter_mem hU' hD))
  obtain ⟨A, hA, B', hB', hAB⟩ := mem_nhds_prod_iff.mp hcont
  have hN₁ : {γ : sourceGraphSet B b F x t c | γ.val.1 ∈ A} ∈
      𝓝 (⟨proj B b F x t c g d E j v hvj w₀.1, w₀.2.2.1⟩ : sourceGraphSet B b F x t c) :=
    (continuous_fst.comp continuous_subtype_val).continuousAt.preimage_mem_nhds hA
  have hN₂ : {p : strictChartCarrier E.target.charts (targetGraphSet B b t) j | p.val ∈ B'} ∈
      𝓝 (⟨actualMap B b F x t c g d E j v hvj w₀.1, w₀.2.2.2⟩ :
        strictChartCarrier E.target.charts (targetGraphSet B b t) j) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hB'
  have hc := c.chart_open.base_open.isOpenMap.image_mem_nhds hN₁
  have ht := (targetChartMap_isOpenImmersion B b F x t c g d E j).base_open.isOpenMap.image_mem_nhds hN₂
  filter_upwards [prod_mem_nhds hc ht] with q hq hrel
  obtain ⟨⟨γ, hγ, hγq⟩, ⟨p, hp, hpq⟩⟩ := hq
  exact cover_aux B b F x t c g d E j v hvj h0 U' U hU'U A B' hAB q γ hγ hγq p hp hpq hrel

theorem exists_origin_aux (p : strictChartCarrier E.target.charts (targetGraphSet B b t) j)
    (v : ComplexModel (c.embedding.dim+t.rank)) (hvj : v (j.natAdd c.embedding.dim) = 0)
    (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)
    (hr : (c.baseMap c.point.val.1, c.point.val.2) = p.val.val.base)
    (horig : arbitraryCanonicalRecenteredChart E.source.charts j v hvj
      (realOpenOrigin c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) h0) =
        liftPoint E.source.charts E.target.charts j c.point.val.1 p.val)
    (hx : c.chart.hom.left.base c.point = x) :
    ∃ (w₀ : W B b F x t c g d E j v hvj h0),
      w₀.1 = realOpenOrigin c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) h0 ∧
      proj B b F x t c g d E j v hvj w₀.1 = c.point.val ∧ pY B b F x t c g d E j v hvj h0 w₀ = x ∧
      pT B b F x t c g d E j v hvj h0 w₀ = (targetChartMap B b F x t c g d E j).base p := by
  have he : realOpenOrigin c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) h0 =
      chartPt B b F x t c g d E j v hvj c.point.val.1 p.val :=
    ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj).symm_apply_apply _).symm.trans
      (congrArg (arbitraryCanonicalRecenteredChart E.source.charts j v hvj).symm horig)
  have hproj : proj B b F x t c g d E j v hvj
      (realOpenOrigin c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) h0) =
        c.point.val :=
    (congrArg (proj B b F x t c g d E j v hvj) he).trans
      ((proj_chartPt B b F x t c g d E j v hvj c.point.val.1 p.val).trans
        (Prod.ext rfl (congrArg Prod.snd hr).symm))
  have hact : actualMap B b F x t c g d E j v hvj
      (realOpenOrigin c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) h0) = p.val :=
    (congrArg (actualMap B b F x t c g d E j v hvj) he).trans
      (actualMap_chartPt B b F x t c g d E j v hvj c.point.val.1 p.val (congrArg Prod.fst hr))
  have hmem : realOpenOrigin c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) h0 ∈
      locus B b F x t c g d E j v hvj h0 :=
    ⟨origin_mem_localDomain c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v)
        (originalGraph B b F x t c g d E j v) h0 (originalGraph_analytic B b F x t c g d E j v),
      (congrArg (fun a => a ∈ sourceGraphSet B b F x t c) hproj).mpr c.point.property,
      (congrArg (fun a => a ∈ targetStrict B b F x t c g d E j) hact).mpr p.property⟩
  refine ⟨⟨_, hmem⟩, rfl, hproj, ?_, ?_⟩
  · exact (congrArg c.chart.hom.left.base (Subtype.ext hproj)).trans hx
  · exact congrArg (targetChartMap B b F x t c g d E j).base (Subtype.ext hact)

/-- **The chart origin over a pair** `(x, targetChartMap p)` with `F x = π (targetChartMap p)`: recentre the source
chart at the point over `c.point` with the normal coordinates of `p` (zero pivot coordinate); its origin lies in `W`,
over `c.point`, with pair `(x, targetChartMap p)`. -/
theorem exists_origin (p : strictChartCarrier E.target.charts (targetGraphSet B b t) j)
    (hpj : productChartCoordinates E.target.charts j p.val (j.natAdd t.embedding.dim) = 0)
    (hp : F.hom.left.base x = (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
      ((targetChartMap B b F x t c g d E j).base p)) :
    ∃ (v : ComplexModel (c.embedding.dim+t.rank)) (hvj : v (j.natAdd c.embedding.dim) = 0)
      (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)
      (w₀ : W B b F x t c g d E j v hvj h0),
      w₀.1 = realOpenOrigin c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) h0 ∧
      proj B b F x t c g d E j v hvj w₀.1 = c.point.val ∧ pY B b F x t c g d E j v hvj h0 w₀ = x ∧
      pT B b F x t c g d E j v hvj h0 w₀ = (targetChartMap B b F x t c g d E j).base p := by
  have hr := (graph_rel B b F x t c g d E c.point j p).mp ((congrArg F.hom.left.base c.point_over).trans hp)
  have hvj : productChartCoordinates E.source.charts j
      (liftPoint E.source.charts E.target.charts j c.point.val.1 p.val) (j.natAdd c.embedding.dim) = 0 := by
    rw [coordinates_liftPoint, liftCoords_normal]
    exact hpj
  have h0 := canonical_target_origin B b F x t c g d E j
    (liftPoint E.source.charts E.target.charts j c.point.val.1 p.val)
  obtain ⟨w₀, hw₀⟩ := exists_origin_aux B b F x t c g d E j p _ hvj h0 hr
    (arbitrary_canonical_origin_eq E.source.charts j _ hvj h0) c.point_over
  exact ⟨_, hvj, h0, w₀, hw₀⟩


end

end Hironaka.Analytic.Unibranch.HironakaG10NfFibreCover
