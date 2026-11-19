import Hironaka.Analytic.Unibranch.HironakaG10NfFibreCover
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreIdentity
import Hironaka.Analytic.Unibranch.HironakaG10NfRealOpenChartIdeal

/-!
# H3 (3): the fibre identity at every point of the fibre-product locus of a canonical source chart

Lane G10FI, run 0081 (H3 item (3)).  Canonical setting of `HironakaG10NfFibreCover` (`F : X ⟶ Y`, `π : Bl_B Y ⟶ Y`,
data `t c g d E M`, pivot `j`, recentring `v`, local saturation domain `h0`).  At every `w ∈ W` (the fibre-product locus;
`w` NOT assumed on the strict transform), with `γ := proj w ∈ Γ_X`, for every germ `h` of the ambient
`c.subdomain × ℂ^r` at `γ`:

  `proj^♯ h ∈ jointIdeal w + actualMap^♯ 𝔪  ⟹  h ∈ I(Γ_X)_γ + (c.baseMap × id)^♯ 𝔪`   (`fibreIdentityAt`)

i.e. `comap β (𝔪_{Bl} · B) ⊆ 𝔪_Y · 𝒪_{Γ_X, γ}` for the joint quotient `B = JointQuotient w` and `β = mk ∘ proj^♯`:
**`B/𝔪_{X'}B ≅ 𝒪_X/𝔪_Y𝒪_X`** (Hironaka 1975, proof of Lemma 4.4.5, p. 538).  Instance of the generic
`HironakaG10NfFibreIdentity.fibre_identity` with `ρ = realOpenProjection`, `κ` = the recentred product-chart
coordinates, `L = actualMap`, and the normal slice `u ↦ chartPt u (actualMap w)` (`HironakaG10NfFibreCover`).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFibreIdentityCanonical

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaSmoothCentreRealDomainActualSheafStalk BlowupConstruction BlowupMonomialCharts
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel HironakaG10JointStrictTorsion
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialStrictRestriction
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
  Hironaka.Analytic.Unibranch.HironakaG10NfFibreChartLift Hironaka.Analytic.Unibranch.HironakaG10NfFibreCover
  Hironaka.Analytic.Unibranch.HironakaG10NfFibreIdentity

/-! ### Generic smoothness of the chart lift in the base variable -/

section Generic

variable {n m r : ℕ} {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
  (a : ProductNormalCharts n r P) (b : ProductNormalCharts m r Q) (j : Fin r)

include j in
theorem chartAt_source_univ : (chartAt (ComplexModel n) a.base).source = univ := by
  apply eq_univ_of_forall
  intro u
  have hd : ((u,0) : P × ComplexModel r) ∈ (productNormalChart (n := n) a.base j).dom := by
    rw [a.domain j]
    trivial
  have hs : ((u,0) : P × ComplexModel r) ∈
      (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r)).source := hd.1
  rw [ProductComplexManifold.chartAt_prod, ProductComplexManifold.prodChart_source] at hs
  exact hs.1

include j in
theorem chartAt_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (chartAt (ComplexModel n) a.base) := by
  rw [← contMDiffOn_univ, ← chartAt_source_univ a j]
  exact contMDiffOn_chart

theorem contMDiff_liftPoint_left (p : productChartOpen b j) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+r)) ∞ (fun u : P => liftPoint a b j u p) := by
  have hpair : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n × ComplexModel r) ∞
      (fun u : P => (chartAt (ComplexModel n) a.base u,
        ((ProductComplexManifold.prodModelEquiv m r).symm (productChartCoordinates b j p)).2)) :=
    (chartAt_contMDiff a j).prodMk_space contMDiff_const
  have h1 : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+r)) ∞ (fun u : P => liftCoords a b j u p) :=
    (ProductComplexManifold.prodModelEquiv n r).contDiff.contMDiff.comp hpair
  exact (productChartDiffeomorph a j).symm.contMDiff.comp
    (BlowupRestrictOpen.contMDiff_opens_mk h1 (fun u => liftCoords_mem a b j u p))

end Generic

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
  (M : AllAmbientMonomialLiftData B b F x t c g d E)
  (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
  (hvj : v (j.natAdd c.embedding.dim) = 0)

theorem proj_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) ∞
      (proj B b F x t c g d E j v hvj) :=
  contMDiff_blowupProj.comp
    (contMDiff_subtype_val.comp (arbitraryCanonicalRecenteredChart E.source.charts j v hvj).contMDiff)

theorem baseMap_prod_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)) ∞
      (Prod.map c.baseMap id : c.subdomain × ComplexModel t.rank → t.domain × ComplexModel t.rank) :=
  ProductComplexManifold.contMDiff_prodMk (c.holomorphic.comp ProductComplexManifold.contMDiff_fst)
    ProductComplexManifold.contMDiff_snd


theorem dom_mem (q : c.subdomain × ComplexModel t.rank) : q ∈ (productNormalChart (n := c.embedding.dim) E.source.charts.base j).dom := by
  rw [E.source.charts.domain j]
  trivial

theorem kappa_mem (q : c.subdomain × ComplexModel t.rank) :
    (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)) q - (monomial c.embedding.dim (j.natAdd c.embedding.dim) v) ∈ targetOpen B b F x t c g d E j v := by
  change (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)) q - (monomial c.embedding.dim (j.natAdd c.embedding.dim) v) + (monomial c.embedding.dim (j.natAdd c.embedding.dim) v) ∈ canonicalTargetOpen E.source.charts j
  rw [sub_add_cancel]
  exact (dom_mem B b F x t c g d E j q).2

/-- The recentred product-chart coordinates of a point of `c.subdomain × ℂ^r`. -/
def kappa (q : c.subdomain × ComplexModel t.rank) : targetOpen B b F x t c g d E j v :=
  ⟨(chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)) q - (monomial c.embedding.dim (j.natAdd c.embedding.dim) v), kappa_mem B b F x t c g d E j v q⟩

theorem kappa_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) ∞
      (kappa B b F x t c g d E j v) := by
  have hs : (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)).source = univ :=
    eq_univ_of_forall fun q => (dom_mem B b F x t c g d E j q).1
  have hc : ContMDiff 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) ∞
      (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)) := by
    rw [← contMDiffOn_univ, ← hs]
    exact contMDiffOn_chart
  exact BlowupRestrictOpen.contMDiff_opens_mk (hc.sub contMDiff_const) (kappa_mem B b F x t c g d E j v)

include hvj in
theorem chi_target (s : sourceDomain B b F x t c g d E j v) : s.val + v ∈ (productNormalChart (n := c.embedding.dim) E.source.charts.base j).target := by
  have h2 : productChartCoordinates E.source.charts j ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj) s) ∈ (productNormalChart (n := c.embedding.dim) E.source.charts.base j).target :=
    ((productChartDiffeomorph E.source.charts j) ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj) s)).property
  rwa [arbitrary_canonical_recentered_coordinates E.source.charts j v hvj s] at h2

theorem chi_val (s : sourceDomain B b F x t c g d E j v) : ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj) s).val = (productNormalChart (n := c.embedding.dim) E.source.charts.base j).invFun (s.val + v) :=
  ((productNormalChart (n := c.embedding.dim) E.source.charts.base j).left_inv ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj) s).property).symm.trans
    (congrArg (productNormalChart (n := c.embedding.dim) E.source.charts.base j).invFun (arbitrary_canonical_recentered_coordinates E.source.charts j v hvj s))

theorem kappa_proj (s : sourceDomain B b F x t c g d E j v) :
    kappa B b F x t c g d E j v (proj B b F x t c g d E j v hvj s) =
      realOpenProjection c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) s := by
  apply Subtype.ext
  have htarget := chi_target B b F x t c g d E j v hvj s
  change (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)) ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj) s).val.base - (monomial c.embedding.dim (j.natAdd c.embedding.dim) v) = _
  rw [chi_val B b F x t c g d E j v hvj s, (productNormalChart (n := c.embedding.dim) E.source.charts.base j).base_invFun htarget]
  change (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)) ((chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)).symm (monomial c.embedding.dim (j.natAdd c.embedding.dim) (s.val + v))) - (monomial c.embedding.dim (j.natAdd c.embedding.dim) v) = _
  have ht' : monomial c.embedding.dim (j.natAdd c.embedding.dim) (s.val + v) ∈ (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)).target := htarget
  rw [(chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)).right_inv ht', recentered_projection_arbitrary_tangent c.embedding.dim t.rank j v hvj s.val,
    add_sub_cancel_right]
  rfl

theorem kappa_mapsTo :
    MapsTo (kappa B b F x t c g d E j v) (sourceGraphSet B b F x t c) (originalGraph B b F x t c g d E j v) := by
  intro q hq
  change (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)).symm ((productNormalChart (n := c.embedding.dim) E.source.charts.base j).Φ.invFun ((chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)) q - (monomial c.embedding.dim (j.natAdd c.embedding.dim) v) + (monomial c.embedding.dim (j.natAdd c.embedding.dim) v))) ∈ sourceGraphSet B b F x t c
  rw [sub_add_cancel]
  change (chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)).symm ((chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)) q) ∈ sourceGraphSet B b F x t c
  rw [(chartAt (ComplexModel (c.embedding.dim+t.rank)) ((E.source.charts.base, 0) : c.subdomain × ComplexModel t.rank)).left_inv (dom_mem B b F x t c g d E j q).1]
  exact hq

theorem chartPt_contMDiff (p : productChartOpen E.target.charts j) :
    ContMDiff 𝓘(ℂ,ComplexModel c.embedding.dim) 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) ∞
      (fun u => chartPt B b F x t c g d E j v hvj u p) :=
  (arbitraryCanonicalRecenteredChart E.source.charts j v hvj).symm.contMDiff.comp (contMDiff_liftPoint_left E.source.charts E.target.charts j p)

/-- The actual map on the normal slice is the target normal slice of `c.baseMap`. -/
theorem actualMap_chartPt' (u : c.subdomain) (p : productChartOpen E.target.charts j) :
    actualMap B b F x t c g d E j v hvj (chartPt B b F x t c g d E j v hvj u p) =
      liftPoint E.target.charts E.target.charts j (c.baseMap u) p := by
  apply (productChartDiffeomorph E.target.charts j).injective
  apply Subtype.ext
  change productChartCoordinates E.target.charts j (monomialLiftOnChart E.source.charts E.target.charts
      c.holomorphic (explicitAmbientLift B b F x t c g E.target E.source) E.square.holomorphic
      E.square.ambient_projection j ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj) ((arbitraryCanonicalRecenteredChart E.source.charts j v hvj).symm (liftPoint E.source.charts E.target.charts j u p)))) =
    productChartCoordinates E.target.charts j (liftPoint E.target.charts E.target.charts j (c.baseMap u) p)
  rw [(arbitraryCanonicalRecenteredChart E.source.charts j v hvj).apply_symm_apply, coordinates_lift, coordinates_liftPoint, liftCoords, monomialCandidateCoordinates,
    monomialCandidateCoordinates, liftPoint_base, coordinates_liftPoint, liftCoords, monomialCandidateCoordinates]
  simp only [ContinuousLinearEquiv.symm_apply_apply]


/-- **The fibre identity at a source chart point** `s`: `comap (mk ∘ proj^♯) (𝔪_{Bl} · B) ⊆ 𝔪_Y · 𝒪_{Γ_X}`, written on
the ambient stalks (`B = JointQuotient s = AmbientStalk s ⧸ jointIdeal s`). -/
def FibreIdentityAt (s : sourceDomain B b F x t c g d E j v) : Prop :=
  ∀ h : (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
      (c.subdomain × ComplexModel t.rank)).presheaf.stalk (proj B b F x t c g d E j v hvj s),
    sm (proj_contMDiff B b F x t c g d E j v hvj) s h ∈
        jointIdeal (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
          (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
          (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) s ⊔
        Ideal.map (sm (actualMap_holomorphic B b F x t c g d E M j v hvj) s)
          (mx (productChartOpen E.target.charts j) (actualMap B b F x t c g d E j v hvj s)) →
      h ∈ actualWholeSheafStalkIdeal (vanishingIdeal (n := c.embedding.dim+t.rank) (sourceGraphSet B b F x t c))
          (proj B b F x t c g d E j v hvj s) ⊔
        Ideal.map (sm (baseMap_prod_contMDiff B b F x t c) (proj B b F x t c g d E j v hvj s))
          (mx (t.domain × ComplexModel t.rank) (Prod.map c.baseMap id (proj B b F x t c g d E j v hvj s)))

/-- The fibre identity at the slice points `chartPt u p`. -/
theorem fibreIdentityAt_chartPt (u : c.subdomain) (p : productChartOpen E.target.charts j)
    (hu : c.baseMap u = p.val.base.1) (hG : p.val.base.2 = t.functions (c.baseMap u))
    (hV : p ∈ targetStrict B b F x t c g d E j) :
    FibreIdentityAt B b F x t c g d E M j v hvj (chartPt B b F x t c g d E j v hvj u p) := by
  intro h hh
  have hLV : actualMap B b F x t c g d E j v hvj (chartPt B b F x t c g d E j v hvj u p) ∈
      targetStrict B b F x t c g d E j := by
    rw [actualMap_chartPt B b F x t c g d E j v hvj u p hu]
    exact hV
  exact fibre_identity (f := c.baseMap) c.holomorphic t.holomorphic
    ((Subtype.val : c.subdomain → c.domain) ⁻¹' ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹'
      c.embedding.carrier))
    (proj_contMDiff B b F x t c g d E j v hvj)
    (HironakaG10NfRealOpenChartIdeal.realOpenProjection_contMDiff c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v))
    (kappa_contMDiff B b F x t c g d E j v) (kappa_proj B b F x t c g d E j v hvj)
    (originalGraph B b F x t c g d E j v) (kappa_mapsTo B b F x t c g d E j v)
    (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict B b F x t c g d E j)
    (chartPt_contMDiff B b F x t c g d E j v hvj p)
    (contMDiff_liftPoint_left E.target.charts E.target.charts j p) p.val.base.2
    (fun u' => proj_chartPt B b F x t c g d E j v hvj u' p)
    (fun u' => actualMap_chartPt' B b F x t c g d E j v hvj u' p)
    (baseMap_prod_contMDiff B b F x t c) u hG hLV h hh

variable (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)

/-- **H3 (3): the fibre identity `B/𝔪_{X'}B ≅ 𝒪_X/𝔪_Y𝒪_X` at every point of the fibre-product locus `W`.** -/
theorem fibreIdentityAt_of_W (w : W B b F x t c g d E j v hvj h0) :
    FibreIdentityAt B b F x t c g d E M j v hvj w.1 := by
  have hpb := actualMap_base B b F x t c g d E j v hvj w.1
  have hΓ := w.2.2.1
  have h := fibreIdentityAt_chartPt B b F x t c g d E M j v hvj (proj B b F x t c g d E j v hvj w.1).1
    (actualMap B b F x t c g d E j v hvj w.1) (congrArg Prod.fst hpb).symm
    ((congrArg Prod.snd hpb).trans hΓ.2) w.2.2.2
  rwa [chartPt_self] at h

end

end Hironaka.Analytic.Unibranch.HironakaG10NfFibreIdentityCanonical
