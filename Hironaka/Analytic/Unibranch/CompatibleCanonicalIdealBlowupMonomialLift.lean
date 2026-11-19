import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts

/-! SAME canonical ambient lift in the fixed ORIGINAL zero-plane charts.
Blueprint FIRST. Whole ambient points, including epsilon0; strict source may
be EMPTY. No shear, extension, supplied ratio/lift packet or raw cancellation.
Held UP/quotient/criterion engines receive zero duplicate credit. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka ProductComplexManifold BlowupFlatCoordinates
  BlowupConstruction BlowupMonomialCharts HironakaReducedComplexAnalyticSpaces
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualWholeStalkHolomorphicPullback
  HironakaActualAnalyticSubspaceOpenRestriction HironakaSingularModuleSheafStalk
  CompatibleCanonicalIdealBlowupSquareCharts CompatibleCanonicalIdealBlowupNormalSections
  CompatibleCanonicalIdealBlowupExplicitProductCharts
open scoped ProductComplexManifold

private theorem join_left {n r : ℕ} (a : ComplexModel n) (b : ComplexModel r) (i : Fin n) :
    prodModelEquiv n r (a,b) (i.castAdd r)=a i := by
  simp [prodModelEquiv,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd]

private theorem join_right {n r : ℕ} (a : ComplexModel n) (b : ComplexModel r) (i : Fin r) :
    prodModelEquiv n r (a,b) (i.natAdd n)=b i := by
  simp [prodModelEquiv,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd]

private theorem split_right {n r : ℕ} (w : ComplexModel (n+r)) (i : Fin r) :
    ((prodModelEquiv n r).symm w).2 i=w (i.natAdd n) := by
  simp [prodModelEquiv,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd]

private theorem monomial_tangent {n r : ℕ} (j : Fin r) (w : ComplexModel (n+r)) (a : Fin n) :
    monomial n (j.natAdd n) w (a.castAdd r)=w (a.castAdd r) := by
  rw [monomial_apply,if_neg]
  intro h
  exact (Nat.not_le_of_lt a.isLt) h.1

private theorem monomial_normal {n r : ℕ} (j i : Fin r) (w : ComplexModel (n+r)) :
    monomial n (j.natAdd n) w (i.natAdd n)=
      if i=j then w (i.natAdd n) else w (i.natAdd n)*w (j.natAdd n) := by
  by_cases h : i=j
  · subst i
    simp [monomial_apply]
  · have hij : i.natAdd n ≠ j.natAdd n := by simpa using h
    rw [monomial_apply,if_pos ⟨by simp,hij⟩,if_neg h]

section ProductCharts
variable {n m r : ℕ} {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]

/-- Literal source of the already existing product-normal chart. -/
def productChartOpen (a : ProductNormalCharts n r P) (j : Fin r) :
    Opens (BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0}) :=
  ⟨(productNormalChart (n := n) a.base j).source,
    (productNormalChart (n := n) a.base j).isOpen_source⟩

/-- Literal coordinate target of that SAME chart, not a smaller open. -/
def productCoordinateOpen (a : ProductNormalCharts n r P) (j : Fin r) :
    Opens (ComplexModel (n+r)) :=
  monomialDomain (productNormalChart (n := n) a.base j).Φ n (j.natAdd n)

def productChartCoordinates (a : ProductNormalCharts n r P) (j : Fin r) :
    productChartOpen a j → ComplexModel (n+r) :=
  fun z => (productNormalChart (n := n) a.base j).toFun z.val

def productChartPlot (a : ProductNormalCharts n r P) (j : Fin r) :
    productCoordinateOpen a j → BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0} :=
  fun w => (productNormalChart (n := n) a.base j).invFun w.val

private theorem flat_product_vector (a : ProductNormalCharts n r P) (j : Fin r)
    (q : P × ComplexModel r) :
    (productNormalChart (n := n) a.base j).Φ.toFun
        (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r) q)=
      prodModelEquiv n r ((chartAt (ComplexModel n) a.base) q.1,q.2) := by
  change prodModelEquiv n r ((chartAt (ComplexModel n) a.base) q.1,
    (chartAt (ComplexModel r) (0 : ComplexModel r)) q.2)=_
  rw [chartAt_self_eq]
  rfl

private theorem preferred_source (a : ProductNormalCharts n r P) (j : Fin r) :
    (chartAt (ComplexModel n) a.base).source=univ := by
  apply eq_univ_of_forall
  intro p
  have hd : ((p,0) : P × ComplexModel r)∈(productNormalChart (n := n) a.base j).dom := by
    rw [a.domain j]
    trivial
  have hs : ((p,0) : P × ComplexModel r)∈
      (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r)).source := hd.1
  rw [ProductComplexManifold.chartAt_prod,ProductComplexManifold.prodChart_source] at hs
  exact hs.1

/-- Change only the genuine tangential block by the SAME actual f. -/
def monomialCandidateCoordinates (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) (f : P → Q) (j : Fin r)
    (z : productChartOpen a j) : ComplexModel (m+r) :=
  prodModelEquiv m r ((chartAt (ComplexModel m) b.base) (f z.val.base.1),
    ((prodModelEquiv n r).symm (productChartCoordinates a j z)).2)

/-- The complete vector covariance, with the original normal offsets. -/
theorem product_monomial_covariance (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) (f : P → Q) (j : Fin r)
    (z : productChartOpen a j) :
    monomial m (j.natAdd m) (monomialCandidateCoordinates a b f j z)=
      (productNormalChart (n := m) b.base j).Φ.toFun
        (chartAt (ComplexModel (m+r)) ((b.base,0) : Q × ComplexModel r)
          (f z.val.base.1,z.val.base.2)) := by
  rw [flat_product_vector]
  ext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [monomial_tangent,join_left]
    exact join_left _ _ i
  · rw [monomial_normal,join_right]
    have hsrc := congrArg (fun w : ComplexModel (n+r) => w (i.natAdd n))
      ((productNormalChart (n := n) a.base j).monomial_toFun z.property)
    change monomial n (j.natAdd n) (productChartCoordinates a j z) (i.natAdd n)=
      ((productNormalChart (n := n) a.base j).Φ.toFun
        (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r) z.val.base))
          (i.natAdd n) at hsrc
    rw [flat_product_vector,join_right,monomial_normal] at hsrc
    simpa only [monomialCandidateCoordinates,join_right,split_right] using hsrc

private theorem candidate_target (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) (f : P → Q) (j : Fin r)
    (z : productChartOpen a j) :
    monomialCandidateCoordinates a b f j z∈(productNormalChart (n := m) b.base j).target := by
  change monomial m (j.natAdd m) _∈(productNormalChart (n := m) b.base j).Φ.target
  rw [product_monomial_covariance]
  have hd : (f z.val.base.1,z.val.base.2)∈(productNormalChart (n := m) b.base j).dom := by
    rw [b.domain j]
    trivial
  exact hd.2

def monomialCandidate (a : ProductNormalCharts n r P) (b : ProductNormalCharts m r Q)
    (f : P → Q) (j : Fin r) :
    productChartOpen a j → BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0} :=
  fun z => (productNormalChart (n := m) b.base j).invFun (monomialCandidateCoordinates a b f j z)

private theorem candidate_mem (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) (f : P → Q) (j : Fin r)
    (z : productChartOpen a j) :
    monomialCandidate a b f j z∈(productNormalChart (n := m) b.base j).source :=
  (productNormalChart (n := m) b.base j).map_target (candidate_target a b f j z)

private theorem candidate_projection (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) (f : P → Q) (j : Fin r)
    (z : productChartOpen a j) :
    (monomialCandidate a b f j z).base=(f z.val.base.1,z.val.base.2) := by
  rw [monomialCandidate,(productNormalChart (n := m) b.base j).base_invFun (candidate_target a b f j z)]
  change (chartAt (ComplexModel (m+r)) ((b.base,0) : Q × ComplexModel r)).symm
    ((productNormalChart (n := m) b.base j).Φ.invFun
      (monomial m (j.natAdd m) (monomialCandidateCoordinates a b f j z)))=_
  rw [product_monomial_covariance]
  have hd : (f z.val.base.1,z.val.base.2)∈(productNormalChart (n := m) b.base j).dom := by
    rw [b.domain j]
    trivial
  change (chartAt (ComplexModel (m+r)) ((b.base,0) : Q × ComplexModel r)).symm
    ((chartAt (ComplexModel (m+r)) ((b.base,0) : Q × ComplexModel r))
      (f z.val.base.1,z.val.base.2))=_
  exact (chartAt (ComplexModel (m+r)) ((b.base,0) : Q × ComplexModel r)).left_inv hd.1

private theorem coordinates_continuous (a : ProductNormalCharts n r P) (j : Fin r) :
    Continuous (productChartCoordinates a j) :=
  (productNormalChart (n := n) a.base j).homeo.continuousOn.domRestrict

private theorem coordinates_holomorphic (a : ProductNormalCharts n r P) (j : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (n+r)) ∞
      (productChartCoordinates a j) := by
  let c := productNormalChart (n := n) a.base j
  have hm := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,ComplexModel (n+r))) (n := ∞)
    (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  intro z
  exact ((contMDiffOn_of_mem_maximalAtlas hm).contMDiffAt
    (c.isOpen_source.mem_nhds z.property)).comp z contMDiff_subtype_val.contMDiffAt

private theorem plot_holomorphic (a : ProductNormalCharts n r P) (j : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (n+r)) ∞
      (productChartPlot a j) := by
  let c := productNormalChart (n := n) a.base j
  have hm := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,ComplexModel (n+r))) (n := ∞)
    (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  intro w
  exact ((contMDiffOn_symm_of_mem_maximalAtlas hm).contMDiffAt
    (c.isOpen_target.mem_nhds w.property)).comp w contMDiff_subtype_val.contMDiffAt

/-- The genuine atlas chart and inverse, using the existing functions. -/
def productChartDiffeomorph (a : ProductNormalCharts n r P) (j : Fin r) :
    productChartOpen a j ≃ₘ⟮𝓘(ℂ,ComplexModel (n+r)),𝓘(ℂ,ComplexModel (n+r))⟯
      productCoordinateOpen a j where
  toFun z := ⟨productChartCoordinates a j z,
    (productNormalChart (n := n) a.base j).map_source z.property⟩
  invFun w := ⟨productChartPlot a j w,
    (productNormalChart (n := n) a.base j).map_target w.property⟩
  left_inv z := Subtype.ext ((productNormalChart (n := n) a.base j).left_inv z.property)
  right_inv w := Subtype.ext ((productNormalChart (n := n) a.base j).right_inv w.property)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (productCoordinateOpen a j) _).mp
    (coordinates_holomorphic a j)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (productChartOpen a j) _).mp
    (plot_holomorphic a j)

private theorem candidate_coordinates_continuous (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) {f : P → Q}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f) (j : Fin r) :
    Continuous (monomialCandidateCoordinates a b f j) := by
  have ht : Continuous (chartAt (ComplexModel m) b.base) := by
    rw [←continuousOn_univ,←preferred_source b j]
    exact (chartAt (ComplexModel m) b.base).continuousOn
  have hb : Continuous (fun z : productChartOpen a j => z.val.base.1) :=
    continuous_fst.comp (contMDiff_blowupProj.continuous.comp continuous_subtype_val)
  exact (prodModelEquiv m r).continuous.comp
    ((ht.comp (hf.continuous.comp hb)).prodMk
      (continuous_snd.comp ((prodModelEquiv n r).symm.continuous.comp
        (coordinates_continuous a j))))

private theorem candidate_continuous (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) {f : P → Q}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f) (j : Fin r) :
    Continuous (monomialCandidate a b f j) :=
  (productNormalChart (n := m) b.base j).homeo.continuousOn_symm.comp_continuous
    (candidate_coordinates_continuous a b hf j) (candidate_target a b f j)

private theorem epsilon_dense (a : ProductNormalCharts n r P) (j : Fin r) :
    Dense {z : productChartOpen a j | productChartCoordinates a j z (j.natAdd n)≠0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨z,hz⟩
  let c := productNormalChart (n := n) a.base j
  let V : Set (BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0}) := Subtype.val '' U
  have hVo : IsOpen V := (productChartOpen a j).isOpen.isOpenMap_subtype_val U hU
  have hzV : z.val∈V := ⟨z,hz,rfl⟩
  have hN : c.homeo '' V ∈ 𝓝 (c.homeo z.val) :=
    c.homeo.image_mem_nhds z.property (hVo.mem_nhds hzV)
  obtain ⟨w,⟨q,⟨z',hz',hzq⟩,hqw⟩,hne⟩ := exists_coord_ne_zero_of_mem_nhds hN (j.natAdd n)
  refine ⟨z',hz',?_⟩
  rw [←hqw,←hzq] at hne
  exact hne

/-- The actual lift equals the candidate at ALL ambient chart points.
The ordinary caller below internally discharges the held projection/holo laws. -/
theorem allambient_lift_formula (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) {f : P → Q}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0} →
      BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
    (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
      Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0})
    (j : Fin r) (z : productChartOpen a j) : L z.val=monomialCandidate a b f j z := by
  have heq : EqOn (L ∘ Subtype.val) (monomialCandidate a b f j)
      {z : productChartOpen a j | productChartCoordinates a j z (j.natAdd n)≠0} := by
    intro w hw
    have hs : w.val.base∉{q : P × ComplexModel r | q.2=0} := by
      intro h
      exact hw (((productNormalChart (n := n) a.base j).toFun_j_eq_zero_iff w.property).mpr h)
    have hbase := congrFun hπ w.val
    apply eq_of_base_eq_of_not_mem (hbase.trans (candidate_projection a b f j w).symm)
    intro ht
    apply hs
    change w.val.base.2=0
    exact (congrArg Prod.snd hbase).symm.trans ht
  exact congrFun (Continuous.ext_on (epsilon_dense a j)
    (hL.continuous.comp continuous_subtype_val) (candidate_continuous a b hf j) heq) z

private theorem actual_lift_target (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) {f : P → Q}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0} →
      BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
    (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
      Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0})
    (j : Fin r) (z : productChartOpen a j) : L z.val∈productChartOpen b j := by
  rw [allambient_lift_formula a b hf L hL hπ j z]
  exact candidate_mem a b f j z

/-- Literal codomain restriction of the SAME actual ambient L. -/
def monomialLiftOnChart (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) {f : P → Q}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0} →
      BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
    (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
      Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0})
    (j : Fin r) : productChartOpen a j → productChartOpen b j :=
  fun z => ⟨L z.val,actual_lift_target a b hf L hL hπ j z⟩

private theorem lift_on_chart_holomorphic (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) {f : P → Q}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0} →
      BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
    (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
      Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0}) (j : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞
      (monomialLiftOnChart a b hf L hL hπ j) :=
  (ContMDiff.subtypeVal_comp_iff (productChartOpen b j) _).mp
    (hL.comp contMDiff_subtype_val)

/-- Literal coordinate map; all normal coordinates are unchanged even at epsilon0. -/
def monomialCoordinateMap (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) (f : P → Q) (j : Fin r) :
    productCoordinateOpen a j → productCoordinateOpen b j :=
  fun w => ⟨monomialCandidateCoordinates a b f j ((productChartDiffeomorph a j).symm w),
    candidate_target a b f j ((productChartDiffeomorph a j).symm w)⟩

private theorem lift_coordinates (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) {f : P → Q}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0} →
      BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
    (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
      Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0})
    (j : Fin r) (z : productChartOpen a j) :
    productChartCoordinates b j (monomialLiftOnChart a b hf L hL hπ j z)=
      monomialCandidateCoordinates a b f j z := by
  change (productNormalChart (n := m) b.base j).toFun (L z.val)=_
  rw [allambient_lift_formula a b hf L hL hπ]
  exact (productNormalChart (n := m) b.base j).right_inv (candidate_target a b f j z)

private theorem coordinate_map_conjugate (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) {f : P → Q}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0} →
      BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
    (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
      Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0}) (j : Fin r) :
    monomialCoordinateMap a b f j=(productChartDiffeomorph b j) ∘
      monomialLiftOnChart a b hf L hL hπ j ∘ (productChartDiffeomorph a j).symm := by
  funext w
  exact Subtype.ext (lift_coordinates a b hf L hL hπ j ((productChartDiffeomorph a j).symm w)).symm

private theorem coordinate_map_holomorphic (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) {f : P → Q}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0} →
      BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
    (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
      Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0}) (j : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞
      (monomialCoordinateMap a b f j) := by
  rw [coordinate_map_conjugate a b hf L hL hπ j]
  exact (productChartDiffeomorph b j).contMDiff.comp
    ((lift_on_chart_holomorphic a b hf L hL hπ j).comp (productChartDiffeomorph a j).symm.contMDiff)

private theorem coordinate_map_normal (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) (f : P → Q) (j i : Fin r)
    (w : productCoordinateOpen a j) :
    (monomialCoordinateMap a b f j w).val (i.natAdd m)=w.val (i.natAdd n) := by
  change (monomialCandidateCoordinates a b f j ((productChartDiffeomorph a j).symm w))
    (i.natAdd m)=_
  rw [monomialCandidateCoordinates,join_right,split_right]
  have he := congrArg (fun v : productCoordinateOpen a j => v.val (i.natAdd n))
    ((productChartDiffeomorph a j).apply_symm_apply w)
  exact he

private theorem coordinate_map_tangent (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) (f : P → Q) (j : Fin r) (i : Fin m)
    (w : productCoordinateOpen a j) :
    (monomialCoordinateMap a b f j w).val (i.castAdd r)=
      (chartAt (ComplexModel m) b.base (f (productChartPlot a j w).base.1)) i := by
  exact join_left _ _ i

private theorem coordinate_map_plot (a : ProductNormalCharts n r P)
    (b : ProductNormalCharts m r Q) {f : P → Q}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0} →
      BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
    (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
      Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0}) (j : Fin r) :
    L ∘ productChartPlot a j=productChartPlot b j ∘ monomialCoordinateMap a b f j := by
  funext w
  exact allambient_lift_formula a b hf L hL hπ j ((productChartDiffeomorph a j).symm w)

def productChartNativeIso (a : ProductNormalCharts n r P) (j : Fin r) :
    ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (n+r)) (productChartOpen a j) ≅
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (n+r)) (productCoordinateOpen a j) where
  hom := ChartedSpace.locallyRingedSpaceMap (productChartDiffeomorph a j)
    (productChartDiffeomorph a j).contMDiff
  inv := ChartedSpace.locallyRingedSpaceMap (productChartDiffeomorph a j).symm
    (productChartDiffeomorph a j).symm.contMDiff
  hom_inv_id := by
    rw [←ChartedSpace.locallyRingedSpace_comp]
    have hi : (productChartDiffeomorph a j).symm ∘ (productChartDiffeomorph a j)=id :=
      funext (productChartDiffeomorph a j).symm_apply_apply
    simpa only [hi] using ChartedSpace.locallyRingedSpace_id
      𝓘(ℂ,ComplexModel (n+r)) (productChartOpen a j)
  inv_hom_id := by
    rw [←ChartedSpace.locallyRingedSpace_comp]
    have hi : (productChartDiffeomorph a j) ∘ (productChartDiffeomorph a j).symm=id :=
      funext (productChartDiffeomorph a j).apply_symm_apply
    simpa only [hi] using ChartedSpace.locallyRingedSpace_id
      𝓘(ℂ,ComplexModel (n+r)) (productCoordinateOpen a j)

def nativeProductChartPlot (a : ProductNormalCharts n r P) (j : Fin r) :=
  ChartedSpace.locallyRingedSpaceMap (productChartPlot a j) (plot_holomorphic a j)

private theorem native_holomorphic_point {f : P → Q}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f) :
    ChartedSpace.locallyRingedSpaceMap f hf ≫ ambientPointMap m Q=ambientPointMap n P :=
  (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ,ComplexModel n))
    (IN := 𝓘(ℂ,ComplexModel m)) (IP := 𝓘(ℂ,ComplexModel 0)) hf
    (show ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel 0) ∞
      (fun _ : Q => (0 : ComplexModel 0)) from contMDiff_const)).symm

def productNormalFunction (a : ProductNormalCharts n r P) (j i : Fin r) :
    productChartOpen a j → ℂ := fun z => productChartCoordinates a j z (i.natAdd n)

private theorem normal_holomorphic (a : ProductNormalCharts n r P) (j i : Fin r)
    (z : productChartOpen a j) : HolomorphicAt (n+r) (productNormalFunction a j i) z :=
  ((productNormalChart (n := n) a.base j).holomorphicAt_coord z.property (i.natAdd n)).comp_contMDiff
    (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)

section NativeLift
variable (a : ProductNormalCharts n r P) (b : ProductNormalCharts m r Q) {f : P → Q}
  (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
  (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0} →
    BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
  (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
  (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
    Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0})

def nativeMonomialLiftOnChart (j : Fin r) :=
  ChartedSpace.locallyRingedSpaceMap (monomialLiftOnChart a b hf L hL hπ j)
    (lift_on_chart_holomorphic a b hf L hL hπ j)

def nativeMonomialCoordinateMap (j : Fin r) :=
  ChartedSpace.locallyRingedSpaceMap (monomialCoordinateMap a b f j)
    (coordinate_map_holomorphic a b hf L hL hπ j)

private theorem native_plot_square (j : Fin r) :
    nativeProductChartPlot a j ≫ ChartedSpace.locallyRingedSpaceMap L hL=
      nativeMonomialCoordinateMap a b hf L hL hπ j ≫ nativeProductChartPlot b j := by
  change ChartedSpace.locallyRingedSpaceMap _ _ ≫ ChartedSpace.locallyRingedSpaceMap _ _=
    ChartedSpace.locallyRingedSpaceMap _ _ ≫ ChartedSpace.locallyRingedSpaceMap _ _
  rw [←ChartedSpace.locallyRingedSpace_comp,←ChartedSpace.locallyRingedSpace_comp]
  congr 1
  exact coordinate_map_plot a b hf L hL hπ j

private theorem native_chart_square (j : Fin r) :
    nativeMonomialLiftOnChart a b hf L hL hπ j ≫ (productChartNativeIso b j).hom=
      (productChartNativeIso a j).hom ≫ nativeMonomialCoordinateMap a b hf L hL hπ j := by
  change ChartedSpace.locallyRingedSpaceMap _ _ ≫ ChartedSpace.locallyRingedSpaceMap _ _=
    ChartedSpace.locallyRingedSpaceMap _ _ ≫ ChartedSpace.locallyRingedSpaceMap _ _
  rw [←ChartedSpace.locallyRingedSpace_comp,←ChartedSpace.locallyRingedSpace_comp]
  congr 1
  funext z
  rw [coordinate_map_conjugate a b hf L hL hπ j]
  change (productChartDiffeomorph b j) (monomialLiftOnChart a b hf L hL hπ j z)=
    (productChartDiffeomorph b j) (monomialLiftOnChart a b hf L hL hπ j
      ((productChartDiffeomorph a j).symm ((productChartDiffeomorph a j) z)))
  rw [(productChartDiffeomorph a j).symm_apply_apply]

private theorem native_inclusion_square (j : Fin r) :
    nativeMonomialLiftOnChart a b hf L hL hπ j ≫
        ChartedSpace.locallyRingedSpaceMap (Subtype.val : productChartOpen b j → _)
          contMDiff_subtype_val =
      ChartedSpace.locallyRingedSpaceMap (Subtype.val : productChartOpen a j → _)
          contMDiff_subtype_val ≫ ChartedSpace.locallyRingedSpaceMap L hL := by
  unfold nativeMonomialLiftOnChart
  rw [←ChartedSpace.locallyRingedSpace_comp,←ChartedSpace.locallyRingedSpace_comp]
  rfl

private theorem native_plot_all_numerators (j : Fin r) (w : productCoordinateOpen a j)
    (s : actualComplexStructureStalk (n := m+r)
      (M := BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
      ((nativeProductChartPlot a j ≫ ChartedSpace.locallyRingedSpaceMap L hL).base w)) :
    (nativeProductChartPlot a j ≫ ChartedSpace.locallyRingedSpaceMap L hL).stalkMap w s=
      (nativeMonomialCoordinateMap a b hf L hL hπ j ≫ nativeProductChartPlot b j).stalkMap w
        ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (m+r))
          (BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})).presheaf.stalkSpecializes
          (specializes_of_eq (congrArg (fun H => H.base w) (native_plot_square a b hf L hL hπ j)).symm) s) :=
  ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_congr_hom _ _
    (native_plot_square a b hf L hL hπ j) w) s

private theorem lift_normal (j i : Fin r) (z : productChartOpen a j) :
    productNormalFunction b j i (monomialLiftOnChart a b hf L hL hπ j z)=
      productNormalFunction a j i z := by
  change productChartCoordinates b j (monomialLiftOnChart a b hf L hL hπ j z) (i.natAdd m)=_
  rw [lift_coordinates,monomialCandidateCoordinates,join_right,split_right]
  rfl

private theorem native_normal_germ (j i : Fin r) (z : productChartOpen a j) :
    (nativeMonomialLiftOnChart a b hf L hL hπ j).stalkMap z
      (actualOriginalFunctionGerm (monomialLiftOnChart a b hf L hL hπ j z)
        (productNormalFunction b j i) (normal_holomorphic b j i _))=
      actualOriginalFunctionGerm z (productNormalFunction a j i) (normal_holomorphic a j i z) := by
  unfold nativeMonomialLiftOnChart
  apply (actualStalkChartEquiv (n := n+r) z).injective
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function,actualOriginalFunctionGerm_chart]
  apply chartTranslatedGerm_congr_original
  exact Eventually.of_forall (lift_normal a b hf L hL hπ j i)

/-- OUTPUT laws on the SAME fixed charts and actual lift. The ordinary
canonical caller below constructs all of them; none is an incoming packet. -/
structure MonomialLiftLaws : Prop where
  formula : ∀ (j : Fin r) (z : productChartOpen a j),
    L z.val=monomialCandidate a b f j z
  target : ∀ (j : Fin r) (z : productChartOpen a j), L z.val∈productChartOpen b j
  restricted_holomorphic : ∀j : Fin r,
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞
      (monomialLiftOnChart a b hf L hL hπ j)
  coordinate_holomorphic : ∀j : Fin r,
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ (monomialCoordinateMap a b f j)
  normal_slots : ∀ (j i : Fin r) (w : productCoordinateOpen a j),
    (monomialCoordinateMap a b f j w).val (i.natAdd m)=w.val (i.natAdd n)
  tangent_slots : ∀ (j : Fin r) (i : Fin m) (w : productCoordinateOpen a j),
    (monomialCoordinateMap a b f j w).val (i.castAdd r)=
      (chartAt (ComplexModel m) b.base (f (productChartPlot a j w).base.1)) i
  plot_formula : ∀j : Fin r,
    L ∘ productChartPlot a j=productChartPlot b j ∘ monomialCoordinateMap a b f j
  plot_square : ∀j : Fin r,
    nativeProductChartPlot a j ≫ ChartedSpace.locallyRingedSpaceMap L hL=
      nativeMonomialCoordinateMap a b hf L hL hπ j ≫ nativeProductChartPlot b j
  chart_square : ∀j : Fin r,
    nativeMonomialLiftOnChart a b hf L hL hπ j ≫ (productChartNativeIso b j).hom=
      (productChartNativeIso a j).hom ≫ nativeMonomialCoordinateMap a b hf L hL hπ j
  inclusion_square : ∀j : Fin r,
    nativeMonomialLiftOnChart a b hf L hL hπ j ≫
        ChartedSpace.locallyRingedSpaceMap (Subtype.val : productChartOpen b j → _) contMDiff_subtype_val=
      ChartedSpace.locallyRingedSpaceMap (Subtype.val : productChartOpen a j → _)
        contMDiff_subtype_val ≫ ChartedSpace.locallyRingedSpaceMap L hL
  ambient_scalar : ChartedSpace.locallyRingedSpaceMap L hL ≫
      ambientPointMap (m+r) (BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})=
    ambientPointMap (n+r) (BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0})
  restricted_scalar : ∀j : Fin r, nativeMonomialLiftOnChart a b hf L hL hπ j ≫
    ambientPointMap (m+r) (productChartOpen b j)=ambientPointMap (n+r) (productChartOpen a j)
  coordinate_scalar : ∀j : Fin r, nativeMonomialCoordinateMap a b hf L hL hπ j ≫
    ambientPointMap (m+r) (productCoordinateOpen b j)=ambientPointMap (n+r) (productCoordinateOpen a j)
  source_chart_scalar : ∀j : Fin r, (productChartNativeIso a j).hom ≫
    ambientPointMap (n+r) (productCoordinateOpen a j)=ambientPointMap (n+r) (productChartOpen a j)
  target_chart_scalar : ∀j : Fin r, (productChartNativeIso b j).hom ≫
    ambientPointMap (m+r) (productCoordinateOpen b j)=ambientPointMap (m+r) (productChartOpen b j)
  source_plot_scalar : ∀j : Fin r, nativeProductChartPlot a j ≫
      ambientPointMap (n+r) (BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0})=
    ambientPointMap (n+r) (productCoordinateOpen a j)
  target_plot_scalar : ∀j : Fin r, nativeProductChartPlot b j ≫
      ambientPointMap (m+r) (BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})=
    ambientPointMap (m+r) (productCoordinateOpen b j)
  all_numerators : ∀ (j : Fin r) (w : productCoordinateOpen a j)
    (s : actualComplexStructureStalk (n := m+r)
      (M := BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
      ((nativeProductChartPlot a j ≫ ChartedSpace.locallyRingedSpaceMap L hL).base w)),
    (nativeProductChartPlot a j ≫ ChartedSpace.locallyRingedSpaceMap L hL).stalkMap w s=
      (nativeMonomialCoordinateMap a b hf L hL hπ j ≫ nativeProductChartPlot b j).stalkMap w
        ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (m+r))
          (BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})).presheaf.stalkSpecializes
          (specializes_of_eq (congrArg (fun H => H.base w) (native_plot_square a b hf L hL hπ j)).symm) s)
  restricted_chart_dictionary : ∀ (j : Fin r) (z : productChartOpen a j)
    (s : actualComplexStructureStalk (n := m+r) (M := productChartOpen b j)
      (monomialLiftOnChart a b hf L hL hπ j z)),
    actualStalkChartEquiv (n := n+r) z ((nativeMonomialLiftOnChart a b hf L hL hπ j).stalkMap z s)=
      actualHolomorphicGermPullback (lift_on_chart_holomorphic a b hf L hL hπ j) z
        (actualStalkChartEquiv (n := m+r) (monomialLiftOnChart a b hf L hL hπ j z) s)
  coordinate_chart_dictionary : ∀ (j : Fin r) (w : productCoordinateOpen a j)
    (s : actualComplexStructureStalk (n := m+r) (M := productCoordinateOpen b j)
      (monomialCoordinateMap a b f j w)),
    actualStalkChartEquiv (n := n+r) w ((nativeMonomialCoordinateMap a b hf L hL hπ j).stalkMap w s)=
      actualHolomorphicGermPullback (coordinate_map_holomorphic a b hf L hL hπ j) w
        (actualStalkChartEquiv (n := m+r) (monomialCoordinateMap a b f j w) s)
  normal_germs : ∀ (j i : Fin r) (z : productChartOpen a j),
    (nativeMonomialLiftOnChart a b hf L hL hπ j).stalkMap z
      (actualOriginalFunctionGerm (monomialLiftOnChart a b hf L hL hπ j z)
        (productNormalFunction b j i) (normal_holomorphic b j i _))=
      actualOriginalFunctionGerm z (productNormalFunction a j i) (normal_holomorphic a j i z)

private theorem constructedMonomialLaws : MonomialLiftLaws a b hf L hL hπ where
  formula := allambient_lift_formula a b hf L hL hπ
  target := actual_lift_target a b hf L hL hπ
  restricted_holomorphic := lift_on_chart_holomorphic a b hf L hL hπ
  coordinate_holomorphic := coordinate_map_holomorphic a b hf L hL hπ
  normal_slots := coordinate_map_normal a b f
  tangent_slots := coordinate_map_tangent a b f
  plot_formula := coordinate_map_plot a b hf L hL hπ
  plot_square := native_plot_square a b hf L hL hπ
  chart_square := native_chart_square a b hf L hL hπ
  inclusion_square := native_inclusion_square a b hf L hL hπ
  ambient_scalar := native_holomorphic_point hL
  restricted_scalar j := by
    unfold nativeMonomialLiftOnChart
    exact native_holomorphic_point (lift_on_chart_holomorphic a b hf L hL hπ j)
  coordinate_scalar j := by
    unfold nativeMonomialCoordinateMap
    exact native_holomorphic_point (coordinate_map_holomorphic a b hf L hL hπ j)
  source_chart_scalar j := native_holomorphic_point (productChartDiffeomorph a j).contMDiff
  target_chart_scalar j := native_holomorphic_point (productChartDiffeomorph b j).contMDiff
  source_plot_scalar j := native_holomorphic_point (plot_holomorphic a j)
  target_plot_scalar j := native_holomorphic_point (plot_holomorphic b j)
  all_numerators := native_plot_all_numerators a b hf L hL hπ
  restricted_chart_dictionary j z s := by
    unfold nativeMonomialLiftOnChart
    exact actualNativeStalk_chart_pullback (lift_on_chart_holomorphic a b hf L hL hπ j) z s
  coordinate_chart_dictionary j w s := by
    unfold nativeMonomialCoordinateMap
    exact actualNativeStalk_chart_pullback (coordinate_map_holomorphic a b hf L hL hπ j) w s
  normal_germs := native_normal_germ a b hf L hL hπ

end NativeLift
end ProductCharts

section SameCanonicalModels
open OriginalFiniteIdealGraphChart HironakaResolutionSpaceComplex
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

/-- Only OUTPUT data on the SAME actual parent model, with all its full
canonical/whole-ideal/normal-section/scalar laws retained by E. -/
abbrev AllAmbientMonomialLiftData (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (d : CanonicalNormalSectionData B b F x t c g)
    (E : SameCanonicalExplicitProductModels B b F x t c g d) : Prop :=
  MonomialLiftLaws E.source.charts E.target.charts c.holomorphic
    (explicitAmbientLift B b F x t c g E.target E.source)
    E.square.holomorphic E.square.ambient_projection

/-- ONLY ordinary original inputs and the GIVEN target point. Call accepted920
ONCE, before ALL j/points/numerators. No incoming lift, desired square, ratio,
Cartier, image/shrink or source-point packet. Strict source may be EMPTY.
Pivot-open coverage/restrictions, Qsat, raw fibres and G10 closure stay separate. -/
theorem exists_same_canonical_allambient_monomial_lift
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x=(OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    ∃ (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g)
      (E : SameCanonicalExplicitProductModels B b F x t c g d),
      Nonempty (AllAmbientMonomialLiftData B b F x t c g d E) := by
  obtain ⟨t,c,g,d,⟨E⟩⟩ := exists_same_canonical_explicit_product_models B b F x y hxy
  exact ⟨t,c,g,d,E,⟨constructedMonomialLaws E.source.charts E.target.charts c.holomorphic
    (explicitAmbientLift B b F x t c g E.target E.source)
    E.square.holomorphic E.square.ambient_projection⟩⟩

end SameCanonicalModels
end
end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
