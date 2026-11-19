import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift

/-!
# H3 (1), generic part: source chart points from a base point and a target chart point

Lane G10FI, run 0081 (H3 item (1) of `G10N5/hfib-H3-route.md`).  Two product zero-plane blowups `P × ℂ^r ⊇ P × 0`,
`Q × ℂ^r ⊇ Q × 0` with fixed product-normal pivot charts `a`, `b`, and an ambient lift `L` of `f × id`
(`πT ∘ L = (f × id) ∘ πS`, as in `monomialLiftOnChart`).  In the `j`-th charts, `L` changes only the tangential block
(`allambient_lift_formula`); hence the source blowup chart is, near every point, the fibre product of `P` and the
target chart over `Q`:

* `liftPoint u p` — the source chart point with tangential coordinates `u` and the normal coordinates of the target
  chart point `p`; it depends continuously on `(u, p)` (`continuous_liftPoint`);
* `liftPoint_base` — it lies over `(u, (πT p).2)`;
* `lift_liftPoint` — if `f u = (πT p).1` then `L (liftPoint u p) = p`;
* `liftPoint_self` — every source chart point `z` is `liftPoint (πS z).1 (L z)`.

No named input.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFibreChartLift

noncomputable section

open Hironaka Hironaka ProductComplexManifold BlowupFlatCoordinates
  BlowupConstruction BlowupMonomialCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
open scoped ProductComplexManifold

variable {n m r : ℕ} {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]

private theorem monomial_tangent' (j : Fin r) (w : ComplexModel (n+r)) (a : Fin n) :
    monomial n (j.natAdd n) w (a.castAdd r) = w (a.castAdd r) := by
  rw [monomial_apply, if_neg]
  intro h
  exact (Nat.not_le_of_lt a.isLt) h.1

private theorem split_right' (w : ComplexModel (n+r)) (i : Fin r) :
    ((prodModelEquiv n r).symm w).2 i = w (i.natAdd n) := by
  simp [prodModelEquiv, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

private theorem join_right' (a : ComplexModel n) (c : ComplexModel r) (i : Fin r) :
    prodModelEquiv n r (a, c) (i.natAdd n) = c i := by
  simp [prodModelEquiv, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

/-- Two coordinate vectors with the same monomial image and the same normal block are equal. -/
theorem eq_of_monomial_eq (j : Fin r) {w w' : ComplexModel (n+r)}
    (hm : monomial n (j.natAdd n) w = monomial n (j.natAdd n) w')
    (hn : ∀ i : Fin r, w (i.natAdd n) = w' (i.natAdd n)) : w = w' := by
  ext k
  refine Fin.addCases (fun a => ?_) (fun i => hn i) k
  rw [← monomial_tangent' j w a, ← monomial_tangent' j w' a, hm]

/-- The chart coordinates of a chart point are its own candidate coordinates for `f = id`. -/
theorem coordinates_eq_candidate (b : ProductNormalCharts m r Q) (j : Fin r) (p : productChartOpen b j) :
    monomialCandidateCoordinates b b id j p = productChartCoordinates b j p := by
  apply eq_of_monomial_eq j
  · rw [product_monomial_covariance b b id j p]
    exact ((productNormalChart (n := m) b.base j).monomial_toFun p.property).symm
  · intro i
    simp only [monomialCandidateCoordinates, join_right', split_right']

variable (a : ProductNormalCharts n r P) (b : ProductNormalCharts m r Q) (j : Fin r)

/-- Tangential coordinates of `u`, normal coordinates of the target chart point `p`. -/
def liftCoords (u : P) (p : productChartOpen b j) : ComplexModel (n+r) :=
  monomialCandidateCoordinates b a (fun _ => u) j p

theorem liftCoords_mem_target (u : P) (p : productChartOpen b j) :
    liftCoords a b j u p ∈ (productNormalChart (n := n) a.base j).target := by
  change monomial n (j.natAdd n) _ ∈ (productNormalChart (n := n) a.base j).Φ.target
  rw [liftCoords, product_monomial_covariance]
  have hd : (u, p.val.base.2) ∈ (productNormalChart (n := n) a.base j).dom := by
    rw [a.domain j]
    trivial
  exact hd.2

theorem liftCoords_mem (u : P) (p : productChartOpen b j) :
    liftCoords a b j u p ∈ productCoordinateOpen a j :=
  liftCoords_mem_target a b j u p

/-- The source chart point over `u` with the normal coordinates of `p`. -/
def liftPoint (u : P) (p : productChartOpen b j) : productChartOpen a j :=
  (productChartDiffeomorph a j).symm ⟨liftCoords a b j u p, liftCoords_mem a b j u p⟩

theorem coordinates_liftPoint (u : P) (p : productChartOpen b j) :
    productChartCoordinates a j (liftPoint a b j u p) = liftCoords a b j u p :=
  congrArg Subtype.val ((productChartDiffeomorph a j).apply_symm_apply
    ⟨liftCoords a b j u p, liftCoords_mem a b j u p⟩)

theorem liftPoint_val (u : P) (p : productChartOpen b j) :
    (liftPoint a b j u p).val = (productNormalChart (n := n) a.base j).invFun (liftCoords a b j u p) :=
  rfl

theorem liftPoint_base (u : P) (p : productChartOpen b j) :
    (liftPoint a b j u p).val.base = (u, p.val.base.2) := by
  rw [liftPoint_val, (productNormalChart (n := n) a.base j).base_invFun (liftCoords_mem_target a b j u p)]
  change (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r)).symm
    ((productNormalChart (n := n) a.base j).Φ.invFun
      (monomial n (j.natAdd n) (monomialCandidateCoordinates b a (fun _ => u) j p))) = _
  rw [product_monomial_covariance]
  have hd : (u, p.val.base.2) ∈ (productNormalChart (n := n) a.base j).dom := by
    rw [a.domain j]
    trivial
  exact (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r)).left_inv hd.1

include j in
theorem chartAt_continuous : Continuous (chartAt (ComplexModel n) a.base) := by
  have hs : (chartAt (ComplexModel n) a.base).source = univ := by
    apply eq_univ_of_forall
    intro u
    have hd : ((u,0) : P × ComplexModel r) ∈ (productNormalChart (n := n) a.base j).dom := by
      rw [a.domain j]
      trivial
    have hs : ((u,0) : P × ComplexModel r) ∈
        (chartAt (ComplexModel (n+r)) ((a.base,0) : P × ComplexModel r)).source := hd.1
    rw [ProductComplexManifold.chartAt_prod, ProductComplexManifold.prodChart_source] at hs
    exact hs.1
  rw [← continuousOn_univ, ← hs]
  exact (chartAt (ComplexModel n) a.base).continuousOn

theorem continuous_coordinates : Continuous (productChartCoordinates b j) :=
  continuous_subtype_val.comp (productChartDiffeomorph b j).continuous

theorem continuous_liftCoords : Continuous (fun q : P × productChartOpen b j => liftCoords a b j q.1 q.2) :=
  (prodModelEquiv n r).continuous.comp
    (((chartAt_continuous a j).comp continuous_fst).prodMk
      (continuous_snd.comp ((prodModelEquiv m r).symm.continuous.comp
        ((continuous_coordinates b j).comp continuous_snd))))

theorem continuous_liftPoint : Continuous (fun q : P × productChartOpen b j => liftPoint a b j q.1 q.2) :=
  (productChartDiffeomorph a j).symm.continuous.comp
    ((continuous_liftCoords a b j).subtype_mk _)


theorem candidate_mem_target {f : P → Q} (z : productChartOpen a j) :
    monomialCandidateCoordinates a b f j z ∈ (productNormalChart (n := m) b.base j).target := by
  change monomial m (j.natAdd m) _ ∈ (productNormalChart (n := m) b.base j).Φ.target
  rw [product_monomial_covariance]
  have hd : (f z.val.base.1, z.val.base.2) ∈ (productNormalChart (n := m) b.base j).dom := by
    rw [b.domain j]
    trivial
  exact hd.2

variable {f : P → Q} (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
  (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0} → BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
  (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
  (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
    Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0})

include hL hπ in
/-- The target chart coordinates of the lift: tangential block `f`, normal block unchanged. -/
theorem coordinates_lift (z : productChartOpen a j) :
    productChartCoordinates b j (monomialLiftOnChart a b hf L hL hπ j z) =
      monomialCandidateCoordinates a b f j z := by
  change (productNormalChart (n := m) b.base j).toFun (L z.val) = _
  rw [allambient_lift_formula a b hf L hL hπ j z]
  exact (productNormalChart (n := m) b.base j).right_inv (candidate_mem_target a b j z)

include hf hL hπ in
/-- **The lift of `liftPoint u p` is `p`** when `f u` is the base point of `p`. -/
theorem lift_liftPoint (u : P) (p : productChartOpen b j) (hu : f u = p.val.base.1) :
    L (liftPoint a b j u p).val = p.val := by
  rw [allambient_lift_formula a b hf L hL hπ j (liftPoint a b j u p)]
  have hc : monomialCandidateCoordinates a b f j (liftPoint a b j u p) = productChartCoordinates b j p := by
    rw [← coordinates_eq_candidate b j p]
    simp only [monomialCandidateCoordinates]
    rw [liftPoint_base, coordinates_liftPoint, liftCoords, monomialCandidateCoordinates,
      ContinuousLinearEquiv.symm_apply_apply]
    simp only [id, hu]
  change (productNormalChart (n := m) b.base j).invFun (monomialCandidateCoordinates a b f j _) = p.val
  rw [hc]
  exact (productNormalChart (n := m) b.base j).left_inv p.property

include hL hπ in
/-- **Every source chart point is the lift point of its base point and its image.** -/
theorem liftPoint_self (z : productChartOpen a j) :
    liftPoint a b j z.val.base.1 (monomialLiftOnChart a b hf L hL hπ j z) = z := by
  apply (productChartDiffeomorph a j).injective
  apply Subtype.ext
  change productChartCoordinates a j (liftPoint a b j _ _) = productChartCoordinates a j z
  rw [coordinates_liftPoint, ← coordinates_eq_candidate a j z, liftCoords, monomialCandidateCoordinates,
    coordinates_lift a b j hf L hL hπ z, monomialCandidateCoordinates, monomialCandidateCoordinates]
  simp only [ContinuousLinearEquiv.symm_apply_apply, id]

end

end Hironaka.Analytic.Unibranch.HironakaG10NfFibreChartLift
