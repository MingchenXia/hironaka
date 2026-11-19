import Hironaka.Resolution.HironakaG8GeneralCentreStrictTangent

set_option autoImplicit false

/-!
# Tangent-space membership in a native exceptional fibre

For closed submanifolds `C ⊆ W`, a native exceptional point belongs to the
geometric strict transform of `W` exactly when its actual direction space
is contained in the tangent space of `W`. The converse constructs nearby
off-centre points in an actual nested-flattening monomial chart.

Centre containment is explicit. This is a single-blowup fibre criterion,
not a residual successor theorem or a comparison of two marked records.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8GeneralCentreFibreCriterion

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupConstruction BlowupSpaceTangent BlowupStrictSubmanifold
  BlowupFlatCoordinates BlowupMonomialCharts NestedFlattening
  HironakaG8GeneralCentreStrictTangent

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {C : Set X} [Fact (IsClosedSubmanifold n C)]

omit [Fact (IsClosedSubmanifold n C)] in
private theorem tangentSpace_le_of_subset {W : Set X} (hCW : C ⊆ W) (x : X) :
    tangentSpace n C x ≤ tangentSpace n W x := by
  intro ξ hξ
  apply mem_tangentSpace.mpr
  intro f hfW
  apply germDiff_eq_zero_of_mem_tangentSpace hξ
  refine ⟨hfW.1, ?_⟩
  filter_upwards [hfW.2] with y hy hyC
  exact hy (hCW hyC)

omit [Fact (IsClosedSubmanifold n C)] in
/-- The genuine native chart normal represents the actual direction space
of the exceptional point, modulo the tangent space of the centre. -/
theorem dir_eq_tangentCentre_sup_normal_direction (c : FlatChart n C)
    {p : BlowupSpace n C} (hps : p ∈ c.source) (hpC : p.base ∈ C) :
    p.dir = tangentSpace n C p.base ⊔
      ℂ ∙ flatVec c.Φ p.base (c.normalVec (c.toFun p)) := by
  have hinv := c.left_inv hps
  rw [c.invFun_of_eq (c.map_source hps) ((c.toFun_j_eq_zero_iff hps).mpr hpC)] at hinv
  have hdir := congrArg BlowupSpace.dir hinv
  change tangentSpace n C (c.pt (c.toFun p)) ⊔
    ℂ ∙ flatVec c.Φ (c.pt (c.toFun p)) (c.normalVec (c.toFun p)) = p.dir at hdir
  rw [c.pt_toFun hps] at hdir
  exact hdir.symm

/-- The actual direction space of any exceptional strict-transform point
is tangent to the original set. This implication needs only `C ⊆ W`. -/
theorem dir_le_tangentSpace_of_mem_geoStrictTransform {W : Set X}
    (hCW : C ⊆ W) {p : BlowupSpace n C}
    (hp : p ∈ geoStrictTransform (blowupProj n C) C W) (hpC : p.base ∈ C) :
    p.dir ≤ tangentSpace n W p.base := by
  obtain ⟨j, hj, hps⟩ := exists_mem_flatSource hpC
    (mem_flatDomain_self (flatΦ n hpC)) hpC
  let c : FlatChart n C := mkFlat hpC j hj
  rw [dir_eq_tangentCentre_sup_normal_direction c hps hpC]
  refine sup_le (tangentSpace_le_of_subset hCW p.base) ?_
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr
    (normal_direction_mem_tangentSpace_of_mem_geoStrictTransform c hCW hp hps hpC)

/-- Varying the actual pivot gives points of the original smooth set away
from the centre, whenever the native chart also flattens that set. -/
private theorem mem_geoStrictTransform_of_nested_coordinates (c : FlatChart n C)
    {W : Set X} {kW : ℕ} (hkw : c.k ≤ kW)
    (hflatW : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) c.y₀).source →
      chartAt (ComplexModel n) c.y₀ x ∈ c.Φ.source →
        (x ∈ W ↔ c.Φ.toFun (chartAt (ComplexModel n) c.y₀ x) ∈ complexCoordinatePlane n kW))
    {p : BlowupSpace n C} (hps : p ∈ c.source)
    (hjW : c.j.val < kW) (hpj : c.toFun p c.j = 0)
    (hpW : c.toFun p ∈ complexCoordinatePlane n kW) :
    p ∈ geoStrictTransform (blowupProj n C) C W := by
  let w₀ := c.toFun p
  let eⱼ : ComplexModel n := EuclideanSpace.single c.j (1 : ℂ)
  let curve : ℂ → ComplexModel n := fun t => w₀ + t • eⱼ
  have hw₀ : w₀ ∈ c.target := c.map_source hps
  have hcurve : Tendsto curve (𝓝 (0 : ℂ)) (𝓝 w₀) := by
    have hc : Continuous curve := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [curve, zero_smul, add_zero] using hc.tendsto 0
  have hinverse : Tendsto (fun t => c.invFun (curve t)) (𝓝 (0 : ℂ)) (𝓝 p) := by
    have h := (c.homeo.continuousAt_symm hw₀).tendsto.comp hcurve
    change Tendsto (fun t => c.invFun (curve t)) (𝓝 (0 : ℂ)) (𝓝 (c.invFun w₀)) at h
    simpa only [w₀, c.left_inv hps] using h
  have htarget : ∀ᶠ t in 𝓝 (0 : ℂ), curve t ∈ c.target :=
    hcurve (c.isOpen_target.mem_nhds hw₀)
  rw [geoStrictTransform, mem_closure_iff_nhds]
  intro U hU
  have hUevent : ∀ᶠ t in 𝓝 (0 : ℂ), c.invFun (curve t) ∈ U := hinverse hU
  have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      curve t ∈ c.target ∧ c.invFun (curve t) ∈ U :=
    nhdsWithin_le_nhds (htarget.and hUevent)
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      (curve t ∈ c.target ∧ c.invFun (curve t) ∈ U) ∧ t ≠ 0 :=
    hnear.and self_mem_nhdsWithin
  obtain ⟨t, ⟨ht, htU⟩, htne⟩ := hev.exists
  refine ⟨c.invFun (curve t), htU, ?_⟩
  rw [mem_preimage, c.blowupProj_invFun ht]
  have htpivot : curve t c.j = t := by
    simp [curve, w₀, eⱼ, hpj]
  refine ⟨?_, fun hC => htne (htpivot ▸ (c.pt_mem_iff ht).mp hC)⟩
  apply (hflatW (c.pt_mem_dom ht).1 (c.pt_mem_dom ht).2).mpr
  rw [c.flat_pt ht]
  intro i hi
  have hij : i ≠ c.j := by
    intro h
    subst h
    omega
  have hci : c.k ≤ i.val := hkw.trans hi
  have hcurvei : curve t i = 0 := by
    simp [curve, w₀, eⱼ, hij, hpW i hi]
  rw [monomial_apply, if_pos ⟨hci, hij⟩, hcurvei, zero_mul]

/-- The converse fibre implication is constructed from nested flattening
and actual inverse-chart arcs, without assuming strict-transform membership. -/
theorem mem_geoStrictTransform_of_dir_le_tangentSpace {W : Set X}
    (hW : IsClosedSubmanifold n W) (hCW : C ⊆ W)
    {p : BlowupSpace n C} (hpC : p.base ∈ C)
    (hpdir : p.dir ≤ tangentSpace n W p.base) :
    p ∈ geoStrictTransform (blowupProj n C) C W := by
  obtain ⟨kC, hkC⟩ := (Fact.out : IsClosedSubmanifold n C).2 p.base hpC
  obtain ⟨kW, hkW⟩ := hW.2 p.base (hCW hpC)
  have hkw : kC ≤ kW := le_of_regularAtDim_subset hkC hkW hCW
  obtain ⟨Φ, hΦsrc, _hΦ0, hflat⟩ := exists_nested_flattening hkw hkC hkW hCW
  have hdom : p.base ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hflatC : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) p.base).source →
      chartAt (ComplexModel n) p.base x ∈ Φ.source →
        (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) p.base x) ∈ complexCoordinatePlane n kC) :=
    fun hx hΦx => (hflat hx hΦx).1
  have hflatW : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) p.base).source →
      chartAt (ComplexModel n) p.base x ∈ Φ.source →
        (x ∈ W ↔ Φ.toFun (chartAt (ComplexModel n) p.base x) ∈ complexCoordinatePlane n kW) :=
    fun hx hΦx => (hflat hx hΦx).2
  have hnot := p.dirVec_not_mem hpC
  rw [mem_tangentSpace_iff hΦsrc hflatC hdom hpC] at hnot
  push Not at hnot
  obtain ⟨j, hj, hne⟩ := hnot
  let c : FlatChart n C := ⟨p.base, kC, Φ, hΦsrc, hflatC, j, hj⟩
  have hps : p ∈ c.source := by
    refine ⟨hdom, ?_⟩
    change extVal (flatCoord Φ j) p ≠ 0
    rw [extVal_of_mem hpC]
    exact hne
  have hξdir : flatVec c.Φ p.base (c.normalVec (c.toFun p)) ∈ p.dir := by
    rw [dir_eq_tangentCentre_sup_normal_direction c hps hpC]
    apply (show ℂ ∙ flatVec c.Φ p.base (c.normalVec (c.toFun p)) ≤
      tangentSpace n C p.base ⊔ ℂ ∙ flatVec c.Φ p.base (c.normalVec (c.toFun p)) from le_sup_right)
    exact Submodule.mem_span_singleton_self _
  have hξW := hpdir hξdir
  have hnormalZero : ∀ i : Fin n, kW ≤ i.val → c.normalVec (c.toFun p) i = 0 := by
    intro i hi
    have hz := (mem_tangentSpace_iff hΦsrc hflatW hdom (hCW hpC)).mp hξW i hi
    exact (germDiff_flatCoord_flatVec hΦsrc hdom i (c.normalVec (c.toFun p))).symm.trans hz
  have hjW : c.j.val < kW := by
    by_contra h
    have hz := hnormalZero c.j (by omega)
    rw [c.normalVec_j] at hz
    exact one_ne_zero hz
  have hpW : c.toFun p ∈ complexCoordinatePlane n kW := by
    intro i hi
    have hij : i ≠ c.j := by
      intro h
      exact (Nat.not_le_of_lt hjW) (h ▸ hi)
    have hci : c.k ≤ i.val := hkw.trans hi
    have hz := hnormalZero i hi
    simpa only [c.normalVec_apply, if_neg hij, if_pos hci] using hz
  exact mem_geoStrictTransform_of_nested_coordinates c hkw hflatW hps hjW
    ((c.toFun_j_eq_zero_iff hps).mpr hpC) hpW

/-- Native exceptional-fibre membership is exactly containment of the
actual direction space in the tangent space of the smooth original set. -/
theorem mem_geoStrictTransform_iff_dir_le_tangentSpace {W : Set X}
    (hW : IsClosedSubmanifold n W) (hCW : C ⊆ W)
    {p : BlowupSpace n C} (hpC : p.base ∈ C) :
    p ∈ geoStrictTransform (blowupProj n C) C W ↔
      p.dir ≤ tangentSpace n W p.base :=
  ⟨fun hp => dir_le_tangentSpace_of_mem_geoStrictTransform hCW hp hpC,
    fun hdir => mem_geoStrictTransform_of_dir_le_tangentSpace hW hCW hpC hdir⟩

end

end Hironaka.HironakaG8GeneralCentreFibreCriterion
