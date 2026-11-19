import Hironaka.Blowup.BlowupSpaceManifold
import Hironaka.Blowup.BlowupStrictSubmanifold

set_option autoImplicit false

/-!
# Native normal directions on a general-centre geometric strict transform

The actual monomial chart already provides `normalVec` and the extended
quotient `ratio`. Its holomorphic extension and exceptional-value formula
are reused here. The new bridge is closure-to-vanishing: an equation of
`W` containing the centre has zero extended quotient on the geometric
strict transform, hence its differential kills the native normal direction.

The centre containment is essential and remains explicit. This proves
one first-order inclusion; it does not prove a converse, compare two
carriers, or discharge the residual successor step (r1).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8GeneralCentreStrictTangent

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupConstruction BlowupSpaceTangent BlowupStrictSubmanifold

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {C : Set X} [Fact (IsClosedSubmanifold n C)]

omit [IsComplexManifold n X] [Fact (IsClosedSubmanifold n C)] in
private theorem mem_centreIdeal_on_open {W V : Set X} (hCW : C ⊆ W)
    (hV : IsOpen V) {f : X → ℂ}
    (hhol : ∀ x ∈ V, HolomorphicAt n f x)
    (hzero : ∀ x ∈ W, x ∈ V → f x = 0) :
    ∀ x ∈ V, (vanishingIdeal (n := n) C).mem x f := by
  intro x hxV
  refine ⟨hhol x hxV, ?_⟩
  filter_upwards [hV.mem_nhds hxV] with y hyV hyC
  exact hzero y (hCW hyC) hyV

/-- The actual extended quotient of an equation vanishing on `W` is zero
on the geometric strict transform, when `W` contains the centre. -/
theorem ratio_eq_zero_of_mem_geoStrictTransform (c : FlatChart n C)
    {W V : Set X} (hCW : C ⊆ W) (hV : IsOpen V) {f : X → ℂ}
    (hhol : ∀ x ∈ V, HolomorphicAt n f x)
    (hzero : ∀ x ∈ W, x ∈ V → f x = 0)
    {p : BlowupSpace n C}
    (hp : p ∈ geoStrictTransform (blowupProj n C) C W)
    (hps : p ∈ c.source) (hpV : p.base ∈ V) :
    c.ratio f (c.toFun p) = 0 := by
  have hfC := mem_centreIdeal_on_open hCW hV hhol hzero
  have hptV : c.pt (c.toFun p) ∈ V := by
    rw [c.pt_toFun hps]
    exact hpV
  have hratio : ContinuousAt (fun q : BlowupSpace n C => c.ratio f (c.toFun q)) p :=
    ((c.differentiableAt_ratio hfC hV (c.map_source hps) hptV).continuousAt).comp
      (show ContinuousAt c.toFun p from c.homeo.continuousAt hps)
  let B : Set (BlowupSpace n C) := (blowupProj n C) ⁻¹' (W \ C)
  let l : Filter (BlowupSpace n C) := 𝓝[B] p
  have : l.NeBot := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hlim : Tendsto (fun q : BlowupSpace n C => c.ratio f (c.toFun q))
      l (𝓝 (c.ratio f (c.toFun p))) :=
    hratio.tendsto.mono_left nhdsWithin_le_nhds
  have hB : ∀ᶠ q in l, q ∈ B := self_mem_nhdsWithin
  have hsource : ∀ᶠ q in l, q ∈ c.source :=
    nhdsWithin_le_nhds (c.isOpen_source.mem_nhds hps)
  have hbase : ∀ᶠ q in l, q.base ∈ V :=
    nhdsWithin_le_nhds
      ((continuous_blowupProj (n := n) (C := C)).continuousAt.preimage_mem_nhds
        (hV.mem_nhds hpV))
  have heq : (fun q : BlowupSpace n C => c.ratio f (c.toFun q)) =ᶠ[l]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hB, hsource, hbase] with q hqB hqSource hqV
    have hqNotC : q.base ∉ C := hqB.2
    have hqj : c.toFun q c.j ≠ 0 := fun hj =>
      hqNotC ((c.toFun_j_eq_zero_iff hqSource).mp hj)
    rw [c.ratio_of_ne (c.map_source hqSource) hqj, c.pt_toFun hqSource,
      hzero q.base hqB.1 hqV, zero_div]
  exact tendsto_nhds_unique hlim
    (Filter.Tendsto.congr' heq.symm tendsto_const_nhds)

/-- At an exceptional point of the actual geometric strict transform, a
qualified holomorphic equation kills the actual native normal direction. -/
theorem germDiff_normalVec_eq_zero_of_mem_geoStrictTransform (c : FlatChart n C)
    {W V : Set X} (hCW : C ⊆ W) (hV : IsOpen V) {f : X → ℂ}
    (hhol : ∀ x ∈ V, HolomorphicAt n f x)
    (hzero : ∀ x ∈ W, x ∈ V → f x = 0)
    {p : BlowupSpace n C}
    (hp : p ∈ geoStrictTransform (blowupProj n C) C W)
    (hps : p ∈ c.source) (hpV : p.base ∈ V) (hpC : p.base ∈ C) :
    germDiff n f p.base (flatVec c.Φ p.base (c.normalVec (c.toFun p))) = 0 := by
  have hfc : (vanishingIdeal (n := n) C).mem (c.pt (c.toFun p)) f := by
    rw [c.pt_toFun hps]
    exact mem_centreIdeal_on_open hCW hV hhol hzero _ hpV
  have hr := c.ratio_of_eq (c.map_source hps)
    ((c.toFun_j_eq_zero_iff hps).mpr hpC) hfc
  rw [c.pt_toFun hps] at hr
  exact hr.symm.trans
    (ratio_eq_zero_of_mem_geoStrictTransform c hCW hV hhol hzero hp hps hpV)

/-- The actual normal direction at an exceptional point of the geometric
strict transform belongs to the original set's common-kernel tangent space. -/
theorem normal_direction_mem_tangentSpace_of_mem_geoStrictTransform (c : FlatChart n C)
    {W : Set X} (hCW : C ⊆ W) {p : BlowupSpace n C}
    (hp : p ∈ geoStrictTransform (blowupProj n C) C W)
    (hps : p ∈ c.source) (hpC : p.base ∈ C) :
    flatVec c.Φ p.base (c.normalVec (c.toFun p)) ∈ tangentSpace n W p.base := by
  apply mem_tangentSpace.mpr
  intro f hfW
  obtain ⟨V, hVsub, hV, hpV⟩ :=
    mem_nhds_iff.mp (hfW.1.eventually.and hfW.2)
  exact germDiff_normalVec_eq_zero_of_mem_geoStrictTransform c hCW hV
    (fun x hx => (hVsub hx).1) (fun x hxW hxV => (hVsub hxV).2 hxW)
    hp hps hpV hpC

end

end Hironaka.HironakaG8GeneralCentreStrictTangent
