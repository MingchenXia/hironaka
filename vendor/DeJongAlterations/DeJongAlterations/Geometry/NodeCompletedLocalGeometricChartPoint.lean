import DeJongAlterations.Geometry.NodeCompletedLocalGeometricChartCompletion
import DeJongAlterations.Algebra.NodeFittingOmegaStalk

/-! An ORIGINAL affine source/base chart and actual geometric-chart point through EVERY
SAME actual original geometric point, constructed internally without finiteness assumptions. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.NodeCompletedLocalGeometricChartPoint

open Algebra.NodeFittingOmegaCharts NodeCompletedLocalGeometricChart
  NodeCompletedLocalGeometricChartCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
  (K : Type u) [Field K] [Algebra (S.residueField s) K]

/-- The ACTUAL original geometric coefficient map has precisely its original base point. -/
theorem originalFieldMap_apply (t : Spec (.of K)) : originalFieldMap s K t = s := by
  have ht : S.fromSpecResidueField s
      ((Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K))) t) ∈
      Set.range (S.fromSpecResidueField s) := Set.mem_range_self _
  rw [Scheme.range_fromSpecResidueField] at ht
  exact ht

/-- The ORIGINAL source image of the SAME actual geometric point lies above ORIGINAL s. -/
theorem originalProjection_basePoint (y : OriginalGeometricScheme f s K) :
    f (pullback.fst f (originalFieldMap s K) y) = s := by
  have h := congrArg (fun p : OriginalGeometricScheme f s K ⟶ S => p y)
    (pullback.condition (f := f) (g := originalFieldMap s K))
  change f (pullback.fst f (originalFieldMap s K) y) =
    originalFieldMap s K (pullback.snd f (originalFieldMap s K) y) at h
  exact h.trans (originalFieldMap_apply s K _)

/-- Membership of the ORIGINAL base point in this SAME original chart is internally derived. -/
theorem originalBase_mem (C : Chart f) (y : OriginalGeometricScheme f s K)
    (hx : pullback.fst f (originalFieldMap s K) y ∈ C.source.1) : s ∈ C.base.1 := by
  have h := C.le_preimage hx
  change f (pullback.fst f (originalFieldMap s K) y) ∈ C.base.1 at h
  rwa [originalProjection_basePoint] at h

/-- EVERY actual original geometric point admits an internally chosen ORIGINAL source/base
chart and an ACTUAL point of its actual affine geometric pullback above the SAME point. -/
theorem exists_originalChartPoint (y : OriginalGeometricScheme f s K) :
    ∃ (C : Chart f) (hs : s ∈ C.base.1) (z : ChartScheme f C s hs K),
      chartMap f C s hs K z = y := by
  obtain ⟨C, hx⟩ := Algebra.NodeFittingOmegaStalk.exists_chart_mem f
    (pullback.fst f (originalFieldMap s K) y)
  let hs := originalBase_mem f s K C y hx
  obtain ⟨z, hz, -⟩ := existsUnique_chartPoint f C s hs K y hx
  exact ⟨C, hs, z, hz⟩

end DeJongAlterations.Geometry.NodeCompletedLocalGeometricChartPoint
