import DeJongAlterations.StableModification.CurvesField.StableDownGeometricGraph

/-! Actual original component branch counts at original ordinary double points. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenBoundaryBranches

open StableModification.CurvesField.Genus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from Y))]
    [Finite (genericPoints Y)] [IsReduced Y] {k : Type u} [Field k]
    (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    (hdim : topologicalKrullDim Y ≤ 1) (z : Y) (hzc : IsClosed {z})
    (hzg : z ∉ genericPoints Y) (hnode : Geometry.IsGeometricOrdinaryDoublePoint q z)
    {v : Y} (hv : v ∈ genericPoints Y) (hzv : z ∈ closure {v})

include q hdim hzc hzg hnode hv hzv

/-- Two different ORIGINAL components through the ORIGINAL node each carry one actual branch. -/
theorem branchCount_eq_one_of_meets_other {w : Y} (hw : w ∈ genericPoints Y)
    (hne : v ≠ w) (hzw : z ∈ closure {w}) : branchCount v z = 1 := by
  classical
  have htotal := natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint q hdim z hzc hzg hnode
  rw [natCard_fiber_eq_sum_of_eq q (genericPoints Y) (genericFinset Y)
    coe_genericFinset.symm z] at htotal
  have hsub : ({v, w} : Finset Y) ⊆ genericFinset Y := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact mem_genericFinset.mpr hv
    · exact Finset.mem_singleton.mp ht ▸ mem_genericFinset.mpr hw
  have hle : (∑ t ∈ ({v, w} : Finset Y), branchCount t z) ≤
      ∑ t ∈ genericFinset Y, branchCount t z :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_pair hne] at hle
  have hpv := Nat.pos_of_ne_zero ((branchCount_ne_zero_iff q v z).mpr hzv)
  have hpw := Nat.pos_of_ne_zero ((branchCount_ne_zero_iff q w z).mpr hzw)
  omega

omit hzv in
/-- With no other ORIGINAL component at the node, its SAME component has two actual branches. -/
theorem branchCount_eq_two_of_no_other
    (hother : ∀ w ∈ genericPoints Y, w ≠ v → z ∉ closure {w}) : branchCount v z = 2 := by
  classical
  have htotal := natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint q hdim z hzc hzg hnode
  rw [natCard_fiber_eq_sum_of_eq q (genericPoints Y) (genericFinset Y)
    coe_genericFinset.symm z] at htotal
  have hzero : ∀ w ∈ genericFinset Y, w ≠ v → branchCount w z = 0 := by
    intro w hw hne
    by_contra h
    exact hother w (mem_genericFinset.mp hw) hne ((branchCount_ne_zero_iff q w z).mp h)
  rw [Finset.sum_eq_single v hzero (fun h => (h (mem_genericFinset.mpr hv)).elim)] at htotal
  exact htotal

end DeJongAlterations.StableModificationBridge.StableOpenBoundaryBranches
