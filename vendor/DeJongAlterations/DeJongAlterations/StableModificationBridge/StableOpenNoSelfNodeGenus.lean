import DeJongAlterations.StableModificationBridge.StableOpenBoundaryBranches
import DeJongAlterations.StableModificationBridge.StableOpenFiniteUnramifiedImmersion
import DeJongAlterations.StableModification.Omega.ComponentNormalizationUnramified
import DeJongAlterations.StableModification.BlowDown.ExcSpecializeGenus
import DeJongAlterations.StableModification.BlowDown.StabilityTop

/-! The SAME original reduced nodal component and native normalization agree without self-nodes. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenNoSelfNodeGenus

open StableModification
open CurvesField.Genus Omega.ComponentNormalization BlowDown.ClosureComponent Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from Y))]
    [Finite (genericPoints Y)] [IsReduced Y] {k : Type u} [Field k] [IsAlgClosed k]
    (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    (hN : Curves.IsNodalFiber q) (v : Y) (hv : v ∈ genericPoints Y)
    (hother : ∀ z ∈ closure {v}, IsClosed ({z} : Set Y) →
      Geometry.IsGeometricOrdinaryDoublePoint q z →
      ∃ w ∈ genericPoints Y, w ≠ v ∧ z ∈ closure {w})

include hN hv hother

/-- The actual native normalization is internally identified with the SAME reduced component,
with the ENTIRE original normalization triangle; no normality/iso/genus certificate is supplied. -/
theorem exists_normalization_iso_reduced_component :
    ∃ e : normalizationPoints ({v} : Set Y) ≅ closureScheme v,
      e.hom ≫ closureι v = normalizationPointsMap ({v} : Set Y) := by
  have hdim : topologicalKrullDim Y ≤ 1 :=
    BlowDown.topologicalKrullDim_le_one_of_forall_irreducibleComponents
      fun Z hZ => (hN.pure Z hZ).le
  have hgen : ∀ z : Y, IsClosed ({z} : Set Y) → z ∉ genericPoints Y :=
    fun z hz => BlowDown.not_mem_genericPoints_of_isClosed hN.pure hz
  have hnodes : ∀ z : Y, IsClosed ({z} : Set Y) →
      z ∈ q.smoothLocus ∨ Geometry.IsGeometricOrdinaryDoublePoint q z := by
    intro z hz
    exact (hN.nodes z hz).imp_left (DeJong.isSmoothAt_iff_mem_smoothLocus q z).mp
  let π := normalizationPointsMap ({v} : Set Y)
  have : IsFinite π := isFinite_normalizationPointsMap (S := ({v} : Set Y)) q
  have : FormallyUnramified π :=
    formallyUnramified_normalizationPointsMap_singleton q hdim hgen hnodes hv
  have hcard : ∀ z : Y, IsClosed ({z} : Set Y) → z ∈ closure {v} → branchCount v z = 1 := by
    intro z hzc hzv
    rcases hN.nodes z hzc with hsm | hnode
    · have htotal := natCard_fiber_eq_one_of_isSmoothAt q hdim z hzc (hgen z hzc) hsm
      rw [natCard_fiber_eq_sum_of_eq q (genericPoints Y) (genericFinset Y)
        coe_genericFinset.symm z] at htotal
      have hle : branchCount v z ≤ ∑ t ∈ genericFinset Y, branchCount t z :=
        Finset.single_le_sum (f := fun t => branchCount t z)
          (fun _ _ => Nat.zero_le _) (mem_genericFinset.mpr hv)
      have hpos := Nat.pos_of_ne_zero ((branchCount_ne_zero_iff q v z).mpr hzv)
      omega
    · obtain ⟨w, hw, hne, hzw⟩ := hother z hzv hzc hnode
      exact StableOpenBoundaryBranches.branchCount_eq_one_of_meets_other q hdim z hzc
        (hgen z hzc) hnode hv hzv hw hne.symm hzw
  have : IsClosedImmersion π := by
    apply StableOpenFiniteUnramifiedImmersion.closedImmersion_of_closedPoint_injective π q
    intro x y hx _hy hxy
    have hzc : IsClosed ({π x} : Set Y) :=
      Curves.isClosed_image_of_isClosed (q := π ≫ q) (q' := q) π rfl hx
    have hbranch := hcard (π x) hzc (normalizationPointsMap_mem_closure v x)
    have hsub := (Nat.card_eq_one_iff_unique.mp hbranch).1
    exact congrArg Subtype.val (@Subsingleton.elim _ hsub
      (⟨x, rfl⟩ : ↥(π ⁻¹' {π x})) (⟨y, hxy.symm⟩ : ↥(π ⁻¹' {π x})))
  have hker : (closureι v).ker = π.ker := ker_eq_of_range_eq (closureι v) π (by
    rw [range_closureι, range_normalizationPointsMap])
  have : IsIso (IsClosedImmersion.lift (closureι v) π hker.le) :=
    IsClosedImmersion.isIso_lift (closureι v) π hker
  exact ⟨asIso (IsClosedImmersion.lift (closureι v) π hker.le), IsClosedImmersion.lift_fac _ _ _⟩

/-- Arithmetic genus of the SAME reduced original component equals its native normalized genus;
the original coefficient comparison is proved from the entire original isomorphism triangle. -/
theorem arithmeticGenus_eq_componentGenus [CompactSpace Y] :
    arithmeticGenus (closureScheme v) (structureCoeff (closureι v ≫ q)) =
      componentGenus (structureCoeff q) v := by
  obtain ⟨e, he⟩ := exists_normalization_iso_reduced_component q hN v hv hother
  have : CompactSpace (normalizationPoints ({v} : Set Y)) :=
    compactSpace_of_isAffineHom (normalizationPointsMap ({v} : Set Y))
  have : IsAffineHom (pullback.diagonal
      (terminal.from (normalizationPoints ({v} : Set Y)))) :=
    isAffineHom_diagonal_of_isAffineHom (normalizationPointsMap ({v} : Set Y))
  have hχ := BlowDown.eulerChar_eq_of_iso (normalizationPointsMap ({v} : Set Y) ≫ q)
    (closureι v ≫ q) e (by rw [← Category.assoc, he])
  unfold componentGenus arithmeticGenus
  rw [← BlowDown.ExcSpecialize.structureCoeff_comp q (normalizationPointsMap ({v} : Set Y)), hχ]

end DeJongAlterations.StableModificationBridge.StableOpenNoSelfNodeGenus
