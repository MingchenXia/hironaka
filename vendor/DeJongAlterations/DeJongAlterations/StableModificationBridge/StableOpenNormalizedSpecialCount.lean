import DeJongAlterations.StableModificationBridge.StableOpenNoSelfNodeGenus
import DeJongAlterations.StableModificationBridge.StableOpenSpecialBoundary
import DeJongAlterations.StableModification.Omega.ComponentDegree

/-! Original numerical stability internally produces three actual normalized special preimages. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenNormalizedSpecialCount

open StableModification
open CurvesField.Genus Omega.ComponentNormalization Omega.ComponentDegree Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Three ACTUAL special preimages on the SAME native normalized rational contracted component,
from original native stability and corrected contraction geometry alone. -/
theorem three_le_encard_preimage_specialPoints {X C S : Scheme.{u}}
    (β : X ⟶ C) (g : C ⟶ S) [DeJong.IsNodalCurve (β ≫ g)] [IsProper (β ≫ g)]
    (D' : X.IdealSheafData) {K : Type u} [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S)
    [CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) a)]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) (β ≫ g) a)))]
    (hnum : Global.NumericallyStableFibre β g D' a)
    (hno : Global.NoContractedClopen β g a)
    (v : pullback (C := Scheme.{u}) (β ≫ g) a)
    (hv : v ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hcon : (Curves.pullbackCompMap β g a '' closure {v}).Subsingleton)
    (hg : componentGenus (structureCoeff (pullback.snd (β ≫ g) a)) v = 0) :
    3 ≤ (normalizationPointsMap ({v} : Set (pullback (C := Scheme.{u}) (β ≫ g) a)) ⁻¹'
      Global.specialPoints β g D' a).encard := by
  classical
  let Y := pullback (C := Scheme.{u}) (β ≫ g) a
  let q := pullback.snd (β ≫ g) a
  let π := normalizationPointsMap ({v} : Set Y)
  let T := Global.specialPoints β g D' a
  have : Finite (genericPoints Y) := finite_genericPoints q
  have : IsReduced Y := DeJong.IsNodalCurve.isReduced_pullback (β ≫ g) K a
  have hN : Curves.IsNodalFiber q := Curves.IsNodalCurve.isNodalFiber (β ≫ g) K a
  have hdim := topologicalKrullDim_fibre_le_one (β ≫ g) a
  have : IsSeparated (terminal.from Y) := by
    rw [← terminal.comp_from q]
    infer_instance
  by_cases hother : ∀ z ∈ closure {v}, IsClosed ({z} : Set Y) →
      Geometry.IsGeometricOrdinaryDoublePoint q z →
      ∃ w ∈ genericPoints Y, w ≠ v ∧ z ∈ closure {w}
  · have hpa := StableOpenNoSelfNodeGenus.arithmeticGenus_eq_componentGenus q hN v hv hother
    rw [hg] at hpa
    have : IsSeparated (terminal.from (BlowDown.ClosureComponent.closureScheme v)) := by
      rw [← terminal.comp_from (BlowDown.ClosureComponent.closureι v)]
      infer_instance
    have h3 := @hnum (closure {v}) hv hcon
      (BlowDown.ClosureComponent.compactSpace_closureScheme v)
      (inferInstanceAs (IsSeparated (terminal.from (BlowDown.ClosureComponent.closureScheme v)))) hpa
    have himage : π '' (π ⁻¹' T) = closure {v} ∩ T := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨normalizationPointsMap_mem_closure v y, hy⟩
      · rintro ⟨hx, hs⟩
        rw [← range_normalizationPointsMap] at hx
        obtain ⟨y, rfl⟩ := hx
        exact ⟨y, hs, rfl⟩
    change 3 ≤ (π ⁻¹' T).encard
    change 3 ≤ (closure {v} ∩ T).encard at h3
    rw [← himage] at h3
    exact h3.trans (Set.encard_image_le π (π ⁻¹' T))
  · obtain ⟨z, hzv, hzc, hnode, hzother⟩ : ∃ z : Y, z ∈ closure {v} ∧
        IsClosed ({z} : Set Y) ∧ Geometry.IsGeometricOrdinaryDoublePoint q z ∧
        ¬ ∃ w ∈ genericPoints Y, w ≠ v ∧ z ∈ closure {w} := by
      simpa only [not_forall, exists_prop] using hother
    have hself : ∀ w ∈ genericPoints Y, w ≠ v → z ∉ closure {w} :=
      fun w hw hne hzw => hzother ⟨w, hw, hne, hzw⟩
    have hzg : z ∉ genericPoints Y := not_mem_genericPoints_fibre (β ≫ g) a hzc
    have hb2 := StableOpenBoundaryBranches.branchCount_eq_two_of_no_other q hdim z hzc hzg
      hnode hv hself
    have hzT : z ∈ T := Or.inr (by
      intro hsm
      have h1 := natCard_fiber_eq_one_of_isSmoothAt q hdim z hzc hzg hsm
      have h2 := natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint q hdim z hzc hzg hnode
      omega)
    obtain ⟨W, hW, hne, x, hx, _hns, hxT⟩ :=
      StableOpenSpecialBoundary.contracted_component_has_special_point β g D' a hno
        (closure {v}) hv hcon
    obtain ⟨w, hw⟩ := QuasiSober.sober hW.prop (isClosed_of_mem_irreducibleComponents W hW)
    have hwg : w ∈ genericPoints Y := by
      change closure {w} ∈ irreducibleComponents Y
      rw [hw.def]
      exact hW
    have hwv : w ≠ v := by
      intro h
      apply hne
      rw [← hw.def, h]
    have hxz : x ≠ z := by
      intro h
      apply hself w hwg hwv
      rw [hw.def, ← h]
      exact hx.2
    obtain ⟨y, hy⟩ : x ∈ Set.range π := by
      rw [range_normalizationPointsMap]
      exact hx.1
    change Nat.card ↥(π ⁻¹' {z}) = 2 at hb2
    obtain ⟨b₁, b₂, hbne, _⟩ := Nat.card_eq_two_iff.mp hb2
    have hbne' : b₁.1 ≠ b₂.1 := fun h => hbne (Subtype.ext h)
    have hb₁y : b₁.1 ≠ y := by
      intro h
      have heq := congrArg π h
      rw [b₁.2, hy] at heq
      exact hxz heq.symm
    have hb₂y : b₂.1 ≠ y := by
      intro h
      have heq := congrArg π h
      rw [b₂.2, hy] at heq
      exact hxz heq.symm
    let A : Finset (normalizationPoints ({v} : Set Y)) := {b₁.1, b₂.1, y}
    have hA : A.card = 3 := by simp [A, hbne', hb₁y, hb₂y]
    have hsub : (A : Set (normalizationPoints ({v} : Set Y))) ⊆ π ⁻¹' T := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · change π b₁.1 ∈ T
        rw [b₁.2]
        exact hzT
      · rcases Finset.mem_insert.mp ht with rfl | ht
        · change π b₂.1 ∈ T
          rw [b₂.2]
          exact hzT
        · have ht' : t = y := Finset.mem_singleton.mp ht
          rw [ht']
          change π y ∈ T
          rw [hy]
          exact hxT
    change 3 ≤ (π ⁻¹' T).encard
    calc (3 : ℕ∞) = (A : Set (normalizationPoints ({v} : Set Y))).encard := by simp [hA]
         _ ≤ (π ⁻¹' T).encard := Set.encard_le_encard hsub

end DeJongAlterations.StableModificationBridge.StableOpenNormalizedSpecialCount
