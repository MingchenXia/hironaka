import Hironaka.Resolution.HironakaG3PairSeparationMeasure
import Hironaka.Resolution.HironakaMixedDimensionalBoundaryFiniteSeparation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3FiniteMixedSeparation
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaG3PairSeparationMeasure HironakaOriginalCanonicalSumSeparation
  HironakaOriginalNCOldStratumStrictEquality HironakaMixedDimensionalBoundaryFiniteSeparation

private theorem pairwise_disjoint_of_empty {k : ℕ} {X : Type*} (F : Fin k → Set X)
    (h : intersectingPairs F = ∅) : ∀ a b, a ≠ b → Disjoint (F a) (F b) := by
  classical
  intro a b hab
  by_contra hnot
  rcases lt_or_gt_of_ne hab with hab' | hab'
  · have hm : (a,b) ∈ intersectingPairs F := by
      simp only [intersectingPairs,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hab',hnot⟩
    rw [h] at hm
    simp at hm
  · have hm : (b,a) ∈ intersectingPairs F := by
      simp only [intersectingPairs,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hab',fun hd => hnot hd.symm⟩
    rw [h] at hm
    simp at hm

/-- A finite well-founded sequence of actual full-boundary test towers
separates all compact irreducible components without erasing any of them. -/
theorem exists_disjoint_compact_subvariety_tower {n k : ℕ} :
    ∀ (m : ℕ) {X : CMfd.{0} n} (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
      (_hCompact : ∀ a, IsCompact (V a).carrier) (_hDim : ∀ a, (V a).dim < n)
      (_hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
      (E : List (Set X)) (_hE : IsSNCDivisor n E)
      (_hBound : (intersectingPairs (fun a => (V a).carrier)).card ≤ m),
      ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y)
        (V' : Fin k → ClosedIrreducibleAnalyticSubvariety n Y),
        IsGeoTestTower (boundaryGeometry E) T ∧
        IsSNCDivisor n (geoTransformAlong (boundaryGeometry E) T).E ∧
        (∀ a, (V' a).carrier = strictTransform n T.proj (V a).carrier) ∧
        (∀ a, (V' a).dim = (V a).dim) ∧
        (∀ a, T.proj '' (V' a).carrier = (V a).carrier) ∧
        (∀ a b, a ≠ b → Disjoint (V' a).carrier (V' b).carrier) := by
  intro m
  induction m with
  | zero =>
    intro X V hCompact hDim hDistinct E hE hBound
    have hEmpty : intersectingPairs (fun a => (V a).carrier) = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hBound)
    refine ⟨X,.refl,V,trivial,hE,?_,?_,?_,pairwise_disjoint_of_empty _ hEmpty⟩
    · intro a
      simp [strictTransform,exceptionalLocus_id,(V a).isClosed_carrier.closure_eq]
    · intro a
      rfl
    · intro a
      simp [BlowupTower.proj]
  | succ m ih =>
    intro X V hCompact hDim hDistinct E hE hBound
    by_cases hEmpty : intersectingPairs (fun a => (V a).carrier) = ∅
    · refine ⟨X,.refl,V,trivial,hE,?_,?_,?_,pairwise_disjoint_of_empty _ hEmpty⟩
      · intro a
        simp [strictTransform,exceptionalLocus_id,(V a).isClosed_carrier.closure_eq]
      · intro a
        rfl
      · intro a
        simp [BlowupTower.proj]
    · obtain ⟨⟨i,j⟩,hij⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      simp only [intersectingPairs,Finset.mem_filter,Finset.mem_univ,true_and] at hij
      obtain ⟨Y,T,V₁,hdom,hcan,hres,hcent,hSNC,hV₁,hDim₁,hCompact₁,hDistinct₁,hProj₁,hdec⟩ :=
        exists_compact_subvariety_pair_decrease V hCompact hDim hDistinct hij.1 hij.2 E hE
      let M := sumMarkedIdeal (V i).carrier (V j).carrier E
      let D := boundaryGeometry E
      let E₁ := (geoTransformAlong D T).E
      have hDT : IsGeoTestTower D T := boundaryGeometry_test M hE T hres.1
      have hEeq : (geoTransformAlong M T).E = E₁ :=
        MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := M) (𝔫 := D) rfl T
      have hSNC₁ : IsSNCDivisor n E₁ := hEeq ▸ hSNC
      have hDim₁' : ∀ a, (V₁ a).dim < n := fun a => (hDim₁ a) ▸ hDim a
      have hBound₁ : (intersectingPairs (fun a => (V₁ a).carrier)).card ≤ m := by omega
      obtain ⟨Z,Q,V₂,hDQ,hSNC₂,hV₂,hDim₂,hProj₂,hDis⟩ :=
        ih V₁ hCompact₁ hDim₁' hDistinct₁ E₁ hSNC₁ hBound₁
      have hCurrent : IsGeoTestTower (geoTransformAlong D T) Q := by
        rw [boundaryGeometry_geoTransformAlong E T]
        exact hDQ
      have hAppend : IsGeoTestTower D (T.append Q) :=
        (isGeoTestTower_append_iff D T Q).mpr ⟨hDT,hCurrent⟩
      have hEnd : (geoTransformAlong D (T.append Q)).E = (geoTransformAlong (boundaryGeometry E₁) Q).E := by
        rw [geoTransformAlong_append,boundaryGeometry_geoTransformAlong E T]
      refine ⟨Z,T.append Q,V₂,hAppend,hEnd ▸ hSNC₂,?_,?_,?_,hDis⟩
      · intro a
        rw [hV₂ a,hV₁ a,BlowupTower.proj_append,
          StrictTransformComposition.strictTransform_comp T.contMDiff_proj Q.contMDiff_proj]
      · intro a
        exact (hDim₂ a).trans (hDim₁ a)
      · intro a
        rw [BlowupTower.proj_append,Set.image_comp,hProj₂ a,hProj₁ a]

/-- Finite compact mixed components admit an actual simultaneous separating
tower, with no supplied schedule or termination bound. -/
theorem exists_finite_compact_mixed_separation {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hCompact : ∀ a, IsCompact (V a).carrier) (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y)
      (V' : Fin k → ClosedIrreducibleAnalyticSubvariety n Y),
      IsGeoTestTower (boundaryGeometry E) T ∧
      IsSNCDivisor n (geoTransformAlong (boundaryGeometry E) T).E ∧
      (∀ a, (V' a).carrier = strictTransform n T.proj (V a).carrier) ∧
      (∀ a, (V' a).dim = (V a).dim) ∧
      (∀ a, T.proj '' (V' a).carrier = (V a).carrier) ∧
      (∀ a b, a ≠ b → Disjoint (V' a).carrier (V' b).carrier) :=
  exists_disjoint_compact_subvariety_tower (intersectingPairs (fun a => (V a).carrier)).card
    V hCompact hDim hDistinct E hE le_rfl

end
end Hironaka.HironakaG3FiniteMixedSeparation
