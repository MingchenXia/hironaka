import DeJongAlterations.StableModificationBridge.StableOpenComponentBoundary
import DeJongAlterations.Geometry.RegularSmooth
import DeJongAlterations.Algebra.RegularLocalDomain

/-! Actual external component boundary points are native original nonsmooth/special points. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenSpecialBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ACTUAL domain stalk forces uniqueness of the ORIGINAL component through its point. -/
theorem components_eq_of_isDomain_stalk {X : Scheme.{u}} (x : X)
    [IsDomain (X.presheaf.stalk x)] (Z W : Set X)
    (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X)
    (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W := by
  have hI : IsIrreducible (Set.range (X.fromSpecStalk x)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image
        (X.fromSpecStalk x) (X.fromSpecStalk x).continuous.continuousOn
  have hZG := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  have hWG := hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  have hz : hZ.1.genericPoint ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hZG.specializes hxZ
  have hw : hW.1.genericPoint ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hWG.specializes hxW
  have hZle : Z ⊆ closure (Set.range (X.fromSpecStalk x)) := by
    rw [← hZG.def]
    exact closure_mono (Set.singleton_subset_iff.mpr hz)
  have hWle : W ⊆ closure (Set.range (X.fromSpecStalk x)) := by
    rw [← hWG.def]
    exact closure_mono (Set.singleton_subset_iff.mpr hw)
  exact Set.Subset.antisymm (hZle.trans (hW.2 hI.closure hWle))
    (hWle.trans (hZ.2 hI.closure hZle))

/-- An ACTUAL intersection of distinct ORIGINAL components is outside the SAME original smooth locus. -/
theorem component_intersection_not_smooth {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation p] (Z W : Set X)
    (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X) (hne : W ≠ Z)
    (x : X) (hxZ : x ∈ Z) (hxW : x ∈ W) : x ∉ p.smoothLocus := by
  intro hsm
  let : IsRegularLocalRing (X.presheaf.stalk x) :=
    Geometry.RegularSmooth.isRegularLocalRing_of_mem_smoothLocus p x hsm
  let : IsDomain (X.presheaf.stalk x) :=
    Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  exact hne (components_eq_of_isDomain_stalk x Z W hZ hW hxZ hxW).symm

/-- ONLY original corrected contraction geometry constructs an ACTUAL original special point. -/
theorem contracted_component_has_special_point {X C S : Scheme.{u}}
    (β : X ⟶ C) (g : C ⟶ S) [IsProper (β ≫ g)] [LocallyOfFinitePresentation (β ≫ g)]
    (D' : X.IdealSheafData) {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    (hno : StableModification.Global.NoContractedClopen β g a)
    (Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hZ : Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hcon : (StableModification.Curves.pullbackCompMap β g a '' Z).Subsingleton) :
    ∃ W ∈ irreducibleComponents (pullback (C := Scheme.{u}) (β ≫ g) a), W ≠ Z ∧
      ∃ x ∈ Z ∩ W, x ∉ (pullback.snd (β ≫ g) a).smoothLocus ∧
        x ∈ StableModification.Global.specialPoints β g D' a := by
  obtain ⟨W, hW, hne, x, hxZ, hxW⟩ :=
    StableOpenComponentBoundary.contracted_geometric_component_meets_another β g a hno Z hZ hcon
  have hns := component_intersection_not_smooth (pullback.snd (β ≫ g) a) Z W hZ hW hne x hxZ hxW
  refine ⟨W, hW, hne, x, ⟨hxZ, hxW⟩, hns, Or.inr ?_⟩
  intro hs
  exact hns ((StableModification.DeJong.isSmoothAt_iff_mem_smoothLocus _ _).mp hs)

end DeJongAlterations.StableModificationBridge.StableOpenSpecialBoundary
