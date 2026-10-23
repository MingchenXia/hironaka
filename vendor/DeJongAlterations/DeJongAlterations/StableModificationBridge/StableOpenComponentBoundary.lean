import DeJongAlterations.StableModification.Global.StableOpenStatement
import Mathlib.AlgebraicGeometry.Noetherian

/-! Actual original component intersections from the corrected no-contracted-clopen hypothesis.
The finite-complement argument is adapted from the repository's native Hironaka
Resolution/Algebraic/Kol07/Thm36/Identification.lean component-openness proof.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenComponentBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A fixed ORIGINAL component disjoint from all the others is actually open. -/
theorem isClopen_of_component_disjoint {T : Type*} [TopologicalSpace T] [NoetherianSpace T]
    (Z : Set T) (hZ : Z ∈ irreducibleComponents T)
    (h : ∀ W ∈ irreducibleComponents T, W ≠ Z → ¬ (Z ∩ W).Nonempty) : IsClopen Z := by
  let D : Set (Set T) := {W | W ∈ irreducibleComponents T ∧ W ≠ Z}
  have hfin : D.Finite := NoetherianSpace.finite_irreducibleComponents.subset fun W hW => hW.1
  have hclosed : IsClosed (⋃ W ∈ D, W) :=
    hfin.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
  have heq : Z = (⋃ W ∈ D, W)ᶜ := by
    ext x
    constructor
    · intro hx hmem
      obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp hmem
      exact h W hW.1 hW.2 ⟨x, hx, hxW⟩
    · intro hx
      by_cases hcomp : irreducibleComponent x = Z
      · rw [← hcomp]
        exact mem_irreducibleComponent
      · exact False.elim (hx (Set.mem_iUnion₂.mpr ⟨irreducibleComponent x,
          ⟨irreducibleComponent_mem_irreducibleComponents x, hcomp⟩, mem_irreducibleComponent⟩))
  exact ⟨isClosed_of_mem_irreducibleComponents Z hZ, heq ▸ hclosed.isOpen_compl⟩

/-- The ACTUAL no-contracted-clopen condition forces each contracted native component
to meet ANOTHER native original component. -/
theorem contracted_component_meets_another {X C S : Scheme.{u}}
    (β : X ⟶ C) (g : C ⟶ S) {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    [NoetherianSpace (pullback (C := Scheme.{u}) (β ≫ g) a)]
    (hno : StableModification.Global.NoContractedClopen β g a)
    (Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hZ : Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hcon : (StableModification.Curves.pullbackCompMap β g a '' Z).Subsingleton) :
    ∃ W ∈ irreducibleComponents (pullback (C := Scheme.{u}) (β ≫ g) a),
      W ≠ Z ∧ (Z ∩ W).Nonempty := by
  by_contra hn
  push Not at hn
  have hclopen := isClopen_of_component_disjoint Z hZ (fun W hW hne => by
    rw [hn W hW hne]
    exact Set.not_nonempty_empty)
  exact hno Z hclopen hZ.1.1 hcon

/-- ORIGINAL proper finite-type family geometry derives the Noetherian fibre internally;
no boundary point or stability-open certificate is supplied. -/
theorem contracted_geometric_component_meets_another {X C S : Scheme.{u}}
    (β : X ⟶ C) (g : C ⟶ S) [IsProper (β ≫ g)]
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    (hno : StableModification.Global.NoContractedClopen β g a)
    (Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hZ : Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hcon : (StableModification.Curves.pullbackCompMap β g a '' Z).Subsingleton) :
    ∃ W ∈ irreducibleComponents (pullback (C := Scheme.{u}) (β ≫ g) a),
      W ≠ Z ∧ (Z ∩ W).Nonempty := by
  let f := pullback.snd (β ≫ g) a
  let : IsLocallyNoetherian (pullback (C := Scheme.{u}) (β ≫ g) a) :=
    LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) a) :=
    QuasiCompact.compactSpace_of_compactSpace f
  let : AlgebraicGeometry.IsNoetherian (pullback (C := Scheme.{u}) (β ≫ g) a) := ⟨⟩
  exact contracted_component_meets_another β g a hno Z hZ hcon

end DeJongAlterations.StableModificationBridge.StableOpenComponentBoundary
