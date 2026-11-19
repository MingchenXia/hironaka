import Hironaka.Resolution.Algebraic.ActualIntrinsicComponentDimensions

/-!
# Actual global dimension-separation ideal and its open restrictions

Source-first proof: `actual-global-dimension-separation-ideal-20261102.tex`.
The ideal is constructed from actual global closed components; finite
generation and exact open compatibility are derived internally.  Its exact
affine identification and global resolution histories remain separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalDimensionSeparationIdeal

noncomputable section
open ActualIntrinsicComponentDimensions

variable (X : Scheme.{u}) [NoetherianSpace X]

def complementaryClosed (d : WithBot ℕ∞) : Closeds X :=
  ⟨⋃ C : irreducibleComponents X, ⋃ (_ : componentDimension C ≠ d), C.val, by
    have : Finite (irreducibleComponents X) :=
      NoetherianSpace.finite_irreducibleComponents.to_subtype
    exact isClosed_iUnion_of_finite fun C => isClosed_iUnion_of_finite fun _ =>
      (componentClosed C).isClosed⟩

theorem mem_complementaryClosed (d : WithBot ℕ∞) (x : X) :
    x ∈ complementaryClosed X d ↔
      ∃ C : irreducibleComponents X, componentDimension C ≠ d ∧ x ∈ C.val := by
  simp only [complementaryClosed, Closeds.mem_mk, Set.mem_iUnion, exists_prop]

def separationIdeal : X.IdealSheafData :=
  ⨆ d : WithBot ℕ∞, Scheme.IdealSheafData.vanishingIdeal (complementaryClosed X d)

theorem separationIdeal_finitelyGenerated [IsLocallyNoetherian X] (U : X.affineOpens) :
    ((separationIdeal X).ideal U).FG := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  exact IsNoetherian.noetherian _

theorem complementaryClosed_eq_top_of_absent (d : WithBot ℕ∞)
    (hd : d ∉ Set.range (componentDimension (X := X))) :
    complementaryClosed X d = ⊤ := by
  apply top_le_iff.mp
  intro x _
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  apply (mem_complementaryClosed X d x).mpr
  exact ⟨C, fun h => hd ⟨C, h⟩, mem_irreducibleComponent⟩

theorem separationIdeal_eq_finite_sum [IsReduced X] :
    separationIdeal X = ⨆ d : dimensionIndex X,
      Scheme.IdealSheafData.vanishingIdeal (complementaryClosed X d.val) := by
  unfold separationIdeal
  apply le_antisymm
  · apply iSup_le
    intro d
    by_cases hd : d ∈ Set.range (componentDimension (X := X))
    · exact le_iSup_of_le ⟨d, hd⟩ le_rfl
    · rw [complementaryClosed_eq_top_of_absent X d hd,
        Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
      exact bot_le
  · exact iSup_le fun d => le_iSup_of_le d.val le_rfl

variable {X} {Y Z : Scheme.{u}} [NoetherianSpace Y] [NoetherianSpace Z]

theorem complementaryClosed_preimage {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsOpenImmersion j] (d : WithBot ℕ∞) :
    (complementaryClosed X d).preimage j.continuous = complementaryClosed Y d := by
  ext y
  change j y ∈ complementaryClosed X d ↔ y ∈ complementaryClosed Y d
  rw [mem_complementaryClosed, mem_complementaryClosed]
  constructor
  · rintro ⟨C, hC, hy⟩
    let hmeet : (C.val ∩ Set.range j).Nonempty := ⟨j y, hy, y, rfl⟩
    refine ⟨componentRestrict j C hmeet, ?_, hy⟩
    exact fun h => hC ((componentDimension_restrict p j C hmeet).symm.trans h)
  · rintro ⟨D, hD, hy⟩
    obtain ⟨C, hmeet, rfl⟩ := componentRestrict_surjective j D
    refine ⟨C, ?_, hy⟩
    exact fun h => hD ((componentDimension_restrict p j C hmeet).trans h)

theorem separationIdeal_open {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsOpenImmersion j] :
    (separationIdeal X).comap j = separationIdeal Y := by
  unfold separationIdeal
  rw [(Scheme.IdealSheafData.map_gc j).l_iSup]
  congr 1
  funext d
  rw [Hironaka.Smooth.comap_vanishingIdeal_of_smooth,
    complementaryClosed_preimage p j]

theorem separationIdeal_open_composite {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (j : Y ⟶ X) [IsOpenImmersion j] (i : Z ⟶ Y) [IsOpenImmersion i] :
    ((separationIdeal X).comap j).comap i = separationIdeal Z ∧
      (separationIdeal X).comap (i ≫ j) = separationIdeal Z := by
  constructor
  · rw [separationIdeal_open p j, separationIdeal_open (j ≫ p) i]
  · exact separationIdeal_open p (i ≫ j)

end
end Hironaka.Resolution.Algebraic.ActualGlobalDimensionSeparationIdeal
