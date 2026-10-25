import DeJongAlterations.Geometry.CurveCompactificationRestriction

/-!
# The actual open inverse lift through a finite modification

Normality identifies the whole preimage of the given open, and its inverse
constructs the requested actual open immersion over the original target.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.CurveCompactification

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X B C : Scheme.{u}}

/-- A normal nonempty open actually lifts through a finite modification;
the constructed immersion has the original target triangle and dense image. -/
theorem exists_open_lift_of_finite_modification
    (f : B ⟶ C) [hf : IsModification f] [IsFinite f]
    (j : X ⟶ C) [IsOpenImmersion j] [Nonempty X] (hn : IsNormalScheme X) :
    ∃ i : X ⟶ B, IsOpenImmersion i ∧ IsDominant i ∧ i ≫ f = j := by
  let := hf.sourceIntegral
  let U := j.opensRange
  let e : X ≅ U.toScheme := j.isoOpensRange
  let : Nonempty U := ⟨e.hom (Classical.choice inferInstance)⟩
  have hnU : IsNormalScheme U.toScheme := isNormalScheme_of_isOpenImmersion e.inv hn
  let : IsIso (f ∣_ U) := finite_modification_restrict_isIso f U hnU
  let i : X ⟶ B := e.hom ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  let : IsOpenImmersion i := by dsimp only [i]; infer_instance
  have heq : i ≫ f = j := by
    dsimp only [i]
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι,
      IsIso.inv_hom_id_assoc]
    exact j.isoOpensRange_hom_ι
  have hd : IsDominant i := ⟨i.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty i)⟩
  exact ⟨i, inferInstance, hd, heq⟩

end DeJongAlterations.Geometry.CurveCompactification
