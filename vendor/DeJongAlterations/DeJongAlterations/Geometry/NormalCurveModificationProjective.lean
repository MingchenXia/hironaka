import DeJongAlterations.Geometry.NormalCurveModification
import DeJongAlterations.Geometry.ProjectiveReduction
import DeJongAlterations.Geometry.ProjectiveIdentity

/-!
# Actual projectivity of proper normal curves

The genuine projective Chow modification is an isomorphism over a normal
curve. Transporting its actual closed projective embedding proves projectivity
of the original structure morphism, over arbitrary ground fields.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.NormalCurveModification

universe u

/-- Every normal variety of dimension at most one has an actual projective
immersion over its original field, obtained from the native Chow modification. -/
theorem isQuasiProjectiveOver_of_normal_curve
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 1) :
    IsQuasiProjectiveOver p := by
  obtain ⟨Y, π, hπ, _, hp⟩ := ChowLemma.exists_quasiProjective_modification p
  let := hπ
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsIso π := isIso_of_isModification π hnormal hdim
  obtain ⟨n, e, he, hbase⟩ := hp
  let := he
  refine ⟨n, inv π ≫ e, inferInstance, ?_⟩
  rw [Category.assoc, hbase, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- Every proper normal variety of dimension at most one is genuinely
projective over its original field. No projective model is supplied. -/
theorem isProjectiveOver_of_isProper_normal_curve
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p] [IsProper p]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 1) :
    IsProjectiveOver p := by
  obtain ⟨Y, π, hπ, _, hp⟩ := ProjectiveReduction.exists_projective_modification_of_isProper p
  let := hπ
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsIso π := isIso_of_isModification π hnormal hdim
  have H := hp.precomp_isIso (inv π)
  simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] using H

end DeJongAlterations.Geometry.NormalCurveModification
