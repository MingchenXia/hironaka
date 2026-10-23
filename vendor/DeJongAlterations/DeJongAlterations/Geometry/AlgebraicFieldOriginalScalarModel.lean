import DeJongAlterations.Geometry.AlgebraicFieldFiniteModel

/-! The ORIGINAL scheme has its literal native scalar model at EVERY actual finite field level. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlgebraicFieldOriginalScalarModel

open StableModification.Limits AlgebraicFieldFiniteModel

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (i : Index k L)

/-- The SAME actual original scalar scheme maps canonically to its actual finite-field scalar scheme. -/
def scalarLift : pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶
    pullback p (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i)))) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (levelField k L i).val.toRingHom)) (by
      rw [Category.assoc, levelField_coefficient_triangle]
      exact pullback.condition)

/-- The WHOLE actual original X projection is retained. -/
theorem scalarLift_fst : scalarLift k L p i ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The WHOLE actual original finite-field coefficient projection is retained. -/
theorem scalarLift_snd : scalarLift k L p i ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (levelField k L i).val.toRingHom) :=
  pullback.lift_snd _ _ _

/-- The ORIGINAL scheme gives its SAME literal original finite-field model, with native Cartesian square. -/
def originalModel : Model (diagram k L) (scalarCone k L)
    (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) i where
  Y := pullback p (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i))))
  fY := pullback.snd _ _
  g := scalarLift k L p i
  isPullback := by
    rw [scalarCone_π]
    refine IsPullback.of_right ?_ (scalarLift_snd k L p i) (IsPullback.of_hasPullback _ _)
    rw [scalarLift_fst, levelField_coefficient_triangle]
    exact IsPullback.of_hasPullback _ _

/-- Original finite presentation proves native FP of EVERY SAME literal scalar model. -/
theorem originalModel_isFP [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p] :
    (originalModel k L p i).IsFP := by
  dsimp only [Model.IsFP, originalModel]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Every ENTIRE actual finite-level coefficient triangle fixes the original k structure. -/
theorem diagram_map_coefficient {i j : Index k L} (h : j ⟶ i) :
    (diagram k L).map h ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j))) := by
  change Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h.unop.le).toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  rfl

/-- The SAME fixed original scalar model remains the actual scalar pullback at every further level. -/
theorem originalModel_baseChange_isPullback {i j : Index k L} (h : j ⟶ i) :
    IsPullback
      (pullback.fst (originalModel k L p i).fY ((diagram k L).map h) ≫
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i)))))
      ((originalModel k L p i).baseChange h).fY p
      (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j)))) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i)))
  have H := (IsPullback.of_hasPullback (pullback.snd p c) ((diagram k L).map h)).paste_horiz
    (IsPullback.of_hasPullback p c)
  change IsPullback _ _ p ((diagram k L).map h ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i)))) at H
  rw [diagram_map_coefficient] at H
  exact H

end DeJongAlterations.Geometry.AlgebraicFieldOriginalScalarModel
