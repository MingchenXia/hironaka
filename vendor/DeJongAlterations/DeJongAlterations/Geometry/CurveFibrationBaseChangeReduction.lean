import DeJongAlterations.Geometry.CurveFibrationBaseChange
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Actual base changes of the whole reduction retain their topology

The original canonical comparison maps are closed immersions and
surjective, and hence actual homeomorphisms. All-fibre geometric
connectedness is transferred through these actual maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S Y Q : Scheme.{u}}

instance reductionι_surjective (f : X ⟶ S) (g : Y ⟶ S) : Surjective (reductionι f g) :=
  ⟨fun z => ⟨⟨z, by trivial⟩, rfl⟩⟩

/-- The actual comparison of arbitrary base changes of the original whole reduction. -/
def reductionBaseChangeMap (f : X ⟶ S) (g : Y ⟶ S) (a : Q ⟶ Y) :
    pullback (reductionι f g ≫ pullback.snd f g) a ⟶ pullback (pullback.snd f g) a :=
  pullback.map _ _ _ _ (reductionι f g) (𝟙 Q) (𝟙 Y) (by simp) (by simp)

/-- The actual comparison is the native base change of the original reduction map. -/
theorem reductionBaseChangeMap_isPullback (f : X ⟶ S) (g : Y ⟶ S) (a : Q ⟶ Y) :
    IsPullback (pullback.fst (reductionι f g ≫ pullback.snd f g) a)
      (reductionBaseChangeMap f g a) (reductionι f g)
      (pullback.fst (pullback.snd f g) a) := by
  refine .of_bot (v₂₁ := pullback.snd (pullback.snd f g) a) (v₂₂ := pullback.snd f g)
    ?_ ?_ (IsPullback.of_hasPullback (pullback.snd f g) a)
  · simpa [reductionBaseChangeMap] using
      (IsPullback.of_hasPullback (reductionι f g ≫ pullback.snd f g) a)
  · simp [reductionBaseChangeMap]

/-- The canonical comparison is genuinely a homeomorphism, after every actual base change. -/
theorem reductionBaseChangeMap_isHomeomorph (f : X ⟶ S) (g : Y ⟶ S) (a : Q ⟶ Y) :
    IsHomeomorph (reductionBaseChangeMap f g a) := by
  let : IsClosedImmersion (reductionBaseChangeMap f g a) :=
    MorphismProperty.of_isPullback (reductionBaseChangeMap_isPullback f g a) inferInstance
  let : Surjective (reductionBaseChangeMap f g a) :=
    MorphismProperty.of_isPullback (reductionBaseChangeMap_isPullback f g a) inferInstance
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(reductionBaseChangeMap f g a).isEmbedding, (reductionBaseChangeMap f g a).surjective⟩

/-- The original whole-reduction projection retains geometric connectedness of every actual fibre. -/
theorem reducedSecond_geometricallyConnected (f : X ⟶ S) [GeometricallyConnected f]
    (g : Y ⟶ S) : GeometricallyConnected (reductionι f g ≫ pullback.snd f g) := by
  constructor
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ a
  let b := reductionBaseChangeMap f g a
  let : ConnectedSpace (pullback (pullback.snd f g) a : Scheme.{u}) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  exact ((reductionBaseChangeMap_isHomeomorph f g a).homeomorph b).connectedSpace_iff.mpr
    inferInstance

/-- Every actual field-valued fibre retains its topological Krull dimension. -/
theorem reducedSecond_fieldFiber_dimension (f : X ⟶ S) (g : Y ⟶ S)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ Y) :
    topologicalKrullDim (pullback (reductionι f g ≫ pullback.snd f g) a : Scheme.{u}) =
      topologicalKrullDim (pullback (pullback.snd f g) a : Scheme.{u}) := by
  exact IsHomeomorph.topologicalKrullDim_eq (reductionBaseChangeMap f g a)
    (reductionBaseChangeMap_isHomeomorph f g a)

end DeJongAlterations.Geometry.CurveFibrationBaseChange
