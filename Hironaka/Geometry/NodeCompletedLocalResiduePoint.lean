import Hironaka.Geometry.NodeCompletedLocalGeometricChart
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! The actual geometric point selected by a prescribed ORIGINAL point-residue embedding.
Both entire original projection maps and its actual base coefficient action are retained. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.NodeCompletedLocalResiduePoint

open NodeCompletedLocalGeometricChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
  (L : Type u) [Field L] [Algebra (X.residueField x) L]

/-- The unique point of the ACTUAL chosen field spectrum. -/
def fieldPoint : Spec (.of L) := ⟨⊥, inferInstance⟩

/-- The ACTUAL source point map determined by the prescribed original residue embedding. -/
def sourcePointMap : Spec (.of L) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) L)) ≫ X.fromSpecResidueField x

/-- Its SAME actual original composite base-field map. -/
def selectedBaseMap : Spec (.of L) ⟶ S := sourcePointMap x L ≫ f

/-- The literal ACTUAL geometric fibre for this original residue embedding. -/
abbrev SelectedFiber := pullback f (selectedBaseMap f x L)

/-- The prescribed residue embedding gives an actual section of this SAME geometric fibre. -/
def selectedSection : Spec (.of L) ⟶ SelectedFiber f x L :=
  pullback.lift (sourcePointMap x L) (𝟙 _) (by simp [selectedBaseMap])

/-- The WHOLE source projection is the SAME original residue-point map. -/
theorem selectedSection_source :
    selectedSection f x L ≫ pullback.fst f (selectedBaseMap f x L) = sourcePointMap x L :=
  pullback.lift_fst _ _ _

/-- The WHOLE field projection is the identity on the ACTUAL prescribed field. -/
theorem selectedSection_field :
    selectedSection f x L ≫ pullback.snd f (selectedBaseMap f x L) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- EVERY original field-point representative has the SAME ORIGINAL source image. -/
theorem sourcePointMap_apply (t : Spec (.of L)) : sourcePointMap x L t = x := by
  change X.fromSpecResidueField x
    ((Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) L))) t) = x
  exact Scheme.fromSpecResidueField_apply x _

/-- The chosen actual point, with no arbitrary point-existence certificate. -/
def selectedPoint : SelectedFiber f x L := selectedSection f x L (fieldPoint L)

/-- Its ACTUAL geometric source projection is the ORIGINAL x. -/
theorem selectedPoint_source :
    pullback.fst f (selectedBaseMap f x L) (selectedPoint f x L) = x := by
  have h := congrArg (fun g : Spec (.of L) ⟶ X => g (fieldPoint L))
    (selectedSection_source f x L)
  change pullback.fst f (selectedBaseMap f x L) (selectedPoint f x L) =
    sourcePointMap x L (fieldPoint L) at h
  exact h.trans (sourcePointMap_apply x L _)

/-- The original base residue action is the prescribed WHOLE residue-map composite. -/
@[instance_reducible]
def originalBaseAlgebra : Algebra (S.residueField (f x)) L :=
  ((algebraMap (X.residueField x) L).comp (f.residueFieldMap x).hom).toAlgebra

/-- The ENTIRE selected base morphism is the canonical ORIGINAL geometric coefficient map. -/
theorem selectedBaseMap_eq_originalFieldMap :
    letI := originalBaseAlgebra f x L
    selectedBaseMap f x L = originalFieldMap (f x) L := by
  let := originalBaseAlgebra f x L
  unfold selectedBaseMap sourcePointMap originalFieldMap
  rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField x, ← Category.assoc,
    ← Spec.map_comp]
  rfl

variable [IsSeparated f]

/-- The SAME selected section is a closed immersion in the original separated application. -/
theorem selectedSection_isClosedImmersion : IsClosedImmersion (selectedSection f x L) := by
  let : IsSeparated (pullback.snd f (selectedBaseMap f x L)) := inferInstance
  let : IsClosedImmersion
      (selectedSection f x L ≫ pullback.snd f (selectedBaseMap f x L)) := by
    rw [selectedSection_field]
    infer_instance
  exact IsClosedImmersion.of_comp (selectedSection f x L) (pullback.snd f (selectedBaseMap f x L))

/-- The SAME actual selected geometric point is closed, with no closure certificate input. -/
theorem selectedPoint_isClosed : IsClosed ({selectedPoint f x L} : Set (SelectedFiber f x L)) := by
  let := selectedSection_isClosedImmersion f x L
  have hr : Set.range (selectedSection f x L) = {selectedPoint f x L} := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      change selectedSection f x L t = selectedSection f x L (fieldPoint L)
      exact congrArg (selectedSection f x L) (Subsingleton.elim t (fieldPoint L))
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨fieldPoint L, rfl⟩
  rw [← hr]
  exact (selectedSection f x L).isClosedEmbedding.isClosed_range

end Hironaka.Geometry.NodeCompletedLocalResiduePoint
