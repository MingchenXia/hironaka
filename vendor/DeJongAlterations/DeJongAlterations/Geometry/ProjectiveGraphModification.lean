import DeJongAlterations.Geometry.ProjectiveCompactification
import DeJongAlterations.Geometry.ModificationCenterBirational
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual projective graph modifications

The actual schematic closure of the graph of a projective-valued map on
an open subscheme. Its proper projection and internally constructed native
partial isomorphism give a genuine modification. This is one indeterminacy
elimination producer toward source 4.6, not a quasi-projectivity or Chow theorem.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ProjectiveGraphModification

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {n : ℕ}
    (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens)
    (f : U.toScheme ⟶ projectiveSpace R n)
    (hf : f ≫ projectiveSpaceStructure R n = U.ι ≫ p)

/-- The actual graph of the given map on the actual open subscheme. -/
def graph : U.toScheme ⟶ pullback p (projectiveSpaceStructure R n) :=
  pullback.lift U.ι f hf.symm

@[reassoc (attr := simp)]
theorem graph_fst : graph p U f hf ≫ pullback.fst _ _ = U.ι := by
  simp [graph]

@[reassoc (attr := simp)]
theorem graph_snd : graph p U f hf ≫ pullback.snd _ _ = f := by
  simp [graph]

instance graph_isImmersion : IsImmersion (graph p U f hf) := by
  have : IsImmersion (graph p U f hf ≫ pullback.fst _ _) := by
    rw [graph_fst]
    infer_instance
  exact IsImmersion.of_comp _ (pullback.fst _ _)

instance graph_isQuasiCompact [QuasiCompact U.ι] : QuasiCompact (graph p U f hf) := by
  have : QuasiCompact (graph p U f hf ≫ pullback.fst _ _) := by
    rw [graph_fst]
    infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst _ _)

/-- The actual kernel closed subscheme of the graph in the native product. -/
def modification : Scheme.{u} := (graph p U f hf).image

/-- The native factorization of the original open into its graph closure. -/
def inclusion : U.toScheme ⟶ modification p U f hf := (graph p U f hf).toImage

/-- The actual kernel closed immersion of the graph closure into the product. -/
def embedding : modification p U f hf ⟶ pullback p (projectiveSpaceStructure R n) :=
  (graph p U f hf).imageι

/-- The actual modification projection to the original scheme. -/
def projection : modification p U f hf ⟶ X :=
  embedding p U f hf ≫ pullback.fst _ _

/-- The actual everywhere-defined extension of the original projective-valued map. -/
def projectiveMap : modification p U f hf ⟶ projectiveSpace R n :=
  embedding p U f hf ≫ pullback.snd _ _

instance embedding_isClosedImmersion : IsClosedImmersion (embedding p U f hf) := by
  unfold embedding
  infer_instance

instance projection_isProper : IsProper (projection p U f hf) := by
  unfold projection
  infer_instance

instance inclusion_isOpenImmersion [QuasiCompact U.ι] :
    IsOpenImmersion (inclusion p U f hf) := by
  unfold inclusion
  infer_instance

instance inclusion_isDominant [QuasiCompact U.ι] :
    IsDominant (inclusion p U f hf) := by
  unfold inclusion
  infer_instance

@[reassoc (attr := simp)]
theorem inclusion_embedding :
    inclusion p U f hf ≫ embedding p U f hf = graph p U f hf :=
  (graph p U f hf).toImage_imageι

@[reassoc (attr := simp)]
theorem inclusion_projection : inclusion p U f hf ≫ projection p U f hf = U.ι := by
  rw [projection, inclusion_embedding_assoc, graph_fst]

@[reassoc (attr := simp)]
theorem inclusion_projectiveMap : inclusion p U f hf ≫ projectiveMap p U f hf = f := by
  rw [projectiveMap, inclusion_embedding_assoc, graph_snd]

/-- The original coefficient structure is preserved by the actual extension. -/
@[reassoc]
theorem structure_triangle :
    projectiveMap p U f hf ≫ projectiveSpaceStructure R n =
      projection p U f hf ≫ p := by
  unfold projectiveMap projection
  rw [Category.assoc, Category.assoc, pullback.condition]

instance modification_isIntegral [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    IsIntegral (modification p U f hf) :=
  ProjectiveCompactification.image_isIntegral (graph p U f hf)

/-- The actual common open, not a supplied birationality certificate. -/
def partialIso [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    (modification p U f hf).PartialIso X where
  source := (inclusion p U f hf).opensRange
  dense_source := (inclusion p U f hf).denseRange
  target := U
  dense_target := U.isOpen.dense (by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨U.ι x, x.2⟩)
  iso := (inclusion p U f hf).isoOpensRange.symm

/-- The native partial isomorphism is literally compatible with the original base. -/
theorem partialIso_isOver [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    (partialIso p U f hf).IsOver (projection p U f hf) (𝟙 X) := by
  change (inclusion p U f hf).isoOpensRange.inv ≫ U.ι ≫ 𝟙 X =
    (inclusion p U f hf).opensRange.ι ≫ projection p U f hf
  rw [Category.comp_id, ← inclusion_projection p U f hf, ← Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp]

/-- Native birationality is produced from the two actual dense open immersions. -/
theorem projection_birationalOver [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    Scheme.BirationalOver (projection p U f hf) (𝟙 X) :=
  ⟨partialIso p U f hf, partialIso_isOver p U f hf⟩

instance projection_isModification [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    IsModification (projection p U f hf) where
  sourceIntegral := inferInstance
  targetIntegral := inferInstance
  birational := projection_birationalOver p U f hf

/-- The full inverse image of the original open has no extra points or scheme structure. -/
theorem projection_restrict_isIso [QuasiCompact U.ι] [IsIntegral X] [Nonempty U] :
    IsIso (projection p U f hf ∣_ U) :=
  ModificationCenter.isIso_restrict_partialIso_target (projection p U f hf)
    (partialIso p U f hf) (partialIso_isOver p U f hf)

variable {k : Type u} [Field k]

/-- For a variety, the original Noetherian geometry supplies quasi-compactness of its actual open. -/
theorem projection_isModification_of_variety
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p] (U : X.Opens) [Nonempty U]
    {n : ℕ} (f : U.toScheme ⟶ projectiveSpace k n)
    (hf : f ≫ projectiveSpaceStructure k n = U.ι ≫ p) :
    IsModification (projection p U f hf) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  exact projection_isModification p U f hf

/-- The actual graph modification remains a variety over the original field. -/
theorem modification_isVariety
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p] (U : X.Opens) [Nonempty U]
    {n : ℕ} (f : U.toScheme ⟶ projectiveSpace k n)
    (hf : f ≫ projectiveSpaceStructure k n = U.ι ≫ p) :
    IsVariety (projection p U f hf ≫ p) := by
  let : IsModification (projection p U f hf) := projection_isModification_of_variety p U f hf
  let : IsIntegral (modification p U f hf) :=
    (inferInstance : IsModification (projection p U f hf)).sourceIntegral
  exact {}

/-- The bounded indeterminacy-elimination producer, with the actual original open and every structure triangle. -/
theorem exists_projective_graph_modification
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p] (U : X.Opens) [Nonempty U]
    {n : ℕ} (f : U.toScheme ⟶ projectiveSpace k n)
    (hf : f ≫ projectiveSpaceStructure k n = U.ι ≫ p) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (F : Y ⟶ projectiveSpace k n) (j : U.toScheme ⟶ Y),
      IsModification π ∧ IsVariety (π ≫ p) ∧ IsOpenImmersion j ∧ IsDominant j ∧
        j ≫ π = U.ι ∧ j ≫ F = f ∧
        F ≫ projectiveSpaceStructure k n = π ≫ p ∧ IsIso (π ∣_ U) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  exact ⟨modification p U f hf, projection p U f hf, projectiveMap p U f hf,
    inclusion p U f hf, inferInstance, modification_isVariety p U f hf,
    inferInstance, inferInstance, inclusion_projection p U f hf,
    inclusion_projectiveMap p U f hf, structure_triangle p U f hf,
    projection_restrict_isIso p U f hf⟩

end DeJongAlterations.Geometry.ProjectiveGraphModification
